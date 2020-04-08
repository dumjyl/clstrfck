## Global state helpers macros.

import
   core,
   std/macrocache

func read[T: NimNode](node: NimNode, _: type[T]): T = node

func write[T: NimNode](val: T): NimNode = val

func read[T: object](node: NimNode, _: type[T]): T =
   result = T()
   node.expect(nnk_par)
   var i = 0
   for name, result_field in field_pairs(result):
      node[i].expect(nnk_expr_colon_expr)
      assert(node[i][0].eq_ident(name))
      result_field = read(node[i][1], type_of(result_field))
      inc(i)

func write[T: object](val: T): NimNode =
   result = nnk_par{}
   for name, val_field in field_pairs(val):
      result.add(nnk_expr_colon_expr{name, write(val_field)})

func read[T: ref object](node: NimNode, _: type[T]): T =
   if node of nnk_nil_lit:
      result = nil
   else:
      result = read(node, type_of(default(T)[]))

func write[T: ref object](val: T): NimNode =
   if val == nil:
      result = !nil
   else:
      result = write(val[])

func read[T](node: NimNode, _: type[seq[T]]): seq[T] =
   node.expect(nnk_bracket)
   for node in node:
      result.add(read(node, T))

func write[T: seq](vals: T): NimNode =
   result = ![]
   for val in vals:
      result.add(write(val))

type GlobalTable*[T] = object
   name: string

func detail[T](self: GlobalTable[T]): CacheTable = CacheTable(self.name)

template `{}`*[T](Self: type[GlobalTable[T]]): Self = Self(name: $instantiation_info(-1, true))

func has_key*[T](self: GlobalTable[T], key: string): bool =
   for tab_key, _ in pairs(detail(self)):
      if key == tab_key:
         return true
   result = false

func `[]`*[T](self: GlobalTable[T], key: string): T =
   result = read(detail(self)[key][0], T)

func `[]=`*[T](self: GlobalTable[T], key: string, val: T) =
   if not has_key(self, key):
      detail(self)[key] = nnk_par{write(val)}
   else:
      detail(self)[key].expect(nnk_par)
      detail(self)[key][0] = write(val)

iterator pairs*[T](self: GlobalTable[T]): (string, T) =
   for name, val in pairs(detail(self)):
      yield (name, read(val, T))

type GlobalVar*[T] = object
   name: string

func detail[T](self: GlobalVar[T]): CacheSeq = CacheSeq(self.name)

template `{}`*[T](Self: type[GlobalVar[T]], val: T): Self =
   var temp = Self[T](name: $instantiation_info(-1, true))
   add(detail(temp), nnk_par{write(val)})
   temp

func read*[T](self: GlobalVar[T]): T =
   result = read(self.detail[0][0], T)

func write*[T](self: GlobalVar[T], val: T) =
   self.detail[0][0] = write(val)