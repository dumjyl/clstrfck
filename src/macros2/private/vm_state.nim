when false:
   import
      core,
      std/macrocache

   func read[T: NimNode](node: NimNode, _: type[T]): T = node

   func write[T: NimNode](val: T): NimNode = val

   func read[T: object](node: NimNode, _: type[T]): T =
      result = T()
      node.expect(nnkPar)
      var i = 0
      for name, result_field in field_pairs(result):
         node[i].expect(nnkExprColonExpr)
         assert(node[i][0].eq_ident(name))
         result_field = read(node[i][1], type_of(result_field))
         inc(i)

   func write[T: object](val: T): NimNode =
      result = nnkPar{}
      for name, val_field in field_pairs(val):
         result.add(nnkExprColonExpr{name, write(val_field)})

   func read[T: ref object](node: NimNode, _: type[T]): T =
      result = if node of nnkNilLit: result = nil else: result = read(node, type_of(default(T)[]))

   func write[T: ref object](val: T): NimNode =
      result = if val == nil: result = !nil else: result = write(val[])

   func read[T](node: NimNode, _: type[seq[T]]): seq[T] =
      node.expect(nnkBracket)
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
         detail(self)[key] = nnkPar{write(val)}
      else:
         detail(self)[key].expect(nnkPar)
         detail(self)[key][0] = write(val)

   iterator pairs*[T](self: GlobalTable[T]): (string, T) =
      for name, val in pairs(detail(self)):
         yield (name, read(val, T))

   type GlobalVar*[T] = object
      name: string

   func detail[T](self: GlobalVar[T]): CacheSeq = CacheSeq(self.name)

   template `{}`*[T](Self: type[GlobalVar[T]], val: T): Self =
      var temp = Self[T](name: $instantiation_info(-1, true))
      add(detail(temp), nnkPar{write(val)})
      temp

   func read*[T](self: GlobalVar[T]): T = read(self.detail[0][0], T)

   func write*[T](self: GlobalVar[T], val: T) = self.detail[0][0] = write(val)
