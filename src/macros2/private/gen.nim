import
   mainframe,
   lca_data,
   core,
   std/strutils

type
   MetaKind* {.pure.} = enum
      All
      Sub
      Record
      # Base
      # RecordBase
   IR = ref object
      name: string
      kinds: array[MetaKind, seq[string]]
      subs: seq[IR]

template kind(ir: IR): string = ir.name & "Kind"

iterator items(ir: IR): IR =
   for ir in ir.subs: yield ir

func `{}`(Self: type[IR], n: NimNode): IR =
   if n of nnkIdent:
      result = IR(name: $n)
      result.kinds[All].add(result.name)
      result.kinds[Record].add(result.name)
   elif n of nnkCall and n.len == 2 and n[1] of nnkStmtList:
      result = IR(name: $n[0])
      result.kinds[All].add(result.name)
      for stmt in n[1]:
         result.subs.add(IR{stmt})
         result.kinds[All].add(result.subs[^1].kinds[All])
         result.kinds[Sub].add(result.subs[^1].kinds[All])
         result.kinds[Record].add(result.subs[^1].kinds[Record])
   else: n.error("failed to parse 'generate' declaration")

func add_kind_enum(types: NimNode, ir: IR) =
   types.add(nnkTypeDef{pub_ident(ir.kind, [!pure]), nnkEmpty{}, nnkEnumTy{nnkEmpty{}}})
   for kind in ir.kinds[Record]:
      types[^1][2].add(kind.ident)

func add_inheritance_tree(types: NimNode, ir: IR, inherits: NimNode) =
   let name = ir.name.pub_ident
   let type_sec =
      if inherits == nil:
         AST:
            type `name` {.inheritable, pure, requires_init.} = object
               detail: NimNode
      else:
         AST:
            type `name` = object of `inherits`
   for typ in type_sec:
      types.add(typ)
   if ir.name.ends_with("TypeDefBody"):
      types.add(nnkTypeDef{ir.name.replace("TypeDefBody", "TDB").pub_ident, nnkEmpty{}, ir.name})
   for sub_ir in ir:
      types.add_inheritance_tree(sub_ir, ir.name.ident)

func range_type(name, kind_name, a, b: string): NimNode =
   result = nnkTypeDef{name.pub_ident, nnkEmpty{}, !range[`kind_name.ident`.`a.ident` ..
                                                          `kind_name.ident`.`b.ident`]}

func add_kind_subranges(types: NimNode, ir: IR, base_ir: IR) =
   let kinds = ir.kinds[Record]
   types.add(range_type(ir.kind, base_ir.kind, kinds[0], kinds[^1]))
   for ir in ir:
      types.add_kind_subranges(ir, base_ir)

proc solve_lca(ir: IR, base_ir: IR): NimNode =
   proc rec(ir: IR, base_ir: IR): LCAData =
      var subs = seq[LCAData].default
      var kinds = set[LCAKind].default
      for sub_ir in ir:
         subs.add(rec(sub_ir, base_ir))
         kinds.incl(subs[^1].kinds)
      if ir.subs.len == 0:
         block found_kind:
            for i, kind in base_ir.kinds[Record]:
               if kind == ir.name:
                  kinds.incl(i.LCAKind)
                  break found_kind
            fatal "failed to lookup kind"
      result = LCAData{ir.name, kinds, subs}
   let data = rec(ir, base_ir).lit
   let data_sym = nskLet.gen
   result = AST:
      let `data_sym` {.compile_time.} = `data`
      macro solve_lca(
            Self: type[`base_ir.name.ident`],
            kinds: static[set[`base_ir.kind.ident`]]
            ): auto =
         result = `bind solve`(`data_sym`, kinds)

      # FIXME(nim): when kinds is static, we get the nkRange crash
      template unsafe_lca_subconv(
            self: `base_ir.name.ident`,
            kinds: set[`base_ir.kind.ident`]
            ): auto =
         unsafe_conv(self, solve_lca(`base_ir.name.ident`, kinds))

proc visit*(ir: IR, fn: proc (ir: IR, base_ir: IR): NimNode): NimNode =
   proc rec(stmts: NimNode, ir: IR, base_ir: IR, fn: auto) =
      stmts.add(fn(ir, base_ir))
      for ir in ir:
         stmts.rec(ir, base_ir, fn)
   result = nnkStmtList{}
   result.rec(ir, ir, fn)

proc gen_meta(ir: IR, base_ir: IR): NimNode =
   func typeclass(kinds: seq[string]): NimNode =
      if kinds.len > 0:
         result = kinds[0].ident
         for i in 1 ..< kinds.len:
            result = !typedesc(`result` | `kinds[i].ident`)
      else:
         result = AST: {.fatal: "empty meta typeclass: " & $Self & "; " & $kind .}
   let all = typeclass(ir.kinds[All])
   let sub = typeclass(ir.kinds[Sub])
   let rec = typeclass(ir.kinds[Record])
   result = AST:
      template meta*(Self: type[`ir.name.ident`], kind: static[MetaKind]): auto =
         when kind == All: `all`
         elif kind == Sub: `sub`
         elif kind == Record: `rec`
         else: {.fatal: "unrecognized kind: " & $kind.}

proc gen_kind(ir: IR, base_ir: IR): NimNode =
   result = AST:
      proc kind*(self: `ir.name.ident`): `ir.kind.ident` =
         result = `ir.kind.ident`(`base_ir.kind.ident`{self.detail})

proc gen_kinds_of(ir: IR, base_ir: IR): NimNode =
   let kinds = ir.kinds[Record]
   let kind_name = base_ir.kind.ident
   result = AST:
      # FIXME(nim): this has an nkRange node without a type which is invalid.
      #proc kinds_of*(Self: type[`ir.name.ident`]): set[`kind_name`] =
      #   result = {`kind_name`.`kinds[0].ident` .. `kind_name`.`kinds[^1].ident`}

      proc kinds_of*(Self: type[`ir.name.ident`]): set[`kind_name`] =
         result = {`kind_name`.`kinds[0].ident` .. `kind_name`.`kinds[^1].ident`}

macro generate*(base, derived) =
   let ir = IR{nnkCall{base, derived}}
   let types = nnkTypeSection{}
   result = nnkStmtList{types}
   types.add_kind_enum(ir)
   types.add_inheritance_tree(ir, nil)
   for subs_ir in ir:
      types.add_kind_subranges(subs_ir, ir)
   result.add(solve_lca(ir, ir))

   result.add(ir.visit(gen_meta))
   if base.eq_ident("Stmt"):
      result.add_AST:
         func `!{}`*(Self: type[`ir.kind.ident`], node: NimNode): Self
      result.add(ir.visit(gen_kind))
   result.add(ir.visit(gen_kinds_of))
   result.add_AST:
      proc `!of`*(self: meta(`ir.name.ident`, All), T: type[meta(`ir.name.ident`, All)]): bool =
         self.kind in kinds_of(T)

template impl_expect*(x, y) {.dirty.} =
   proc expect*[X: x; Y: y](self: X, _: type[Y]): Y =
      {.push hint[ConvFromXToItSelfNotNeeded]: off.}
      {.push hint[CondTrue]: off.}
      result = unsafe_default(Y)
      ## Cast `self` to `T` or error fatally.
      if self of Y:
         result = unsafe_conv(self, Y)
      else:
         # FIXME: make this nicer
         when defined(dump_node) and X is Stmt: dbg self
         fatal("expected variant: '", Y, "', got variant: '", self.kind, '\'')
      {.pop.}
      {.pop.}

template idx(x, offset): int =
   when x is BackwardsIndex: self.len - int(x) else: x

template check_bounds*(i, len: int) =
   if i < 0 or i > len:
      raise new_Exception(IndexDefect, format_error_index_bound(i, len))

template impl_field*(T, f, FT; i: untyped = 0) {.dirty.} =
   proc f*(self: T): FT = FT{self.detail[i]}
   proc `f=`*(self: T, val: FT) = self.detail[i] = val.detail

macro impl_items*(T) =
   AST:
      iterator items*(self: `T`): auto =
         for i in 0 ..< self.len:
            yield self[i]

macro impl_slice_index*(T, Val, offset) =
   AST:
      proc `![]`*(self: `T`, i: HSlice): seq[`Val`] =
         let a = `bind idx`(i.a, `offset`)
         let b = `bind idx`(i.b, `offset`)
         `bind check_bounds`(a, self.len)
         `bind check_bounds`(b, self.len)
         for i in a .. b:
            result.add(self[i])

macro impl_container*(Self, Val: untyped, offset: untyped = 0) =
   AST:
      func len*(self: `Self`): int = self.detail.len - `offset`
      proc `![]`*(self: `Self`, i: Index): `Val` =
         let i = `bind idx`(i, `offset`)
         check_bounds(i, self.len)
         result = `Val`{self.detail[i + `offset`]}
      proc `![]=`*(self: `Self`, i: Index, val: `Val`) =
         let i = `bind idx`(i, `offset`)
         check_bounds(i, self.len)
         self.detail[i + `offset`] = val.detail
      impl_items(`Self`)
      impl_slice_index(`Self`, `Val`, `offset`)
