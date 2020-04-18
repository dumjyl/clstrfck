import
   mainframe,
   core,
   lca_data,
   vm_timings

type
   KindsFilter = enum All, Concrete
   IR = ref object
      name: string
      kinds: array[KindsFilter, seq[string]]
      children: seq[IR]

# typeclass that contains all types with an associated kind
template records_typeclass(ir: IR): string = ir.name & "RecordsMeta"

# typeclass that contains all types that are children of a type
template children_typeclass(ir: IR): string = ir.name & "ChildrenMeta"

# like children_typeclass but includes itself too
template all_typeclass(ir: IR): string = ir.name & "AllMeta"

template kind(ir: IR): string = ir.name & "Kind"

iterator items(ir: IR): IR =
   for ir in ir.children:
      yield ir

func `{}`(Self: type[IR], n: NimNode): IR {.time.} =
   result = IR()
   if n of nnkIdent:
      result.name = $n
   elif n of nnkCall and n.len == 2 and n[1] of nnkStmtList:
      result.name = $n[0]
      for stmt in n[1]:
         result.children.add(IR{stmt})
   else: n.error("failed to parse 'gens' declaration")

func calc_kinds(ir: IR, filter: KindsFilter): seq[string] {.time.} =
   if ir.children.len == 0 or filter == All:
      result = @[ir.name]
      ir.kinds[filter].add(result)
   for ir in ir:
      let kinds = ir.calc_kinds(filter)
      result.add(kinds)
      ir.kinds[filter].add(kinds)

func `{}`(Self: type[IR], base, derived: NimNode): IR {.time.} =
   result = IR(name: $base)
   for derived in derived:
      result.children.add(IR{derived})
   result.kinds[All] = result.calc_kinds(All)
   result.kinds[Concrete] = result.calc_kinds(Concrete)

func add_rtti_enum(types: NimNode, ir: IR) {.time.} =
   types.add(nnkTypeDef{pub_ident(ir.kind, [!pure]), nnkEmpty{}, nnkEnumTy{nnkEmpty{}}})
   for kind in ir.kinds[Concrete]:
      types[^1][2].add(kind.ident)

func add_inheritance_tree(types: NimNode, ir: IR, inherits: NimNode) {.time.} =
   let name = ir.name.pub_ident
   let type_sec =
      if inherits == nil:
         when defined(nim_macros2_requires_init) or true:
            AST:
               type `name` {.inheritable, pure, requires_init.} = object
                  detail: NimNode
         else:
            AST:
               type `name` {.inheritable, pure.} = object
                  detail: NimNode
      else:
         AST:
            type `ir.name.pub_ident` = object of `inherits`
   types.add(type_sec[0])
   for child_ir in ir:
      types.add_inheritance_tree(child_ir, ir.name.ident)

func gen_range_type(name, kind_name, a, b: string): NimNode {.time.} =
   result = nnkTypeDef{name.pub_ident, nnkEmpty{}, !range[`kind_name.ident`.`a.ident` ..
                                                          `kind_name.ident`.`b.ident`]}

func add_rtti_ranges(types: NimNode, ir: IR, base_ir: IR) {.time.} =
   let kinds = ir.kinds[Concrete]
   types.add(gen_range_type(ir.kind, base_ir.kind, kinds[0], kinds[^1]))
   for ir in ir:
      types.add_rtti_ranges(ir, base_ir)

func add_typeclass(types: NimNode, name: string, kinds: seq[string]) {.time.} =
   if kinds.len > 0:
      var ident_kinds = seq[NimNode].default
      for kind in kinds:
         ident_kinds.add(kind.ident)
      types.add(nnkTypeDef{name.pub_ident, nnkEmpty{}, ident_kinds.infix_join("|")})

func add_typeclasses(types: NimNode, ir: IR) {.time.} =
   types.add_typeclass(ir.records_typeclass, ir.kinds[Concrete])
   types.add_typeclass(ir.children_typeclass, ir.kinds[All][1 .. ^1])
   types.add_typeclass(ir.all_typeclass, ir.kinds[All])
   for ir in ir:
      types.add_typeclasses(ir)

func add_rtti_range_stmts(stmts: NimNode, ir: IR, base_ir: IR) {.time.} =
   let kinds = ir.kinds[Concrete]
   let kind_name = base_ir.kind.ident
   stmts.add_AST:
      func rtti_range*(T: type[`ir.name.ident`]): set[`kind_name`] =
         result = {`kind_name`.`kinds[0].ident` .. `kind_name`.`kinds[^1].ident`}
   for ir in ir:
      stmts.add_rtti_range_stmts(ir, base_ir)

proc unsafe_downconv(ir: IR, base_ir: IR): NimNode {.time.} =
   proc `{}`(Self: type[LCAData], ir: IR, base_ir: IR): Self {.time.} =
      var children = seq[Self].default
      var kinds = set[LCAKind].default
      for child_ir in ir:
         children.add(LCAData{child_ir, base_ir})
         kinds.incl(children[^1].kinds)
      if ir.children.len == 0:
         block found_kind:
            for i, kind in base_ir.kinds[Concrete]:
               if kind == ir.name:
                  kinds.incl(i.LCAKind)
                  break found_kind
            fatal "failed to lookup kind"
      result = LCAData{ir.name, kinds, children}
   let data = LCAData{ir, base_ir}.lit
   result = AST:
      import macros2/private/lca_data
      {.push hint[ConvFromXtoItselfNotNeeded]: off.}
      func `!{}`*(Self: type[LCAData], _: type[`base_ir.name.ident`]): Self = `data`

func add_of_stmts(stmts: NimNode, ir: IR, base_ir: IR) {.time.} =
   stmts.add_AST:
      proc `!of`*(self: `base_ir.name.ident`, Self: type[`ir.name.ident`]): bool =
         result = self.kind.ord in `ir.kind.ident`.low.ord .. `ir.kind.ident`.high.ord
   for ir in ir:
      stmts.add_of_stmts(ir, base_ir)

func add_kind_stmts(stmts: NimNode, ir: IR, base_ir: IR) {.time.} =
   stmts.add_AST:
      proc kind(self: `ir.name.ident`): `ir.kind.ident` =
         result = `ir.kind.ident`(`base_ir.name.ident`(self).kind)
   for ir in ir:
      stmts.add_kind_stmts(ir, base_ir)

macro generate*(base, derived) {.time.} =
   let ir = IR{base, derived}
   let types = nnkTypeSection{}
   result = nnkStmtList{types}
   types.add_rtti_enum(ir)
   types.add_inheritance_tree(ir, nil)
   for child_ir in ir:
      types.add_rtti_ranges(child_ir, ir)
   types.add_typeclasses(ir)
   result.add_rtti_range_stmts(ir, ir)
   result.add(unsafe_downconv(ir, ir))
   result.add_of_stmts(ir, ir)
   result.add_AST:
      proc kind*(self: `ir.name.ident`): `ir.kind.ident`
   for child_ir in ir:
      result.add_kind_stmts(child_ir, ir)


template impl_expect*(x, y) {.dirty.} =
   proc expect*[X: x; Y: y](self: X, _: type[Y]): Y {.time.} =
      {.push hint[ConvFromXToItSelfNotNeeded]: off.}
      result = unsafe_default(Y)
      ## Cast `self` to `T` or error fatally.
      if self of Y: result = unsafe_conv(self, Y)
      else:
         # FIXME: make this nicer
         when defined(dump_node) and X is Stmt: dbg self
         fatal("expected variant: '", Y, "', got variant: '", self.kind, '\'')
      {.pop.}

template impl_field*(T, f, FT, i) {.dirty.} =
   proc f*(self: T): FT = FT{self.detail[i]}
   proc `f=`*(self: T, val: FT) = self.detail[i] = val.detail

template impl_items*(T) {.dirty.} =
   iterator items*(self: T): auto =
      for i in 0 ..< self.len:
         yield self[i]

template impl_slice_index*(T, Val) {.dirty.} =
   proc `[]`*(self: T, i: HSlice): seq[Val] =
      template idx(x): int =
         when x is BackwardsIndex: self.len - int(x) else: int(x)
      for i in idx(i.a) .. idx(i.b):
         result.add(self[i])

macro impl_container*(Self, Val: untyped, offset: untyped = 0) =
   result = AST:
      func len*(self: `Self`): int = self.detail.len - `offset`
      proc `![]`*(self: `Self`, i: Index): `Val` = `Val`{self.detail[i + `offset`]}
      proc `![]=`*(self: `Self`, i: Index, val: `Val`) = self.detail[i + `offset`] = val.detail
      impl_items(`Self`)
      impl_slice_index(`Self`, `Val`)
