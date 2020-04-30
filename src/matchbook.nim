## A closed inheritance library.

# FIXME: friend/acquaintance pragma
#        {.friend.} {.friend: module/path.}

# FIXME: pure pragma
#        {.pure.}, {.pure(bool_expr).}

# FIXME: inherit macro to avoid sigmatch rules
#        rewrites to a base proc and an upcasting template


# FIXME: dyn macro
#        proc render(self: Operator) = ...
#        proc render(self: Method) = ...
#
#        proc render(self: Function) {.dyn.} =
#        expands to:
#
#        proc render_gensymed(self: Function) {.inline.} =
#           match self:
#           of Opterator: render(self)
#           of Method: render(self)
#        proc render(self: Function) =
#           render_gensymed(self)

# FIXME: fields pairs must be rewritten
# FIXME: introduce {.strictInheritance.} for nim
# FIXME: support when stmts
# FIXME: validate that abstract have at least one record sub
# FIXME: validate that no fields are shadowed by children.

import
   macros2,
   matchbook/private/parser,
   std/sequtils
import matchbook/private/matches; export matches

# A deterministic mangle is used to avoid a bit of bookkeeping.
const rand = "_tQ7x3n1pE71aLekQ1xMO"

template `+`(a: Ident, b: string): Ident = Ident{$a & b}
template `+`(a: Ident, b: Ident): Ident = Ident{$a & $b}

template kind_type_name(self: RecordDef): Ident = self.name.ident + "Kind"
template union_type_name(self: RecordDef): Ident = self.name.ident + "_Union" + rand
template impl_type_name(self: RecordDef): Ident = self.name.ident + "_Impl" + rand
template impl_field_name(self: RecordDef): Ident = !impl + "_" + self.name.ident + rand
template union_field_name: Ident = !union + rand
template field_name(self: RecordField): Ident = self.name.ident + rand
template kind_field_name: Ident = !kind + rand

proc zero_sized(self: RecordDef): bool =
   # Possibly save a byte because c++ requires unique addresses, but probaly doesn't matter.
   if self.body.fields.len > 0:
      return false
   for sub in self.body.subs:
      if not sub.zero_sized:
         return false
   result = true

proc with_qual(obj_def: ObjectTDB, base_rec: RecordDef): TDB =
   # Append the proper qualifier for the object definition, inherited from the base.
   case base_rec.body.prefix.qual:
   of RecordQual.Ptr: result = PtrTDB{obj_def}
   of RecordQual.Ref: result = RefTDB{obj_def}
   of RecordQual.None: result = obj_def

proc gen(self: RecordDef, types: TypeDefs, stmts: StmtList) =

   proc enum_kind(self: RecordDef, types: TypeDefs) =
      # Add an enum with a field of the same name for each `record`
      proc rec(typ: EnumTDB, def: RecordDef) =
         if not def.body.prefix.is_abstract:
            typ.add(def.name.ident)
         for sub in def.body.subs:
            typ.rec(sub)
      let typ = EnumTDB{}
      typ.rec(self)
      types.add(TypeDef{self.kind_type_name, self.name.exported, Pragmas{[Expr(!pure)]}, typ})

   proc range_kinds(base: RecordDef, self: RecordDef, types: TypeDefs): seq[Ident] =
      # Add the kind types for the subtypes.
      for sub in self.subs:
         result.add(base.range_kinds(sub, types))
      if not self.body.prefix.is_abstract:
         result.add(self.name.ident)
      if self.parent != nil:
         types.add(TypeDef{self.kind_type_name, self.name.exported,
                           !range[`base.kind_type_name`.`result[0]` ..
                                  `base.kind_type_name`.`result[^1]`]})

   proc rec_a(self: RecordDef, types: TypeDefs, stmts: StmtList, first = false) {.nim_call.} =
      # Generate the internal type structures.
      # Slightly complicated by the fact we want to avoid generating fieldless struct.
      let impl_def = ObjectTDB{}
      for field in self.fields:
         impl_def.add(FieldDef{field.name.ident + rand, field.typ})
      if not self.body.subs.all(zero_sized):
         impl_def.add(FieldDef{!union + rand, self.union_type_name})
         let union_def = ObjectTDB{}
         for sub in self.subs:
            if not sub.zero_sized:
               sub.rec_a(types, stmts)
               union_def.add(FieldDef{sub.impl_field_name, sub.impl_type_name})
         types.add(TypeDef{self.union_type_name, Pragmas{!union}, union_def})
      types.add(TypeDef{self.impl_type_name, impl_def})

   proc rec_b(
         base: RecordDef,
         self: RecordDef,
         types: TypeDefs,
         stmts: StmtList,
         parent: Option[RecordDef]) {.nim_call.} =
      # Generate the exposed inheritance hierarchy types and kind accessors.
      let def = ObjectTDB{parent.map(x => x.name.ident.AnyIdent)}
      let pragmas = Pragmas{}
      if parent of None:
         pragmas.add([Expr(!inheritable), !pure, !requires_init])
         def.add(FieldDef{kind_field_name(), self.kind_type_name})
         def.add(FieldDef{self.impl_field_name, self.impl_type_name})
      types.add(TypeDef{self.name.ident, base.name.exported, pragmas, def.with_qual(base)})
      stmts.add_AST:
         func kind*(self: `self.name.ident`): `self.kind_type_name` =
            result = `self.kind_type_name`(self.`kind_field_name()`)
      for sub in self.subs:
         base.rec_b(sub, types, stmts, self.some)

   proc rec_c(rec_stack: var seq[RecordDef], self: RecordDef) =
      # Generate field accessors.
      let T = self.name.ident
      rec_stack.add(self)
      var fields = Expr(!self)
      for i, rec in rec_stack:
         let union_field_name = !union + rand
         fields = !`fields`.`rec.impl_field_name`
         if i != rec_stack.high:
            fields = !`fields`.`union_field_name`

      for field in self.fields:
         var field_access = !`fields`.`field.field_name`
         let setter_ident = field.name.ident + "="
         stmts.add_AST:
            proc `field.name.ident`(self: `T`): `field.typ` {.used.} =
               `field_access`
            proc `setter_ident`(self: var `T`, val: `field.typ`) {.used.} =
               `field_access` = val
            proc `field.name.ident`(self: var `T`): var `field.typ` {.used.} =
               `field_access`
         stmts[^1].expect(RoutineDecl).exported = field.name.exported
         stmts[^2].expect(RoutineDecl).exported = field.name.exported

      stmts.add_AST:
         # FIXME: perhaps {.error.} should impl {.used.}
         iterator fields(self: `T`): RootObj {.error, used.} = discard
         iterator field_pairs(self: `T`): tuple[key: string, val: RootObj] {.error, used.} =
            discard
         iterator fields(a: `T`, b: `T`): RootObj {.error, used.} = discard
         iterator field_pairs(a: `T`, b: `T`): tuple[key: string, val: RootObj] {.error, used.} =
            discard

      for sub in self.body.subs:
         rec_stack.rec_c(sub)
      discard rec_stack.pop

   proc rec_d(self: RecordDef, stmts: StmtList) =
      # Generate the constructors.
      #[
      see tmatchbook for corresponding hierarchy.
      proc `{}`*(Self: type[SubA], id: int, val: NeedsInit): SubA =
         result = SubA(
            kind: BaseKind.SubA,
            impl_Base: BaseImpl(
               id: id,
               union: BaseUnion(
                  impl_Sub: SubImpl(
                     val: val
                  )
               )
            )
         )
      ]#
      for sub in self.subs:
         sub.rec_d(stmts)
      if not self.body.prefix.is_abstract:
         var records = @[self]
         while records[^1].parent != nil:
            records.add(records[^1].parent)

         var maybe_constr = ObjectConstr.none
         for i, rec in records:
            # skip to the first record in the stack with an impl type
            if rec.zero_sized:
               continue
            # generate the impl ctor with its fields
            let impl_constr = ObjectConstr{rec.impl_type_name}
            for field in rec.fields:
               impl_constr.add(field.field_name, field.name.ident)

            match maybe_constr as constr of Some:
               let union_constr = ObjectConstr{rec.union_type_name}
               union_constr.add(records[i - 1].impl_field_name, constr)
               impl_constr.add(union_field_name, union_constr)
            maybe_constr = impl_constr.some

         let constr = ObjectConstr{self.name.ident}
         constr.add(kind_field_name(), !`records[^1].kind_type_name`.`self.name.ident`)
         match maybe_constr of Some:
            constr.add(records[^1].impl_field_name, maybe_constr)

         let init_fn = ProcDecl{Ident{"{}"},
                                exported = self.name.exported,
                                formals = [IdentDef{!Self, !type[`self.name.ident`]}],
                                return_type = self.name.ident,
                                pragmas = [Expr(!used)],
                                body = constr}
         for rec in records:
            for field in rec.fields:
               init_fn.formals.add(IdentDef{field.name.ident, field.typ})
         stmts.add(init_fn)

   if self.is_simple:
      let obj_def = ObjectTDB{}
      for field in self.fields:
         obj_def.add(FieldDef{field.name.ident, field.name.exported, field.typ})
      types.add(TypeDef{self.name.ident, self.name.exported, self.name.pragmas, obj_def})
      let constr = ObjectConstr{self.name.ident}
      let init_fn = ProcDecl{Ident{"{}"},
                             formals = [IdentDef{!Self, !type[`self.name.ident`]}],
                             return_type = self.name.ident,
                             pragmas = [Expr(!used)],
                             body = constr}
      for field in self.fields:
         init_fn.formals.add(IdentDef{field.name.ident, field.typ})
         constr.add(field.name.ident, field.name.ident)
      stmts.add(init_fn)
   else:
      self.enum_kind(types)
      discard self.range_kinds(self, types)
      self.rec_a(types, stmts, first = true)
      self.rec_b(self, types, stmts, RecordDef.none)
      var rec_stack = seq[RecordDef].default
      rec_stack.rec_c(self)
      self.rec_d(stmts)

proc gen(self: OtherDef, types: TypeDefs, stmts: StmtList) =
   types.add(TypeDef{self.name.ident, self.name.exported, self.name.pragmas, self.body})

macro typedef*(type_defs: {StmtList}): {StmtList} {.m2.} =
   ## `pub`, `ref`, and `ptr` qualifiers get inherited from the base.
   runnable_examples:
      typedef:
         pub MyBase = ref abstract:
            id: int
            Lit = abstract:
               IntLit = record:
                  val: int
               FloatLit = record:
                  val: float
               StrLit = record:
                  val: string
            Container = abstract:
               vals: seq[Lit]
               Set = record
               List = record
   var defs = seq[Def].default
   for type_def in type_defs:
      defs.add(type_def.expect(Asgn).parse(Def))
   let types = TypeDefs{}
   result = StmtList{types}
   for def in defs:
      case def.kind:
      of DefKind.Record: def.rec.gen(types, result)
      of DefKind.Other: def.other.gen(types, result)
   # echo result
