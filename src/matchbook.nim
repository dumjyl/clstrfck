# how should ctors work. Foo{}, but how to conditionally export them.

# friend pragma
# Bar {.friend: module/path.}

# pure pragma
# {.pure.}, {.pure(bool_expr).}

# inherit macro
# rewrites to a base proc and an upcasting template


#[
dyn macro
   proc render(self: Operator) = ...
   proc render(self: Method) = ...

   proc render(self: Function) {.dyn.} =
   expands to:

   proc render_gensymed(self: Function) {.inline.} =
      match self:
      of Opterator: render(self)
      of Method: render(self)
   proc render(self: Function) =
      render_gensymed(self)
]#

# FIXME: fields pairs must be rewritten
# FIXME: introduce a strictInheritance pramga forr nim
# FIXME: support when stmts
# FIXME: validate that abstract have at least one record sub
# FIXME: validate that no fields are shadowed by children.

import
   macros2,
   matchbook/private/parser,
   std/sequtils

# type structure

# A deterministic mangle is used to avoid a little bookkeeping.
const rand = "_tQ7x3n1pE71aLekQ1xMO"

proc `+`(a: Ident, b: string): Ident = Ident{$a & b}

proc kind_type_name(self: RecordDef): Ident = self.name.ident + "Kind"
proc union_type_name(self: RecordDef): Ident = self.name.ident + "Union" + rand
proc impl_type_name(self: RecordDef): Ident = self.name.ident + "Impl" + rand

proc kind_type(self: RecordDef): TypeDef =
   # Add an enum with a field of the same name for each `record`
   proc rec(typ: EnumTypeDefBody, def: RecordDef) =
      if not def.body.is_abstract:
         typ.add(def.name.ident)
      for sub in def.body.subs:
         typ.rec(sub)
   let typ = EnumTypeDefBody{}
   typ.rec(self)
   if typ.len == 0:
      self.name.ident.error("at least one record is required")
   result = TypeDef{self.kind_type_name, self.name.pub, Pragmas{[Expr(!pure)]}, typ}

proc zero_sized*(self: RecordDef): bool =
   # possibly save a byte.
   if self.body.fields.len > 0:
      return false
   for sub in self.body.subs:
      if not sub.zero_sized:
         return false
   result = true

proc gen(self: RecordDef, types: TypeDefs, stmts: StmtList) =

   proc rec_a(self: RecordDef, types: TypeDefs, stmts: StmtList, first = false) {.nim_call.} =
      # generate the internal type structures.
      # this is complicated by the fact we want to avoid generating zero sized structs.
      let impl_def = ObjectTypeDefBody{}
      for field in self.body.fields:
         impl_def.add(FieldDef{field.name.ident + rand, field.typ})
      if not self.body.subs.all(zero_sized):
         impl_def.add(FieldDef{!union + rand, self.union_type_name})
         let union_def = ObjectTypeDefBody{}
         var i = 0
         for sub in self.body.subs:
            if not sub.zero_sized:
               sub.rec_a(types, stmts)
               union_def.add(FieldDef{!impl + $i + rand, sub.impl_type_name})
               inc(i)
         types.add(TypeDef{self.union_type_name, Pragmas{!union}, union_def})
      types.add(TypeDef{self.impl_type_name, impl_def})

   proc rec_b(
         self: RecordDef,
         types: TypeDefs,
         stmts: StmtList,
         parent: Option[RecordDef]) {.nim_call.} =
      let def = ObjectTypeDefBody{parent.map(x => x.name.ident.AnyIdent)}
      let pragmas = Pragmas{}
      let kind_field_name = Ident{"kind"} + rand
      if parent of None:
         pragmas.add([Expr(!inheritable), !pure, !requires_init])
         def.add(FieldDef{kind_field_name, self.kind_type_name})
         def.add(FieldDef{!impl + rand, self.impl_type_name})
      types.add(TypeDef{self.name.ident, pragmas, def})
      stmts.add_AST:
         func kind*(self: `self.name.ident`): `self.kind_type_name` =
            result = `self.kind_type_name`(self.`kind_field_name`)
      for sub in self.body.subs:
         sub.rec_b(types, stmts, self.some)

   if self.is_simple:
      let obj_def = ObjectTypeDefBody{}
      for field in self.body.fields:
         obj_def.add(FieldDef{field.name.ident, field.name.pub, field.typ})
      types.add(TypeDef{self.name.ident, self.name.pub, self.name.pragmas, obj_def})
   else:
      types.add(self.kind_type)
      self.rec_a(types, stmts, first = true)
      self.rec_b(types, stmts, RecordDef.none)

proc gen(self: OtherDef, types: TypeDefs, stmts: StmtList) =
   # FIXME: pragmas
   types.add(TypeDef{self.name.ident, self.name.pub, self.body})

macro typedef*(type_defs: {StmtList}): {StmtList} {.m2.} =
   var defs = seq[Def].default
   for type_def in type_defs:
      defs.add(Def{type_def.expect(Asgn)})
   let types = TypeDefs{}
   result = StmtList{types}
   for def in defs:
      case def.kind:
      of DefKind.Record: def.record.gen(types, result)
      of DefKind.Other: def.other.gen(types, result)
   echo result
