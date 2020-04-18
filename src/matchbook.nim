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

import
   macros2,
   macros2/checks,
   mainframe

type
   RecordField = object
      pub: bool
      name: Ident
      pragmas: Pragmas
      typ: Expr
   RecordName = object
      pub: bool
      name: Ident
      pragmas: Pragmas # FIXME: impliment
   # RecordDefKind {.pure.} = enum Object, RefObject, PtrObject
   RecordDef = object
      # kind: RecordDefKind
      is_abstract: bool
      fields: seq[RecordField]
      children: seq[Record]
   Record = ref object
      name: RecordName
      def: RecordDef
   DefKind {.pure.} = enum Record, Other
   Def = object
      case kind: DefKind:
      of DefKind.Record: record: Record
      of DefKind.Other: expr: Expr

proc `{}`(Self: type[RecordName], expr: Expr): Self =
   match expr.is_command_call("pub", 1) as call of Some:
      result = Self(pub: true, name: call.args[0].expect(Ident), pragmas: Pragmas{})
   else:
      result = Self(pub: false, name: expr.expect(Ident), pragmas: Pragmas{})

proc is_record_kw(expr: Expr): bool =
   match expr of Ident and (expr == "record" or expr == "abstract"): result = true

proc is_record_def(expr: Expr): bool =
   match expr of Call and expr.args.len == 1 and expr.args[0] of StmtList:
      match expr.is_record_kw: result = true
      elif expr of ObjectConstr: result = expr.name.is_record_kw

proc `{}`(Self: type[RecordDef], expr: Expr): Self =
   match expr.is_call(["record", "abstract"], 1) as call of Some and call.args[0] of StmtList:
      result = Self(is_abstract: call.name.expect(Ident) == "abstract")
   else:
      dbg expr
      expr.error("FIXME")

proc `{}`(Self: type[Record], type_def: Asgn): Self =
   result = Self(name: RecordName{type_def.lhs}, def: RecordDef{type_def.rhs})

proc gen(self: Record): Stmt =
   result = StmtList{}

proc `{}`(Self: type[DefKind], type_def: Asgn): Self =
   if type_def.rhs.is_record_def: result = Self.Record
   else: result = Self.Other

proc `{}`(Self: type[Def], type_def: Asgn): Self =
   case DefKind{type_def}:
   of DefKind.Record: result = Self(kind: DefKind.Record, record: Record{type_def})
   of DefKind.Other: result = Self(kind: DefKind.Other, expr: Ident{"PLACEHOLDER"})

proc gen(defs: seq[Def]): StmtList =
   result = StmtList{}
   for def in defs:
      case def.kind:
      of DefKind.Record: discard def.record.gen
      of DefKind.Other: fatal("FIXME")

macro typedef*(type_defs: {StmtList}) {.m2.} =
   ## If the toplevel type name is exported with `pub` all derived object are public.
   ## The same rule applies for `ref` and `ptr` annotations.
   var defs = seq[Def].default
   for type_def in type_defs:
      defs.add(Def{type_def.expect(Asgn)})
   result = defs.gen
