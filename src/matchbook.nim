# how should ctors work. Foo.init, but how to conditionally export them.

# friend pragma
# Bar {.friend: module/path.}

# pure pragma
# {.pure.}, {.pure(bool_expr).}

# inherit macro
# rewrites to a base proc and an upcasting template

# dyn macro
#[
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

#[
fields pairs must be rewritten
]#

import macros2

type
   RecordField = object
      name: AnyIdent
      pragmas: Pragmas
      typ: Expr
      is_pub: bool
   RecordKind {.pure.} = enum Object, RefObject, PtrObject
   Record = ref object
      pub: bool
      kind: RecordKind
      is_abstract: bool
      pragmas: Pragmas
      fields: seq[RecordField]
      children: seq[Record]
   DefKind {.pure.} = enum Record
   Def = object
      case kind: DefKind:
      of DefKind.Record: record: Record

proc `{}`*(Self: type[Record], type_def: Asgn): Self =
   dbg type_def

proc `{}`*(Self: type[DefKind], type_def: Asgn): Self = Self.Record

proc `{}`*(Self: type[Def], type_def: Asgn): Self =
   case DefKind{type_def}:
   of DefKind.Record: Self(kind: DefKind.Record, record: Record{type_def})

template check_pub(val) {.dirty.} =
   var is_pub {.inject.}: bool
   let val: type_of(val)

macro typedef*(type_defs: {StmtList}) {.m2.} =
   ## If the toplevel type name is exported with `pub` all derived object are public.
   ## The same rule applies for `ref` and `ptr` annotations.
   var defs = seq[Def].default
   for type_def in type_defs:
      defs.add(Def{type_def.expect(Asgn)})
   dbg type_defs
   dbg result
