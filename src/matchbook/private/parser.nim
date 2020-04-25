import
   macros2,
   macros2/checks

type
   Name* = object
      pub*: bool
      ident*: Ident
      pragmas*: Pragmas # FIXME: impliment
   RecordField* = object
      name*: Name
      typ*: Expr
   RecordBody* = object
      is_abstract*: bool
      fields*: seq[RecordField]
      subs*: seq[RecordDef]
   RecordDef* = ref object
      name*: Name
      body*: RecordBody
   OtherDef* = ref object
      name*: Name
      body*: Expr
   DefKind* {.pure.} = enum Record, Other
   Def* = object
      case kind*: DefKind:
      of DefKind.Record: record*: RecordDef
      of DefKind.Other: other*: OtherDef

proc `{}`(Self: type[Name], expr: Expr): Self =
   match expr.is_command_call("pub", 1) as call of Some:
      result = Self(pub: true, ident: call.args[0].expect(Ident), pragmas: Pragmas{})
   else:
      result = Self(pub: false, ident: expr.expect(Ident), pragmas: Pragmas{})

proc is_record_kw(expr: Expr): bool =
   match expr of Ident and (expr == "record" or expr == "abstract"):
      result = true

proc is_record_body(expr: Expr): bool =
   match expr of Call and expr.args.len == 1 and expr.args[0] of StmtList:
      match expr.name:
      of RefTypeExpr, PtrTypeExpr: result = name.val.is_record_kw
      else: result = name.is_record_kw

proc is_field_like(stmt: Stmt): Option[tuple[name: Ident, typ: Expr]] =
   match stmt of Call and stmt.name of Ident and stmt.args.len == 1 and
         stmt.args[0] as stmt_list of StmtList and stmt_list.len == 1 and
         stmt_list[0] as typ of Expr:
      result = some((name: name, typ: typ))

proc `{}`(Self: type[RecordDef], type_def: Asgn): Self

proc `{}`(Self: type[RecordBody], expr: Expr): Self =
   match expr.is_call(["record", "abstract"], 1) as call of Some and
         call.args[0] as body of StmtList:
      result = Self(is_abstract: call.name.expect(Ident) == "abstract")
      for field_or_sub in body:
         match field_or_sub as sub of Asgn:
            result.subs.add(RecordDef{sub})
         elif field_or_sub.is_field_like as field of Some:
            result.fields.add(RecordField(name: Name(ident: field.name), typ: field.typ))
         else:
            field_or_sub.error("failed to parse field")
   elif expr.is_record_kw:
      result = Self(is_abstract: expr.expect(Ident) == "abstract")
   else:
      expr.error("FIXME")

proc `{}`(Self: type[RecordDef], type_def: Asgn): Self =
   result = Self(name: Name{type_def.lhs}, body: RecordBody{type_def.rhs})

proc `{}`(Self: type[OtherDef], type_def: Asgn): Self =
   result = Self(name: Name{type_def.lhs}, body: type_def.rhs)

proc `{}`(Self: type[DefKind], type_def: Asgn): Self =
   result = if type_def.rhs.is_record_body: Self.Record else: Self.Other

proc `{}`*(Self: type[Def], type_def: Asgn): Self =
   case DefKind{type_def}:
   of DefKind.Record:
      result = Self(kind: DefKind.Record, record: RecordDef{type_def})
   of DefKind.Other:
      result = Self(kind: DefKind.Other, other: OtherDef{type_def})

proc is_simple*(self: RecordDef): bool = not self.body.is_abstract and self.body.subs.len == 0
