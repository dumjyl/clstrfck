import
   macros2,
   macros2/checks

# FIXME: error on pub for subs

type
   Name* = object
      exported*: bool
      ident*: Ident
      pragmas*: Pragmas # FIXME: impliment
   RecordField* = object
      name*: Name
      typ*: Expr
   RecordQual* {.pure.} = enum None, Ref, Ptr
   RecordBodyPrefix* = object
      qual*: RecordQual
      is_abstract*: bool
   RecordBody* = object
      prefix*: RecordBodyPrefix
      fields*: seq[RecordField]
      subs*: seq[RecordDef]
   RecordDef* = ref object
      name*: Name
      body*: RecordBody
      parent*: RecordDef
   OtherDef* = ref object
      name*: Name
      body*: Expr
   DefKind* {.pure.} = enum Record, Other
   Def* = object
      case kind*: DefKind:
      of DefKind.Record: rec*: RecordDef
      of DefKind.Other: other*: OtherDef

iterator subs*(self: RecordDef): RecordDef =
   ## Yield direct descendants of `self`.
   for sub in self.body.subs:
      yield sub

iterator fields*(self: RecordDef): RecordField =
   ## Yield the fields of `self`.
   for field in self.body.fields:
      yield field

proc parse(expr: Expr, Self: type[Name]): Self =
   ## Parse a typedef name.
   result = Self(ident: !placeholder, pragmas: Pragmas{})
   var expr = expr
   match expr.is_command_call("pub", 1) as call of Some:
      result.exported = true
      expr = call.args[0]
   match expr as pragma_expr of PragmaExpr:
      result.pragmas = pragma_expr.pragmas
      expr = pragma_expr.expr
   result.ident = expr.expect(Ident)

proc is_abstract(expr: Expr): Option[bool] =
   ## `None` if `expr` is not a record keyword.
   match expr of Ident and (expr == "record" or expr == "abstract"):
      result = some(expr == "abstract")

proc is_field_like(stmt: Stmt): Option[tuple[name: Ident, typ: Expr]] =
   match stmt of Call and stmt.name of Ident and stmt.args.len == 1 and
         stmt.args[0] as stmt_list of StmtList and stmt_list.len == 1 and
         stmt_list[0] as typ of Expr:
      result = some((name: name, typ: typ))

proc parse(expr: Expr, Self: type[RecordBodyPrefix]): Option[Self] =
   ## Try to parse record keywords and ref like annotations.
   match expr:
   of RefTypeExpr, PtrTypeExpr:
      var self = ? expr.val.parse(Self)
      if self.qual == RecordQual.None:
         match expr:
         of RefTypeExpr:
            #self.qual = RecordQual.Ref
            expr.error("FIXME: ptr qualifiers")
         of PtrTypeExpr: self.qual = RecordQual.Ptr
         else: discard
         result = self.some
      else: result = Self.none
   else: result = Self(is_abstract: ? expr.is_abstract).some

proc parse(type_def: Asgn, Self: type[RecordDef]): Option[Self] =
   let expr = type_def.rhs
   match expr of Call and expr.args.len == 1 and expr.args[0] as body of StmtList:
      var rec = Self(name: type_def.lhs.parse(Name),
                     body: RecordBody(prefix: ? expr.name.parse(RecordBodyPrefix)))
      for field_or_sub in body:
         match field_or_sub as sub of Asgn:
            rec.body.subs.add(sub.parse(RecordDef).expect("failed to parse record"))
            rec.body.subs[^1].parent = rec
         elif field_or_sub.is_field_like as field of Some:
            rec.body.fields.add(RecordField(name: Name(ident: field.name), typ: field.typ))
         else:
            field_or_sub.error("failed to parse field")
      result =  rec.some
   else: result = Self(name: type_def.lhs.parse(Name),
                       body: RecordBody(prefix: ? expr.parse(RecordBodyPrefix))).some

proc parse(type_def: Asgn, Self: type[OtherDef]): Self =
   ## Parse an alias type
   result = Self(name: type_def.lhs.parse(Name), body: type_def.rhs)

proc parse*(type_def: Asgn, Self: type[Def]): Self =
   match type_def.parse(RecordDef) as rec of Some:
      result = Self(kind: DefKind.Record, rec: rec)
   else:
      result = Self(kind: DefKind.Other, other: type_def.parse(OtherDef))

proc is_simple*(self: RecordDef): bool =
   result = not self.body.prefix.is_abstract and self.body.subs.len == 0
