proc visit[Visit, Ctx](
      self: IdentDef,
      ctx: Ctx,
      visit_fn: proc (self: Visit, ctx: Ctx): Stmt {.nim_call.}) =
   template v(x): auto = expect(visit(Visit, x, ctx, visit_fn), type_of(x))
   self.ident = self.ident.v
   match self.typ of Some:
      self.typ = typ.v
   match self.val of Some:
      self.val = val.v

proc visit*[Visit: Stmt; Ctx](
      _: type[Visit],
      self: Stmt,
      ctx: Ctx,
      visit_fn: proc (self: Visit, ctx: Ctx): Stmt {.nim_call.}
      ): Stmt =
   result = self
   match self of Visit:
      result = visit_fn(self, ctx)
   else:
      template v(x): auto = expect(visit(Visit, x, ctx, visit_fn), type_of(x))
      match self:
      of ExprContainer:
         for i in 0 ..< self.len:
            self[i] = self[i].v
      of Container - ExprContainer:
         match self of ObjectConstr:
            self.name = self.name.v
         for i in 0 ..< self.len:
            match self[i] as f:
            of Colon:
               f.name = f.name.v
               f.val = f.val.v
            of NoColon:
               self[i] = f.v
      of ...[StmtList, ChoiceSym, CompoundIdent]:
         for i in 0 ..< self.len:
            self[i] = self[i].v
      of AnyCall:
         self.name = self.name.v
         for i in 0 ..< self.args.len:
            self.args[i] = self.args[i].v
      of ForLoop:
         for i in 0 ..< self.vars.len:
            self.vars[i] = self.vars[i].v
         self.expr = self.expr.v
         self.body = self.body.v
      of ...[Asgn, Dot]:
         self.lhs = self.lhs.v
         self.rhs = self.rhs.v
      of RoutineDecl:
         self.ident = self.ident.v
         match self.return_type of Some:
            self.return_type = return_type.v
         # FIXME: generic params
         # FIXME: patterns
         # FIXME: pragmas
         for i in 0 ..< self.formals.len:
            visit(self.formals[i], ctx, visit_fn)
         match self.body of Some:
            self.body = body.v
      of Block:
         ## Yuck, because of generic symbol resolution.
         match self.label of Some:
            self.label = label.v
         self.label = self.label.expect.v
         self.body = self.body.v
      of Discard:
         match self.val of Some:
            self.val = val.v
      of QualTypeExpr: self.val = self.val.v
      of TupleTypeExpr:
         for i in 0 ..< self.len:
            visit(self[i], ctx, visit_fn)
      of SingleSym, Ident, Lit, Comment, Unexposed: discard # nothing to recurse
      else: self.error("FIXME: visit{", self.kind, "}")
