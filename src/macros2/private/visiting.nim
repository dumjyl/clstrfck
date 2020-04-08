proc visit*[Visit: StmtAllMeta; Ctx](
      _: type[Visit],
      self: Stmt,
      ctx: Ctx,
      fn: proc (self: Visit, ctx: Ctx): Stmt {.nim_call.}
      ): Stmt =
   result = self
   match self of Visit:
      result = fn(self, ctx)
   else:
      template v(x): auto = expect(visit(Visit, x, ctx, fn), type_of(x))
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
            of NoColon: self[i] = f.v
      of ...[StmtList, ChoiceSym, CompoundIdent]:
         for i in 0 ..< self.len:
            self[i] = self[i].v
      of AnyCall:
         self.name = self.name.v
         for i in 0 ..< self.arguments.len:
            self.arguments[i] = self.arguments[i].v
      of ForLoop:
         for i in 0 ..< self.vars.len:
            self.vars[i] = self.vars[i].v
         self.expr = self.expr.v
         self.body = self.body.v
      of ...[Asgn, Dot]:
         self.lhs = self.lhs.v
         self.rhs = self.rhs.v
      of Block:
         # Yuck, because of generic symbol resolution.
         match self.label of Some:
            self.label = self.label.expect.v
         self.body = self.body.v
      of SingleSym, Ident, Lit, Comment, Unexposed: discard # nothing to recurse
      else: self.error("TODO: visit{", self.kind, "}")
