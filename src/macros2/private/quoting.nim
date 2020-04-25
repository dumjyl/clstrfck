func into_ast*(self: NimNode): NimNode = self
func into_ast*(self: Stmt): NimNode = self.detail

proc classify_quote_type(self: Stmt): Expr =
   # handle any possible mutation after quoting here, currently conservative.
   match self:
   of ...[StmtList, AnyCall, Ident]: Ident{$type_of(self)}
   else: Ident{"Stmt"}

proc internal_quote(stmts: Stmt, gensym: bool): StmtList =

   type VisitCtx = ref object
      args: seq[Expr] # arguments to pass to the get_ast call.
      params: seq[Ident] # param names to give the template

   proc add(self: VisitCtx, expr: Expr): Ident =
      self.args.add(Ident{"into_ast"}.call(expr))
      # somewhat hacky, gensyming template params does not work because of a template implimentation detail
      self.params.add(Ident{nskVar.gen.`$` & "_c8bd78kl46hqm9wpf0wnso8n0"})
      result = self.params[^1]

   proc visitor(self: CompoundIdent, ctx: VisitCtx): Stmt =
      result = unsafe_default(Stmt)
      # FIXME: this check is bad for `!{}`; parsed as `Ident"!{}"`
      if self[0] == Ident{"!"}:
         self.delete(0)
         result = self
      else:
         if self.len == 1:
            result = ctx.add(self[0])
         elif self[0] == Ident{"bind"}:
            result = ctx.add(Sym{"{}"}.call(Ident{"typedesc"}.call(Sym{"Sym"}),
                             self[1 .. ^1].join.lit))
         else:
            let expr_str = self.val.join
            try:
               result = ctx.add(Expr{macros.parse_expr(expr_str)})
            except ValueError:
               self.error("failed to parse AST injection expr: '" & expr_str & "'")

   # is this still needed?
   proc sym_visitor(self: Sym, ctx: tuple[]): Stmt = Ident{self.val}

   let ctx = VisitCtx()
   let stmt_stripped = stmts of StmtList and stmts.detail.len == 1
   # FIXME(nim): switch these next two stmts and watch the compiler segfault
   let stmts = CompoundIdent.visit(Sym.visit(stmts, (), sym_visitor), ctx, visitor)
   let typ = stmts.classify_quote_type

   # generate the temporary template
   let templ_sym = TemplateSym{}
   let templ_def = TemplateDecl{templ_sym, return_type = some(Ident{"untyped"}.Expr),
                                pragmas = [Ident{"dirty"}.Expr], body = some(stmts)}
   for param in ctx.params:
      templ_def.formals.add(param, typ = Ident{"untyped"})
   result = StmtList{templ_def}
   template ctor(Self, val): auto = Sym{"{}"}.call(Ident{"typedesc"}.call(Self), val)
   var ast =
      if stmt_stripped: # add back a stmt list.
         ctor(Sym{"StmtList"}, ctor(Sym{"Stmt"}, Sym{"get_ast"}.call(templ_sym.call(ctx.args))))
      else:
         ctor(typ, Sym{"get_ast"}.call(templ_sym.call(ctx.args)))
   result.add(ast)

macro AST*(stmts): untyped = internal_quote(Stmt{stmts}, gensym = false).detail
   ## An untyped quoting operator with some extensions.
   # FIXME: document extensions

macro AST_gensym*(stmts): untyped = internal_quote(Stmt{stmts}, gensym = true).detail
   ## A quoting operator similar to `macros.quote`.

template add_AST*(self, stmts): untyped = add(self, AST(stmts))
   ## Shorthand for `self.add(AST do: stmts)`.

macro `!`*(expr): untyped =
   ## An alias for `AST`, for concise expression generation.
   let expr = Expr{expr}.skip(Paren)
   result = internal_quote(expr, gensym = false).detail
