import pkg/mainframe
from std/strutils import join, indent

template dbg_repr_flair(self): string = self.`$`.bright_yellow

template list(stmts) =
   result.add("{\n")
   stmts
   result.add("}")

template `<<`(val: string) = result.add val.indent(2) & '\n'

template `<<`(vals: openarray[string]) = result.add(vals.join)

template dbg_eq(a, b): auto = a & " = " & b

proc dbg_repr*(self: ForLoopVars): string =
   result = dbg_repr_flair("ForLoopVars")
   list:
      for for_var in self:
         << for_var.dbg_repr

proc dbg_repr*(self: MaybeColon): string =
   match self:
   of Colon:
      result = dbg_repr_flair("Colon")
      list:
         << self.name.dbg_repr
         << self.val.dbg_repr
   of NoColon:
      result = self.dbg_repr

proc dbg_repr*(self: IdentDef): string =
   result = dbg_repr_flair("IdentDef")
   list:
      << "name".dbg_eq(self.ident.dbg_repr)
      match self.typ of Some:
         << "typ".dbg_eq(typ.dbg_repr)
      match self.val of Some:
         << "val".dbg_eq(val.dbg_repr)

template qdbg(x): string =
   var y = string.default
   y.add_quoted(x)
   y

proc dbg_repr*(self: Pragmas): string =
   result = dbg_repr_flair("Pragmas")
   list:
      for pragma in self:
         << pragma.dbg_repr

proc dbg_repr*(self: AnyVarDef): string =
   match self:
   of IdentVarDef: result = self.dbg_repr
   of UnpackVarDef:
      result = dbg_repr_flair("Pragmas")
      for ident in self:
         << "var".dbg_eq(ident.dbg_repr)
      match self.typ of Some:
         << "typ".dbg_eq(typ.dbg_repr)
      match self.val of Some:
         << "val".dbg_eq(val.dbg_repr)

# TODO: add a line info option

proc dbg_repr*(self: Stmt): string =

   template quotes(x): string =  '"' & x & '"'

   template flair(line_info = false) =
      result.add(dbg_repr_flair(self.kind))
      #if line_info:
      #   result.add("[" & self.sys.line_info & "]")

   flair
   match self:
   of Ident, SingleSym:
      << [blue('\"' & $self & '\"')]
   of CompoundIdent:
      list:
         for ident in self:
            << self.dbg_repr
   of ChoiceSym:
      list:
         for sym in self:
            << sym.dbg_repr
   of RoutineDecl:
      list:
         << "name".dbg_eq(self.ident.dbg_repr)
         # TODO: patterns
         # TODO: generic params
         for formal in self.formals:
            << formal.dbg_repr
         match self.return_type of Some:
            << "return_type".dbg_eq(return_type.dbg_repr)
         # TODO: pragmas
         match self.body of Some:
            << "body".dbg_eq(body.dbg_repr)
   of Comment:
      << ["{", quotes(self.val), "}"]
   of StmtList:
      list:
         for stmt in self:
            << stmt.dbg_repr
   of ForLoop:
      list:
         << "vars".dbg_eq(self.vars.dbg_repr)
         << "expr".dbg_eq(self.expr.dbg_repr)
         << "body".dbg_eq(self.body.dbg_repr)
   of AnyCall:
      list:
         << "name".dbg_eq(self.name.dbg_repr)
         for argument in self.arguments:
            << argument.dbg_repr
   of NilLit: discard
   of NumericLit:
      << ["{", $self, "}"]
   of Asgn:
      list:
         << self.lhs.dbg_repr
         << self.rhs.dbg_repr
   of PragmaExpr:
      list:
         << self.expr.dbg_repr
         << self.pragmas.dbg_repr
   of Container:
      list:
         match self of ObjectConstr:
            << "name".dbg_eq(self.name.dbg_repr)
         for field in self:
            << field.dbg_repr
   of TypeExpr:
      list:
         << self.val.dbg_repr
   of AnyVarDefs:
      list:
         for var_def in self:
            << self.dbg_repr
   else:
      dump self.sys
      fatal("TODO: dbg_repr{", self.kind, "}")

proc dbg*(self: Stmt | Colon | IdentDef | ForLoopVars) = debug_echo self.dbg_repr
