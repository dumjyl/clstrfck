# FIXME: rendering of multiline string value nodes

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
   result = dbg_repr_flair($type_of(self))
   list:
      for for_var in self:
         << for_var.dbg_repr

proc dbg_repr*(self: MaybeColon): string =
   match self:
   of Colon:
      result = dbg_repr_flair($type_of(self))
      list:
         << self.name.dbg_repr
         << self.val.dbg_repr
   of NoColon:
      result = self.dbg_repr

proc dbg_repr*(self: IdentDef): string =
   result = dbg_repr_flair($type_of(self))
   list:
      << "name".dbg_eq(self.ident.dbg_repr)
      match self.typ of Some:
         << "typ".dbg_eq(typ.dbg_repr)
      match self.val of Some:
         << "val".dbg_eq(val.dbg_repr)

proc dbg_repr*(self: Pragmas): string =
   result = dbg_repr_flair($type_of(self))
   list:
      for pragma in self:
         << pragma.dbg_repr

proc dbg_repr*(self: AnyVarDef): string =
   match self:
   of IdentVarDef: result = self.dbg_repr
   of TupleVarDef:
      result = dbg_repr_flair($type_of(self))
      for ident in self:
         << "var".dbg_eq(ident.dbg_repr)
      match self.typ of Some:
         << "typ".dbg_eq(typ.dbg_repr)
      match self.val of Some:
         << "val".dbg_eq(val.dbg_repr)

# FIXME: add a line info option

proc dbg_repr*(self: Stmt): string =

   template flair(line_info = false) =
      result.add(dbg_repr_flair(self.kind))
      #if line_info:
      #   result.add("[" & self.detail.line_info & "]")

   flair
   match self:
   of Ident, SingleSym, Comment:
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
         # FIXME: patterns
         # FIXME: generic params
         for formal in self.formals:
            << formal.dbg_repr
         match self.return_type of Some:
            << "return_type".dbg_eq(return_type.dbg_repr)
         # FIXME: pragmas
         match self.body of Some:
            << "body".dbg_eq(body.dbg_repr)
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
         for arg in self.args:
            << arg.dbg_repr
   of NilLit: discard
   of NumericLit: << ["{", $self, "}"]
   of ...[Asgn, Dot]:
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
   of QualTypeExpr:
      list:
         << self.val.dbg_repr
   of AnyVarDefs:
      list:
         for var_def in self:
            << var_def.dbg_repr
   else:
      dump self.detail
      fatal("FIXME: dbg_repr{", self.kind, "}")

proc dbg*(self: Stmt | MaybeColon | IdentDef | ForLoopVars | Pragmas | AnyVarDef) =
   debug_echo self.dbg_repr
