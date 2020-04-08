## Naming conventions for type hierarchies
##    `FooRecordsMeta` is a typeclass containing all variants below `Foo` with a singular enum `kind`.
##    `FooChildrenMeta` is a typeclass containing all types below `Foo`.
##    `FooAllMeta` is a typeclass like `FooChildrenMeta` but containing `Foo` too.

# Every nimnode must go through a canonicalizing Stmt`{}`

# TODO: restrict AnyIdent to weed out invalid bound sym kinds.

# TODO: make static[int] expect work
#   expect erroring

# TODO: should expect always return a value? but sometimes we just want to verify a property.
#       {.discardable.}?

# XXX: we generate a lot of stuff which is not so nice for doc generation.
# TODO: expect_match

# TODO: CompoundIdent can hold syms.

import
   std/sequtils,
   mainframe,
   options2,
   matchbook/private/matches,
   macros2/private/[vm_timings, expects]

export
   expects,
   matches

from std/strutils import join
from std/macros import nil
import macros2/private/core except AST, add_AST, `!`, lit, bind_ident, ident

export NimNode

import macros2/private/gens

gens Stmt:
   Unexposed
   Expr:
      StmtList
      Block
      PragmaExpr
      AnyIdent:
         Ident
         CompoundIdent
         Sym:
            ChoiceSym:
               OpenChoiceSym
               ClosedChoiceSym
            SingleSym:
               UnexposedSym
               ParamSym
               GenericParamSym
               ModuleSym
               TypeSym
               AnyVarSym:
                  VarSym
                  LetSym
                  ConstSym
               ResultSym
               RoutineSym:
                  ProcSym
                  FuncSym
                  IteratorSym
                  ConverterSym
                  MethodSym
                  TemplateSym
                  MacroSym
               FieldSym
               EnumFieldSym
               ForVarSym
               LabelSym
      Lit:
         CharLit
         NumericLit:
            AnyIntLit:
               IntLit
               Int8Lit
               Int16Lit
               Int32Lit
               Int64Lit
            AnyUIntLit:
               UIntLit
               UInt8Lit
               UInt16Lit
               UInt32Lit
               UInt64Lit
            AnyFloatLit:
               FloatLit
               Float32Lit
               Float64Lit
               Float128Lit
         AnyStringLit:
            StringLit
            MultilineStringLit
         NilLit
      Container:
         ExprContainer:
            Paren # in the form `(expr)` only
            Bracket # [a, b, c] # simple
         Curly # {1, 2, 3} or {a: 123, b: "abc"} or mixed {x, "blah": x, y}
         RecordConstr:
            ObjectConstr # Foo(a: 123) can be mixed like curly
            TupleConstr # () | (,) | (1, 2) | (a: 123) can be mixed too
      AnyCall:
         Call # foo(a, b)
         CommandCall # foo a, b
         StringLitCall # foo"abc"
         CurlyCall # foo{"abc"}
         BracketCall # foo["abc"]
         OperatorCall:
            InfixCall # 1 + 1
            PrefixCall # $x
      Conv
      Dot
      TypeExpr:
         PtrTypeExpr
         RefTypeExpr
         VarTypeExpr
   Decl:
      RoutineDecl:
         ProcDecl
         FuncDecl
         IteratorDecl
         ConverterDecl
         MethodDecl
         TemplateDecl
         MacroDecl
      AnyVarDefs:
         VarDefs
         LetDefs
         ConstDefs
      TypeDefs
   Loop:
      ForLoop
      WhileLoop
   Asgn
   Discard
   Comment

gens MaybeColon:
   NoColon
   Colon

gens AnyVarDef:
   IdentVarDef
   UnpackVarDef

type
   NimNodeParseError* = object of ValueError
      node: NimNode
   Formals* = object ## The non-generic, non-return-type parameters of a function.
      sys: NimNode
   Arguments* = object ## The arguments of some sort of call.
      sys: NimNode
   ForLoopVars* = object
      sys: NimNode
   IdentDef* = object ## A triplet of `AnyIdent, Option[Expr], Option[Expr]`
      sys: NimNode
   Pragmas* = object
      sys: NimNode
   Index* = int | BackwardsIndex ## The index type apis should be migrated too.

const
   # routine_name_pos = 0
   # routine_pattern_pos = 1
   # routine_generic_params_pos = 2
   routine_params_pos = 3
   # routine_pragmas_pos = 4
   # routine_reserved_pos = 5
   routine_body_pos = 6

template impl_expect(x, y) {.dirty.} =
   proc expect*[X: x; Y: y](self: X, _: type[Y]): Y {.time.} =
      {.push hint[ConvFromXToItSelfNotNeeded]: off.}
      ## Cast `self` to `T` or error fatally.
      if self of Y: result = unsafe_conv(self, Y)
      else:
         # TODO: make this nicer
         when defined(dump_node) and X is Stmt:
            dbg self
         fatal("expected variant: ", Y, ", got variant: ", self.kind)
      {.pop.}

template impl_field(T, f, FT, i) {.dirty.} =
   proc f*(self: T): FT = FT{self.sys[i]}
   proc `f=`*(self: T, val: FT) = self.sys[i] = val.sys

template impl_items(T) {.dirty.} =
   iterator items*(self: T): auto =
      for i in 0 ..< self.len:
         yield self[i]

template impl_slice_index(T, Val) {.dirty.} =
   proc `[]`*(self: T, i: HSlice): seq[Val] =
      template idx(x): int =
         when x is BackwardsIndex: self.len - int(x) else: int(x)
      for i in idx(i.a) .. idx(i.b):
         result.add(self[i])

template impl_container(T, Val: untyped, offset: untyped = 0) {.dirty.} =
   func len*(self: T): int = self.sys.len - offset
   proc `[]`*(self: T, i: Index): Val = Val{self.sys[i + offset]}
   proc `[]=`*(self: T, i: Index, val: Val) = self.sys[i + offset] = val.sys
   impl_items(T)
   impl_slice_index(T, Val)

# --- NimNode

template throw_ast(self: NimNode, msg = "") =
   var msg_b = "failed to parse AST"
   if msg.len != 0:
      msg_b &= "; " & msg
   let e = new_Exception(NimNodeParseError, msg_b)
   e.node = self
   raise e

proc canon_and_verify(self: NimNode): NimNode {.time.} =
   template v(x): auto = canon_and_verify(x)
   ## Perform AST canonicalization here.
   result = self
   match self:
   of nnk_formal_params:
      var ident_defs = seq[NimNode].default
      for i in 1 ..< self.len:
         for j in 0 ..< self[i].len - 2:
            ident_defs.add(nnk_ident_defs{self[i][j], self[i][^2], self[i][^1]})
      self.set_len(1)
      for ident_def in ident_defs:
         self.add(ident_def)
   of nnk_stmt_list, nnk_stmt_list_expr:
      # 2
      # TODO: stmt list flattening?
      for i in 0 ..< self.len:
         self[i] = self[i].v
   of nnk_acc_quoted:
      for i in 0 ..< self.len:
         self[i] = self[i].v
         self[i].expect(nnk_ident_like)
   of nnk_call:
      for i in 0 ..< self.len:
         self[i] = self[i].v
   of nnk_ident, nnk_sym: discard
   else:
      when false:
         self.error("TODO: canonicalize " & $self.kind & " \n" & self.tree_repr)
      else:
         for i in 0 ..< self.len:
            self[i] = self[i].v

# --- Stmt

template throw_ast(self: Stmt, msg = "") = throw_ast(self.sys, msg)

func `==`*(a: StmtAllMeta, b: StmtAllMeta): bool = a.sys == b.sys
   ## Uses same equality as `NimNode`.

template unsafe_downconv(self: Stmt, kinds: openarray[set[StmtKind]]): auto = unsafe_lca_downconv()

func `{}`*(Self: type[StmtKind], kind: NimSymKind): Self

func `{}`*(Self: type[StmtKind], node: NimNode): Self {.time.} =
   match node:
   of nnk_ident: StmtKind.Ident
   of nnk_acc_quoted: StmtKind.CompoundIdent
   of nnk_open_sym_choice: StmtKind.OpenChoiceSym
   of nnk_closed_sym_choice: StmtKind.ClosedChoiceSym
   of nnk_sym: StmtKind{node.sym_kind}

   of nnk_char_lit: StmtKind.CharLit
   of nnk_int_lit: StmtKind.IntLit
   of nnk_int8_lit: StmtKind.Int8Lit
   of nnk_int16_lit: StmtKind.Int16Lit
   of nnk_int32_lit: StmtKind.Int32Lit
   of nnk_int64_lit: StmtKind.Int64Lit
   of nnk_uint_lit: StmtKind.UIntLit
   of nnk_uint8_lit: StmtKind.UInt8Lit
   of nnk_uint16_lit: StmtKind.UInt16Lit
   of nnk_uint32_lit: StmtKind.UInt32Lit
   of nnk_uint64_lit: StmtKind.UInt64Lit
   of nnk_float_lit: StmtKind.FloatLit
   of nnk_float32_lit: StmtKind.Float32Lit
   of nnk_float64_lit: StmtKind.Float64Lit
   of nnk_float128_lit: StmtKind.Float128Lit
   of nnk_str_lit: StmtKind.StringLit
   of nnk_triple_str_lit: StmtKind.MultilineStringLit
   of nnk_nil_lit: StmtKind.NilLit
   of nnk_curly, nnk_table_constr: StmtKind.Curly
   of nnk_tuple_constr: StmtKind.TupleConstr
   of nnk_par:
      if node.len == 1 and node[0].kind != nnk_expr_colon_expr: StmtKind.Paren
      else: StmtKind.TupleConstr
   of nnk_bracket: StmtKind.Bracket
   of nnk_rstr_lit: StmtKind.StringLitCall # own kind | StringLitCall | property on string lit.
   of nnk_call: StmtKind.Call
   of nnk_prefix: StmtKind.PrefixCall
   of nnk_infix: StmtKind.InfixCall
   of nnk_command: StmtKind.CommandCall
   of nnk_call_str_lit: StmtKind.StringLitCall
   of nnk_proc_def: StmtKind.ProcDecl
   of nnk_func_def: StmtKind.FuncDecl
   of nnk_iterator_def: StmtKind.IteratorDecl
   of nnk_converter_def: StmtKind.ConverterDecl
   of nnk_method_def: StmtKind.MethodDecl
   of nnk_template_def: StmtKind.TemplateDecl
   of nnk_macro_def: StmtKind.MacroDecl
   of nnk_stmt_list, nnk_stmt_list_expr, nnk_stmt_list_type: StmtKind.StmtList
   of nnk_block_stmt, nnk_block_expr, nnk_block_type: StmtKind.Block
   of nnk_asgn, nnk_fast_asgn: StmtKind.Asgn
   of nnk_conv, nnk_obj_down_conv, nnk_obj_up_conv, nnk_hidden_sub_conv,
      nnk_string_to_cstring, nnk_cstring_to_string: StmtKind.Conv
   of nnk_obj_constr: StmtKind.ObjectConstr
   of nnk_comment_stmt: StmtKind.Comment
   of nnk_for_stmt, nnk_par_for_stmt: StmtKind.ForLoop # TODO: expose the par part
   of nnk_while_stmt: StmtKind.WhileLoop
   of nnk_curly_expr: StmtKind.CurlyCall
   of nnk_bracket_expr: StmtKind.BracketCall
   of nnk_pragma_expr: StmtKind.PragmaExpr
   of nnk_ref_ty: StmtKind.RefTypeExpr
   of nnk_ptr_ty: StmtKind.PtrTypeExpr
   of nnk_var_ty: StmtKind.VarTypeExpr
   of nnk_dot_expr: StmtKind.Dot
   of nnk_discard_stmt: StmtKind.Discard
   of nnk_type_section: StmtKind.TypeDefs
   of nnk_var_section: StmtKind.VarDefs
   of nnk_let_section: StmtKind.LetDefs
   of nnk_const_section: StmtKind.ConstDefs
   of nnk_dot_call,
         nnk_type,
         nnk_comes_from,
         nnk_postfix,
         nnk_hidden_call_conv,
         nnk_var_tuple,
         nnk_range, nnk_checked_field_expr,
         nnk_if_expr, nnk_elif_expr, nnk_else_expr,
         nnk_lambda, nnk_do, # wth is do
         nnk_hidden_std_conv,
         nnk_cast, nnk_static_expr,
         nnk_expr_eq_expr,

         nnk_expr_colon_expr, # error: Colon
         nnk_ident_defs, # error: IdentDef
         nnk_type_def, # error: TypeDef
         nnk_formal_params, # error: Formals
         nnk_pragma, # error: Pragmas
         nnk_else, # error: part of If | Case | When
         nnk_of_inherit, # error: part of object blah

         nnk_addr, nnk_hidden_addr, # Addr
         nnk_deref_expr, nnk_hidden_deref, # Deref
         nnk_asm_stmt,
         nnk_mixin_stmt, nnk_bind, nnk_bind_stmt,
         nnk_const_ty, nnk_mutable_ty, nnk_shared_ty, # unused

         nnk_chck_range_f, nnk_chck_range64, nnk_chck_range,

         nnk_import_stmt, nnk_import_except_stmt,
         nnk_export_stmt, nnk_export_except_stmt,
         nnk_from_stmt, nnk_include_stmt,

         nnk_import_as, nnk_of_branch, nnk_elif_branch,
         nnk_pragma_block, nnk_if_stmt,
         nnk_when_stmt,
         nnk_case_stmt, nnk_yield_stmt, nnk_defer,
         nnk_return_stmt,
         nnk_break_stmt, nnk_continue_stmt, nnk_static_stmt,
         nnk_using_stmt,
         nnk_with, nnk_without, nnk_type_of_expr, nnk_object_ty,
         nnk_tuple_ty, nnk_tuple_class_ty, nnk_type_class_ty, nnk_static_ty,
         nnk_rec_list, nnk_rec_case, nnk_rec_when, nnk_distinct_ty,
         nnk_proc_ty, nnk_iterator_ty, nnk_enum_ty,
         nnk_enum_field_def, nnk_arglist, nnk_pattern,
         nnk_closure, nnk_goto_state, nnk_state, nnk_break_state,

         nnk_try_stmt, nnk_hidden_try_stmt, nnk_finally, nnk_except_branch, nnk_raise_stmt,

         nnk_const_def, nnk_generic_params,
         nnk_none, nnk_empty:
      node.throw_ast("unexpected kind resolution: " & $node.kind)

proc kind*(self: Stmt): StmtKind = StmtKind{self.sys}

impl_expect Stmt, StmtAllMeta

proc `{}`*(Self: type[StmtAllMeta], node: NimNode): Self =
   ## Constructor for any `Stmt` from a NimNode, performs canonicalizations. Low level api.
   {.line.}: expect(Stmt(sys: canon_and_verify(node)), Self)

func `$`*(self: Stmt): string {.time.} = $self.sys

template `$`*(self: StmtChildrenMeta): string = $unsafe_conv(self, Stmt)

func copy*[T: Stmt](self: T): T {.time.} =
   ## Perform a recusive copy of `self`
   result = T(sys: self.sys.copy)

func error(self: Stmt, msg: varargs[string, `$`]) {.time.} =
   # TODO: dump node here
   core.error(msg.join, self.sys)

proc dbg*(self: Stmt | Colon | IdentDef | ForLoopVars)
proc dbg_repr*(self: ForLoopVars): string
proc dbg_repr*(self: MaybeColon): string
proc dbg_repr*(self: IdentDef): string
proc dbg_repr*(self: Pragmas): string
proc dbg_repr*(self: Stmt): string

proc verbose_note*(self: Stmt | ForLoopVars): string {.time.} =
   when defined(dump_node):
      result = expects.enclose(self.dbg_repr) & '\n' & expects.enclose($self.sys)
   else:
      result = "Note: recompile with '-d:dump_node' to dump the offending node"

template expect*(self: untyped, expected_len: static[int], msg: string = ""): auto =
   impl_expect(self.len == expected_len, msg, self)
   when expected_len == 1:
      self[0]
   else:
      var res = default array[expected_len, type_of self[0]]
      for i in 0 ..< self.len:
         res[i] = self[i]
      res

# --- ident stuff

# Structure of identifiers
# single_ident # some symbol, can be vm generated and not representable without backticks.
# `compound identifier` # a backticked ident or multiple idents. also abused for quoting expressions.
# symbols # single bound sym, open/closed sym choices

# routine name # can be postfixed, TODO: no pragmas?

# TODO: merge result with var sym? but what does the `impl` look like return?

func `{}`(Self: type[StmtKind], kind: NimSymKind): Self =
   case kind:
   of nsk_unknown, nsk_conditional, nsk_dyn_lib, nsk_temp, nsk_stub: StmtKind.UnexposedSym
   of nsk_param: StmtKind.ParamSym
   of nsk_generic_param: StmtKind.GenericParamSym
   of nsk_module: StmtKind.ModuleSym
   of nsk_type: StmtKind.TypeSym
   of nsk_var: StmtKind.VarSym
   of nsk_let: StmtKind.LetSym
   of nsk_const: StmtKind.ConstSym
   of nsk_result: StmtKind.ResultSym
   of nsk_proc: StmtKind.ProcSym
   of nsk_func: StmtKind.FuncSym
   of nsk_method: StmtKind.MethodSym
   of nsk_iterator: StmtKind.IteratorSym
   of nsk_converter: StmtKind.ConverterSym
   of nsk_macro: StmtKind.MacroSym
   of nsk_template: StmtKind.TemplateSym
   of nsk_field: StmtKind.FieldSym
   of nsk_enum_field: StmtKind.EnumFieldSym
   of nsk_for_var: StmtKind.ForVarSym
   of nsk_label: StmtKind.LabelSym

# --- Ident

proc `{}`*(Self: type[Ident], val: string): Self = Ident{macros.ident(val)}
   ## Create a new unbound identifier.

# --- CompoundIdent

impl_container CompoundIdent, AnyIdent

proc delete*(self: CompoundIdent, i: Index) = core.delete(self.sys, i)

proc `{}`*(Self: type[CompoundIdent], vals: varargs[AnyIdent]): Self =
   result = Self{nnk_acc_quoted{}}
   for val in vals:
      result.sys.add(val.sys)

# --- ChoiceSym

impl_container ChoiceSym, SingleSym

# --- AnyIdent

proc val*(self: AnyIdent): string =
   match self:
   of ChoiceSym: result = self[0].val
   of CompoundIdent:
      for ident in self:
         result &= ident.val
   else: result = macros.str_val(self.sys)

# --- SymRecordsMeta

proc gen*(Self: type[SymRecordsMeta], val: string = ""): Self = Self{gen(NimSymKind{Self}, val)}

proc `{}`*(Self: type[SymRecordsMeta]): Self = gen(Self)

func `{}`(Self: type[NimSymKind], T: type[SymRecordsMeta]): Self =
   when T is UnexposedSym: static_error("cannot generate an UnexposedSym")
   elif T is ParamSym: nsk_param
   elif T is GenericParamSym: nsk_generic_param
   elif T is ModuleSym: nsk_module
   elif T is TypeSym: nsk_type
   elif T is VarSym: nsk_var
   elif T is LetSym: nsk_let
   elif T is ConstSym: nsk_const
   elif T is ResultSym: nsk_result
   elif T is ProcSym: nsk_proc
   elif T is FuncSym: nsk_func
   elif T is MethodSym: nsk_method
   elif T is IteratorSym: nsk_iterator
   elif T is ConverterSym: nsk_converter
   elif T is MacroSym: nsk_macro
   elif T is TemplateSym: nsk_template
   elif T is FieldSym: nsk_field
   elif T is EnumFieldSym: nsk_enum_field
   elif T is ForVarSym: nsk_for_var
   elif T is LabelSym: nsk_label
   else: static_error("cannot generate a symbol of type: ", T)


# XXX: nim bug: cannon use Sym{core.bind_ident(val)}, bind_ident is an actual symbol not nimnode
#proc bind_ident(val: static[string]): Sym =
#   ## Bind a new symbol from `val`.
#   result = Sym(sys: core.bind_ident(val))
#   assert(result.sys != nil)

proc `{}`*(Self: type[Sym], val: static[string]): Self = Sym{macros.bind_sym(val)}

func skip_ident_quals(self: NimNode): NimNode =
   match self:
   of nnk_postfix:
      assert(self.len == 2)
      assert(self[0].eq_ident("*"))
      result = skip_ident_quals(self[1])
   of nnk_ident_like: result = self
   else: self.error("unhandled ident quals")

# --- IdentDef

proc ident*(self: IdentDef): AnyIdent = AnyIdent{self.sys[0].skip_ident_quals}
   ## Return the ident in `self` skipping any backquotes or export markers.

proc typ*(self: IdentDef): Option[Expr] =
   result = if self.sys[^2] of nnk_empty: none(Expr) else: some(Expr{self.sys[^2]})

proc `typ=`*(self: IdentDef, typ: Option[Expr]) =
   match typ of Some: self.sys[^2] = typ.sys
   else: self.sys[^2] = nnk_empty{}

proc `typ=`*(self: IdentDef, typ: Expr) = self.sys[^2] = typ.sys

proc val*(self: IdentDef): Option[Expr] =
   result = if self.sys[^1] of nnk_empty: none(Expr) else: some(Expr{self.sys[^1]})

proc `val=`*(self: IdentDef, val: Expr) = self.sys[^1] = val.sys

proc `$`*(self: IdentDef): string = $self.sys
   ## Render this `IdentDef` as source code.

template empty_opt(self): NimNode = self.map((x) => x.sys).or_val(nnk_empty{})

proc `{}`*(Self: type[IdentDef], ident_def: NimNode): IdentDef =
   Self(sys: ident_def.canon_and_verify)

proc `{}`*(Self: type[IdentDef], name: AnyIdent, typ = none(Expr), val = none(Expr)): Self =
   result = Self(sys: nnk_ident_defs{name.sys, empty_opt(typ), empty_opt(val)})

# --- Formals

impl_container Formals, IdentDef, 1

func add(self: Formals, name: AnyIdent, typ: Expr, val: Expr) =
   self.sys.add(IdentDef{name, some(typ), some(val)}.sys)

func add(self: Formals, name: AnyIdent, typ: Expr) =
   self.sys.add(IdentDef{name, some(typ), none(Expr)}.sys)

func formals*(self: RoutineDecl): Formals =
   result = Formals(sys: self.sys[routine_params_pos])

# --- StmtList

proc `{}`*(Self: type[StmtList], stmts: varargs[Stmt]): Self =
   result = Self{nnk_stmt_list{}}
   for stmt in stmts:
      result.sys.add(stmt.sys)

impl_container StmtList, Stmt

func add*(self: StmtList, stmt: Stmt) = self.sys.add(stmt.sys)

# --- RoutineDecl

func `{}`(Self: type[NimNodeKind], kind: RoutineDeclKind): Self =
   match kind:
   of ProcDecl: nnk_proc_def
   of FuncDecl: nnk_func_def
   of IteratorDecl: nnk_iterator_def
   of ConverterDecl: nnk_converter_def
   of MethodDecl: nnk_method_def
   of TemplateDecl: nnk_template_def
   of MacroDecl: nnk_macro_def

func `{}`(Self: type[NimNodeKind], T: type[RoutineDeclRecordsMeta]): Self =
   when T is ProcDecl: nnk_proc_def
   elif T is FuncDecl: nnk_func_def
   elif T is IteratorDecl: nnk_iterator_def
   elif T is ConverterDecl: nnk_converter_def
   elif T is MethodDecl: nnk_method_def
   elif T is TemplateDecl: nnk_template_def
   elif T is MacroDecl: nnk_macro_def
   else: {.fatal: "unreachable".}

func return_type*(self: RoutineDecl): Option[Expr] =
   ## Get the return type of `self` if it has one.
   if self.sys[routine_params_pos][0] of nnk_empty:
      result = none Expr
   else:
      result = some Expr(sys: self.sys[routine_params_pos][0])

func `return_type=`*(self: RoutineDecl, typ: Expr) =
   ## Set the return type of `self`.
   self.sys[routine_params_pos][0] = typ.sys

proc body*(self: RoutineDecl): Option[Stmt] =
   ## Return the body of this `RoutineDecl` if it has one.
   match self.sys[routine_body_pos]:
   of nnk_empty: none(Stmt)
   else: some(Stmt{self.sys[routine_body_pos]})

proc `body=`*(self: RoutineDecl, stmt: Stmt) =
   ## Set the body of this `RoutineDecl`.
   self.sys[routine_body_pos] = stmt.sys

proc copy_as*(self: RoutineDecl, kind: RoutineDeclKind): RoutineDecl =
   result = RoutineDecl{NimNodeKind{kind}{}}
   for n in self.sys:
      result.sys.add(n.copy)

proc copy_as*(self: RoutineDecl, T: type[RoutineDeclRecordsMeta]): RoutineDecl =
   result = self.copy_as(first(rtti_range(T)))

func read_pub(self: NimNode): bool =
   # TODO: account for sem checked symbols here too.
   match self:
   of nnk_postfix: result = true
   else: result = false

func pub*(self: RoutineDecl): bool = self.sys[0].read_pub

func `pub=`(self: RoutineDecl, val: bool) =
   match self.sys[0]:
   of nnk_postfix:
      assert(self.sys[0][0].eq_ident("*"))
      if not val:
         self.sys[0] = self.sys[0][1]
   elif val:
      self.sys[0] = nnk_postfix{"*", self.sys[0]}

proc ident*(self: RoutineDecl): AnyIdent = AnyIdent{self.sys[0].skip_ident_quals}

func `ident=`*(self: RoutineDecl, name: AnyIdent) =
   ## Set the name of `self` to
   match self.sys[0]:
   of nnk_postfix: self.sys[0][1] = name.sys
   of nnk_acc_quoted, nnk_ident, nnk_sym: self.sys[0] = name.sys
   else: self.throw_ast

proc `{}`*(
      Self: type[RoutineDeclRecordsMeta],
      ident: AnyIdent,
      formals: openarray[IdentDef] = [],
      return_type = none(Expr),
      body = some(Stmt(StmtList{})),
      pragmas: openarray[Expr] = [],
      ): Self =
   ## Initializer for routine decls.
   let params = nnk_formal_params{}
   match return_type of Some:
      params.add(return_type.sys)
   else:
      params.add(nnk_empty{})
   for formal in formals:
      params.add(formal.sys)
   var pragmas =
      if pragmas.len > 0:
         let pragma_node = nnk_pragma{}
         for pragma in pragmas:
            pragma_node.add(pragma.sys)
         pragma_node
      else:
         nnk_empty{}
   var body = block:
      match body of Some: body.sys
      else: nnk_empty{}
   result = Self{NimNodeKind{Self}{
      ident.sys, # name
      nnk_empty{}, # patterns
      nnk_empty{}, # TODO: generic params
      params,
      pragmas,
      nnk_empty{}, # reserved
      body}}

# --- Arguments

impl_container Arguments, Expr, 1

proc arguments*(self: AnyCall): Arguments = Arguments(sys: self.sys)

# --- AnyCall

impl_field AnyCall, name, Expr, 0

template unpack*(self: AnyCall, name_name: untyped, arguments_name: untyped) =
   template name_name: Expr {.used.} = self.name
   template `name_name=`(val: Expr) {.used.} = self.name = val
   template arguments_name: Arguments {.used.} = self.arguments

# --- Call

proc add*(self: Call, argument: Expr) =
   self.sys.add(argument.sys)

proc `{}`*(Self: type[Call], name: AnyIdent, arguments: varargs[Expr]): Self =
   result = Self{nnk_call{name.sys}}
   for argument in arguments:
      result.add(argument)

proc bind_call*(self: static[string], arguments: varargs[Expr]): Call =
   result = Call{Sym{self}, arguments}

proc call*(self: AnyIdent, arguments: varargs[Expr]): Call = Call{self, arguments}

proc call*(self: RoutineDecl, arguments: varargs[Expr]): Call = Call{self.ident, arguments}

# XXX: careful, adding to a Paren can mutate it into an anonymous tuple constructor.

# --- TypeExpr

impl_field TypeExpr, val, Expr, 0

# --- MaybeColon

proc kind*(self: MaybeColon): MaybeColonKind =
   match self.sys.kind of nnk_expr_colon_expr: MaybeColonKind.Colon
   else: MaybeColonKind.NoColon

proc `{}`*(Self: type[MaybeColon], node: NimNode): Self = Self(sys: node.canon_and_verify)

template unsafe_downconv*(self: MaybeColon, kinds: openarray[set[MaybeColonKind]]): auto =
   when type_of(unsafe_lca_downconv()) is NoColon: val(unsafe_lca_downconv())
   else: unsafe_lca_downconv()

impl_expect MaybeColon, MaybeColonAllMeta

# --- Colon

impl_field Colon, name, Expr, 0

impl_field Colon, val, Expr, 1

proc `{}`*(Self: type[Colon], node: NimNode): Self = Self(sys: node.canon_and_verify)

proc `{}`*(Self: type[Colon], name, val: Expr): Self = Self{nnk_expr_colon_expr{name.sys, val.sys}}

# --- NoColon

proc val*(self: NoColon): Expr = Expr{self.sys}

# --- Container

proc offset*(self: Container): int =
   match self of ObjectConstr: 1
   else: 0

proc len*(self: Container): int = self.sys.len - self.offset

proc `[]`*(self: Container, i: Index): MaybeColon = MaybeColon{self.sys[i + self.offset]}

proc `[]=`*(self: Container, i: Index, maybe_colon: MaybeColon) =
   self.sys[i + self.offset] = maybe_colon.sys

proc `[]=`*(self: Container, i: Index, expr: Expr) =
   self.sys[i + self.offset] = expr.sys

impl_items Container

# --- ExprContainer

impl_container ExprContainer, Expr

# --- ObjectConstr

# TODO: name can be an option too...

proc name*(self: ObjectConstr): Expr = Expr{self.sys[0]}

func `name=`*(self: ObjectConstr, expr: Expr) = self.sys[0] = expr.sys

template unpack*(self: ObjectConstr, name_name: untyped, fields_name: untyped) =
   template name_name: Expr {.used.} = self.name
   template `name_name=`(val: Expr) {.used.} = self.name = val

# --- Pragmas

proc `{}`*(Self: type[Pragmas], node: NimNode): Self = Self(sys: node.canon_and_verify)

impl_container Pragmas, MaybeColon

# --- PragmaExpr

proc expr*(self: PragmaExpr): Expr = Expr{self.sys[0]}

proc pragmas*(self: PragmaExpr): Pragmas = Pragmas{self.sys[1]}

# --- StringLit

func lit*(val: string): StringLit =
   result = StringLit(sys: nnk_str_lit{})
   macros.`str_val=`(result.sys, val)

# --- AnyVarDef

# TODO: maybe expose the availability of the let/const val.

proc kind*(self: AnyVarDef): AnyVarDefKind =
   match self.sys:
   of nnk_ident_defs, nnk_const_def: AnyVarDefKind.IdentVarDef
   of nnk_var_tuple: AnyVarDefKind.UnpackVarDef
   else: self.sys.throw_ast

template unsafe_downconv*(self: AnyVarDef, kinds: openarray[set[AnyVarDefKind]]): auto =
   when type_of(unsafe_lca_downconv()) is IdentVarDef: IdentDef{unsafe_lca_downconv().sys}
   else: unsafe_lca_downconv()

# --- UnpackVarDef

proc len*(self: UnpackVarDef): int = self.sys.len - 2

proc `[]`*(self: UnpackVarDef, i: Index): AnyIdent = AnyIdent{self.sys[i]}

proc `[]=`*(self: UnpackVarDef, i: Index, ident: AnyIdent) = self.sys[i] = ident.sys

impl_items UnpackVarDef

impl_field UnpackVarDef, typ, Expr, ^2

impl_field UnpackVarDef, val, Expr, ^1

# --- AnyVarDefs

template `{}`(Self: type[NimNodeKind], T: type[AnyVarDefsRecordsMeta]): Self =
   when T is VarDefs: nnk_var_section
   elif T is LetDefs: nnk_let_section
   elif T is VarDefs: nnk_const_section
   else: {.fatal: "unreachable".}

func `{}`*(Self: type[AnyVarDefsRecordsMeta], name: AnyIdent, val: Expr): Self =
   result = Self(sys: NimNodeKind{Self}{})
   when result is VarDefs or result is LetDefs: # XXX nim bug: when this is a match statement weird case coverage errors.
      result.sys.add(init(IdentDef, name, val = some(val)).sys)
   elif result is ConstDefs: {.fatal: "TODO".}
   else: {.fatal: "unreachable".}

impl_container AnyVarDefs, VarDefs

# --- Block

func `{}`(Self: type[Block], stmts: varargs[Stmt]): Self =
   # XXX: stmt list vs stmt list expr
   result = Self{nnk_block_stmt{nnk_empty{}, StmtList{stmts}.sys}}

proc label*(self: Block): Option[AnyIdent] =
   match self.sys[0]:
   of nnk_ident_like: some(AnyIdent{self.sys[0]})
   else: none(AnyIdent)

proc `label=`*(self: Block, val: AnyIdent) = self.sys[0] = val.sys

impl_field Block, body, Stmt, 1

# --- Dot

impl_field Dot, lhs, Expr, 0
impl_field Dot, rhs, Expr, 1

# --- Asgn

func `{}`*(Self: type[Asgn], lhs, rhs: Expr): Self = Self{nnk_asgn{lhs.sys, rhs.sys}}

impl_field Asgn, lhs, Expr, 0
impl_field Asgn, rhs, Expr, 1

template unpack*(self: Asgn, lhs_name, rhs_name) =
   template lhs_name: Expr = self.lhs
   template rhs_name: Expr = self.rhs

# --- Discard

func `{}`*(Self: type[Discard]): Self = Self{nnk_discard_stmt{nnk_empty{}}}

# --- Comment

func val*(self: Comment): string = macros.str_val(self.sys)

template unpack*(self: Comment, val_name) =
   template val_name: string = self.val

# --- ForLoop

proc vars*(self: ForLoop): ForLoopVars = ForLoopVars(sys: self.sys)

impl_field ForLoop, expr, Expr, ^2

impl_field ForLoop, body, Stmt, ^1

template unpack*(self: ForLoop, vars_name, expr_name, body_name) =
   template vars_name: ForLoopVars = self.vars
   template expr_name: Expr = self.expr
   template body_name: Stmt = self.body

# --- ForLoopVars

# TODO: expose the structure of these somehow, right now they are being flattened.

proc collect_for_loop_vars(self: NimNode): seq[NimNode] =
   for i in 0 ..< self.len - 2:
      match self[i]:
      of nnk_ident_like: result.add(self[i])
      of nnk_var_tuple:
         for j in 0 ..< self[i].len - 1:
            match self[i][j]:
            of nnk_ident_like: result.add(self[i][j])
            else: self[i][j].error("unreachable")
      else: self[i].error("unreachable")

proc len*(self: ForLoopVars): int = self.sys.collect_for_loop_vars.len

proc `[]`*(self: ForLoopVars, i: Index): AnyIdent = AnyIdent{collect_for_loop_vars(self.sys)[i]}

proc `[]=`*(self: ForLoopVars, i: Index, ident: AnyIdent) =
   var cur_var_i = 0
   template check(x) =
      if i == cur_var_i: x
      inc(cur_var_i)
   for var_base_i in 0 ..< self.sys.len - 2:
      match self.sys[var_base_i]:
      of nnk_ident_like:
         check: self.sys[var_base_i] = ident.sys
      of nnk_var_tuple:
         for tuple_i in 0 ..< self.sys[var_base_i].len - 1:
            match self.sys[var_base_i][tuple_i]:
            of nnk_ident_like:
               check: self.sys[var_base_i][tuple_i] = ident.sys
            else: self.sys[var_base_i][tuple_i].error("unreachable")
      else: self.sys[var_base_i].error("unreachable")

impl_items ForLoopVars

# ---

proc lit*(val: bool): EnumFieldSym =
   result = expect(if val: Sym{"true"} else: Sym{"false"}, EnumFieldSym)

proc skip(self: Stmt, Skip: type[Paren], n = high(int)): Stmt =
   result = self
   while true:
      match result of Paren and n > 0: Stmt(result) = result
      else: break

include macros2/private/[dbg, visiting, quoting]

proc m2_parse_type(typ: Expr): auto =
   match typ:
   of Curly: result = (macro_type: none(Expr),
                       variant_type: some(typ.expect(1).expect(NoColon).val))
   else: typ.error("failed to parse 'm2' type expression")

macro m2*(macro_decl): auto =
   # TODO: fix doc comments
   ## Process macro signature extensions. This is a pragma macro for macros.

   let def = Stmt{macro_decl}.expect(MacroDecl)
   let inner_def = def.copy_as(ProcDecl)
   inner_def.ident = ProcSym.gen(def.ident.val)
   inner_def.body = def.body.expect("macros cannot be forward declared")
   inner_def.pub = false

   match def.return_type of Some:
      let type_info = m2_parse_type(return_type)
      match type_info.macro_type of Some:
         def.return_type = macro_type
      else:
         def.return_type = !auto
      match type_info.variant_type of Some:
         inner_def.return_type = variant_type
      else:
         inner_def.return_type = !Stmt
   else:
      def.return_type = !auto
      inner_def.return_type = !Stmt

   let call = inner_def.call
   for i in 0 ..< def.formals.len:
      match def.formals[i].typ of Some:
         let type_info = m2_parse_type(typ)
         match type_info.macro_type of Some:
            def.formals[i].typ = macro_type
         else:
            def.formals[i].typ = !auto
         match type_info.variant_type of Some:
            inner_def.formals[i].typ = variant_type
            call.add(!`variant_type`{`def.formals[i].ident`})
         else:
            inner_def.formals[i].typ = !Stmt
            call.add(!Stmt{`def.formals[i].ident`})

   def.body = AST:
      `inner_def`
      result = `call`.sys
   result = def.sys
   dbg def
   echo def
