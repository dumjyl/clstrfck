# Every nimnode must go through a canonicalizing Stmt`{}`

# FIXME: indexing should not introduce subtle bugs, we need to handle backwards better.
# FIXME: restrict AnyIdent to weed out invalid bound sym kinds. WTF does this mean?
# FIXME: should expect always return a value? but sometimes we just want to verify a property.
#        {.discardable.}?
# FIXME: we generate a lot of stuff which is not so nice for doc generation.
#        mostly resolved through gen.dispatch but we could hide the sub ranges too.
#        and its slow as fuck... when defined(nimdoc) instead.
# FIXME: expect_match
# FIXME: these FooBlahMeta typeclasses should be replaced with meta(Foo, blah)
# FIXME: add stack limit to vm.

import mainframe, macros2/private/gen
import options2; export options2
import macros2/private/expects; export expects
import matchbook/private/matches; export matches
from std/strutils import join
from std/macros import nil
import macros2/private/core except AST, add_AST, `!`, lit, bind_ident, ident
export NimNode

generate Stmt:
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
            Paren   # in the form `(expr)` only
            Bracket # [a, b, c] # simple
         Curly      # {1, 2, 3} or {a: 123, b: "abc"} or mixed {x, "blah": x, y}
         RecordConstr:
            ObjectConstr # Foo(a: 123) can be mixed like curly
            TupleConstr  # () | (,) | (1, 2) | (a: 123) can be mixed too
      AnyCall:
         Call          # foo(a, b)
         CommandCall   # foo a, b
         StringLitCall # foo"abc"
         CurlyCall     # foo{"abc"}
         BracketCall   # foo["abc"]
         OperatorCall:
            InfixCall  # 1 + 1
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

generate TypeDefBody:
   EnumTypeDefBody
   ObjectTypeDefBody
   ExprTypeDefBody

generate MaybeColon:
   NoColon
   Colon

generate AnyVarDef:
   IdentVarDef
   TupleVarDef

generate Params:
   FormalParams
   GenericParams

type
   MacroError* = object of ValueError
      node: NimNode
   Arguments* = object ## The arguments of some sort of call.
      detail: NimNode
   ForLoopVars* = object
      detail: NimNode
   IdentDef* = object ## A triplet of `AnyIdent, Option[Expr], Option[Expr]`
      detail: NimNode
   Pragmas* = object
      detail: NimNode
   TypeDef* = object
      detail: NimNode
   FieldDef* = object
      detail: NimNode
   Name* = object
      detail: NimNode
   Index* = int | BackwardsIndex ## The index type apis should be migrated too.

# --- NimNode

template throw_ast(self: NimNode, msg = "") =
   var msg_b = "unexpected AST"
   if msg.len != 0:
      msg_b &= "; " & msg
   let e = new_Exception(MacroError, msg_b)
   e.node = self
   raise e

proc canon_and_verify(self: NimNode): NimNode =
   template v(x): auto = canon_and_verify(x)
   # FIXME: stmt list flattening
   result = self
   match self:
   of nnkFormalParams:
      var ident_defs = seq[NimNode].default
      for i in 1 ..< self.len:
         for j in 0 ..< self[i].len - 2:
            ident_defs.add(nnkIdentDefs{self[i][j], self[i][^2], self[i][^1]})
      self.set_len(1)
      for ident_def in ident_defs:
         self.add(ident_def)
   of nnkAccQuoted:
      for i in 0 ..< self.len:
         self[i] = self[i].v
         self[i].expect(nnkIdentLike)
   else:
      when false:
         self.error("FIXME: canonicalize " & $self.kind & " \n" & self.tree_repr)
      else:
         #for i in 0 ..< self.len: self[i] = self[i].v
         discard

# --- Stmt

template throw_ast(self: Stmt, msg = "") = throw_ast(self.detail, msg)

func `==`*[A: Stmt, B: Stmt](a: A, b: B): bool = a.detail == b.detail
   ## Uses same equality as `NimNode`.

template unsafe_subconv*(self: Stmt, kinds: set[StmtKind]): auto =
   unsafe_lca_subconv(self, kinds)

func `{}`*(Self: type[StmtKind], kind: NimSymKind): Self

func `{}`*(Self: type[StmtKind], node: NimNode): Self =
   if node.is_uninit: node.throw_ast("node is not initialized")
   match node:
   of nnkIdent: Self.Ident
   of nnkAccQuoted: Self.CompoundIdent
   of nnkOpenSymChoice: Self.OpenChoiceSym
   of nnkClosedSymChoice: Self.ClosedChoiceSym
   of nnkSym: Self{node.sym_kind}
   of nnkCharLit: Self.CharLit
   of nnkIntLit: Self.IntLit
   of nnkInt8Lit: Self.Int8Lit
   of nnkInt16Lit: Self.Int16Lit
   of nnkInt32Lit: Self.Int32Lit
   of nnkInt64Lit: Self.Int64Lit
   of nnkUIntLit: Self.UIntLit
   of nnkUInt8Lit: Self.UInt8Lit
   of nnkUInt16Lit: Self.UInt16Lit
   of nnkUInt32Lit: Self.UInt32Lit
   of nnkUInt64Lit: Self.UInt64Lit
   of nnkFloatLit: Self.FloatLit
   of nnkFloat32Lit: Self.Float32Lit
   of nnkFloat64Lit: Self.Float64Lit
   of nnkFloat128Lit: Self.Float128Lit
   of nnkStrLit: Self.StringLit
   of nnkTripleStrLit: Self.MultilineStringLit
   of nnkNilLit: Self.NilLit
   of nnkCurly, nnkTableConstr: Self.Curly
   of nnkTupleConstr: Self.TupleConstr
   of nnkPar:
      if node.len == 1 and node[0].kind != nnkExprColonExpr: Self.Paren else: Self.TupleConstr
   of nnkBracket: Self.Bracket
   of nnkRStrLit: Self.StringLitCall # own kind | StringLitCall | property on string lit.
   of nnkCall: Self.Call
   of nnkPrefix: Self.PrefixCall
   of nnkInfix: Self.InfixCall
   of nnkCommand: Self.CommandCall
   of nnkCallStrLit: Self.StringLitCall
   of nnkProcDef: Self.ProcDecl
   of nnkFuncDef: Self.FuncDecl
   of nnkIteratorDef: Self.IteratorDecl
   of nnkConverterDef: Self.ConverterDecl
   of nnkMethodDef: Self.MethodDecl
   of nnkTemplateDef: Self.TemplateDecl
   of nnkMacroDef: Self.MacroDecl
   of nnkStmtListLike: Self.StmtList
   of nnkBlockLike: Self.Block
   of nnkAsgn, nnkFastAsgn: Self.Asgn
   of nnkConv, nnkObjDownConv, nnkObjUpConv, nnkHiddenSubConv, nnkStringToCString,
      nnkCStringToString: Self.Conv
   of nnkObjConstr: Self.ObjectConstr
   of nnkCommentStmt: Self.Comment
   of nnkForStmt, nnk_par_for_stmt: Self.ForLoop # FIXME: expose the par part
   of nnkWhileStmt: Self.WhileLoop
   of nnkCurlyExpr: Self.CurlyCall
   of nnkBracketExpr: Self.BracketCall
   of nnkPragmaExpr: Self.PragmaExpr
   of nnkRefTy: Self.RefTypeExpr
   of nnkPtrTy: Self.PtrTypeExpr
   of nnkVarTy: Self.VarTypeExpr
   of nnkDotExpr: Self.Dot
   of nnkDiscardStmt: Self.Discard
   of nnkTypeSection: Self.TypeDefs
   of nnkVarSection: Self.VarDefs
   of nnkLetSection: Self.LetDefs
   of nnkConstSection: Self.ConstDefs
   #of nnkWhenStmt: Self.When
   #of nnkCaseStmt: Self.Case
   of nnkWhenStmt, nnkCaseStmt, nnkDotCall,
         nnkType,
         nnkComesFrom,
         nnkPostfix,
         nnkHiddenCallConv,
         nnkVarTuple,
         nnkRange, nnkCheckedFieldExpr,

         nnkLambda, nnkDo, # wth is do
         nnkHiddenStdConv,
         nnkCast, nnkStaticExpr,
         nnkExprEqExpr,

         nnkIfLike,
         nnkElifLike,
         nnkElseLike,

         nnkExprColonExpr, # error: Colon
         nnkIdentDefs, # error: IdentDef
         nnkTypeDef, # error: TypeDefs
         nnkFormalParams, # error: Formals
         nnkPragma, # error: Pragmas

         nnkOfInherit, # error: part of object blah

         nnkAddr, nnkHiddenAddr, # Addr
         nnkDerefExpr, nnkHiddenDeref, # Deref
         nnkAsmStmt,
         nnkMixinStmt, nnkBind, nnkBindStmt,
         nnkConstTy, nnkMutableTy, nnkSharedTy, # unused

         nnkChckRangeF, nnkChckRange64, nnkChckRange,

         nnkImportStmt, nnkImportExceptStmt,
         nnkExportStmt, nnkExportExceptStmt,
         nnkFromStmt, nnkIncludeStmt,

         nnkImportAs,
         nnkOfBranch,
         nnkPragmaBlock,

         nnkYieldStmt, nnkDefer,
         nnkReturnStmt,
         nnkBreakStmt, nnkContinueStmt, nnkStaticStmt,
         nnkUsingStmt, # UsingDefs

         nnkTypeOfExpr, nnkObjectTy,
         nnkTupleTy, nnkTupleClassTy, nnkTypeClassTy, nnkStaticTy,
         nnkRecList, nnkRecCase, nnkRecWhen, nnkDistinctTy,
         nnkProcTy, nnkIteratorTy, nnkEnumTy,
         nnkEnumFieldDef, nnkArgList, nnkPattern,
         nnkClosure, nnkGotoState, nnkState, nnkBreakState,

         nnkTryStmt, nnkHiddenTryStmt, nnkFinally, nnkExceptBranch, nnkRaiseStmt,

         nnkConstDef, nnkGenericParams,
         nnkWith, nnkWithout,
         nnkNone, nnkEmpty:
      node.throw_ast("StmtKind error: " & $node.kind)

impl_expect Stmt, meta(Stmt, All)

proc `{}`*(Self: type[meta(Stmt, All)], node: NimNode): Self =
   ## Constructor for any `Stmt` from a NimNode, performs canonicalizations. Low level api.
   {.line.}: expect(Stmt(detail: canon_and_verify(node)), Self)

func `$`*(self: Stmt): string = $self.detail

template `$`*(self: meta(Stmt, Sub)): string = $unsafe_conv(self, Stmt)

func copy*(self: meta(Stmt, All)): auto =
   ## Perform a recusive copy of `self`
   result = typeof(self)(detail: self.detail.copy)

func error*(self: Stmt, msg: varargs[string, `$`]) =
   # FIXME: dump node here
   core.error(msg.join, self.detail)

proc dbg*(self: Stmt | MaybeColon | IdentDef | ForLoopVars | Pragmas | AnyVarDef)
proc dbg_repr*(self: Stmt): string
proc dbg_repr*(self: MaybeColon): string
proc dbg_repr*(self: IdentDef): string
proc dbg_repr*(self: ForLoopVars): string
proc dbg_repr*(self: Pragmas): string
proc dbg_repr*(self: AnyVarDef): string

proc verbose_note*(self: Stmt | ForLoopVars): string =
   when defined(dump_node):
      result = expects.enclose(self.dbg_repr) & '\n' & expects.enclose($self.detail)
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

# FIXME: merge result with var sym? but what does the `impl` look like return?

func `{}`(Self: type[StmtKind], kind: NimSymKind): Self =
   case kind:
   of nskUnknown, nskConditional, nskDynLib, nskTemp, nskStub: Self.UnexposedSym
   of nskParam: Self.ParamSym
   of nskGenericParam: Self.GenericParamSym
   of nskModule: Self.ModuleSym
   of nskType: Self.TypeSym
   of nskVar: Self.VarSym
   of nskLet: Self.LetSym
   of nskConst: Self.ConstSym
   of nskResult: Self.ResultSym
   of nskProc: Self.ProcSym
   of nskFunc: Self.FuncSym
   of nskMethod: Self.MethodSym
   of nskIterator: Self.IteratorSym
   of nskConverter: Self.ConverterSym
   of nskMacro: Self.MacroSym
   of nskTemplate: Self.TemplateSym
   of nskField: Self.FieldSym
   of nskEnumField: Self.EnumFieldSym
   of nskForVar: Self.ForVarSym
   of nskLabel: Self.LabelSym

# --- Ident

proc `{}`*(Self: type[Ident], val: string): Self = Ident{macros.ident(val)}
   ## Create a new unbound identifier.

proc `==`*(a: Ident, b: string): bool = macros.eq_ident(a.detail, b)

# --- CompoundIdent

impl_container CompoundIdent, AnyIdent

proc delete*(self: CompoundIdent, i: Index) = core.delete(self.detail, i)

proc `{}`*(Self: type[CompoundIdent], vals: varargs[AnyIdent]): Self =
   result = Self{nnkAccQuoted{}}
   for val in vals:
      result.detail.add(val.detail)

# --- ChoiceSym

impl_container ChoiceSym, SingleSym

# --- AnyIdent

# FIXME: add `=~=` as an eq_ident like thing

proc val*(self: AnyIdent): string =
   # FIXME: nim bug: self instantiates endlessly, must use inner.
   match self:
   of ChoiceSym: result = self[0].val
   of CompoundIdent:
      for ident in self:
         result &= ident.val
   else: result = macros.str_val(self.detail)

# --- Sym

func `{}`(Self: type[NimSymKind], T: type[meta(Sym, Record)]): Self =
   when T is UnexposedSym: static_error("cannot generate an UnexposedSym")
   elif T is ParamSym: nskParam
   elif T is GenericParamSym: nskGenericParam
   elif T is ModuleSym: nskModule
   elif T is TypeSym: nskType
   elif T is VarSym: nskVar
   elif T is LetSym: nskLet
   elif T is ConstSym: nskConst
   elif T is ResultSym: nskResult
   elif T is ProcSym: nskProc
   elif T is FuncSym: nskFunc
   elif T is MethodSym: nskMethod
   elif T is IteratorSym: nskIterator
   elif T is ConverterSym: nskConverter
   elif T is MacroSym: nskMacro
   elif T is TemplateSym: nskTemplate
   elif T is FieldSym: nskField
   elif T is EnumFieldSym: nskEnumField
   elif T is ForVarSym: nskForVar
   elif T is LabelSym: nskLabel
   else: static_error("cannot generate a symbol of type: ", T)

proc gen*(Self: type[meta(Sym, Record)], val: string = ""): Self = Self{gen(NimSymKind{Self}, val)}

proc `{}`*(Self: type[meta(Sym, Record)]): Self = gen(Self)

# FIXME(nim): cannon use Sym{core.bind_ident(val)}, bind_ident is an actual symbol not nimnode
#proc bind_ident(val: static[string]): Sym =
#   ## Bind a new symbol from `val`.
#   result = Sym(detail: core.bind_ident(val))
#   assert(result.detail != nil)

proc `{}`*(Self: type[Sym], val: static[string]): Self = Sym{macros.bind_sym(val)}

# --- Name

# FIXME: what to do about `exported=` where the `ident` is a type checked symbol,
#        same issue for `ident=` where we have a postfix.

proc `{}`(Self: type[Name], node: NimNode): Self = Self(detail: node)

proc pos(self: Name): int =
   match self.detail:
   of nnkRoutines, nnkIdentDefs: result = 0
   else: self.detail.throw_ast

template verify_postfix(self: NimNode) =
   if not(self[call_like_name_pos] of nnkIdent and self[call_like_name_pos].eq_ident("*") and
          self[postfix_ident_pos] of nnkIdentLike):
      throw_ast(self)

proc ident*(self: Name): AnyIdent =
   match self.detail[self.pos]:
   of nnkPostfix:
      verify_postfix(self.detail[self.pos])
      result = AnyIdent{self.detail[self.pos][postfix_ident_pos]}
   of nnkIdentLike, nnkAccQuoted: result = AnyIdent{self.detail[self.pos]}
   else: self.detail.throw_ast

proc `ident=`*(self: Name, ident: AnyIdent) =
   match self.detail[self.pos]:
   of nnkPostfix:
      verify_postfix(self.detail[self.pos])
      self.detail[self.pos][postfix_ident_pos] = ident.detail
   of nnkIdentLike, nnkAccQuoted: self.detail[self.pos] = ident.detail
   else: self.detail.throw_ast

proc exported(self: NimNode): bool =
   match self:
   of nnkPostfix:
      verify_postfix(self)
      result = true
   of nnkSym: result = core.is_exported(self)
   of nnkIdent, nnkAccQuoted: result = false
   else: self.throw_ast

proc exported*(self: Name): bool = self.detail[self.pos].exported

proc `exported=`*(self: Name, exported: bool) =
   # FIXME: this is semchecked so we should error.
   #        We can't detect if it was gensymed so can't prevent the non-exported type checked case.
   #        Or can we by checking the type?
   if self.exported and self.detail[self.pos] of nnkSym:
      self.detail[self.pos].throw_ast("cannot set exported on a type checked symbol")
   self.detail[self.pos] = if exported: nnkPostfix{Ident{"*"}.detail, self.ident.detail}
                           else: self.ident.detail

# --- IdentDef

proc ident*(self: IdentDef): AnyIdent = Name{self.detail}.ident
   ## Return the ident in `self` skipping any backquotes or export markers.

proc `ident=`*(self: IdentDef, ident: AnyIdent) = Name{self.detail}.ident = ident

proc typ*(self: IdentDef): Option[Expr] =
   result = if self.detail[^2] of nnkEmpty: Expr.none else: Expr{self.detail[^2]}.some

proc `typ=`*(self: IdentDef, typ: Option[Expr]) =
   match typ of Some: self.detail[^2] = typ.detail
   else: self.detail[^2] = nnkEmpty{}

proc `typ=`*(self: IdentDef, typ: Expr) = self.detail[^2] = typ.detail

proc val*(self: IdentDef): Option[Expr] =
   result = if self.detail[^1] of nnkEmpty: Expr.none else: Expr{self.detail[^1]}.some

proc `val=`*(self: IdentDef, val: Expr) = self.detail[^1] = val.detail

proc `$`*(self: IdentDef): string = $self.detail
   ## Render this `IdentDef` as source code.

template empty_opt(self): NimNode = self.map((x) => x.detail).or_val(nnkEmpty{})

proc `{}`*(Self: type[IdentDef], ident_def: NimNode): IdentDef =
   Self(detail: ident_def.canon_and_verify)

proc `{}`*(Self: type[IdentDef], name: AnyIdent, typ = Expr.none, val = Expr.none): Self =
   result = Self(detail: nnkIdentDefs{name.detail, empty_opt(typ), empty_opt(val)})

# --- FormalParams

impl_container FormalParams, IdentDef, 1

# --- GenericParams

impl_container GenericParams, IdentDef

# --- Params

template unsafe_subconv*(self: Params, kinds: set[ParamsKind]): auto =
   unsafe_lca_subconv(self, kinds)

proc kind*(self: Params): ParamsKind =
   match self.detail:
   of nnkFormalParams: ParamsKind.FormalParams
   of nnkGenericParams: ParamsKind.GenericParams
   else: self.detail.throw_ast

proc len*(self: Params): int =
   match self:
   of FormalParams: result = self.len
   of GenericParams: result = self.len

proc `[]`*(self: Params, i: Index): IdentDef =
   match self:
   of FormalParams: result = self[i]
   of GenericParams: result = self[i]

proc `[]=`*(self: Params, i: Index, val: IdentDef) =
   match self:
   of FormalParams: self[i] = val
   of GenericParams: self[i] = val

impl_items Params

func add(self: Params, name: AnyIdent, typ: Expr, val: Expr) =
   self.detail.add(IdentDef{name, typ.some, val.some}.detail)

func add(self: Params, name: AnyIdent, typ: Expr) =
   self.detail.add(IdentDef{name, typ.some, Expr.none}.detail)

# --- StmtList

proc `{}`*(Self: type[StmtList], stmts: varargs[Stmt]): Self =
   result = Self{nnkStmtList{}}
   for stmt in stmts:
      result.detail.add(stmt.detail)

impl_container StmtList, Stmt

proc add*(self: StmtList, stmt: Stmt) =
   match stmt of StmtList:
      for stmt in stmt:
         self.add(stmt)
   else:
      self.detail.add(stmt.detail)

proc add*(self: StmtList, stmts: openarray[Stmt]) =
   for stmt in stmts:
      self.add(stmt)

# --- RoutineDecl

# FIXME: pragmas

proc ident*(self: RoutineDecl): AnyIdent = Name{self.detail}.ident

proc `ident=`*(self: RoutineDecl, ident: AnyIdent) = Name{self.detail}.ident = ident

proc exported*(self: RoutineDecl): bool = Name{self.detail}.exported

proc `exported=`*(self: RoutineDecl, exported: bool) = Name{self.detail}.exported = exported

#func formals=`

func formals*(self: RoutineDecl): FormalParams =
   result = FormalParams(detail: self.detail[routine_params_pos])

func `{}`(Self: type[NimNodeKind], kind: RoutineDeclKind): Self =
   match kind:
   of ProcDecl: nnkProcDef
   of FuncDecl: nnkFuncDef
   of IteratorDecl: nnkIteratorDef
   of ConverterDecl: nnkConverterDef
   of MethodDecl: nnkMethodDef
   of TemplateDecl: nnkTemplateDef
   of MacroDecl: nnkMacroDef

func `{}`(Self: type[NimNodeKind], T: type[meta(RoutineDecl, Record)]): Self =
   when T is ProcDecl: nnkProcDef
   elif T is FuncDecl: nnkFuncDef
   elif T is IteratorDecl: nnkIteratorDef
   elif T is ConverterDecl: nnkConverterDef
   elif T is MethodDecl: nnkMethodDef
   elif T is TemplateDecl: nnkTemplateDef
   elif T is MacroDecl: nnkMacroDef
   else: {.fatal: "unreachable".}

proc return_type(self: RoutineDecl, T: type[NimNode]): T =
   result = self.detail[routine_params_pos][formals_return_type_pos]

proc `return_type=`(self: RoutineDecl, val: NimNode) =
   self.detail[routine_params_pos][formals_return_type_pos] = val

proc return_type*(self: RoutineDecl): Option[Expr] =
   ## Get the return type of `self` if declared with one.
   result = if self.return_type(NimNode) of nnkEmpty: Expr.none
            else: Expr{self.return_type(NimNode)}.some

func `return_type=`*(self: RoutineDecl, typ: Expr) =
   ## Set the return type of `self`.
   self.return_type = typ.detail

func `return_type=`*(self: RoutineDecl, typ: Option[Expr]) =
   ## Set the  return type of `self`.
   match typ of Some: self.return_type = typ
   else: self.return_type = nnkEmpty{}

# FIXME: `body=`(Option[Stmt])

#proc body(self: RoutineDecl):

proc body*(self: RoutineDecl): Option[Stmt] =
   ## Return the body of this `RoutineDecl` if it has one.
   match self.detail[routine_body_pos] of nnkEmpty: Stmt.none
   else: Stmt{self.detail[routine_body_pos]}.some

proc `body=`*(self: RoutineDecl, stmt: Stmt) =
   ## Set the body of this `RoutineDecl`.
   self.detail[routine_body_pos] = stmt.detail

proc copy_as*(self: RoutineDecl, kind: RoutineDeclKind): RoutineDecl =
   result = RoutineDecl{NimNodeKind{kind}{}}
   for n in self.detail:
      result.detail.add(n.copy)

proc copy_as*(self: RoutineDecl, T: type[meta(RoutineDecl, Record)]): RoutineDecl =
   result = self.copy_as(first(kinds_of(T)))

proc `{}`*(
      Self: type[meta(RoutineDecl, Record)],
      ident: AnyIdent,
      formals: openarray[IdentDef] = [],
      return_type = Expr.none,
      body = StmtList{}.Stmt.some,
      pragmas: openarray[Expr] = [],
      ): Self =
   ## Initializer for routine decls.
   let params = nnkFormalParams{}
   match return_type of Some: params.add(return_type.detail)
   else: params.add(nnkEmpty{})
   for formal in formals:
      params.add(formal.detail)
   let pragmas =
      if pragmas.len > 0:
         let pragma_node = nnkPragma{}
         for pragma in pragmas:
            pragma_node.add(pragma.detail)
         pragma_node
      else: nnkEmpty{}
   let body = block:
      match body of Some: body.detail
      else: nnkEmpty{}
   result = Self{NimNodeKind{Self}{
      ident.detail,
      nnkEmpty{}, # FIXME: patterns
      nnkEmpty{}, # FIXME: generic params
      params,
      pragmas,
      nnkEmpty{}, # reserved
      body}}

# --- Arguments

impl_container Arguments, Expr, 1

proc args*(self: AnyCall): Arguments = Arguments(detail: self.detail)

# --- AnyCall

impl_field AnyCall, name, Expr, 0

template unpack*(self: AnyCall, name_name: untyped, args_name: untyped) =
   template name_name: Expr {.used.} = self.name
   template `name_name=`(val: Expr) {.used.} = self.name = val
   template args_name: Arguments {.used.} = self.args

# --- Call

proc add*(self: Call, arg: Expr) =
   self.detail.add(arg.detail)

proc `{}`*(Self: type[Call], name: AnyIdent, args: varargs[Expr]): Self =
   result = Self{nnkCall{name.detail}}
   for arg in args:
      result.add(arg)

proc bind_call*(self: static[string], args: varargs[Expr]): Call =
   result = Call{Sym{self}, args}

proc call*(self: AnyIdent, args: varargs[Expr]): Call = Call{self, args}

proc call*(self: RoutineDecl, args: varargs[Expr]): Call = Call{self.ident, args}

# FIXME: careful, adding to a Paren can mutate it into an anonymous tuple constructor.

# --- TypeExpr

impl_field TypeExpr, val, Expr, 0

# --- MaybeColon

proc kind*(self: MaybeColon): MaybeColonKind =
   match self.detail.kind of nnkExprColonExpr: MaybeColonKind.Colon
   else: MaybeColonKind.NoColon

proc `{}`*(Self: type[MaybeColon], node: NimNode): Self = Self(detail: node.canon_and_verify)

template unsafe_subconv*(self: MaybeColon, kinds: set[MaybeColonKind]): auto =
   when type_of(unsafe_lca_subconv(self, kinds)) is NoColon: val(unsafe_lca_subconv(self, kinds))
   else: unsafe_lca_subconv(self, kinds)

impl_expect MaybeColon, meta(MaybeColon, All)

# --- Colon

impl_field Colon, name, Expr, 0

impl_field Colon, val, Expr, 1

proc `{}`*(Self: type[Colon], node: NimNode): Self = Self(detail: node.canon_and_verify)

proc `{}`*(Self: type[Colon], name, val: Expr): Self =
   result = Self{nnkExprColonExpr{name.detail, val.detail}}

# --- NoColon

proc `{}`*(Self: type[NoColon], expr: Expr): Self = Self(detail: expr.detail)

proc val*(self: NoColon): Expr = Expr{self.detail}

# --- Container

proc offset*(self: Container): int =
   match self of ObjectConstr: 1
   else: 0

proc len*(self: Container): int = self.detail.len - self.offset

proc `[]`*(self: Container, i: Index): MaybeColon = MaybeColon{self.detail[i + self.offset]}

proc `[]=`*(self: Container, i: Index, maybe_colon: MaybeColon) =
   self.detail[i + self.offset] = maybe_colon.detail

proc `[]=`*(self: Container, i: Index, expr: Expr) =
   self.detail[i + self.offset] = expr.detail

impl_items Container

# --- Paren

proc val*(self: Paren): Expr = Expr{self.detail[0]}

# --- ExprContainer

impl_container ExprContainer, Expr

# --- ObjectConstr

# FIXME: name can be an option too for typechecked nodes or something, idk...

proc name*(self: ObjectConstr): Expr = Expr{self.detail[0]}

func `name=`*(self: ObjectConstr, expr: Expr) = self.detail[0] = expr.detail

template unpack*(self: ObjectConstr, name_name: untyped, fields_name: untyped) =
   template name_name: Expr {.used.} = self.name
   template `name_name=`(val: Expr) {.used.} = self.name = val

# --- Pragmas

proc `{}`*(Self: type[Pragmas], node: NimNode): Self = Self(detail: node.canon_and_verify)

proc into_pragma*(self: Expr): MaybeColon = NoColon{self}

proc add*(self: Pragmas, maybe_colon: MaybeColon) = self.detail.add(maybe_colon.detail)

proc add*(self: Pragmas, maybe_colons: openarray[MaybeColon]) =
   for maybe_colon in maybe_colons:
      self.add(maybe_colon)

proc add*(self: Pragmas, expr: Expr) = self.detail.add(expr.detail)

proc add*(self: Pragmas, exprs: openarray[Expr]) =
   for expr in exprs:
      self.add(expr)

proc `{}`*(Self: type[Pragmas]): Self =
   result = Self(detail: nnkPragma{})

proc `{}`*(Self: type[Pragmas], pragma: Expr | MaybeColon): Self =
   result = Self{}
   result.add(pragma)

proc `{}`*(Self: type[Pragmas], pragmas: openarray[Expr | MaybeColon]): Self =
   result = Self{}
   result.add(pragmas)

impl_container Pragmas, MaybeColon

# --- PragmaExpr

proc expr*(self: PragmaExpr): Expr = Expr{self.detail[0]}

proc pragmas*(self: PragmaExpr): Pragmas = Pragmas{self.detail[1]}

# --- StringLit

func lit*(val: string): StringLit =
   result = StringLit(detail: nnkStrLit{})
   macros.`str_val=`(result.detail, val)

# --- AnyVarDef

# FIXME: maybe expose the availability of the let/const val, WTF does this mean?

proc kind*(self: AnyVarDef): AnyVarDefKind =
   match self.detail:
   of nnkIdentDefs, nnkConstDef: AnyVarDefKind.IdentVarDef
   of nnkVarTuple: AnyVarDefKind.TupleVarDef
   else: self.detail.throw_ast

template unsafe_subconv*(self: AnyVarDef, kinds: set[AnyVarDefKind]): auto =
   when type_of(unsafe_lca_subconv(self, kinds)) is IdentVarDef:
      IdentDef{unsafe_lca_subconv(self, kinds).detail}
   else:
      unsafe_lca_subconv(self, kinds)

proc `{}`*(Self: type[AnyVarDef], node: NimNode): Self = Self(detail: node)

# --- TupleVarDef

proc len*(self: TupleVarDef): int = self.detail.len - 2

proc `[]`*(self: TupleVarDef, i: Index): AnyIdent = AnyIdent{self.detail[i]}

proc `[]=`*(self: TupleVarDef, i: Index, ident: AnyIdent) = self.detail[i] = ident.detail

impl_items TupleVarDef

# FIXME: duplicated with IdentDef

proc typ*(self: TupleVarDef): Option[Expr] =
   result = if self.detail[^2] of nnkEmpty: Expr.none else: Expr{self.detail[^2]}.some

proc `typ=`*(self: TupleVarDef, typ: Option[Expr]) =
   match typ of Some: self.detail[^2] = typ.detail
   else: self.detail[^2] = nnkEmpty{}

proc `typ=`*(self: TupleVarDef, typ: Expr) = self.detail[^2] = typ.detail

proc val*(self: TupleVarDef): Option[Expr] =
   result = if self.detail[^1] of nnkEmpty: Expr.none else: Expr{self.detail[^1]}.some

proc `val=`*(self: TupleVarDef, val: Expr) = self.detail[^1] = val.detail

# --- AnyVarDefs

template `{}`(Self: type[NimNodeKind], T: type[meta(AnyVarDefs, Record)]): Self =
   when T is VarDefs: nnkVarSection
   elif T is LetDefs: nnkLetSection
   elif T is VarDefs: nnkConstSection
   else: {.fatal: "unreachable".}

func `{}`*(Self: type[meta(AnyVarDefs, Record)], name: AnyIdent, val: Expr): Self =
   result = Self(detail: NimNodeKind{Self}{})
   # FIXME(nim): when this is a match statement weird case coverage errors, the code doesn't make sense but the error message was nonsense.
   when result is VarDefs or result is LetDefs:
      result.detail.add(IdentDef{name, val = val.some}.detail)
   elif result is ConstDefs:
      {.fatal: "FIXME".}
   else: {.fatal: "unreachable".}

impl_container AnyVarDefs, AnyVarDef

# --- TypeDefs

proc add*(self: TypeDefs, type_def: TypeDef) =
   self.detail.add(type_def.detail)

proc add*(self: TypeDefs, type_defs: openarray[TypeDef]) =
   for type_def in type_defs: self.add(type_def)

proc `{}`*(Self: type[TypeDefs], type_defs: varargs[TypeDef]): Self =
   result = Self{nnkTypeSection{}}
   result.add(type_Defs)

# --- TypeDef

proc `{}`(Self: type[TypeDef], name: AnyIdent, pub: bool, pragmas: Pragmas, node: NimNode): Self =
   var name = name.detail
   # FIXME: why are brackets needed here?
   if pub: name = nnkPostfix{[Ident{"*"}.detail, name]}
   if pragmas.len != 0: name = nnkPragmaExpr{[name, pragmas.detail]} # FIXME: this could cause unexpected behavior if the user adds to the pragma node later.
   result = Self(detail: nnkTypeDef{[name, nnkEmpty{}, node]})

proc `{}`*(Self: type[TypeDef], name: AnyIdent, pub: bool, expr: Expr): Self =
   result = Self{name, pub, Pragmas{}, expr.detail}

proc `{}`*(Self: type[TypeDef], name: AnyIdent, expr: Expr): Self =
   result = Self{name, false, Pragmas{}, expr.detail}

proc `{}`*(
      Self: type[TypeDef],
      name: AnyIdent,
      pub: bool,
      pragmas: Pragmas,
      body: TypeDefBody
      ): Self =
   result = Self{name, pub, pragmas, body.detail}

proc `{}`*(Self: type[TypeDef], name: AnyIdent, pragmas: Pragmas, body: TypeDefBody): Self =
   result = Self{name, false, pragmas, body.detail}

proc `{}`*(Self: type[TypeDef], name: AnyIdent, pub: bool, body: TypeDefBody): Self =
   result = Self{name, pub, Pragmas{}, body.detail}

proc `{}`*(Self: type[TypeDef], name: AnyIdent, body: TypeDefBody): Self =
   result = Self{name, false, Pragmas{}, body.detail}

# --- Block

func `{}`(Self: type[Block], stmts: varargs[Stmt]): Self =
   # FIXME: stmt list vs stmt list expr
   result = Self{nnkBlockStmt{nnkEmpty{}, StmtList{stmts}.detail}}

proc label*(self: Block): Option[AnyIdent] =
   match self.detail[0]:
   of nnkIdentLike: AnyIdent{self.detail[0]}.some
   else: AnyIdent.none

proc `label=`*(self: Block, val: AnyIdent) = self.detail[0] = val.detail

impl_field Block, body, Stmt, 1

# --- Dot

impl_field Dot, lhs, Expr, 0
impl_field Dot, rhs, Expr, 1

# --- Asgn

func `{}`*(Self: type[Asgn], lhs, rhs: Expr): Self = Self{nnkAsgn{lhs.detail, rhs.detail}}

impl_field Asgn, lhs, Expr, 0
impl_field Asgn, rhs, Expr, 1

template unpack*(self: Asgn, lhs_name, rhs_name) =
   template lhs_name: Expr = self.lhs
   template rhs_name: Expr = self.rhs

# --- Discard

func `{}`*(Self: type[Discard]): Self = Self{nnkDiscardStmt{nnkEmpty{}}}

# --- Comment

func val*(self: Comment): string = macros.str_val(self.detail)

template unpack*(self: Comment, val_name) =
   template val_name: string = self.val

# --- ForLoop

proc vars*(self: ForLoop): ForLoopVars = ForLoopVars(detail: self.detail) # FIXME: canon

impl_field ForLoop, expr, Expr, ^2

impl_field ForLoop, body, Stmt, ^1

template unpack*(self: ForLoop, vars_name, expr_name, body_name) =
   template vars_name: ForLoopVars = self.vars
   template expr_name: Expr = self.expr
   template body_name: Stmt = self.body

# --- ForLoopVars

# FIXME: expose the structure of these somehow, right now they are being flattened.
#        treat them similar to AnyVarDef

proc collect_for_loop_vars(self: NimNode): seq[NimNode] =
   for i in 0 ..< self.len - 2:
      match self[i]:
      of nnkIdentLike: result.add(self[i])
      of nnkVarTuple:
         for j in 0 ..< self[i].len - 1:
            match self[i][j]:
            of nnkIdentLike: result.add(self[i][j])
            else: self[i][j].error("unreachable")
      else: self[i].error("unreachable")

proc len*(self: ForLoopVars): int = self.detail.collect_for_loop_vars.len

proc `[]`*(self: ForLoopVars, i: Index): AnyIdent = AnyIdent{collect_for_loop_vars(self.detail)[i]}

proc `[]=`*(self: ForLoopVars, i: Index, ident: AnyIdent) =
   var cur_var_i = 0
   template check(x) =
      if i == cur_var_i: x
      inc(cur_var_i)
   for var_base_i in 0 ..< self.detail.len - 2:
      match self.detail[var_base_i]:
      of nnkIdentLike:
         check: self.detail[var_base_i] = ident.detail
      of nnkVarTuple:
         for tuple_i in 0 ..< self.detail[var_base_i].len - 1:
            match self.detail[var_base_i][tuple_i]:
            of nnkIdentLike:
               check: self.detail[var_base_i][tuple_i] = ident.detail
            else: self.detail[var_base_i][tuple_i].error("unreachable")
      else: self.detail[var_base_i].error("unreachable")

impl_items ForLoopVars

# --- EnumTypeDefBody

proc `{}`*(Self: type[EnumTypeDefBody]): Self = Self(detail: nnkEnumTy{[nnkEmpty{}]})

proc len*(self: EnumTypeDefBody): int = self.detail.len - 1

proc add*(self: EnumTypeDefBody, name: AnyIdent) = self.detail.add(name.detail)

# --- ObjectTypeDefBody

proc `{}`*(Self: type[ObjectTypeDefBody], inherits = AnyIdent.none): Self =
   let inherits = block:
      match inherits of Some: nnkOfInherit{[inherits.detail]}
      else: nnkEmpty{}
   result = Self(detail: nnkObjectTy{[nnkEmpty{}, inherits, nnkRecList{}]})

proc `{}`*(Self: type[ObjectTypeDefBody], inherits: AnyIdent): Self =
   result = Self{inherits.some}

proc add*(self: ObjectTypeDefBody, field: FieldDef) =
   self.detail[object_def_fields_pos].add(field.detail)

proc add*(self: ObjectTypeDefBody, fields: openarray[FieldDef]) =
   for field in fields:
      self.add(field)

# --- FieldDef

proc `{}`*(Self: type[FieldDef], name: AnyIdent, pub: bool, typ: Expr): Self =
   var name = name.detail
   if pub: name = nnkPostfix{[core.ident("*"), name]}
   result = FieldDef(detail: nnkIdentDefs{[name, typ.detail, nnkEmpty{}]})

proc `{}`*(Self: type[FieldDef], name: AnyIdent, typ: Expr): Self = Self{name, false, typ}

# ---

proc lit*(val: bool): EnumFieldSym =
   result = expect(if val: Sym{"true"} else: Sym{"false"}, EnumFieldSym)

proc skip(self: Stmt, Skip: type[Paren], n = high(int)): Stmt =
   var n = n
   result = self
   while true:
      match result as paren of Paren and n > 0:
         result = paren.val
         dec(n)
      else:
         break

include macros2/private/[dbg, visiting, quoting]

proc m2_parse_type(typ: Expr): auto =
   match typ of Curly: result = (macro_type: Expr.none,
                                 variant_type: typ.expect(1).expect(NoColon).val.some)
   else: typ.error("failed to parse 'm2' type expression")

macro m2*(macro_decl): auto =
   # FIXME: fix doc comments, they are hidden in inner_def
   ## Process macro signature extensions. This is a pragma macro for macros.

   let def = Stmt{macro_decl}.expect(MacroDecl)
   let inner_def = def.copy_as(ProcDecl)
   inner_def.ident = ProcSym.gen(def.ident.val)
   inner_def.body = def.body.expect("macros cannot be forward declared")
   inner_def.exported = false

   match def.return_type of Some:
      let type_info = m2_parse_type(return_type)
      def.return_type = type_info.macro_type.or_val(!auto)
      inner_def.return_type = type_info.variant_type.or_val(!Stmt)
   else:
      def.return_type = !auto
      inner_def.return_type = !Stmt

   let call = inner_def.call
   for i in 0 ..< def.formals.len:
      match def.formals[i].typ of Some:
         let type_info = m2_parse_type(typ)
         def.formals[i].typ = type_info.macro_type
         inner_def.formals[i].typ = type_info.variant_type.or_val(!Stmt)
         call.add(type_info.variant_type
                     .map((typ) => !`typ`{`def.formals[i].ident`})
                     .or_val(!Stmt{`def.formals[i].ident`}))
      else: def.error("FIXME")

   def.body = AST:
      `inner_def`
      result = `call`.detail
   result = def.detail
