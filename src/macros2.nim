# Every nimnode must go through a canonicalizing Stmt`{}`

# FIXME: indexing should not introduce subtle bugs, we need to handle backwards better.
# FIXME: restrict AnyIdent to weed out invalid bound sym kinds.
# FIXME: make static[int] expect work
# FIXME: should expect always return a value? but sometimes we just want to verify a property.
#       {.discardable.}?
# FIXME: we generate a lot of stuff which is not so nice for doc generation.
# FIXME: expect_match
# FIXME: CompoundIdent can hold syms.

import
   std/sequtils,
   mainframe,
   options2,
   macros2/private/[vm_timings, gen]

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

generate MaybeColon:
   NoColon
   Colon

generate AnyVarDef:
   IdentVarDef
   TupleVarDef

type
   NimNodeParseError* = object of ValueError
      node: NimNode
   Formals* = object ## The non-generic, non-return-type parameters of a function.
      detail: NimNode
   Arguments* = object ## The arguments of some sort of call.
      detail: NimNode
   ForLoopVars* = object
      detail: NimNode
   IdentDef* = object ## A triplet of `AnyIdent, Option[Expr], Option[Expr]`
      detail: NimNode
   Pragmas* = object
      detail: NimNode
   Index* = int | BackwardsIndex ## The index type apis should be migrated too.

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
   of nnkFormalParams:
      var ident_defs = seq[NimNode].default
      for i in 1 ..< self.len:
         for j in 0 ..< self[i].len - 2:
            ident_defs.add(nnkIdentDefs{self[i][j], self[i][^2], self[i][^1]})
      self.set_len(1)
      for ident_def in ident_defs:
         self.add(ident_def)
   of nnkStmtListLike:
      # FIXME: stmt list flattening?
      for i in 0 ..< self.len:
         self[i] = self[i].v
   of nnkAccQuoted:
      for i in 0 ..< self.len:
         self[i] = self[i].v
         self[i].expect(nnkIdentLike)
   of nnkCall:
      for i in 0 ..< self.len:
         self[i] = self[i].v
   of nnkIdent, nnkSym: discard
   else:
      when false:
         self.error("FIXME: canonicalize " & $self.kind & " \n" & self.tree_repr)
      else:
         for i in 0 ..< self.len:
            self[i] = self[i].v

# --- Stmt

template throw_ast(self: Stmt, msg = "") = throw_ast(self.detail, msg)

func `==`*(a: StmtAllMeta, b: StmtAllMeta): bool = a.detail == b.detail
   ## Uses same equality as `NimNode`.

template unsafe_downconv*(self: Stmt, kinds: openarray[set[StmtKind]]): auto =
   unsafe_lca_downconv(self, kinds)

func `{}`*(Self: type[StmtKind], kind: NimSymKind): Self

func `{}`*(Self: type[StmtKind], node: NimNode): Self {.time.} =
   if node.is_uninit: node.throw_ast("node is not initialized")
   match node:
   of nnkIdent: StmtKind.Ident
   of nnkAccQuoted: StmtKind.CompoundIdent
   of nnkOpenSymChoice: StmtKind.OpenChoiceSym
   of nnkClosedSymChoice: StmtKind.ClosedChoiceSym
   of nnkSym: StmtKind{node.sym_kind}

   of nnkCharLit: StmtKind.CharLit
   of nnkIntLit: StmtKind.IntLit
   of nnkInt8Lit: StmtKind.Int8Lit
   of nnkInt16Lit: StmtKind.Int16Lit
   of nnkInt32Lit: StmtKind.Int32Lit
   of nnkInt64Lit: StmtKind.Int64Lit
   of nnkUIntLit: StmtKind.UIntLit
   of nnkUInt8Lit: StmtKind.UInt8Lit
   of nnkUInt16Lit: StmtKind.UInt16Lit
   of nnkUInt32Lit: StmtKind.UInt32Lit
   of nnkUInt64Lit: StmtKind.UInt64Lit
   of nnkFloatLit: StmtKind.FloatLit
   of nnkFloat32Lit: StmtKind.Float32Lit
   of nnkFloat64Lit: StmtKind.Float64Lit
   of nnkFloat128Lit: StmtKind.Float128Lit
   of nnkStrLit: StmtKind.StringLit
   of nnkTripleStrLit: StmtKind.MultilineStringLit
   of nnkNilLit: StmtKind.NilLit
   of nnkCurly, nnkTableConstr: StmtKind.Curly
   of nnkTupleConstr: StmtKind.TupleConstr
   of nnkPar:
      if node.len == 1 and node[0].kind != nnkExprColonExpr: StmtKind.Paren
      else: StmtKind.TupleConstr
   of nnkBracket: StmtKind.Bracket
   of nnkRStrLit: StmtKind.StringLitCall # own kind | StringLitCall | property on string lit.
   of nnkCall: StmtKind.Call
   of nnkPrefix: StmtKind.PrefixCall
   of nnkInfix: StmtKind.InfixCall
   of nnkCommand: StmtKind.CommandCall
   of nnkCallStrLit: StmtKind.StringLitCall
   of nnkProcDef: StmtKind.ProcDecl
   of nnkFuncDef: StmtKind.FuncDecl
   of nnkIteratorDef: StmtKind.IteratorDecl
   of nnkConverterDef: StmtKind.ConverterDecl
   of nnkMethodDef: StmtKind.MethodDecl
   of nnkTemplateDef: StmtKind.TemplateDecl
   of nnkMacroDef: StmtKind.MacroDecl
   of nnkStmtListLike: StmtKind.StmtList
   of nnkBlockLike: StmtKind.Block
   of nnkAsgn, nnkFastAsgn: StmtKind.Asgn
   of nnkConv, nnkObjDownConv, nnkObjUpConv, nnkHiddenSubConv, nnkStringToCString,
         nnkCStringToString: StmtKind.Conv
   of nnkObjConstr: StmtKind.ObjectConstr
   of nnkCommentStmt: StmtKind.Comment
   of nnkForStmt, nnk_par_for_stmt: StmtKind.ForLoop # FIXME: expose the par part
   of nnkWhileStmt: StmtKind.WhileLoop
   of nnkCurlyExpr: StmtKind.CurlyCall
   of nnkBracketExpr: StmtKind.BracketCall
   of nnkPragmaExpr: StmtKind.PragmaExpr
   of nnkRefTy: StmtKind.RefTypeExpr
   of nnkPtrTy: StmtKind.PtrTypeExpr
   of nnkVarTy: StmtKind.VarTypeExpr
   of nnkDotExpr: StmtKind.Dot
   of nnkDiscardStmt: StmtKind.Discard
   of nnkTypeSection: StmtKind.TypeDefs
   of nnkVarSection: StmtKind.VarDefs
   of nnkLetSection: StmtKind.LetDefs
   of nnkConstSection: StmtKind.ConstDefs
   of nnkDotCall,
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
         nnkTypeDef, # error: TypeDef
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
         nnkWhenStmt,
         nnkCaseStmt,
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
      node.throw_ast("unexpected kind resolution: " & $node.kind)

proc kind*(self: Stmt): StmtKind = StmtKind{self.detail}

impl_expect Stmt, StmtAllMeta

proc `{}`*(Self: type[StmtAllMeta], node: NimNode): Self =
   ## Constructor for any `Stmt` from a NimNode, performs canonicalizations. Low level api.
   {.line.}: expect(Stmt(detail: canon_and_verify(node)), Self)

func `$`*(self: Stmt): string {.time.} = $self.detail

template `$`*(self: StmtChildrenMeta): string = $unsafe_conv(self, Stmt)

func copy*[T: Stmt](self: T): T {.time.} =
   ## Perform a recusive copy of `self`
   result = T(detail: self.detail.copy)

func error*(self: Stmt, msg: varargs[string, `$`]) {.time.} =
   # FIXME: dump node here
   core.error(msg.join, self.detail)

proc dbg*(self: Stmt | Colon | IdentDef | ForLoopVars | AnyVarDef)
proc dbg_repr*(self: ForLoopVars): string
proc dbg_repr*(self: MaybeColon): string
proc dbg_repr*(self: IdentDef): string
proc dbg_repr*(self: Pragmas): string
proc dbg_repr*(self: AnyVarDef): string
proc dbg_repr*(self: Stmt): string

proc verbose_note*(self: Stmt | ForLoopVars): string {.time.} =
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

# Structure of identifiers
# single_ident # some symbol, can be vm generated and not representable without backticks.
# `compound identifier` # a backticked ident or multiple idents. also abused for quoting expressions.
# symbols # single bound sym, open/closed sym choices

# routine name # can be postfixed, FIXME: no pragmas?

# FIXME: merge result with var sym? but what does the `impl` look like return?

func `{}`(Self: type[StmtKind], kind: NimSymKind): Self =
   case kind:
   of nskUnknown, nskConditional, nskDynLib, nskTemp, nskStub: StmtKind.UnexposedSym
   of nskParam: StmtKind.ParamSym
   of nskGenericParam: StmtKind.GenericParamSym
   of nskModule: StmtKind.ModuleSym
   of nskType: StmtKind.TypeSym
   of nskVar: StmtKind.VarSym
   of nskLet: StmtKind.LetSym
   of nskConst: StmtKind.ConstSym
   of nskResult: StmtKind.ResultSym
   of nskProc: StmtKind.ProcSym
   of nskFunc: StmtKind.FuncSym
   of nskMethod: StmtKind.MethodSym
   of nskIterator: StmtKind.IteratorSym
   of nskConverter: StmtKind.ConverterSym
   of nskMacro: StmtKind.MacroSym
   of nskTemplate: StmtKind.TemplateSym
   of nskField: StmtKind.FieldSym
   of nskEnumField: StmtKind.EnumFieldSym
   of nskForVar: StmtKind.ForVarSym
   of nskLabel: StmtKind.LabelSym

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

proc val*(self: AnyIdent): string =
   # FIXME: nim bug: self instantiates endlessly, must use inner.
   match self:
   of ChoiceSym: result = self[0].val
   of CompoundIdent:
      for ident in self:
         result &= ident.val
   else: result = macros.str_val(self.detail)

# --- SymRecordsMeta

proc gen*(Self: type[SymRecordsMeta], val: string = ""): Self = Self{gen(NimSymKind{Self}, val)}

proc `{}`*(Self: type[SymRecordsMeta]): Self = gen(Self)

func `{}`(Self: type[NimSymKind], T: type[SymRecordsMeta]): Self =
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


# FIXME(nim): cannon use Sym{core.bind_ident(val)}, bind_ident is an actual symbol not nimnode
#proc bind_ident(val: static[string]): Sym =
#   ## Bind a new symbol from `val`.
#   result = Sym(detail: core.bind_ident(val))
#   assert(result.detail != nil)

proc `{}`*(Self: type[Sym], val: static[string]): Self = Sym{macros.bind_sym(val)}

func skip_ident_quals(self: NimNode): NimNode =
   match self:
   of nnkPostfix:
      assert(self.len == 2)
      assert(self[0].eq_ident("*"))
      result = skip_ident_quals(self[1])
   of nnkIdentLike: result = self
   else: self.error("unhandled ident quals")

# --- IdentDef

proc ident*(self: IdentDef): AnyIdent = AnyIdent{self.detail[0].skip_ident_quals}
   ## Return the ident in `self` skipping any backquotes or export markers.

proc typ*(self: IdentDef): Option[Expr] =
   result = if self.detail[^2] of nnkEmpty: none(Expr) else: some(Expr{self.detail[^2]})

proc `typ=`*(self: IdentDef, typ: Option[Expr]) =
   match typ of Some: self.detail[^2] = typ.detail
   else: self.detail[^2] = nnkEmpty{}

proc `typ=`*(self: IdentDef, typ: Expr) = self.detail[^2] = typ.detail

proc val*(self: IdentDef): Option[Expr] =
   result = if self.detail[^1] of nnkEmpty: none(Expr) else: some(Expr{self.detail[^1]})

proc `val=`*(self: IdentDef, val: Expr) = self.detail[^1] = val.detail

proc `$`*(self: IdentDef): string = $self.detail
   ## Render this `IdentDef` as source code.

template empty_opt(self): NimNode = self.map((x) => x.detail).or_val(nnkEmpty{})

proc `{}`*(Self: type[IdentDef], ident_def: NimNode): IdentDef =
   Self(detail: ident_def.canon_and_verify)

proc `{}`*(Self: type[IdentDef], name: AnyIdent, typ = none(Expr), val = none(Expr)): Self =
   result = Self(detail: nnkIdentDefs{name.detail, empty_opt(typ), empty_opt(val)})

# --- Formals

impl_container Formals, IdentDef, 1

func add(self: Formals, name: AnyIdent, typ: Expr, val: Expr) =
   self.detail.add(IdentDef{name, some(typ), some(val)}.detail)

func add(self: Formals, name: AnyIdent, typ: Expr) =
   self.detail.add(IdentDef{name, some(typ), none(Expr)}.detail)

func formals*(self: RoutineDecl): Formals =
   result = Formals(detail: self.detail[routine_params_pos])

# --- StmtList

proc `{}`*(Self: type[StmtList], stmts: varargs[Stmt]): Self =
   result = Self{nnkStmtList{}}
   for stmt in stmts:
      result.detail.add(stmt.detail)

impl_container StmtList, Stmt

func add*(self: StmtList, stmt: Stmt) = self.detail.add(stmt.detail)

# --- RoutineDecl

func `{}`(Self: type[NimNodeKind], kind: RoutineDeclKind): Self =
   match kind:
   of ProcDecl: nnkProcDef
   of FuncDecl: nnkFuncDef
   of IteratorDecl: nnkIteratorDef
   of ConverterDecl: nnkConverterDef
   of MethodDecl: nnkMethodDef
   of TemplateDecl: nnkTemplateDef
   of MacroDecl: nnkMacroDef

func `{}`(Self: type[NimNodeKind], T: type[RoutineDeclRecordsMeta]): Self =
   when T is ProcDecl: nnkProcDef
   elif T is FuncDecl: nnkFuncDef
   elif T is IteratorDecl: nnkIteratorDef
   elif T is ConverterDecl: nnkConverterDef
   elif T is MethodDecl: nnkMethodDef
   elif T is TemplateDecl: nnkTemplateDef
   elif T is MacroDecl: nnkMacroDef
   else: {.fatal: "unreachable".}

func return_type*(self: RoutineDecl): Option[Expr] =
   ## Get the return type of `self` if it has one.
   if self.detail[routine_params_pos][0] of nnkEmpty:
      result = none Expr
   else:
      result = some Expr(detail: self.detail[routine_params_pos][0])

func `return_type=`*(self: RoutineDecl, typ: Expr) =
   ## Set the return type of `self`.
   self.detail[routine_params_pos][0] = typ.detail

proc body*(self: RoutineDecl): Option[Stmt] =
   ## Return the body of this `RoutineDecl` if it has one.
   match self.detail[routine_body_pos] of nnkEmpty: none(Stmt)
   else: some(Stmt{self.detail[routine_body_pos]})

proc `body=`*(self: RoutineDecl, stmt: Stmt) =
   ## Set the body of this `RoutineDecl`.
   self.detail[routine_body_pos] = stmt.detail

proc copy_as*(self: RoutineDecl, kind: RoutineDeclKind): RoutineDecl =
   result = RoutineDecl{NimNodeKind{kind}{}}
   for n in self.detail:
      result.detail.add(n.copy)

proc copy_as*(self: RoutineDecl, T: type[RoutineDeclRecordsMeta]): RoutineDecl =
   result = self.copy_as(first(rtti_range(T)))

func read_pub(self: NimNode): bool =
   # FIXME: account for sem checked symbols here too.
   match self:
   of nnkPostfix: result = true
   else: result = false

func pub*(self: RoutineDecl): bool = self.detail[0].read_pub

func `pub=`(self: RoutineDecl, val: bool) =
   match self.detail[0]:
   of nnkPostfix:
      assert(self.detail[0][0].eq_ident("*"))
      if not val:
         self.detail[0] = self.detail[0][1]
   elif val:
      self.detail[0] = nnkPostfix{"*", self.detail[0]}

proc ident*(self: RoutineDecl): AnyIdent = AnyIdent{self.detail[0].skip_ident_quals}

func `ident=`*(self: RoutineDecl, name: AnyIdent) =
   ## Set the name of `self` to
   match self.detail[0]:
   of nnkPostfix: self.detail[0][1] = name.detail
   of nnkAccQuoted, nnkIdent, nnkSym: self.detail[0] = name.detail
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
   let params = nnkFormalParams{}
   match return_type of Some:
      params.add(return_type.detail)
   else:
      params.add(nnkEmpty{})
   for formal in formals:
      params.add(formal.detail)
   var pragmas =
      if pragmas.len > 0:
         let pragma_node = nnkPragma{}
         for pragma in pragmas:
            pragma_node.add(pragma.detail)
         pragma_node
      else:
         nnkEmpty{}
   var body = block:
      match body of Some: body.detail
      else: nnkEmpty{}
   result = Self{NimNodeKind{Self}{
      ident.detail, # name
      nnkEmpty{}, # patterns
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

template unsafe_downconv*(self: MaybeColon, kinds: openarray[set[MaybeColonKind]]): auto =
   when type_of(unsafe_lca_downconv(self, kinds)) is NoColon: val(unsafe_lca_downconv(self, kinds))
   else: unsafe_lca_downconv(self, kinds)

impl_expect MaybeColon, MaybeColonAllMeta

# --- Colon

impl_field Colon, name, Expr, 0

impl_field Colon, val, Expr, 1

proc `{}`*(Self: type[Colon], node: NimNode): Self = Self(detail: node.canon_and_verify)

proc `{}`*(Self: type[Colon], name, val: Expr): Self =
   result = Self{nnkExprColonExpr{name.detail, val.detail}}

# --- NoColon

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

# --- ExprContainer

impl_container ExprContainer, Expr

# --- ObjectConstr

# FIXME: name can be an option too for typechecked nodes...

proc name*(self: ObjectConstr): Expr = Expr{self.detail[0]}

func `name=`*(self: ObjectConstr, expr: Expr) = self.detail[0] = expr.detail

template unpack*(self: ObjectConstr, name_name: untyped, fields_name: untyped) =
   template name_name: Expr {.used.} = self.name
   template `name_name=`(val: Expr) {.used.} = self.name = val

# --- Pragmas

proc `{}`*(Self: type[Pragmas], node: NimNode): Self = Self(detail: node.canon_and_verify)

proc `{}`*(Self: type[Pragmas]): Self = Self(detail: nnkPragma{})

impl_container Pragmas, MaybeColon

# --- PragmaExpr

proc expr*(self: PragmaExpr): Expr = Expr{self.detail[0]}

proc pragmas*(self: PragmaExpr): Pragmas = Pragmas{self.detail[1]}

# --- StringLit

func lit*(val: string): StringLit =
   result = StringLit(detail: nnkStrLit{})
   macros.`str_val=`(result.detail, val)

# --- AnyVarDef

# FIXME: maybe expose the availability of the let/const val.

proc kind*(self: AnyVarDef): AnyVarDefKind =
   match self.detail:
   of nnkIdentDefs, nnkConstDef: AnyVarDefKind.IdentVarDef
   of nnkVarTuple: AnyVarDefKind.TupleVarDef
   else: self.detail.throw_ast

template unsafe_downconv*(self: AnyVarDef, kinds: openarray[set[AnyVarDefKind]]): auto =
   when type_of(unsafe_lca_downconv(self, kinds)) is IdentVarDef:
      IdentDef{unsafe_lca_downconv(self, kinds).detail}
   else: unsafe_lca_downconv(self, kinds)

proc `{}`*(Self: type[AnyVarDef], node: NimNode): Self = Self(detail: node)

# --- TupleVarDef

proc len*(self: TupleVarDef): int = self.detail.len - 2

proc `[]`*(self: TupleVarDef, i: Index): AnyIdent = AnyIdent{self.detail[i]}

proc `[]=`*(self: TupleVarDef, i: Index, ident: AnyIdent) = self.detail[i] = ident.detail

impl_items TupleVarDef

# FIXME: duplicated with IdentDef

proc typ*(self: TupleVarDef): Option[Expr] =
   result = if self.detail[^2] of nnkEmpty: none(Expr) else: some(Expr{self.detail[^2]})

proc `typ=`*(self: TupleVarDef, typ: Option[Expr]) =
   match typ of Some: self.detail[^2] = typ.detail
   else: self.detail[^2] = nnkEmpty{}

proc `typ=`*(self: TupleVarDef, typ: Expr) = self.detail[^2] = typ.detail

proc val*(self: TupleVarDef): Option[Expr] =
   result = if self.detail[^1] of nnkEmpty: none(Expr) else: some(Expr{self.detail[^1]})

proc `val=`*(self: TupleVarDef, val: Expr) = self.detail[^1] = val.detail

# --- AnyVarDefs

template `{}`(Self: type[NimNodeKind], T: type[AnyVarDefsRecordsMeta]): Self =
   when T is VarDefs: nnkVarSection
   elif T is LetDefs: nnkLetSection
   elif T is VarDefs: nnkConstSection
   else: {.fatal: "unreachable".}

func `{}`*(Self: type[AnyVarDefsRecordsMeta], name: AnyIdent, val: Expr): Self =
   result = Self(detail: NimNodeKind{Self}{})
   when result is VarDefs or result is LetDefs: # FIXME(nim): when this is a match statement weird case coverage errors, the code doesn't make sense but the error message was nonsense.
      result.detail.add(IdentDef{name, val = some(val)}.detail)
   elif result is ConstDefs: {.fatal: "FIXME".}
   else: {.fatal: "unreachable".}

impl_container AnyVarDefs, AnyVarDef

# --- Block

func `{}`(Self: type[Block], stmts: varargs[Stmt]): Self =
   # FIXME: stmt list vs stmt list expr
   result = Self{nnkBlockStmt{nnkEmpty{}, StmtList{stmts}.detail}}

proc label*(self: Block): Option[AnyIdent] =
   match self.detail[0]:
   of nnkIdentLike: some(AnyIdent{self.detail[0]})
   else: none(AnyIdent)

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

proc vars*(self: ForLoop): ForLoopVars = ForLoopVars(detail: self.detail)

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

# ---

proc lit*(val: bool): EnumFieldSym =
   result = expect(if val: Sym{"true"} else: Sym{"false"}, EnumFieldSym)

proc skip(self: Stmt, Skip: type[Paren], n = high(int)): Stmt =
   result = self
   while true:
      match result as paren of Paren and n > 0: result = paren
      else: break

include macros2/private/[dbg, visiting, quoting]

proc m2_parse_type(typ: Expr): auto =
   match typ of Curly: result = (macro_type: none(Expr),
                                 variant_type: some(typ.expect(1).expect(NoColon).val))
   else: typ.error("failed to parse 'm2' type expression")

macro m2*(macro_decl): auto =
   # FIXME: fix doc comments, they are hidden in inner_def
   ## Process macro signature extensions. This is a pragma macro for macros.

   let def = Stmt{macro_decl}.expect(MacroDecl)
   let inner_def = def.copy_as(ProcDecl)
   inner_def.ident = ProcSym.gen(def.ident.val)
   inner_def.body = def.body.expect("macros cannot be forward declared")
   inner_def.pub = false

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
      else:
         def.error("FIXME")

   def.body = AST:
      `inner_def`
      result = `call`.detail
   result = def.detail
