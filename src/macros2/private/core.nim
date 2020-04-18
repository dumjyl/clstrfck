import expects
export expects
from std/strutils import indent
from std/macros import
   NimNodeKind, NimNodeKinds, kind,
   NimSymKind, sym_kind, get_impl,
   NimTypeKind, type_kind, get_type, get_type_inst, get_type_impl,
   `==`, `[]`, `[]=`, len, copy, insert, items,
   eq_ident, error, params, `params=`, body, `body=`, name, nnkCallKinds,
   line_info, line_info_obj, tree_repr, get_ast,
   # private
   str_val
{.push warnings: off.}
export
   NimNodeKind, NimNodeKinds, kind,
   NimSymKind, sym_kind, get_impl,
   NimTypeKind, type_kind, get_type, get_type_inst, get_type_impl,
   `==`, `[]`, `[]=`, len, copy, insert, items,
   eq_ident, error, params, `params=`, body, `body=`, name, nnkCallKinds,
   line_info, line_info_obj, tree_repr, get_ast
{.pop.}

type
   NimTypeKinds* = set[NimTypeKind]
   NimSymKinds* = set[NimSymKind]

const
   routine_name_pos* = 0
   routine_pattern_pos* = 1
   routine_generic_params_pos* = 2
   routine_params_pos* = 3
   routine_pragmas_pos* = 4
   routine_reserved_pos* = 5
   routine_body_pos* = 6

const
   nnkIdentLike* = {nnkIdent, nnkSym, nnkOpenSymChoice, nnkClosedSymChoice}
   nnkStmtListLike* = {nnkStmtList, nnkStmtListExpr, nnkStmtListType}
   nnkBlockLike* = {nnkBlockStmt, nnkBlockExpr, nnkBlockType}
   nnkIfLike* = {nnkIfStmt, nnkIfExpr}
   nnkElifLike* = {nnkElifBranch, nnkElifExpr}
   nnkElseLike* = {nnkElse, nnkElseExpr}

func lit*[T](self: T): NimNode = macros.new_lit(self)

func stmt_dbg(n: NimNode): string = "Stmt repr: " & expects.enclose(repr(n))

func tree_dbg(n: NimNode): string = "Tree repr: " & expects.enclose(macros.tree_repr(n))

template dump*(n: NimNode) =
   debug_echo("Dump '", ast_to_str(n), "':\n",
              indent(tree_dbg(n) & '\n' & stmt_dbg(n), 2))

func verbose_note*(n: NimNode): string = # FIXME: mixin not working, should be private
   when defined(dump_node):
      result = tree_dbg(n) & '\n' & stmt_dbg(n)
   else:
      result = "Note: recompile with '-d:dump_node' to dump the offending node"

template expect*(n: NimNode, kind: NimNodeKind, user_note: string = "") =
   {.line.}: impl_expect(n of kind, user_note, n)

template expect*(n: NimNode, kinds: NimNodeKinds, user_note: string = "") =
   {.line.}: impl_expect(n of kinds, user_note, n)

template expect_min*(n: NimNode, min_len: int, user_note: string = "") =
   {.line.}: impl_expect(n.len >= min_len, user_note, n)

template expect*(n: NimNode, valid_len: int, user_note: string = "") =
   {.line.}: impl_expect(n.len == valid_len, user_note, n)

template expect*(n: NimNode, valid_len: Slice[int], user_note: string = "") =
   {.line.}: impl_expect(n.len in valid_len, user_note, n)

template error*(n: NimNode, user_note: string) =
   macros.error(indent("\nReason: " & user_note & '\n' & verbose_note(n), 2), n)

func low*(self: NimNode): int = 0

func high*(self: NimNode): int = self.len - 1

func add*(self: NimNode, sons: varargs[NimNode]) = discard macros.add(self, sons)

func delete*(self: NimNode, i: int, n = 1) = macros.del(self, i, n)

func set_len*(self: NimNode, len: int, fill = NimNode.default) =
   if len > self.len:
      for _ in 0 ..< len - self.len:
         self.add(copy(fill))
   else:
      self.delete(self.high, self.len - len)

proc `impl{}`*(kind: NimNodeKind, sons: openarray[NimNode]): NimNode =
   result = macros.new_NimNode(kind)
   for son in sons:
      result.add(son)

template `{}`*(kind: NimNodeKind, sons: varargs[NimNode, `into{}`]): NimNode = `impl{}`(kind, @sons)

func `into{}`*(self: NimNode): NimNode = self
func `into{}`*(self: string): NimNode = macros.ident(self)

func is_uninit*(self: NimNode): bool = self == nil and self.isNil

static:
   assert(default(NimNode).is_uninit)
   assert(not nnkNilLit{}.is_uninit)

func gen*(kind: NimSymKind, ident_base: string = ""): NimNode = macros.gen_sym(kind, ident_base)

func ident*(
      name: string,
      public = false,
      pragmas: openarray[NimNode] = [],
      backtick = false
      ): NimNode =
   result = macros.ident(name)
   if backtick: result = nnkAccQuoted{result}
   if public: result = nnkPostfix{"*", result}
   if pragmas.len > 0: result = nnkPragmaExpr{result, nnkPragma{pragmas}}

func pub_ident*(
      name: string,
      pragmas: openarray[NimNode] = [],
      backtick = false
      ): NimNode =
   result = ident(name, true, pragmas, backtick)

func rtti_range*(self: NimNodeKind): set[NimNodeKind] = {self}
func rtti_range*(self: NimTypeKind): set[NimTypeKind] = {self}
func rtti_range*(self: NimSymKind): set[NimSymKind] = {self}
func rtti_range*(self: set[NimNodeKind]): set[NimNodeKind] = self
func rtti_range*(self: set[NimTypeKind]): set[NimTypeKind] = self
func rtti_range*(self: set[NimSymKind]): set[NimSymKind] = self
func `of`*(self: NimNodeKind, kind: NimNodeKind): bool = self == kind
func `of`*(self: NimNodeKind, kinds: NimNodeKinds): bool = self in kinds
func `of`*(self: NimTypeKind, kind: NimTypeKind): bool = self == kind
func `of`*(self: NimTypeKind, kinds: NimTypeKinds): bool = self in kinds
func `of`*(self: NimSymKind, kind: NimSymKind): bool = self == kind
func `of`*(self: NimSymKind, kinds: NimSymKinds): bool = self in kinds
func `of`*(self: NimNode, kind: NimNodeKind): bool = self.kind of kind
func `of`*(self: NimNode, kinds: NimNodeKinds): bool = self.kind of kinds
func `of`*(self: NimNode, kind: NimTypeKind): bool = self.type_kind of kind
func `of`*(self: NimNode, kinds: NimTypeKinds): bool = self.type_kind of kinds
func `of`*(self: NimNode, kind: NimSymKind): bool = self.sym_kind of kind
func `of`*(self: NimNode, kinds: NimSymKinds): bool = self.sym_kind of kinds

func `$`*(self: NimNode): string = self.repr

func infix_join*(nodes: openarray[NimNode], op: string): NimNode =
   result = nodes[0]
   for i in 1 ..< nodes.len:
      result = macros.infix(result, op, nodes[i])

func is_command*(n: NimNode, name: string, valid_argument_range: Slice[int]): bool =
   result = n of nnkCommand and n.len - 1 in valid_argument_range and n[0].eq_ident(name)

func is_infix*(n: NimNode, name: string): bool =
   result = n of nnkInfix and n.len == 3 and n[0].eq_ident(name)

func is_prefix*(n: NimNode, name: string): bool =
   result = n of nnkPrefix and n.len == 2 and n[0].eq_ident(name)

proc replace*[T](
      self: NimNode,
      ctx: T,
      fn: proc (self: NimNode, ctx: T): NimNode {.nim_call.}
      ): NimNode =
   result = fn(self, ctx)
   if result == nil:
      result = self
      for i in 0 ..< self.len:
         self[i] = replace(self[i], ctx, fn)

proc bind_ident*(val: static[string]): NimNode {.compile_time.} =
   result = macros.bind_sym(val) # workaround weird bindsym rule.

proc compound_ident(n: NimNode, sub_i = 0): string =
   result = ""
   for i in sub_i ..< n.len:
      result.add($n[i])

proc internal_quote(stmts: NimNode, dirty: bool): NimNode =
   func mangle(s: string): NimNode = ident(s & "_c8bd72kl260gofgbf0wnsa8i0")

   type ReplaceCtx = ref object
      args: seq[NimNode]
      params: seq[NimNode]

   func replace_fn(self: NimNode, ctx: ReplaceCtx): NimNode =
      if self of nnkAccQuoted:
         let str0 = self[0].str_val
         if str0[0] == '!':
            if str0.len == 1:
               self.delete(0)
               if self.len == 0:
                  self.error("escaped identifier is empty")
            else:
               self[0] = self[0].str_val.substr(1).ident
               result = self[0]
         else:
            if self.len == 1:
               result = self[0].str_val.mangle
               if self[0] notin ctx.args:
                  ctx.args.add(self[0])
                  ctx.params.add(result)
            elif self[0].eq_ident"bind":
               let id = self.compound_ident(1)
               result = id.mangle
               if result notin ctx.args:
                  ctx.args.add(macros.new_call("bind_ident".bind_ident, id.lit))
                  ctx.params.add(result)
            else:
               let expr_str = self.compound_ident
               var expr = NimNode(nil)
               try: expr = macros.parse_expr(expr_str)
               except ValueError: self.error("failed to parse 'AST' expr")
               result = expr_str.mangle
               if result notin ctx.params:
                  ctx.args.add(expr)
                  ctx.params.add(result)

   let ctx = ReplaceCtx()
   let stmts = replace(stmts, ctx, replace_fn)
   let templ_sym = nskTemplate.gen
   let call = macros.new_call(templ_sym, ctx.args)
   let formals = nnkFormalParams{"untyped"}
   for param in ctx.params:
      formals.add(nnkIdentDefs{param, "untyped", nnkEmpty{}})
   let pragma = if dirty: nnkPragma{"dirty"} else: nnkEmpty{}
   let templ_def = nnkTemplateDef{templ_sym, nnkEmpty{}, nnkEmpty{}, formals, pragma, nnkEmpty{},
                                  stmts}
   result = nnkStmtList{templ_def, macros.new_call("get_ast".bind_ident, call)}

macro AST*(stmts): auto = internal_quote(stmts, true)

macro AST_gensym*(stmts): auto = internal_quote(stmts, false)

macro `!`*(expr): NimNode =
   ## A sugar alias for `AST` for quick expression quoting. Strips a single `nnkPar`.
   let expr = if expr of nnkPar and expr.len == 1: expr[0] else: expr
   result = internal_quote(expr, true)

template add_AST*(self, stmts) =
   ## An appending alias for `AST`.
   ## Append `stmts` to `self` using `add`.
   self.add(AST(stmts))

func unsafe_downconv*(self: NimNode, _: openarray[set[NimNodeKind]]): NimNode = self
