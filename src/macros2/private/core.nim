import expects
export expects
from std/strutils import indent
from std/macros import
   NimNodeKind, NimNodeKinds, kind,
   NimSymKind, sym_kind, get_impl,
   NimTypeKind, type_kind, get_type, get_type_inst, get_type_impl,
   `==`, `[]`, `[]=`, len, copy, insert, items,
   eq_ident, error, params, `params=`, new_proc, body, `body=`, name, nnk_call_kinds,
   line_info, line_info_obj, tree_repr, get_ast,
   # private
   str_val,
   new_call, new_var_stmt
{.push warnings: off.}
export
   NimNodeKind, NimNodeKinds, kind,
   NimSymKind, sym_kind, get_impl,
   NimTypeKind, type_kind, get_type, get_type_inst, get_type_impl,
   `==`, `[]`, `[]=`, len, copy, insert, items,
   eq_ident, error, params, `params=`, new_proc, body, `body=`, name, nnk_call_kinds,
   line_info, line_info_obj, tree_repr, get_ast
{.pop.}

type
   NimTypeKinds* = set[NimTypeKind]
   NimSymKinds* = set[NimSymKind]

const nnk_ident_like* = {nnk_ident, nnk_sym, nnk_open_sym_choice, nnk_closed_sym_choice}

func lit*[T](self: T): NimNode = macros.new_lit(self)

func stmt_dbg(n: NimNode): string = "Stmt repr: " & expects.enclose(repr(n))

func tree_dbg(n: NimNode): string = "Tree repr: " & expects.enclose(macros.tree_repr(n))

template dump*(n: NimNode) =
   debug_echo("Dump '", ast_to_str(n), "':\n",
              indent(tree_dbg(n) & '\n' & stmt_dbg(n), 2))

func verbose_note(n: NimNode): string =
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

func gen*(kind: NimSymKind, ident_base: string = ""): NimNode = macros.gen_sym(kind, ident_base)

func ident*(
      name: string,
      public = false,
      pragmas: openarray[NimNode] = [],
      backtick = false
      ): NimNode =
   result = macros.ident(name)
   if backtick: result = nnk_acc_quoted{result}
   if public: result = nnk_postfix{"*", result}
   if pragmas.len > 0: result = nnk_pragma_expr{result, nnk_pragma{pragmas}}

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

func gen_object_type*(
      fields: openarray[NimNode] = [],
      pragmas: openarray[NimNode] = [],
      inherits: NimNode = nil,
      ): NimNode =
   result = nnk_object_ty{}
   result.add(if pragmas.len > 0: nnk_pragma{pragmas} else: nnk_empty{})
   result.add(if inherits != nil: nnk_of_inherit{inherits} else: nnk_empty{})
   result.add(nnk_rec_list{})
   result[2].add(fields)

func gen_enum_type*(names: seq[string]): NimNode =
   result = nnk_enum_ty{nnk_empty{}}
   for name in names:
      result.add(name.ident)

func gen_type_def*(name: NimNode, def: NimNode): NimNode = nnk_type_def{name, nnk_empty{}, def}

func is_command*(n: NimNode, name: string, valid_argument_range: Slice[int]): bool =
   result = n of nnk_command and n.len - 1 in valid_argument_range and n[0].eq_ident(name)

func is_infix*(n: NimNode, name: string): bool =
   result = n of nnk_infix and n.len == 3 and n[0].eq_ident(name)

func is_prefix*(n: NimNode, name: string): bool =
   result = n of nnk_prefix and n.len == 2 and n[0].eq_ident(name)

macro visit_node*(node: untyped, context: untyped, stmts: untyped) =
   let visit_sym = nsk_proc.gen("visit")
   let node_id = "node".ident
   let call = visit_sym.new_call(node)
   let fn = macros.new_proc(visit_sym)
   fn.params[0] = "NimNode".ident
   fn.params.add(nnk_ident_defs{"node", fn.params[0], nnk_empty{}})
   for colon in context:
      fn.params.add(nnk_ident_defs{colon[0], colon[1], nnk_empty{}})
      call.add(colon[0])
   let internal_call = call.copy
   var i_id = "i".ident
   internal_call[1] = nnk_bracket_expr{node_id, i_id}
   fn.body = nnk_stmt_list{nnk_asgn{"result", "node"}, stmts, macros.quote do:
      for `i_id` in 0 ..< `node_id`.len:
         `node_id`[`i_id`] = `internal_call`}
   result = nnk_stmt_list{fn, nnk_asgn{node, call}}

proc bind_ident*(val: static[string]): NimNode {.compile_time.} = macros.bind_sym(val) # workaround weird bindsym rule.

func quote_expr(args, params: seq[NimNode], body: NimNode, dirty: bool): NimNode =
   let templ_sym = nsk_template.gen
   let call = templ_sym.new_call(args)
   let formals = nnk_formal_params{"untyped".ident}
   for param in params:
      formals.add(nnk_ident_defs{param, "untyped", nnk_empty{}})
   let pragma = if dirty: nnk_pragma{"dirty"} else: nnk_empty{}
   let templ_def = nnk_template_def{templ_sym, nnk_empty{}, nnk_empty{}, formals, pragma,
                                    nnk_empty{}, body}
   result = nnk_stmt_list{templ_def, new_call("get_ast".bind_ident, call)}

proc compound_ident(n: NimNode, sub_i = 0): string =
   result = ""
   for i in sub_i ..< n.len:
      result.add($n[i])

proc internal_quote(stmts: NimNode, dirty: bool): NimNode =
   func mangle(s: string): NimNode = ident(s & "_c8bd72kl260gofgbf0wnsa8i0")
   result = stmts
   if result of {nnk_macro_def, nnk_proc_def, nnk_func_def}:
      var lift_stmts = nnk_stmt_list{}
      var body = result.body
      body.visit_node (lift_stmts: NimNode):
         if node of nnk_call and node.len == 2 and node[0].eq_ident("escape") and
               node[1] of nnk_stmt_list:
            lift_stmts.add(node[1])
            result = nnk_discard_stmt{nnk_empty{}}
      result.body = nnk_stmt_list{lift_stmts, "AST".new_call(body)}
      if result of {nnk_proc_def, nnk_func_def}:
         result.params[0].expect(nnk_empty)
         result.params[0] = "NimNode".ident
      return
   var lift_stmts = nnk_stmt_list{}
   var args: seq[NimNode]
   var params: seq[NimNode]
   result.visit_node (args: var seq[NimNode], params: var seq[NimNode], lift_stmts: NimNode):
      if node of nnk_acc_quoted:
         let str0 = node[0].str_val
         if str0[0] == '!':
            if str0.len == 1:
               node.delete(0)
               if node.len == 0:
                  node.error("escaped identifier is empty")
            else:
               node[0] = node[0].str_val.substr(1).ident
               result = node[0]
         else:
            if node.len == 1:
               result = node[0].str_val.mangle
               if node[0] notin args:
                  args.add(node[0])
                  params.add(result)
            elif node[0].eq_ident"bind":
               let id = node.compound_ident(1)
               result = id.mangle
               if result notin args:
                  args.add("bind_ident".bind_ident.new_call(id.lit))
                  params.add(result)
            else:
               let expr_str = node.compound_ident
               var expr = NimNode(nil)
               try: expr = macros.parse_expr(expr_str)
               except ValueError: node.error("failed to parse 'AST' expr")
               result = expr_str.mangle
               if result notin params:
                  args.add(expr)
                  params.add(result)
         return
   result = nnk_stmt_list{lift_stmts, quote_expr(args, params, result, dirty)}

macro AST*(stmts): auto = internal_quote(stmts, true)

macro AST_gensym*(stmts): auto = internal_quote(stmts, false)

macro `!`*(expr): NimNode =
   ## A sugar alias for `AST` for quick expression quoting. Strips a single `nnk_par`.
   let expr = if expr of nnk_par and expr.len == 1: expr[0] else: expr
   result = internal_quote(expr, true)

template add_AST*(self, stmts) =
   ## An appending alias for `AST`.
   ## Append `stmts` to `self` using `add`.
   self.add(AST(stmts))

func unsafe_downconv*(self: NimNode, _: openarray[set[NimNodeKind]]): NimNode = self
