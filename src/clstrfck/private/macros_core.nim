from std/strutils import split, join, indent
from std/macros import
   NimNodeKind, NimNodeKinds, NimSymKind, kind, len, items, eq_ident,
   `[]`, `[]=`, name, get_ast, new_lit, bind_sym, params, `params=`, tree_repr,
   body, `body=`, copy, str_val, new_call, new_var_stmt, `==`, parse_expr
export
   NimNodeKind, NimNodeKinds, NimSymKind, kind, len, items, eq_ident,
   `[]`, `[]=`, name, get_ast, new_lit, bind_sym, params, `params=`, tree_repr,
   body, `body=`, copy, str_val, new_call

func init*[T](Self: type seq[T], len: Natural = 0): seq[T] = new_seq[T](len)

func strip_ends(str: string): string =
   let lines = str.split('\n')
   var new_lines = seq[string].init
   for i, line in lines:
      if line.len == 0 and (i == lines.low or i == lines.high): continue
      new_lines.add(line)
   result = new_lines.join("\n")

func enclose(str: string): string =
   result = str.strip_ends
   if result.split("\n").len > 1:
      result = "'''\n" & result.indent(2) & "\n'''"
   else:
      result = '\'' & result & '\''

func stmt_dbg(n: NimNode): string = "Stmt repr: " & n.repr.enclose

func tree_dbg(n: NimNode): string = "Tree repr: " & n.tree_repr.enclose

template dump*(n: NimNode) =
   debug_echo("Dump '", ast_to_str(n), "':\n",
              indent(n.tree_dbg & '\n' & n.stmt_dbg, 2))

func verbose_note(n: NimNode): string =
   when defined(dump_node):
      result = n.stmt_dbg & '\n' & n.tree_dbg
   else:
      result = "Note: recompile with '-d:dump_node' to dump the offending node"

func expect_string(cond: string, user_note: string, n: NimNode): string =
   result = "\nExpectation failed: '" & cond & "'\n"
   if user_note.len > 0:
      result &= "User note: " & user_note & "\n"
   result &= verbose_note(n)
   result = result.indent(2)

template impl_expect(cond, user_note, n) =
   {.line.}:
      if not(cond):
         macros.error(expect_string(ast_to_str(cond), user_note, n))

template expect*(n: NimNode, kind: NimNodeKind, user_note: string = "") =
   {.line.}: impl_expect(n of kind, user_note, n)

template expect*(n: NimNode, kinds: NimNodeKinds, user_note: string = "") =
   {.line.}: impl_expect(n of kinds, user_note, n)

template expect_min*(n: NimNode, min_len: int, user_note: string = "") =
   {.line.}: impl_expect(n.len >= min_len, user_note, n)

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

func init*(kind: NimNodeKind, sons: varargs[NimNode]): NimNode =
   result = macros.new_NimNode(kind)
   for son in sons:
      result.add(son)

func init*(kind: NimSymKind, ident_base: string = ""): NimNode = macros.gen_sym(kind, ident_base)

func ident*(
      name: string,
      public = false,
      pragmas: openarray[NimNode] = [],
      backtick = false
      ): NimNode =
   result = macros.ident(name)
   if backtick: result = nnk_acc_quoted.init(result)
   if public: result = nnk_postfix.init(macros.ident"*", result)
   if pragmas.len > 0: result = nnk_pragma_expr.init(result, nnk_pragma.init(pragmas))

func pub_ident*(
      name: string,
      pragmas: openarray[NimNode] = [],
      backtick = false
      ): NimNode =
   result = ident(name, true, pragmas, backtick)

func `of`*(self: NimNode, kind: NimNodeKind): bool = self.kind == kind

func `of`*(self: NimNode, kinds: NimNodeKinds): bool = self.kind in kinds

func `$`*(self: NimNode): string = self.repr

template empty*: NimNode = init(nnk_empty)

func ident_def*(name: NimNode, typ = empty, val = empty): NimNode =
   result = nnk_ident_defs.init(name, typ, val)

func ident_def*(name: string, typ = empty, val = empty): NimNode = ident_def(name.ident, typ, val)

func asgn(lhs, rhs: NimNode): NimNode = nnk_asgn.init(lhs, rhs)

func gen_stmts*(sons: varargs[NimNode]): NimNode = nnk_stmt_list.init(sons)

func infix_join*(nodes: openarray[NimNode], op: string): NimNode =
   result = nodes[0]
   for i in 1 ..< nodes.len:
      result = macros.infix(result, op, nodes[i])

func gen_object_type*(
      fields: openarray[NimNode] = [],
      pragmas: openarray[NimNode] = [],
      inherits: NimNode = nil,
      ): NimNode =
   result = nnk_object_ty.init
   result.add(if pragmas.len > 0: nnk_pragma.init(pragmas) else: empty)
   result.add(if inherits != nil: nnk_of_inherit.init(inherits) else: empty)
   result.add(nnk_rec_list.init)
   result[2].add(fields)

func gen_enum_type*(names: seq[string]): NimNode =
   result = nnk_enum_ty.init(empty)
   for name in names:
      result.add(name.ident)

func gen_type_def*(name: NimNode, def: NimNode): NimNode = nnk_type_def.init(name, empty, def)

func is_command*(n: NimNode, name: string, valid_argument_range: Slice[int]): bool =
   result = n of nnk_command and n.len - 1 in valid_argument_range and n[0].eq_ident(name)

func is_infix*(n: NimNode, name: string): bool =
   result = n of nnk_infix and n.len == 3 and n[0].eq_ident(name)

macro visit_node*(node: untyped, context: untyped, stmts: untyped) =
   let visit_sym = nsk_proc.init("visit")
   let node_id = "node".ident
   let call = visit_sym.new_call(node)
   let fn = macros.new_proc(visit_sym)
   fn.params[0] = "NimNode".ident
   fn.params.add(ident_def("node", typ = fn.params[0]))
   for colon in context:
      fn.params.add(ident_def(colon[0], typ = colon[1]))
      call.add(colon[0])
   let internal_call = call.copy
   var i_id = "i".ident
   internal_call[1] = nnk_bracket_expr.init(node_id, i_id)
   fn.body = gen_stmts(asgn("result".ident, "node".ident), stmts, macros.quote do:
      for `i_id` in 0 ..< `node_id`.len:
         `node_id`[`i_id`] = `internal_call`)
   result = gen_stmts(fn, asgn(node, call))

func quote_expr(args, params: seq[NimNode], body: NimNode): NimNode =
   let templ_sym = nsk_template.init
   let call = templ_sym.new_call(args)
   let formals = nnk_formal_params.init("untyped".ident)
   for param in params:
      formals.add(ident_def(param, typ = "untyped".ident))
   let templ_def = nnk_template_def.init(templ_sym, empty, empty, formals,
                                         nnk_pragma.init("dirty".ident), empty,
                                         body)
   result = gen_stmts(templ_def, new_call("get_ast", call))

proc compound_ident(n: NimNode, sub_i = 0): string =
   result = ""
   for i in sub_i ..< n.len:
      result.add($n[i])

macro AST*(stmts: untyped): untyped =
   func mangle(s: string): NimNode = ident(s & "_c8bd72kl260gofgbf0wnsa8i0")
   result = stmts
   if result of nnk_macro_def:
      var lift_stmts = gen_stmts()
      var body = result.body
      body.visit_node (lift_stmts: NimNode):
         if node of nnk_call and node.len == 2 and node[0].eq_ident"escape" and
               node[1] of nnk_stmt_list:
            lift_stmts.add(node[1])
            result = nnk_discard_stmt.init(empty)
      result.body = gen_stmts(lift_stmts, "AST".new_call(body))
      return
   var lift_stmts = gen_stmts()
   var args: seq[NimNode]
   var params: seq[NimNode]
   result.visit_node (args: var seq[NimNode], params: var seq[NimNode], lift_stmts: NimNode):
      if node of nnk_acc_quoted:
         if node[0].eq_ident"!":
            node.delete(0)
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
                  args.add(result)
                  params.add(result)
                  lift_stmts.add(new_var_stmt(result, "bind_sym".new_call(id.new_lit)))
            else:
               let expr_str = node.compound_ident
               var expr = NimNode(nil)
               try: expr = expr_str.parse_expr
               except ValueError: node.error("failed to parse 'AST' expr")
               result = expr_str.mangle
               if result notin args:
                  args.add(result)
                  params.add(result)
                  lift_stmts.add(new_var_stmt(result, expr))
         return
   result = gen_stmts(lift_stmts, quote_expr(args, params, result))

macro `!`*(expr: untyped): NimNode {.AST.} =
   escape:
      let expr = if expr of nnk_par and expr.len == 1: expr[0] else: expr
   `bind AST`(`expr`)

template add_AST*(self: untyped, stmts: untyped) =
   self.add(AST(stmts))
