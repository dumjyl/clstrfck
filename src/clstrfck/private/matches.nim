import macros_core

# XXX: supporting things that are not gc:arc

template not_of*(a, b): auto = not(a of b)

const nnk_ident_like = {nnk_ident, nnk_sym, nnk_open_sym_choice, nnk_closed_sym_choice}

type MatchKind = enum IfLike, CaseLike

proc classify_branches(branches: NimNode): MatchKind =
   const valid_if_kinds = {nnk_stmt_list, nnk_elif_branch, nnk_else}
   const valid_case_kinds = {nnk_of_branch, nnk_else}
   var branch_kinds = default NimNodeKinds
   branches.expect_min(1)
   for branch in branches:
      branch.expect({nnk_stmt_list, nnk_of_branch, nnk_elif_branch, nnk_else})
      branch_kinds.incl(branch.kind)
   if (branch_kinds - valid_case_kinds).len == 0: result = CaseLike
   elif (branch_kinds - valid_if_kinds).len == 0: result = IfLike
   else: branches.error("branch kinds must belong exclusively to one of these sets: " &
                        $valid_if_kinds & ", " & $valid_case_kinds)

proc classify_expr(expr: NimNode): MatchKind =
   var res = CaseLike
   var expr = expr
   expr.visit_node (res: var MatchKind):
      if node.is_infix("of"):
         res = IfLike
   result = res

proc classify(expr: NimNode, branches: NimNode): MatchKind =
   let expr_kind = classify_expr(expr)
   let branches_kind = classify_branches(branches)
   if expr_kind == branches_kind: return expr_kind
   case expr_kind:
   of IfLike: branches.error("invalid branch kinds")
   of CaseLike: result = IfLike

proc parse_of_ident(expr: NimNode): NimNode =
   if expr of nnk_ident_like:
      result = ident(result.str_val)

proc parse_of_variant(expr: NimNode): (NimNode, seq[NimNode]) =
   case expr.kind:
   of nnk_call:
      result[0] = expr[0]
      for i in 1 ..< expr.len:
         result[1].add(expr[i])
   of nnk_ident: result[0] = expr
   else: expr.error("failed to parse match expression")

proc is_ident_aliased(ident: NimNode, unpack_args: seq[NimNode]): bool =
   for arg in unpack_args:
      if arg.eq_ident"_" or ident != nil and ident.eq_ident(arg):
         return true

proc process(unpack_args: var seq[NimNode], ident: NimNode) =
   for i in 0 ..< unpack_args.len:
      unpack_args[i].expect(nnk_ident_like)
      if unpack_args[i].eq_ident"_":
         if ident == nil:
            unpack_args[i].error("failed to infer variable name")
         unpack_args[i] = ident

proc visit_elif_expr(expr: NimNode, safe: bool): NimNode =
   result = expr
   if expr.is_infix("and"):
      expr[1] = expr[1].visit_elif_expr(true)
      expr[2] = expr[2].visit_elif_expr(true)
   elif expr.is_infix"of":
      if not safe:
         expr.error("cannot prove match expression is safe")
      let ident = parse_of_ident(expr[1])
      var (variant, unpack_args) = parse_of_variant(expr[2])
      var ident_aliased = is_ident_aliased(ident, unpack_args)
      unpack_args.process(ident)
      var stmts = nnk_stmt_list_expr.init
      var base_sym = expr[1]
      if base_sym.not_of(nnk_ident_like):
         base_sym = nsk_let.init
         stmts.add_AST:
            let `base_sym` = `expr[1]`
      let is_of_sym = nsk_let.init
      stmts.add_AST:
         let `is_of_sym` = `base_sym` of `variant`
      let downcast_ident = if ident_aliased or ident == nil: nsk_var.init else: ident
      stmts.add_AST:
         var `downcast_ident` = unsafe_expect(`base_sym`, `variant`)
      stmts.add()
      let call = "unpack".new_call(downcast_ident)
      call.add(unpack_args)
      stmts.add(call)
      stmts.add(is_of_sym)
      result = stmts
   else:
      for i in 0 ..< expr.len:
         expr[i] = expr[i].visit_elif_expr(false)

proc if_match(expr: NimNode, branches: NimNode): NimNode =
   branches[0].expect(nnk_stmt_list)
   branches[0] = nnk_elif_branch.init(expr, branches[0])
   result = nnk_if_stmt.init()
   for branch in branches:
      if branch.kind == nnk_elif_branch:
         branch[0] = branch[0].visit_elif_expr(true)
      result.add(branch)

proc case_match(expr: NimNode, branches: NimNode): NimNode =
   expr.error("TODO")
   result = nnk_case_stmt.init(!kind(`expr`))
   for branch in branches:
      result.add(branch)

proc `of`*[T: enum](kind: T, variant: T): bool = kind == variant

proc `of`*[T: enum](kind: T, variants: set[T]): bool = kind in variants

macro match*(self: untyped, branches: varargs[untyped]): untyped =
   ## TODO: add elif support for case like variant.
   case classify(self, branches):
   of IfLike: if_match(self, branches)
   of CaseLike: case_match(self, branches)

macro inherit*(fn: untyped): untyped =
   # TODO: this
   result = fn
