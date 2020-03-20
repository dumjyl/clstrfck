import macros_core

# XXX: supporting things that are not gc:arc

template not_of*(a, b): auto = not(a of b)

proc `of`*[T: enum](kind: T, variant: T): bool = kind == variant
proc `of`*[T: enum](kind: T, variants: set[T]): bool = kind in variants

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
   case expr.kind:
   of nnk_ident, nnk_sym, nnk_open_sym_choice, nnk_closed_sym_choice: result = expr
   of nnk_dot_expr: expr.error"TODO"
   else: result = nil

proc parse_of_variant(expr: NimNode): (NimNode, seq[NimNode]) =
   case expr.kind:
   of nnk_call:
      result[0] = expr[0]
      for i in 1 ..< expr.len:
         result[1].add(expr[i])
   of nnk_ident: result[0] = expr
   else: expr.error("failed to parse match expression")

proc elif_expr(stmts: NimNode, expr: NimNode, safe: bool) =
   if expr.is_infix"and":
      stmts.elif_expr(expr[1], true)
      stmts.elif_expr(expr[2], true)
   elif expr.is_infix"of":
      if not safe:
         expr.error("cannot prove match expression is safe")
      let ident = expr[1].parse_of_ident
      var (variant, unpack_args) = expr[2].parse_of_variant
      expr[2] = variant
      var ident_aliased = false
      let fresh_ident = ident(ident.str_val)
      for i in 0 ..< unpack_args.len:
         if unpack_args[i].eq_ident"_":
            if ident == nil:
               expr.error("failed to infer variable name")
            unpack_args[i] = fresh_ident
            ident_aliased = true
         if unpack_args[i].eq_ident(ident):
            ident_aliased = true
      let downcast_ident = if ident_aliased: nsk_var.init(ident.str_val)
                           else: fresh_ident
      stmts.add_AST:
         var `downcast_ident` = unsafe_expect(`ident`, `variant`)
      let call = "unpack".new_call(downcast_ident)
      call.add(unpack_args)
      stmts.add(call)
   else:
      for i in 0 ..< expr.len:
         stmts.elif_expr(expr[i], false)

proc if_match(expr: NimNode, branches: NimNode): NimNode =
   branches[0].expect(nnk_stmt_list)
   branches[0] = nnk_elif_branch.init(expr, branches[0])
   result = nnk_if_stmt.init()
   for branch in branches:
      if branch.kind == nnk_elif_branch:
         var stmts = gen_stmts()
         stmts.elif_expr(branch[0], true)
         stmts.add(branch[^1])
         branch[^1] = stmts
      result.add(branch)

proc case_match(expr: NimNode, branches: NimNode): NimNode =
   expr.error("TODO")
   result = nnk_case_stmt.init(!kind(`expr`))
   for branch in branches:
      result.add(branch)

macro match*(self: untyped, branches: varargs[untyped]): untyped =
   ## TODO: add elif support for case like variant.
   case classify(self, branches):
   of IfLike: if_match(self, branches)
   of CaseLike: case_match(self, branches)

macro inherit*(fn: untyped): untyped =
   # TODO: this
   result = fn
