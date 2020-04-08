## This module impliments control flow for working with polymorphic objects in
## a safe (WIP), expressive, and (possibly) efficient way.

# XXX: unpacking does not work in generics...

import
   utils,
   macros2/private/[vm_timings, core, vm_state]

export utils

# XXX: a symbol can expand into something else...

# TODO: better downcasting support for the else branch

# TODO: `match` does not work as an expression.

type MatchKind = enum IfLike, CaseLike ## `match` is overloaded to be both an if like and case like control flow stmt. Best guess what the user meant.

proc classify_branches(branches: NimNode): MatchKind {.time.} =
   const valid_if_kinds = {nnk_stmt_list, nnk_elif_branch, nnk_else}
   const valid_case_kinds = {nnk_of_branch, nnk_elif_branch, nnk_else}
   var branch_kinds = default NimNodeKinds
   branches.expect_min(1)
   for branch in branches:
      branch.expect({nnk_stmt_list, nnk_of_branch, nnk_elif_branch, nnk_else})
      branch_kinds.incl(branch.kind)
   if (branch_kinds - valid_case_kinds).len == 0: result = CaseLike
   elif (branch_kinds - valid_if_kinds).len == 0: result = IfLike
   else: branches.error("branch kinds must belong exclusively to one of these sets: " &
                        $valid_if_kinds & ", " & $valid_case_kinds)

proc classify_expr(expr: NimNode): MatchKind {.time.} =
   # XXX: again (see comment at end of visit_elif_expr) this could be within a function
   #      call and not meant to be rewritten.
   var res = CaseLike
   var expr = expr
   expr.visit_node (res: var MatchKind):
      if node.is_infix("of"):
         res = IfLike
   result = res

proc `{}`(Self: type[MatchKind], expr: NimNode, branches: NimNode): MatchKind {.time.} =
   # match is overloaded as to be both if-like control flow and case-like,
   # determine which or error.
   let expr_kind = classify_expr(expr)
   let branches_kind = classify_branches(branches)
   if expr_kind == branches_kind: return expr_kind
   case expr_kind:
   of IfLike: branches.error("invalid branch kinds")
   of CaseLike: result = IfLike

type
   OfExprKind {.pure.} = enum Ident, Sym, FieldIdent, FieldSym, AsExpr, ComplexExpr
   OfExpr = object  # some_expr as blah of Blah(a, b, c)
      expr: NimNode # ^^^^^^^^^^^^^^^^^
      ident: NimNode
      kind: OfExprKind

func `{}`(Self: type[OfExpr], expr: NimNode): Self {.time.} =
   case expr.kind:
   of nnk_ident: result = Self(expr: expr, ident: expr, kind: OfExprKind.Ident)
   of nnk_sym, nnk_open_sym_choice, nnk_closed_sym_choice:
      result = Self(expr: expr, ident: expr, kind: OfExprKind.Sym)
   of nnk_dot_expr:
      result = Self{expr[1]}
      result.expr = expr
      case result.kind:
      of Ident: result.kind = FieldIdent
      of Sym: result.kind = FieldSym
      else:
         result.expr = expr
         result.kind = ComplexExpr
   elif expr of nnk_infix and expr[0].eq_ident("as"):
      result = Self(expr: expr[1], ident: expr[2], kind: AsExpr)
   else: result = Self(expr: expr, kind: ComplexExpr)

type OfVariant = object # some_expr of Blah(a, b, c)
   expr: NimNode        #              ^^^^^^^^^^^^^
   has_unpack_args: bool
   unpack_args: seq[NimNode]

func `{}`(Self: type[OfVariant], variant: NimNode, is_expr = false): Self {.time.} =
   case variant.kind:
   of nnk_infix:
      result.expr = variant
      result.expr[1] = Self{result.expr[1], true}.expr
      result.expr[2] = Self{result.expr[2], true}.expr
   of nnk_call:
      result.expr = !rtti_range(`variant[0]`)
      result.has_unpack_args = true
      for i in 1 ..< variant.len:
         result.unpack_args.add(ident($variant[i])) # TODO: more unpack arg validation
   of nnk_ident_like: result.expr = !rtti_range(`variant`)
   else: variant.error("failed to parse `OfVariant`")

macro downconv_template(expr: typed, ident: untyped, rtti_exprs: untyped) {.time.} =
   ## Create var like template `ident` with `expr` downconverted accordingly to `covers_exprs`
   ident.expect(nnk_ident)
   rtti_exprs.expect(nnk_bracket)
   result = AST:
      template `ident`: auto {.used.} = unsafe_downconv(`expr`, `rtti_exprs`)
   when defined(nim_dump_match): dump result

proc process_elif_expr(expr: OfExpr, variant: OfVariant): NimNode {.time.} =
   assert(not variant.has_unpack_args, "TODO")
   result = nnk_stmt_list_expr{}
   if expr.kind == OfExprKind.ComplexExpr:
      expr.expr.error("TODO: ComplexExpr")
   else:
      let of_sym = nsk_let.gen
      result.add_AST:
         let `of_sym` = `expr.expr`.kind in `variant.expr`
         `bind downconv_template`(`expr.expr`, `ident($expr.ident)`, [`variant.expr`])
         `of_sym`

proc visit_elif_expr(expr: NimNode): NimNode {.time.} =
   # We don't want the user to be able to access any unitialized objects, so
   # downcasts must be direct descendants of an `and`
   result = expr
   if expr.is_infix("and"):
      # Safe because of short circuit evalution
      expr[1] = expr[1].visit_elif_expr
      expr[2] = expr[2].visit_elif_expr
   elif expr.is_infix("of"):
      result = process_elif_expr(OfExpr{expr[1]}, OfVariant{expr[2]})
   # XXX: consider an error or warning for of expressions below this.

proc if_match(expr: NimNode, branches: NimNode): NimNode {.time.} =
   # simple rewrite to if statement.
   branches[0].expect(nnk_stmt_list)
   branches[0] = nnk_elif_branch{expr, branches[0]}
   result = nnk_if_stmt{}
   for branch in branches:
      if branch.kind == nnk_elif_branch:
         branch[0] = branch[0].visit_elif_expr
      result.add(branch)

type UnrollVariants = seq[seq[OfVariant]]

func `{}`(Self: type[UnrollVariants], branch: NimNode): Self =
   # unroll of ...[Foo(blah), Bar]: stmts into
   # of Foo(blah): stmts
   # of Bar: stmts
   if branch.len == 2 and branch[0].is_prefix("...") and branch[0][1] of nnk_bracket:
      for variant in branch[0][1]:
         result.add(@[OfVariant{variant}])
   else:
      var variants = seq[OfVariant].default
      for i in 0 ..< branch.len - 1:
         variants.add(OfVariant{branch[i]})
      result.add(variants)

proc todo_unpack_args(variants: seq[OfVariant]) =
   if variants.len > 2:
      for variant in variants:
         if variant.has_unpack_args:
            error("TODO: multiple expression unpacking")

proc case_match(expr: OfExpr, branches: NimNode): NimNode {.time.} =
   let kind_expr = !kind(`expr.expr`)
   let expr_ident = ident($expr.ident)
   result = nnk_case_stmt{kind_expr}
   for branch in branches:
      case branch.kind:
      of nnk_of_branch:
         var unroll_variants = UnrollVariants{branch}
         for variants in unroll_variants:
            let branch = branch.copy
            result.add(branch)
            let body = branch[^1]
            branch.set_len(variants.len + 1)
            branch[^1] = body

            let covers_exprs = ![]
            for i in 0 ..< variants.len:
               branch[i] = variants[i].expr
               covers_exprs.add(branch[i].copy)
            branch[^1].insert(0, !`bind downconv_template`(`expr.expr`, `expr_ident`,
                                                           `covers_exprs`))
            variants.todo_unpack_args
            if variants.len == 1 and variants[0].has_unpack_args:
               let call = !unpack(`expr_ident`)
               for unpack_arg in variants[0].unpack_args:
                  call.add(unpack_arg)
               branch[^1].insert(1, call)
      of nnk_elif_expr: result.add(branches.visit_elif_expr)
      else: result.add(branch)

macro match*(self: untyped, branches: varargs[untyped]): untyped {.time.} =
   ## Control flow for working with polymorhpic types.
   case MatchKind{self, branches}:
   of IfLike: result = if_match(self, branches)
   of CaseLike: result = case_match(OfExpr{self}, branches)
   when defined(nim_dump_match): dump result
