## This module impliments control flow for working with polymorphic objects in
## a safe (WIP), expressive, and (possibly) efficient way.

# FIXME: unpacking does not work in generics, we could mixin the idents found in the unpack call?
# FIXME: a symbol can expand into something else...
# FIXME: `match` does not work as an expression.
# FIXME: better downcasting support for the else branch
# FIXME: when upconverting a mutable a Base(default(var Foo))
# FIXME: handling types that require qualification.

import utils; export utils
import macros2/private/core

type
   MatchKind = enum IfLike, CaseLike
   UnrollVariants = seq[seq[OfVariant]]
   OfExprKind {.pure.} = enum Ident, Sym, FieldIdent, FieldSym, AsExpr, ComplexExpr
   OfExpr = object  # some_expr as blah of Blah(a, b, c)
      expr: NimNode # ^^^^^^^^^^^^^^^^^
      ident: NimNode
      kind: OfExprKind
   OfVariant = object # some_expr of Blah(a, b, c)
      expr: NimNode   #              ^^^^^^^^^^^^^
      has_unpack_args: bool
      unpack_args: seq[NimNode]

const
   if_branch_kinds = nnkStmtListLike + nnkElifLike + nnkElseLike
   case_branch_kinds = {nnkOfBranch} + nnkElifLike + nnkElseLike
   all_branch_kinds = if_branch_kinds + case_branch_kinds

proc classify_branches(branches: NimNode): MatchKind =
   var branch_kinds = default NimNodeKinds
   branches.expect_min(1)
   for branch in branches:
      branch.expect(all_branch_kinds)
      branch_kinds.incl(branch.kind)
   if (branch_kinds - case_branch_kinds).len == 0: result = CaseLike
   elif (branch_kinds - if_branch_kinds).len == 0: result = IfLike
   else: branches.error("branch kinds must belong exclusively to one of these sets: " &
                        $if_branch_kinds & ", " & $case_branch_kinds)

proc classify_expr(expr: NimNode): MatchKind =
   # FIXME: this is shit
   result = if expr.is_infix("of"): IfLike else: CaseLike

proc `{}`(Self: type[MatchKind], expr: NimNode, branches: NimNode): MatchKind =
   # match is overloaded as to be both if-like control flow and case-like,
   # determine which or error.
   let expr_kind = classify_expr(expr)
   let branches_kind = classify_branches(branches)
   if expr_kind == branches_kind:
      return expr_kind
   case expr_kind:
   of IfLike: branches.error("invalid branch kinds")
   of CaseLike: result = IfLike

func `{}`(Self: type[OfExpr], expr: NimNode): Self =
   case expr.kind:
   of nnkIdent: result = Self(expr: expr, ident: expr, kind: OfExprKind.Ident)
   of nnkIdentLike - {nnkIdent}: result = Self(expr: expr, ident: expr, kind: OfExprKind.Sym)
   of nnkDotExpr:
      result = Self{expr[1]}
      result.expr = expr
      case result.kind:
      of Ident: result.kind = FieldIdent
      of Sym: result.kind = FieldSym
      else:
         result.expr = expr
         result.kind = ComplexExpr
   elif expr of nnkInfix and expr[0].eq_ident("as"):
      result = Self(expr: expr[1], ident: expr[2], kind: AsExpr)
   else: result = Self(expr: expr, kind: ComplexExpr)

func `{}`(Self: type[OfVariant], variant: NimNode, is_expr = false): Self =
   case variant.kind:
   of nnkInfix:
      result.expr = variant
      result.expr[1] = Self{result.expr[1], true}.expr
      result.expr[2] = Self{result.expr[2], true}.expr
   of nnkCall:
      result.expr = !kinds_of(`variant[0]`)
      result.has_unpack_args = true
      for i in 1 ..< variant.len:
         result.unpack_args.add(ident($variant[i])) # FIXME: more unpack arg validation
   of nnkIdentLike: result.expr = !kinds_of(`variant`)
   else: variant.error("failed to parse `OfVariant`")

proc process_elif_expr(
      expr: OfExpr,
      variant: OfVariant,
      new_idents: var seq[string]
      ): NimNode =
   assert(not variant.has_unpack_args, "FIXME: elif unpack args")
   let tmp = nskLet.gen
   result = nnkStmtList{}
   result.add_AST:
      let `tmp` = `expr.expr`
   if expr.kind != OfExprKind.ComplexExpr:
      new_idents.add($expr.ident)
      result.add_AST:
         template `expr.ident`: auto {.used.} = unsafe_subconv(`tmp`, `variant.expr`)
   else:
      discard # expr.expr.error("FIXME: ComplexExpr")
   result.add(!(kind(`tmp`) in `variant.expr`))

proc visit_elif_expr(expr: NimNode, new_idents: var seq[string]): NimNode =
   # We don't want the user to be able to access any unitialized objects, so
   # downcasts must be proven safe through short circuit evaluation
   result = expr
   # FIXME: is or safe?
   if expr.is_infix("and"):
      # Safe because of short circuit evalution
      expr[1] = expr[1].visit_elif_expr(new_idents)
      expr[2] = expr[2].visit_elif_expr(new_idents)
   elif expr.is_infix("of"):
      result = process_elif_expr(OfExpr{expr[1]}, OfVariant{expr[2]}, new_idents)
   # FIXME: consider an error or warning for of expressions below this.

proc process_if_branch(branch: NimNode): NimNode =
   branch.expect(nnkElifLike + nnkElseLike)
   result = branch
   if branch.kind of nnkElifLike:
      var new_idents = seq[string].default
      branch[0] = branch[0].visit_elif_expr(new_idents)

proc if_match(expr: NimNode, branches: NimNode): NimNode =
   # simple rewrite to if statement.
   branches[0].expect(nnkStmtListLike)
   branches[0] = nnkElifBranch{expr, branches[0]}
   result = nnkIfStmt{}
   for branch in branches:
      result.add(process_if_branch(branch))

func `{}`(Self: type[UnrollVariants], branch: NimNode): Self =
   # unroll of ...[Foo(blah), Bar]: stmts into
   # of Foo(blah): stmts
   # of Bar: stmts
   if branch.len == 2 and branch[0].is_prefix("...") and branch[0][1] of nnkBracket:
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
            error("FIXME: multiple expression unpacking")

proc case_match(expr: OfExpr, branches: NimNode): NimNode =
   let kind_expr = !kind(`expr.expr`)
   let expr_ident = ident($expr.ident)
   let tmp = nskLet.gen
   let case_stmt = nnkCaseStmt{kind_expr}
   var else_kinds = NimNode(nil)
   for branch in branches:
      case branch.kind:
      of nnkOfBranch:
         var unroll_variants = UnrollVariants{branch}
         for variants in unroll_variants:
            let branch = branch.copy
            case_stmt.add(branch)
            let body = branch[^1]
            branch.set_len(variants.len + 1)
            branch[^1] = body

            var kinds = NimNode(nil)
            for i in 0 ..< variants.len:
               branch[i] = variants[i].expr
               kinds = if kinds == nil: branch[i]
                       else: !system.`!+`(`kinds`, `branch[i]`)
               else_kinds = if else_kinds == nil: branch[i]
                            else: !system.`!+`(`else_kinds`, `branch[i]`)
            if expr.kind != OfExprKind.ComplexExpr:
               branch[^1].insert(0, AST do:
                  template `expr.ident`: auto {.used.} = unsafe_subconv(`tmp`, `kinds`))
            variants.todo_unpack_args
            if variants.len == 1 and variants[0].has_unpack_args:
               let call = !unpack(`expr_ident`)
               for unpack_arg in variants[0].unpack_args:
                  call.add(unpack_arg)
               branch[^1].insert(1, call)
      of nnkElse:
         if expr.kind != OfExprKind.ComplexExpr:
            branch[0].insert(0, AST do:
               template `expr.ident`: auto {.used.} = unsafe_subconv(`tmp`, `else_kinds`))
         case_stmt.add(branch)
      else: case_stmt.add(process_if_branch(branch))
   result = AST:
      let `tmp` = `expr.expr`
      `case_stmt`

macro match*(self: untyped, branches: varargs[untyped]): untyped =
   ## Control flow for working with polymorhpic types.
   let branches = if branches of all_branch_kinds: nnkArgList{branches} else: branches
   case MatchKind{self, branches}:
   of IfLike: result = if_match(self, branches)
   of CaseLike: result = case_match(OfExpr{self}, branches)
   when defined(dump_match): dump result
