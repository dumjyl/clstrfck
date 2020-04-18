from macros import nil

import macros2

template test(name, stmts) =
   block:
      static:
         stmts

test tfor_loop:
   let ast = AST:
      for a, (b, c) in @[(2, 3), (4, 5), (6, 7)]:
         echo(a * b + c)
   let for_loop = ast.expect(StmtList).expect(1).expect(ForLoop)
   assert(for_loop.vars.expect(3) == [AnyIdent(!a), !b, !c])
   discard for_loop.expr.expect(PrefixCall)
   assert(for_loop.body.expect(StmtList).expect(1) == !echo(a * b + c))

when defined(vm_timings):
   static: log_timings()

test tident:
   dbg "abc".ident
