from macros import nil

import macros2

template test(name, stmts) =
   block:
      static:
         stmts

test StmtList:
   let stmts = StmtList{!(a + b), !"abc"}
   stmts.add_AST:
      blah
      stuff
   stmts.add([!1, !2, !3])
   assert(stmts.len == 7)
   assert(stmts[2].expect(Ident) == "blah")
   assert($stmts == """

a + b
"abc"
blah
stuff
1
2
3""")

test ForLoop:
   let ast = AST:
      for a, (b, c) in @[(2, 3), (4, 5), (6, 7)]:
         echo(a * b + c)
   let for_loop = ast.expect(StmtList).expect(1).expect(ForLoop)
   assert(for_loop.vars.expect(3) == [AnyIdent(!a), !b, !c])
   discard for_loop.expr.expect(PrefixCall)
   assert(for_loop.body.expect(StmtList).expect(1) == !echo(a * b + c))

test Ident:
   let x = Ident{"aBC"}
   let y = !abc
   assert(x == y)
   assert(x == "abc")
