import pkg/macros2/private/core

macro when_native*(branches: varargs[untyped]): untyped =
   branches.expect(1 .. 2)
   for branch in branches:
      branch.expect({nnkStmtList, nnkElse})
   var non_native = if branches.len == 2: branches[1][0] else: nnkDiscardStmt{nnkEmpty{}}
   result = AST:
      when nim_vm: `non_native`
      else:
         when defined(nim_script) or defined(js): `non_native`
         else: `branches[0]`
