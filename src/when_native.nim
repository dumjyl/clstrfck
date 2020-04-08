import pkg/macros2/private/core

macro when_native*(branches: varargs[untyped]): untyped {.AST.} =
   escape:
      branches.expect(1 .. 2)
      for branch in branches:
         branch.expect({nnk_stmt_list, nnk_else})
      var non_native = if branches.len == 2: branches[1][0] else: nnk_discard_stmt{nnk_empty{}}
   when nim_vm: `non_native`
   else:
      when defined(nim_script) or defined(js): `non_native`
      else: `branches[0]`
