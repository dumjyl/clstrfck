# friend pragma
# Bar {.friend: module/path.}

# pure pragma
# {.pure.}, {.pure(bool_expr).}

# inherit macro
# rewrites to a base proc and an upcasting template

# dyn macro
#[
proc render(self: Operator) = ...
proc render(self: Method) = ...

proc render(self: Function) {.dyn.} =
expands to:

proc render_gensymed(self: Function) {.inline.} =
   match self:
   of Opterator: render(self)
   of Method: render(self)
proc render(self: Function) =
   render_gensymed(self)
]#

import macros2

macro types*(type_defs: {StmtList}) {.m2.} =
   ## If the toplevel type name is exported with `pub` all derived object are public.
   ## The same rule applies for `ref` and `ptr` annotations.
   discard
