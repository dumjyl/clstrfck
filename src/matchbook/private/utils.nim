import macros2/private/core

when false:
   proc skip_typedesc(T: NimNode): NimNode =
      result = T.get_type_inst
      if result of ntyTypeDesc:
         result = result[1]

   macro forward_generic_params*(X: typedesc, Y: typedesc): typedesc =
      # FIXME: skip aliases too
      let X = X.skip_typedesc
      let Y = Y.skip_typedesc
      if X of nnkBracketExpr:
         result = X.copy
         result[0] = Y
      else:
         result = Y

   proc to*[From: enum, To: enum](self: set[From], _: type[To]): set[To] =
      for val in self:
         result.incl(To(val))

template unsafe_conv*[X: object, Y: object](self: var X, _: type[Y]): var Y = Y(self)
   ## Unsafe api. Do not use.

template unsafe_conv*[X: object, Y: object](self: X, _: type[Y]): Y = Y(self)
   ## Unsafe api. Do not use.

template not_of*(a, b): auto = not(a of b)
   ## Sugar for `not(a of b)`, not an operator yet.

proc first*[T: enum](self: set[T]): T =
   var has_result = false
   for val in self:
      result = val
      has_result = true
   do_assert(has_result)

proc `+`*[T](sets: openarray[set[T]]): set[T] =
   for set in sets:
      result.incl(set)

func kind*(self: enum): enum = self

proc unsafe_default*(T: typedesc): T =
   {.push warning[UnsafeDefault]: off.}
   result = default(T)
   {.pop.}

template is_mutable*[T](self: var T): bool = true

template is_mutable*[T](self: T): bool = false
