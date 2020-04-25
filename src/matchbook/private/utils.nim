template unsafe_conv*[X: object, Y: object](self: var X, _: type[Y]): var Y = Y(self)

template unsafe_conv*[X: object, Y: object](self: X, _: type[Y]): Y = Y(self)

proc first*[T: enum](self: set[T]): T =
   var has_result = false
   for val in self:
      result = val
      has_result = true
   do_assert(has_result)

func kind*(self: enum): enum = self

proc unsafe_default*(T: typedesc): T =
   {.push warning[UnsafeDefault]: off.}
   result = default(T)
   {.pop.}

when false:
   template is_mutable*[T](self: var T): bool = true

   template is_mutable*[T](self: T): bool = false
