import clstrfck/private/matches
export matches

type
   DefaultIsNone* = pointer |
                        ptr |
                        ref |
           proc {.nimcall.} |
                   c_string |
               c_string_array
   OptionKind* {.pure.} = enum None, Some
   Option* [T] {.pure.} = object {.inheritable.}
      when T is DefaultIsNone:
         value: T
      else:
         value: T
         kind: OptionKind
   None* [T] = object of Option[T]
   Some* [T] = object of Option[T]

proc `=`*[T](dst: var Option[T], src: Option[T]) =
   # XXX: genericAssign is the devil.
   for a, b in fields(dst, src):
      a = b

proc kind*[T](self: Option[T]): OptionKind {.inherit.} =
   when T is DefaultIsNone:
      result = if self.value == default(T): OptionKind.None else: OptionKind.Some
   else:
      result = self.kind

proc `of`*[T](self: Option[T], Variant: type[Some]): bool = self.kind == OptionKind.Some
proc `of`*[T](self: Option[T], Variant: type[None]): bool = self.kind == OptionKind.None

proc unsafe_expect*[T](self: Option[T], Variant: type[Some]): Some[T] =
   assert(self of Some)
   result = cast[Some[T]](self)

proc unsafe_expect*[T](self: Option[T], Variant: type[None]): None[T] =
   assert(self of None)
   result = cast[None[T]](self)

proc some*[T](value: T): Some[T] =
   when T is DefaultIsNone:
      assert(value != default(T))
      result = Some[T](value: value)
   else:
      result = Some[T](value: value, kind: OptionKind.Some)

proc none*[T](_: type[T]): None[T] =
   when T is DefaultIsNone:
      assert(value == default(T))
      result = None[T]()
   else:
      result = None[T](value: default(T), kind: OptionKind.None)

template unpack*[T](self: Some[T], value_name: untyped) =
   var value_name = self.value

proc `$`*[T](self: Option[T]): string {.inherit.} =
   mixin `$`
   match self of Some(_):
      result = "Some("
      result.add_quoted(self)
      result.add(")")
   else:
      result = "None(" & $T & ")"

proc `$`*[T](self: Some[T]): string = $Option[T](self)
proc `$`*[T](self: None[T]): string = $Option[T](self)
