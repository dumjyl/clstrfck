import
   mainframe,
   matchbook/private/matches
from sugar import `=>`
export matches, `=>`

# FIXME: consider alternatives: a wrapopt module like std/wrapnil
#                               a more specialized option type generator that maintains invariants.

{.push warnings: off.}

type
   DefaultIsNone* = pointer |
                        ptr |
                        ref |
           proc {.nimcall.} |
                   c_string |
               c_string_array
   OptionKind* {.pure.} = enum None, Some
   Option* [T] {.pure.} = object {.inheritable.}
      when T is DefaultIsNone and T is_not NimNode:
         val: T
      else:
         val: T
         kind: OptionKind
   None* [T] = object of Option[T]
   Some* [T] = object of Option[T]

{.pop.}

proc `=`*[T](dst: var Option[T], src: Option[T]) =
   # FIXME: genericAssign is the devil.
   for a, b in fields(dst, src):
      a = b

proc kind*[T](self: Option[T]): OptionKind =
   when T is DefaultIsNone and T is_not NimNode:
      result = if self.val == default(T): OptionKind.None else: OptionKind.Some
   else:
      result = self.kind

# FIXME(nim): weirdness when kind(self) -> self.kind for the vm ref optimization.
#             the vm accesses the undeclared field because of local module ufcs precedence
proc `of`*[T](self: Option[T], Variant: type[Some]): bool = kind(self) == OptionKind.Some
proc `of`*[T](self: Option[T], Variant: type[None]): bool = kind(self) == OptionKind.None

proc some*[T](val: T): Option[T] =
   when T is DefaultIsNone and T is_not NimNode:
      assert(val != default(T))
      result = Some[T](val: val)
   else: result = Some[T](val: val, kind: OptionKind.Some)

proc none*[T](_: type[T]): Option[T] =
   when T is DefaultIsNone and T is_not NimNode: result = None[T]()
   else: result = None[T](val: unsafe_default(T), kind: OptionKind.None)

const
   option_kinds = {OptionKind.None, OptionKind.Some}
   some_kinds = {OptionKind.Some}
   none_kinds = {OptionKind.None}

proc kinds_of*(Self: type[Option]): set[OptionKind] = option_kinds
proc kinds_of*(Self: type[Some]): set[OptionKind] = some_kinds
proc kinds_of*(Self: type[None]): set[OptionKind] = none_kinds

template unsafe_subconv*[T](self: Option[T], kinds: set[OptionKind]): auto =
   # FIXME: bad checks
   when kinds == option_kinds: self
   elif kinds == some_kinds: self.val
   elif kinds == none_kinds: unsafe_conv(self, None[T])
   else: {.fatal: "unreachable".}

proc `$`*[T](self: Option[T]): string =
   match self of Some:
      result = "Some("
      result.add_quoted(self)
      result.add(")")
   else: result = "None(" & $T & ")"

template `$`*[T](self: Some[T] | None[T]): string = $unsafe_object_cast(self, Option[T])

proc expect*[T](self: var Option[T]): var T =
   if self of None: fatal("tried to unpack a 'None' variant")
   result = self.val

proc expect*[T](self: var Option[T], msg: string): var T =
   match self of None: fatal("tried to unpack a 'None' variant; ", msg)
   result = self

proc expect*[T](self: Option[T]): T =
   match self of None: fatal("tried to unpack a 'None' variant")
   result = self.val

proc expect*[T](self: Option[T], msg: string): T =
   match self of None: fatal("tried to unpack a 'None' variant; ", msg)
   result = self.val

proc map*[X, Y](self: Option[X], map_fn: proc (val: X): Y): Option[Y] =
   match self of Some: result = some(map_fn(self))
   else: result = none(Y)

proc or_val*[T](self: Option[T], val: T): T =
   match self of Some: result = self
   else: result = val

template `?`*[T](self: Option[T]): T =
   if self of None: return
   self.val
