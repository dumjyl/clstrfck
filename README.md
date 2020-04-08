## macros2


### type unsafety with passing by reference


```nim
typedef:
   Base = abstract:
      Foo = record(val: string)
      Bar = record(val: int)

func use_foo(self: Foo) = echo self.val

var x: Base = Foo{"abc"}
case x.kind:
of BaseKind.Foo:
   template x: auto = Foo(x) # x on the rhs is the prev x
   Base(x) = Bar{123}
   use_foo(x)
else: discard
```

```
func is_mutable[T](self: var T): bool = true
func is_mutable[T](self: T): bool = false
when is_mutable(x): ...
```
