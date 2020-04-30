import pkg/matchbook

typedef:
   NeedsInit {.requires_init.} = record:
      val: string
   Base = abstract:
      id: int
      Sub = abstract:
         val: NeedsInit
         SubA = record
         SubB = record
      SomeInts = record:
         val: seq[int]

var a = SubA{id = 123, val = NeedsInit{val = "abc"}}
var b = a
var c {.used.} = a
assert(b.id == 123)
b.id.inc
b.id = 456
assert(b.id == 456)
assert(b.val.val == "abc")
