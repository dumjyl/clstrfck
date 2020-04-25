## Utilities for calculating the lowest common ancestor from a set of kinds for inheritance trees.

import
   core
   #matchbook/private/utils

from std/algorithm import sort

type
   LCAKind* = range[low(uint8) .. high(uint8)]
   LCAData* = ref object
      name: string
      kinds: set[LCAKind]
      subs: seq[LCAData]
   LCAMatch = object
      name: string
      depth: int

func kinds*(self: LCAData): set[LCAKind] = self.kinds

func `{}`[T](Self: type[LCAKind], vals: set[T]): set[LCAKind] =
   for val in vals: result.incl(LCAKind(val))

func `{}`*[T](Self: type[LCAData], name: string, kinds: set[T], subs: seq[LCAData]): LCAData =
   result = Self(name: name, kinds: LCAKind{kinds}, subs: subs)

func add*(self: LCAData, sub: LCAData) =
   self.subs.add(sub)

func lit*(self: LCAData): NimNode =
   let kinds = !{}
   for kind in self.kinds:
      kinds.add(!`bind LCAKind`(`lit(kind)`))
   var subs = ![]
   for sub in self.subs:
      subs.add(sub.lit)
   subs = !`bind @`(`subs`)
   if self.subs.len == 0:
      subs = !seq[`bind LCAData`](`subs`)
   result = !`bind {}`(typedesc(`bind LCAData`), `self.name.lit`, `kinds`, `subs`)

func solve_rec(matches: var seq[LCAMatch], depth: int, data: LCAData, kinds: set[LCAKind]) =
   if kinds <= data.kinds:
      matches.add(LCAMatch(name: data.name, depth: depth))
      for sub in data.subs:
         solve_rec(matches, depth + 1, sub, kinds)

proc solve*[T](self: LCAData, kinds: set[T]): NimNode =
   var matches = seq[LCAMatch].default
   var lca_kinds = set[LCAKind].default
   for kind in kinds:
      lca_kinds.incl(LCAKind(kind))
   solve_rec(matches, 0, self, lca_kinds)
   do_assert(matches.len != 0)
   sort(matches, proc (a, b: LCAMatch): int = cmp(a.depth, b.depth))
   result = ident(matches[^1].name)
