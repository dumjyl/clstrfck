## Utilities for calculating the lowest common ancestor from a set of kinds for inheritance trees.

import
   options2,
   core,
   vm_timings,
   matchbook/private/utils
from std/algorithm import sort

export options2

type
   LCAKind* = range[low(uint8) .. high(uint8)]
   LCAData* = ref object
      name*: string
      kinds*: set[LCAKind]
      children*: seq[LCAData]
   LCAMatch = object
      name: string
      depth: int

func `{}`[T](Self: type[LCAKind], vals: set[T]): set[LCAKind] {.time.} =
   for val in vals:
      result.incl(LCAKind(val))

func `{}`*(
      Self: type[LCAData],
      name: string,
      kinds: set[LCAKind],
      children: seq[LCAData]
      ): LCAData {.time.} =
   result = Self(name: name, kinds: kinds, children: children)

func add*(self: LCAData, child: LCAData) {.time.} =
   self.children.add(child)

func lit(self: LCAKind): NimNode = !`bind LCAKind`(`core.lit(self)`)

func lit(self: set[LCAKind]): NimNode =
   result = !{}
   for val in self:
      result.add(val.lit)

func lit[T](self: seq[T]): NimNode =
   result = ![]
   for val in self:
      result.add(val.lit)
   result = !seq[`ident($T)`](`bind @` `result`)

func lit*(self: LCAData): NimNode =
   result = !(typedesc(`bind LCAData`){`self.name.lit`, `self.kinds.lit`, `self.children.lit`})

func evaluate_impl(
      matches: var seq[LCAMatch],
      depth: int,
      data: LCAData,
      kinds: set[LCAKind]) {.time.} =
   if kinds <= data.kinds:
      matches.add(LCAMatch(name: data.name, depth: depth))
      for child_data in data.children:
         evaluate_impl(matches, depth + 1, child_data, kinds)

func evaluate[T: enum](self: LCAData, kinds: set[T]): string {.time.} =
   var matches = seq[LCAMatch].default
   evaluate_impl(matches, 0, self, LCAKind{kinds})
   do_assert(matches.len != 0)
   sort(matches, proc (a, b: LCAMatch): int = cmp(a.depth, b.depth))
   result = matches[^1].name

macro make_ident(val: static[string]): auto {.time.} = val.ident

macro unsafe_lca_downconv*: auto =
   let ident = !`bind evaluate`(`bind {}`(`bind LCAData`, type_of(self)), +kinds)
   result = !`bind unsafe_conv`(self, `ident`)
