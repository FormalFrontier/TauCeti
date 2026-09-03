/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# The loop quiver

The loop quiver `•↺` has a single vertex and a single arrow from it to itself. It is the smallest
quiver that is not acyclic, which makes it the standard boundary case of the theory: its path
algebra is the infinite-dimensional `k[X]`
(`TauCeti.RepresentationTheory.Quiver.OneLoop.PathAlgebra`), and it has infinite representation
type over every field (`TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType`).

This file carries only the vertex and arrow data, so that both of those developments can rest on
it without one depending on the other.

## Main definitions

* `TauCeti.Quiver.OneLoop`: the vertex type, a singleton, with a `Quiver` instance whose only
  arrow type is `PUnit`.
* `TauCeti.Quiver.OneLoop.loop`: the unique arrow, from the vertex to itself.

## References

This file supplies the vertex and arrow data of the loop-quiver worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, alongside the generalized
Kronecker quiver of `TauCeti.RepresentationTheory.Quiver.Kronecker.Basic` and the `D₄` quiver of
`TauCeti.RepresentationTheory.Quiver.D4.Basic`.
-/

public section

namespace TauCeti

open _root_.Quiver

namespace Quiver

/-- The quiver with one vertex and one loop. -/
inductive OneLoop : Type
  | vertex
  deriving DecidableEq

namespace OneLoop

instance : Fintype OneLoop where
  elems := {vertex}
  complete x := by cases x; simp

instance : Unique OneLoop where
  default := vertex
  uniq x := by cases x; rfl

instance : _root_.Quiver OneLoop where
  Hom _ _ := PUnit

instance (a b : OneLoop) : Subsingleton (a ⟶ b) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The unique loop in the one-loop quiver. -/
def loop : (vertex : OneLoop) ⟶ vertex := PUnit.unit

end OneLoop

end Quiver

end TauCeti

end
