/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Maximal ideals of a topological ring with open unit group

A maximal ideal of a topological ring is closed as soon as the unit group is open. The closure of
`𝔪` is again an ideal, and it is proper because the units are open, so their complement is a closed
set containing `𝔪` and hence containing its closure; maximality then forces that closure to be `𝔪`.

Openness of the unit group is the only topological input, and it stays a hypothesis so that any
route to it can consume this lemma. `TauCeti.RingTheory.Huber.UnitGroup` supplies one for complete
Huber rings and reads Wedhorn's Proposition 7.51 off it, but nothing here mentions completeness, a
nonarchimedean topology, or commutativity: `Ideal A` is the lattice of left ideals of a ring `A`,
and a proper left ideal already avoids the units.

Contrast `TauCeti.Topology.Algebra.Nonarchimedean.MaximalIdeals`, which proves maximal ideals
*open*. That argument needs a linear topology and is vacuous for a Tate ring, where no proper ideal
is open; closedness is the form that survives.

## Main results

* `Ideal.isClosed_of_isMaximal_of_isOpen_isUnit` : a maximal ideal of a topological ring is closed
  once the unit group is open.

## Provenance

Adapted from AINTLIB (see References), section `MaximalIdealClosed` of the source file, where the
statement is `isClosed_of_isMaximal_of_isOpen_units`. The argument is that file's, essentially
verbatim; only the commutativity hypothesis is dropped.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.51.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/AdicSpectrum.lean`.
-/

public section

/-- **A maximal ideal of a topological ring is closed once the unit group is open.** The closure
of `𝔪` is an ideal containing `𝔪`, and it is proper because it avoids the units — the units are
open, so their complement is a closed set containing `𝔪` and hence its closure. Maximality then
forces the closure to be `𝔪` itself. -/
theorem Ideal.isClosed_of_isMaximal_of_isOpen_isUnit {A : Type*} [Ring A] [TopologicalSpace A]
    [IsTopologicalRing A] (hU : IsOpen {a : A | IsUnit a}) (𝔪 : Ideal A) [𝔪.IsMaximal] :
    IsClosed (𝔪 : Set A) := by
  rw [← closure_eq_iff_isClosed, ← Ideal.coe_closure]
  congr 1
  have hne : 𝔪.closure ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one]
    exact fun h1 ↦ (closure_minimal (fun x hx ↦ mt (Ideal.eq_top_of_isUnit_mem 𝔪 hx)
      (Ideal.IsMaximal.ne_top ‹_›)) hU.isClosed_compl h1) isUnit_one
  exact (Ideal.IsMaximal.eq_of_le ‹_› hne fun x hx ↦ subset_closure hx).symm

end
