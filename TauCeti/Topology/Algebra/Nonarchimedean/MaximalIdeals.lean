/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# Maximal ideals of complete linearly topologized rings

In a complete linearly topologized commutative ring, topologically nilpotent elements lie in
every maximal ideal: if `a ∉ 𝔪` then `1 = r·a + m` with `m ∈ 𝔪`, and `m = 1 - r·a` is a unit by
the geometric series (Proposition 5.38), contradicting properness. Consequently, as soon as the
topologically nilpotent locus is open — as it is for a Huber ring — every maximal ideal is open,
being a neighborhood of each of its points.

These are the openness inputs of Wedhorn's Propositions 7.51 and 7.52 (see
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.Points`), stated here beside the completeness input
`IsTopologicallyNilpotent.isUnit_one_sub` they consume, since neither mentions a valuation
spectrum.

## Main results

* `IsTopologicallyNilpotent.mem_of_isMaximal` : topologically nilpotent elements lie in every
  maximal ideal.
* `Ideal.isOpen_of_isMaximal_of_isOpen_isTopologicallyNilpotent` : every maximal ideal is open
  once the topologically nilpotent locus is.

## Provenance

Adapted from AINTLIB (see References), section `TopNilMaximal` of the source file: the
geometric-series argument for maximal membership and the translation argument for openness are
that file's, with the openness proof rerouted through `AddSubgroup.isOpen_of_mem_nhds`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Propositions 5.38, 7.51,
  7.52.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/AdicSpectrum.lean`.
-/

public section

variable {A : Type*} [CommRing A] [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]
  [IsLinearTopology A A]

/-- **Topologically nilpotent elements lie in every maximal ideal**: otherwise `𝔪` and `a`
generate the unit ideal, `1 = r·a + m`, and `m = 1 - r·a` is a unit by the geometric series
(Proposition 5.38), contradicting properness. -/
theorem IsTopologicallyNilpotent.mem_of_isMaximal {a : A} (ha : IsTopologicallyNilpotent a)
    (𝔪 : Ideal A) [𝔪.IsMaximal] : a ∈ 𝔪 := by
  by_contra ha𝔪
  obtain ⟨r, m, hm, hrm⟩ := Ideal.IsMaximal.exists_inv ‹_› ha𝔪
  exact Ideal.IsMaximal.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem 𝔪 hm
    (eq_sub_of_add_eq' hrm ▸ (ha.mul_left r).isUnit_one_sub))

/-- **Every maximal ideal is open when the topologically nilpotent locus is**: the ideal is a
neighborhood of `0`, since it contains the open set `A°°`. -/
theorem Ideal.isOpen_of_isMaximal_of_isOpen_isTopologicallyNilpotent
    (hopen : IsOpen {a : A | IsTopologicallyNilpotent a}) (𝔪 : Ideal A) [𝔪.IsMaximal] :
    IsOpen (𝔪 : Set A) :=
  𝔪.toAddSubgroup.isOpen_of_mem_nhds <| Filter.mem_of_superset
    (hopen.mem_nhds IsTopologicallyNilpotent.zero) fun _ ha ↦ ha.mem_of_isMaximal 𝔪

end
