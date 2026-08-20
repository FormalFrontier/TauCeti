/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic

/-!
# Points of the adic spectrum with prescribed support

Wedhorn Proposition 7.51, for open prime ideals: an open prime ideal `𝔭` of `A` is the support
of a point of `Spa(A, A⁺)`, namely the point of its trivial valuation, `trivialSection ⟨𝔭, ‹_›⟩`
(Wedhorn, Remark 4.6) — it is continuous because the only value sets to check are `∅` and `𝔭`,
and sub-unit on every subring because the trivial valuation never exceeds `1`. Proposition
7.52(2) follows: an element of `A` on which no point of `Spa(A, A⁺)` vanishes is a unit, because
a non-unit lies in some maximal ideal, and openness of maximal ideals makes that ideal a support.

Openness of maximal ideals enters only as a hypothesis; for complete linearly topologized rings
it is supplied by `Ideal.isOpen_of_isMaximal_of_isOpen_isTopologicallyNilpotent`
(`TauCeti.Topology.Algebra.Nonarchimedean.MaximalIdeals`).

## Main results

* `TauCeti.ValuationSpectrum.exists_mem_spa_supp_eq` : Proposition 7.51 — an open prime ideal
  is the support of a point of the adic spectrum.
* `TauCeti.ValuationSpectrum.isUnit_of_forall_not_vle_zero` : Proposition 7.52(2) — if no point
  of `Spa(A, A⁺)` vanishes on `f`, then `f` is a unit.

## Provenance

Adapted from AINTLIB (see References), section `Prop752` of the source file: the
trivial-valuation witness and the derivation of 7.52(2) are that file's, with the
valuation-spectrum vocabulary adapted to this repository's `Spv`/`ValuativeRel` interface
(`trivialSection`, `mem_spa_iff`, `supp`) and the statement of 7.51 weakened from maximal to
prime ideals.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 4.6, Propositions
  7.51, 7.52.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/AdicSpectrum.lean`.
-/

namespace TauCeti.ValuationSpectrum

public section

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Proposition 7.51**, for open prime ideals: an open prime ideal `𝔭` is the support of a
point of the adic spectrum — the point of its trivial valuation, `trivialSection ⟨𝔭, ‹_›⟩`.
Wedhorn states the proposition for maximal ideals; the proof needs only primality. -/
theorem exists_mem_spa_supp_eq (Aplus : Subring A) (𝔭 : Ideal A) [𝔭.IsPrime]
    (h𝔭 : IsOpen (𝔭 : Set A)) : ∃ v ∈ spa Aplus, supp v = 𝔭 := by
  refine ⟨trivialSection ⟨𝔭, ‹_›⟩, (mem_spa_iff Aplus _).mpr ⟨?_, fun a _ ↦ ?_⟩, ?_⟩
  · exact (isContinuous_trivialSection_iff _).mpr h𝔭
  · exact (trivialSection_vle_iff _ a 1).mpr
      (Or.inr ((Ideal.ne_top_iff_one 𝔭).mp ‹𝔭.IsPrime›.ne_top))
  · rw [← suppFun_asIdeal, suppFun_trivialSection]

/-- **Proposition 7.52(2)**: if every maximal ideal of `A` is open and no point of
`Spa(A, A⁺)` vanishes on `f`, then `f` is a unit — a non-unit lies in a maximal ideal, which is
the support of a point by Proposition 7.51. -/
theorem isUnit_of_forall_not_vle_zero (Aplus : Subring A)
    (hmax : ∀ (𝔪 : Ideal A), 𝔪.IsMaximal → IsOpen (𝔪 : Set A)) {f : A}
    (h : ∀ v ∈ spa Aplus, ¬ v.toValuativeRel.vle f 0) : IsUnit f := by
  by_contra hf
  obtain ⟨𝔪, h𝔪, hf𝔪⟩ := exists_max_ideal_of_mem_nonunits hf
  obtain ⟨v, hv, rfl⟩ := exists_mem_spa_supp_eq Aplus 𝔪 (hmax 𝔪 h𝔪)
  exact h v hv ((mem_supp_iff v f).mp hf𝔪)

end

end TauCeti.ValuationSpectrum
