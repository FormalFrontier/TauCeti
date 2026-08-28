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
* `TauCeti.ValuationSpectrum.span_eq_top_of_forall_mem_spa_exists_not_vle_zero` : the converse
  half of Corollary 7.53 — if every point of `Spa(A, A⁺)` is nonzero somewhere on `T`, then `T`
  generates the unit ideal.

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

/-- **The converse half of Wedhorn Corollary 7.53.** If every maximal ideal of `A` is open and
every point of `Spa(A, A⁺)` is nonzero on some member of `T`, then `T` generates the unit ideal.

Wedhorn states this for a complete affinoid ring, where every maximal ideal is automatically
open; the openness hypothesis is what replaces completeness here, matching the generality the
forward half already has in
`TauCeti.ValuationSpectrum.mem_rationalSubset_of_span_eq_top_of_mem_spa`. `T` is an arbitrary
set: finiteness plays no part, and enters only in the rational-cover corollary. -/
theorem span_eq_top_of_forall_mem_spa_exists_not_vle_zero (Aplus : Subring A)
    (hmax : ∀ (𝔪 : Ideal A), 𝔪.IsMaximal → IsOpen (𝔪 : Set A)) {T : Set A}
    (h : ∀ v ∈ spa Aplus, ∃ t ∈ T, ¬ v.toValuativeRel.vle t 0) :
    Ideal.span T = ⊤ := by
  by_contra hne
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨v, hv, rfl⟩ := exists_mem_spa_supp_eq Aplus 𝔪 (hmax 𝔪 h𝔪)
  obtain ⟨t, ht, hvt⟩ := h v hv
  exact hvt ((mem_supp_iff v t).mp (hle (Ideal.subset_span ht)))

/-- **Proposition 7.52(2)**: if every maximal ideal of `A` is open and no point of
`Spa(A, A⁺)` vanishes on `f`, then `f` is a unit.

Wedhorn states this for a complete affinoid ring; as with the converse above, openness of the
maximal ideals is what replaces completeness.

⚠ That replacement is not innocent: `hmax` is unsatisfiable over a nonzero Tate ring, so this
statement and the converse above are vacuous on the affinoid rings Wedhorn applies them to. In a
Tate ring an ideal is open exactly when it is `⊤`, so no proper ideal is open; see
`TauCeti.Huber.IsTateRing.not_isOpen_of_isMaximal`, and its consequence
`TauCeti.Huber.IsTateRing.subsingleton_of_forall_isMaximal_isOpen`. A form usable for Tate rings
has to reach the point of Proposition 7.51 without going through an open maximal ideal —
`mem_of_forall_vle_one`, which is 7.52(1), avoids the problem entirely. -/
theorem isUnit_of_forall_not_vle_zero (Aplus : Subring A)
    (hmax : ∀ (𝔪 : Ideal A), 𝔪.IsMaximal → IsOpen (𝔪 : Set A)) {f : A}
    (h : ∀ v ∈ spa Aplus, ¬ v.toValuativeRel.vle f 0) : IsUnit f := by
  rw [← Ideal.span_singleton_eq_top]
  simpa using span_eq_top_of_forall_mem_spa_exists_not_vle_zero Aplus hmax
    (T := {f}) fun v hv ↦ ⟨f, Set.mem_singleton f, h v hv⟩

end

end TauCeti.ValuationSpectrum
