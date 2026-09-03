/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring

/-!
# Existence of places of an algebraic function field

Stichtenoth's existence theorem (Theorem 1.1.19) produces a place out of nothing but a subring and
a proper nonzero ideal: if `k ⊆ R ⊆ F` and `I` is a proper nonzero ideal of `R`, then some place
`P` of `F / k` has `R ⊆ 𝒪_P` and `I ⊆ 𝔪_P`. Its consequence (Corollary 1.1.20) is the statement
that gives the divisor theory its substance: every element of `F` transcendental over `k` has both
a zero and a pole, so `ℙ_F` is nonempty and the constants `algebraicClosure k F` are exactly the
functions regular at every place.

The Zorn's lemma half of Theorem 1.1.19 is Mathlib's
`Ideal.image_subset_nonunits_valuationSubring`, which dominates a proper ideal of a subring of a
field by a valuation subring. What is specific to function fields is that the resulting valuation
subring is discrete, and that is
`TauCeti.Place.ofValuationSubring`.

## Main results

* `TauCeti.Place.exists_forall_mem_integers_and_valuation_lt_one`: Stichtenoth, Theorem 1.1.19.
* `TauCeti.Place.exists_ord_pos` and `TauCeti.Place.exists_ord_neg`: an element transcendental over
  the constants has a zero and a pole (Stichtenoth, Corollary 1.1.20).
* `TauCeti.Place.nonempty`: an algebraic function field has at least one place.
* `TauCeti.Place.mem_algebraicClosure_iff_forall_mem_integers` and
  `TauCeti.Place.coe_algebraicClosure_eq_iInter_integers`: `algebraicClosure k F = ⋂_P 𝒪_P`, the
  constants are the everywhere-regular functions.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.1.19 and Corollary 1.1.20.
-/

public section

open Polynomial

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

namespace Place

/-! ### The existence theorem -/

/-- **Stichtenoth, Theorem 1.1.19.** Let `R` be a subring of `F` containing the constants and let
`I` be a proper nonzero ideal of `R`. Then some place of `F / k` has `R` inside its valuation ring
and `I` inside its maximal ideal.

Mathlib's `Ideal.image_subset_nonunits_valuationSubring` supplies a valuation subring `B` of `F`
with `R ≤ B` and `I` inside the nonunits of `B`; because `I` is nonzero, `B` is a *proper*
valuation subring, so `TauCeti.Place.ofValuationSubring` turns it into a place. -/
theorem exists_forall_mem_integers_and_valuation_lt_one (hF : IsFunctionField k F) {R : Subring F}
    (hkR : ∀ c : k, algebraMap k F c ∈ R) {I : Ideal R} (hI : I ≠ ⊤) (hI0 : I ≠ ⊥) :
    ∃ P : Place k F, (∀ r : R, (r : F) ∈ P.integers) ∧ ∀ a ∈ I, P.valuation (a : F) < 1 := by
  obtain ⟨B, hRB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  -- The nonunits of `B` produced from `I` include a nonzero element, so `B` is proper.
  obtain ⟨a, haI, ha0⟩ := Submodule.ne_bot_iff I |>.1 hI0
  have hnonunit : ∀ b ∈ I, ((b : R) : F) ≠ 0 → ((b : R) : F)⁻¹ ∉ B := fun b hb hb0 ↦
    ((B.mem_nonunits_iff_or).1 (hIB ⟨b, hb, rfl⟩)).resolve_left hb0
  have hBtop : B ≠ ⊤ :=
    fun h ↦ hnonunit a haI (by simpa using ha0) (h ▸ ValuationSubring.mem_top _)
  refine ⟨ofValuationSubring hF (fun c ↦ hRB (hkR c)) hBtop, fun r ↦ ?_, fun b hb ↦ ?_⟩
  · rw [integers_ofValuationSubring]
    exact hRB r.2
  · rcases eq_or_ne ((b : R) : F) 0 with h | h
    · simp [h]
    have hb1 : ((b : R) : F)⁻¹ ∉ (ofValuationSubring hF (fun c ↦ hRB (hkR c)) hBtop).integers := by
      rw [integers_ofValuationSubring]
      exact hnonunit b hb h
    rw [mem_integers_iff, not_le, map_inv₀,
      one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h))] at hb1
    exact hb1

/-! ### Zeros and poles -/

/-- **Stichtenoth, Corollary 1.1.20.** An element of an algebraic function field transcendental
over the constants has a zero: some place at which its order is positive. -/
theorem exists_ord_pos (hF : IsFunctionField k F) {x : F} (hx : Transcendental k x) :
    ∃ P : Place k F, 0 < P.ord x := by
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ isAlgebraic_zero)
  have hxR : x ∈ (Algebra.adjoin k ({x} : Set F)).toSubring := Algebra.subset_adjoin rfl
  -- `x` is not a unit of `k[x]`, since `x * f(x) = 1` is an algebraic relation.
  have hnotunit : ¬ IsUnit (⟨x, hxR⟩ : (Algebra.adjoin k ({x} : Set F)).toSubring) := by
    rw [isUnit_iff_exists_inv]
    rintro ⟨w, hw⟩
    obtain ⟨p, hp⟩ : ∃ p : k[X], aeval x p = (w : F) := by
      exact (AlgHom.mem_range _).1
        ((SetLike.ext_iff.1 (Algebra.adjoin_singleton_eq_range_aeval k x) (w : F)).1 w.2)
    have hrel : aeval x (X * p - 1) = 0 := by
      have hxw : x * (w : F) = 1 := congrArg Subtype.val hw
      simp [hp, hxw]
    have hne : (X * p - 1 : k[X]) ≠ 0 := fun h ↦ by
      simpa using congrArg (fun q : k[X] ↦ q.coeff 0) h
    exact hne (transcendental_iff.1 hx _ hrel)
  obtain ⟨P, -, hP⟩ := exists_forall_mem_integers_and_valuation_lt_one hF
    (R := (Algebra.adjoin k ({x} : Set F)).toSubring)
    (fun c ↦ (Algebra.adjoin k ({x} : Set F)).algebraMap_mem c)
    (I := Ideal.span {(⟨x, hxR⟩ : (Algebra.adjoin k ({x} : Set F)).toSubring)})
    (fun h ↦ hnotunit (Ideal.span_singleton_eq_top.1 h))
    (fun h ↦ hx0 (congrArg Subtype.val (Ideal.span_singleton_eq_bot.1 h)))
  exact ⟨P, (P.valuation_lt_one_iff_ord_pos hx0).1 (hP _ (Ideal.mem_span_singleton_self _))⟩

/-- **Stichtenoth, Corollary 1.1.20.** An element of an algebraic function field transcendental
over the constants has a pole: some place at which its order is negative. -/
theorem exists_ord_neg (hF : IsFunctionField k F) {x : F} (hx : Transcendental k x) :
    ∃ P : Place k F, P.ord x < 0 := by
  have hxinv : Transcendental k x⁻¹ := fun h ↦ hx (IsAlgebraic.inv_iff.1 h)
  obtain ⟨P, hP⟩ := exists_ord_pos hF hxinv
  exact ⟨P, by rwa [P.ord_inv, neg_pos] at hP⟩

/-- An algebraic function field has at least one place (Stichtenoth, Corollary 1.1.20). -/
theorem nonempty (hF : IsFunctionField k F) : Nonempty (Place k F) := by
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  obtain ⟨P, -⟩ := exists_ord_pos hF hx
  exact ⟨P⟩

/-! ### The constants are the everywhere-regular functions -/

/-- `algebraicClosure k F = ⋂_P 𝒪_P` (Stichtenoth, Corollary 1.1.20): an element of an algebraic
function field is algebraic over the constants exactly when it has no pole. -/
theorem mem_algebraicClosure_iff_forall_mem_integers (hF : IsFunctionField k F) {f : F} :
    f ∈ algebraicClosure k F ↔ ∀ P : Place k F, f ∈ P.integers := by
  refine ⟨fun h P ↦ P.mem_integers_of_mem_algebraicClosure h, fun h ↦ ?_⟩
  by_contra hf
  obtain ⟨P, hP⟩ := exists_ord_neg hF (mem_algebraicClosure_iff.not.1 hf)
  exact absurd (P.mem_integers_iff_ord_nonneg.1 (h P)) (not_le.2 hP)

/-- `algebraicClosure k F = ⋂_P 𝒪_P`, as an equality of subsets of `F` (Stichtenoth,
Corollary 1.1.20). -/
theorem coe_algebraicClosure_eq_iInter_integers (hF : IsFunctionField k F) :
    (algebraicClosure k F : Set F) = ⋂ P : Place k F, (P.integers : Set F) := by
  ext f
  simpa using mem_algebraicClosure_iff_forall_mem_integers hF

end Place

end TauCeti
