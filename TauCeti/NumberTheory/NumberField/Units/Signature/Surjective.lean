/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import TauCeti.NumberTheory.NumberField.Units.Signature.Basic

/-!
# Sign realization: the field-unit signature map is surjective

By weak approximation for the infinite places (`denseRange_algebraMap_pi`), the diagonal image of a
number field `K` is dense in `∏_v WithAbs v.1`. Any prescribed sign pattern at the real places cuts
out a nonempty open set there (the real embeddings are continuous by
`Completion.isometry_embedding_of_isReal`), so the dense image meets it, giving an element of `K`
realizing the prescribed signs. If a real place exists it has a definite sign, so is nonzero and in
`Kˣ`; otherwise the codomain is trivial. Hence the **field**-signature map
`fieldUnitSignature : Kˣ → ∏_{w real} ℝˣ ⧸ ℝ₊` is **surjective**.

This concerns the signature of all nonzero field elements, *not* the signature of the arithmetic
units `(𝓞 K)ˣ` (`unitSignature`), whose image is generally a proper subspace of the full sign space
`(ℤ/2)ᵗ`. It is the archimedean prerequisite for the genus-theory `2`-rank of the narrow class group
(the Multiquadratic Layer-3 target): surjectivity of the field signature identifies the
narrow-vs-ordinary defect `ker(Cl⁺ → Cl)` with the quotient `sign(Kˣ) ⧸ sign((𝓞 K)ˣ)`, i.e. the
cokernel of the *integer-unit* signature `unitSignature` — a later step.

## Main results

* `TauCeti.NumberField.fieldUnitSignature_surjective`: the field signature `fieldUnitSignature`
  (on `Kˣ`) is surjective.
-/

public section

open NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Sign realization.** The *field*-signature homomorphism `fieldUnitSignature : Kˣ → ∏_{w real}
ℝˣ ⧸ ℝ₊`, on all nonzero elements of `K`, is surjective: every prescribed sign pattern at the real
places is realized by some `x : Kˣ`. (This is the field signature, not the integer-unit signature
`unitSignature` on `(𝓞 K)ˣ`.) -/
theorem fieldUnitSignature_surjective :
    Function.Surjective (fieldUnitSignature (K := K)) := by
  classical
  intro t
  -- Representatives `s w : ℝˣ` of the target cosets `t w`.
  choose s hs using fun w : {w : InfinitePlace K // w.IsReal} =>
    QuotientGroup.mk'_surjective (Units.posSubgroup ℝ) (t w)
  -- The set of tuples realizing all the prescribed signs, as a finite intersection of preimages of
  -- open half-lines under the (continuous, being isometries) real coordinate maps.
  set U : Set (∀ v : InfinitePlace K, WithAbs v.1) :=
    ⋂ w : {w : InfinitePlace K // w.IsReal},
      (fun y => (s w : ℝ) * embedding_of_isReal w.2 (WithAbs.equiv w.1.1 (y w.1))) ⁻¹'
        Set.Ioi (0 : ℝ) with hU
  have hUopen : IsOpen U :=
    isOpen_iInter_of_finite fun w =>
      (continuous_const.mul (((w.1.isometry_embedding_of_isReal w.2).continuous).comp
        (continuous_apply w.1))).isOpen_preimage _ isOpen_Ioi
  have hUne : U.Nonempty := by
    refine ⟨fun v => (WithAbs.equiv v.1).symm
      (if h : v.IsReal then (if 0 < (s ⟨v, h⟩ : ℝ) then 1 else -1) else 0), ?_⟩
    simp only [hU, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi, RingEquiv.apply_symm_apply]
    intro w
    rw [dif_pos w.2, Subtype.coe_eta]
    split_ifs with hpos
    · rw [map_one, mul_one]; exact hpos
    · rw [map_neg, map_one, mul_neg_one, neg_pos]
      exact lt_of_le_of_ne (not_lt.mp hpos) (Units.ne_zero _)
  obtain ⟨x, hx⟩ := (denseRange_algebraMap_pi K).exists_mem_open hUopen hUne
  simp only [hU, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi] at hx
  -- The diagonal coordinate is `x` itself.
  have hcoord : ∀ v : InfinitePlace K,
      WithAbs.equiv v.1 ((algebraMap K (∀ v : InfinitePlace K, WithAbs v.1) x) v) = x := fun v => by
    simp [Pi.algebraMap_apply, WithAbs.algebraMap_right_apply]
  have hx' : ∀ w : {w : InfinitePlace K // w.IsReal},
      0 < (s w : ℝ) * embedding_of_isReal w.2 x := fun w => by
    simpa only [hcoord w.1] using hx w
  -- Package `x` as a unit and check its signature is `t`.
  rcases isEmpty_or_nonempty {w : InfinitePlace K // w.IsReal} with _ | hne
  · exact ⟨1, Subsingleton.elim _ _⟩
  · obtain ⟨w₀⟩ := hne
    have hx0 : x ≠ 0 := fun h0 => by simpa [h0] using (hx' w₀).ne'
    refine ⟨Units.mk0 x hx0, funext fun w => ?_⟩
    rw [fieldUnitSignature_apply, ← hs w, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Units.mem_posSubgroup]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, Units.val_mk0]
    rcases mul_pos_iff.mp (hx' w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact mul_pos (inv_pos.mpr h2) h1
    · exact mul_pos_of_neg_of_neg (inv_lt_zero.mpr h2) h1

end TauCeti.NumberField
