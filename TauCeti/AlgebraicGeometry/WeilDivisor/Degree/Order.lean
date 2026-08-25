/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Order
public import TauCeti.AlgebraicGeometry.WeilDivisor.FixedDegree.Basic
public import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Degree and the divisor order

This file records the monotonicity of the formal Weil-divisor degree maps with respect to the
coefficientwise order.  If `D ≤ E`, then the effective difference `E - D` has nonnegative
weighted degree whenever the weights are nonnegative, so `weightedDegree w D ≤ weightedDegree w E`.
With positive weights this becomes strict unless `D = E`, and equality of degrees under a
coefficientwise inequality forces equality of divisors.

These are Layer A divisor-and-degree facts for the Jacobian challenge roadmap
(`TauCetiRoadmap/JacobianChallenge/README.md`): they are the order-theoretic counterpart of the
existing effective-divisor positivity API and support later complete-linear-system and Abel-map
bookkeeping.  No external mathematics is vendored; the proofs reuse Tau Ceti's
`WeilDivisor.Order` API and Mathlib's ordered-additive-group lemmas.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X : Type*}

/-! ### Weighted degree -/

/-- With nonnegative weights on the support of the difference, a coefficientwise increase does
not decrease weighted degree. -/
lemma weightedDegree_le_of_le_of_nonneg_on_support {w : X → ℤ} {D E : WeilDivisor X}
    (hDE : D ≤ E) (hw : ∀ x ∈ (E - D).support, 0 ≤ w x) :
    weightedDegree w D ≤ weightedDegree w E := by
  have hdiff : IsEffective (E - D) := le_iff_isEffective_sub.mp hDE
  have hnonneg : 0 ≤ weightedDegree w (E - D) := by
    rw [weightedDegree_apply]
    exact Finsupp.sum_nonneg fun x hx =>
      mul_nonneg ((isEffective_iff (E - D)).mp hdiff x) (hw x hx)
  rw [map_sub] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- With nonnegative weights, weighted degree is monotone for the coefficientwise divisor
order. -/
lemma weightedDegree_le_of_le {w : X → ℤ} (hw : ∀ x, 0 ≤ w x) {D E : WeilDivisor X}
    (hDE : D ≤ E) : weightedDegree w D ≤ weightedDegree w E :=
  weightedDegree_le_of_le_of_nonneg_on_support hDE fun x _ => hw x

/-- Bundled monotonicity of weighted degree for nonnegative weights. -/
lemma monotone_weightedDegree {w : X → ℤ} (hw : ∀ x, 0 ≤ w x) :
    Monotone (weightedDegree w : WeilDivisor X → ℤ) :=
  (monotone_iff_map_nonneg (weightedDegree w)).2 fun _ hD =>
    (isEffective_iff_zero_le.mpr hD).weightedDegree_nonneg hw

/-- With positive weights on the support of the difference, a proper coefficientwise increase
strictly increases weighted degree. -/
lemma weightedDegree_lt_of_le_of_ne_of_pos_on_support {w : X → ℤ} {D E : WeilDivisor X}
    (hDE : D ≤ E) (hne : D ≠ E) (hw : ∀ x ∈ (E - D).support, 0 < w x) :
    weightedDegree w D < weightedDegree w E := by
  have hdiff : IsEffective (E - D) := le_iff_isEffective_sub.mp hDE
  have hdiff_ne : E - D ≠ 0 := by
    intro hzero
    apply hne
    exact (sub_eq_zero.mp hzero).symm
  have hnonneg : 0 ≤ weightedDegree w (E - D) := by
    rw [weightedDegree_apply]
    exact Finsupp.sum_nonneg fun x hx =>
      mul_nonneg ((isEffective_iff (E - D)).mp hdiff x) (le_of_lt (hw x hx))
  have hpos : 0 < weightedDegree w (E - D) := by
    refine lt_of_le_of_ne hnonneg ?_
    intro hzero
    exact hdiff_ne ((hdiff.weightedDegree_eq_zero_iff_of_pos_on_support hw).mp hzero.symm)
  rw [map_sub] at hpos
  exact sub_pos.mp hpos

/-- With everywhere-positive weights, a proper coefficientwise increase strictly increases
weighted degree. -/
lemma weightedDegree_lt_of_le_of_ne_of_pos {w : X → ℤ} (hw : ∀ x, 0 < w x)
    {D E : WeilDivisor X} (hDE : D ≤ E) (hne : D ≠ E) :
    weightedDegree w D < weightedDegree w E :=
  weightedDegree_lt_of_le_of_ne_of_pos_on_support hDE hne fun x _ => hw x

/-- With everywhere-positive weights, strict coefficientwise inequality strictly increases
weighted degree. -/
lemma weightedDegree_lt_of_lt_of_pos {w : X → ℤ} (hw : ∀ x, 0 < w x)
    {D E : WeilDivisor X} (hDE : D < E) :
    weightedDegree w D < weightedDegree w E :=
  weightedDegree_lt_of_le_of_ne_of_pos hw hDE.le hDE.ne'.symm

/-- With positive weights on the support of the difference, equality of weighted degrees under a
coefficientwise inequality forces equality of divisors. -/
lemma eq_of_le_of_weightedDegree_eq_of_pos_on_support {w : X → ℤ} {D E : WeilDivisor X}
    (hDE : D ≤ E) (hdeg : weightedDegree w D = weightedDegree w E)
    (hw : ∀ x ∈ (E - D).support, 0 < w x) : D = E := by
  by_contra hne
  exact (weightedDegree_lt_of_le_of_ne_of_pos_on_support hDE hne hw).ne hdeg

/-- With everywhere-positive weights, equality of weighted degrees under a coefficientwise
inequality forces equality of divisors. -/
lemma eq_of_le_of_weightedDegree_eq_of_pos {w : X → ℤ} (hw : ∀ x, 0 < w x)
    {D E : WeilDivisor X} (hDE : D ≤ E) (hdeg : weightedDegree w D = weightedDegree w E) :
    D = E :=
  eq_of_le_of_weightedDegree_eq_of_pos_on_support hDE hdeg fun x _ => hw x

/-- For positive weights, weighted degree is strictly monotone for the coefficientwise divisor
order. -/
lemma strictMono_weightedDegree {w : X → ℤ} (hw : ∀ x, 0 < w x) :
    StrictMono (weightedDegree w : WeilDivisor X → ℤ) := by
  intro D E hDE
  exact weightedDegree_lt_of_le_of_ne_of_pos hw hDE.le hDE.ne'.symm

/-! ### Unweighted degree -/

/-- The unweighted degree is monotone for the coefficientwise divisor order. -/
lemma degree_le_of_le {D E : WeilDivisor X} (hDE : D ≤ E) : degree D ≤ degree E := by
  simpa [weightedDegree_one_eq_degree] using
    weightedDegree_le_of_le (w := fun _ : X => (1 : ℤ)) (fun _ => zero_le_one) hDE

/-- Bundled monotonicity of unweighted degree. -/
lemma monotone_degree : Monotone (degree : WeilDivisor X → ℤ) :=
  fun _ _ hDE => degree_le_of_le hDE

/-- A proper coefficientwise increase strictly increases unweighted degree. -/
lemma degree_lt_of_le_of_ne {D E : WeilDivisor X} (hDE : D ≤ E) (hne : D ≠ E) :
    degree D < degree E := by
  simpa [weightedDegree_one_eq_degree] using
    weightedDegree_lt_of_le_of_ne_of_pos (w := fun _ : X => (1 : ℤ))
      (fun _ => zero_lt_one) hDE hne

/-- Strict coefficientwise inequality strictly increases unweighted degree. -/
lemma degree_lt_of_lt {D E : WeilDivisor X} (hDE : D < E) : degree D < degree E :=
  degree_lt_of_le_of_ne hDE.le hDE.ne'.symm

/-- Equality of unweighted degrees under a coefficientwise inequality forces equality of
divisors. -/
lemma eq_of_le_of_degree_eq {D E : WeilDivisor X} (hDE : D ≤ E) (hdeg : degree D = degree E) :
    D = E := by
  have hdeg' : (weightedDegree (fun _ : X => (1 : ℤ))) D =
      (weightedDegree (fun _ : X => (1 : ℤ))) E := by
    simpa [weightedDegree_one_eq_degree] using hdeg
  simpa [weightedDegree_one_eq_degree] using
    eq_of_le_of_weightedDegree_eq_of_pos (w := fun _ : X => (1 : ℤ))
      (fun _ => zero_lt_one) hDE hdeg'

/-- The unweighted degree is strictly monotone for the coefficientwise divisor order. -/
lemma strictMono_degree : StrictMono (degree : WeilDivisor X → ℤ) := by
  intro D E hDE
  exact degree_lt_of_le_of_ne hDE.le hDE.ne'.symm

/-! ### Inclusion–exclusion at the level of degrees -/

/-- The lattice-ordered-group inclusion–exclusion identity for the unweighted degree:
`deg (D ⊓ E) + deg (D ⊔ E) = deg D + deg E`. -/
lemma degree_inf_add_degree_sup (D E : WeilDivisor X) :
    degree (D ⊓ E) + degree (D ⊔ E) = degree D + degree E := by
  rw [← degree_add, inf_add_sup, degree_add]

/-- The lattice-ordered-group inclusion–exclusion identity for the weighted degree:
`w-deg (D ⊓ E) + w-deg (D ⊔ E) = w-deg D + w-deg E`. -/
lemma weightedDegree_inf_add_weightedDegree_sup (w : X → ℤ) (D E : WeilDivisor X) :
    weightedDegree w (D ⊓ E) + weightedDegree w (D ⊔ E) =
      weightedDegree w D + weightedDegree w E := by
  rw [← weightedDegree_add, inf_add_sup, weightedDegree_add]

namespace EffectiveDivisorOfDegree

variable {d e : ℕ}

/-- If a fixed-degree effective divisor is coefficientwise below another, its degree index is
also bounded above. -/
lemma degree_le_of_le {D : EffectiveDivisorOfDegree X d} {E : EffectiveDivisorOfDegree X e}
    (hDE : (D : WeilDivisor X) ≤ E) : d ≤ e := by
  have hdeg : degree (D : WeilDivisor X) ≤ degree (E : WeilDivisor X) :=
    WeilDivisor.degree_le_of_le hDE
  have hde : (d : ℤ) ≤ e := by
    simpa [D.degree_eq, E.degree_eq] using hdeg
  exact_mod_cast hde

end EffectiveDivisorOfDegree

end WeilDivisor

end AlgebraicGeometry

end TauCeti
