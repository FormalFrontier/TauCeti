/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Topology.Algebra.Polynomial
public import TauCeti.RingTheory.Polynomial.SymmetricPower
public import TauCeti.Topology.Sym

/-!
# The elementary symmetric chart is a homeomorphism

`TauCeti.Sym.coeffEquiv` presents the `n`-th symmetric power of an algebraically closed field `K`
as the affine space `Fin n → K`, by sending an unordered `n`-tuple to the lower coefficients of the
monic polynomial having it as its root multiset. That equivalence is pure algebra. This file proves
that, when `K` is a proper normed field — `ℂ` being the case of interest — it is a
**homeomorphism** for the quotient topology of `TauCeti.Sym.instTopologicalSpace`.

Both halves are elementary, but neither is formal:

* the coefficients are polynomial in the roots, so the chart is continuous;
* the roots are *not* a polynomial function of the coefficients, and continuity of the inverse is
  the classical statement that the roots of a monic polynomial depend continuously on its
  coefficients. It is obtained here from **Cauchy's bound** `Polynomial.cauchyBound`: a root of a
  monic polynomial is bounded by its coefficients, so the coefficient map is proper, hence closed,
  and a closed continuous bijection is a homeomorphism.

## Main declarations

* `TauCeti.Sym.continuous_coeffEquiv_comp_ofFn`: the coefficients depend continuously on an
  ordered tuple of roots.
* `TauCeti.Sym.norm_le_norm_coeffEquiv_ofFn_add_one`: Cauchy's bound on the symmetric power, that
  an ordered tuple is bounded by one more than the norm of its coefficient tuple.
* `TauCeti.Sym.isProperMap_coeffEquiv_comp_ofFn`: consequently the coefficient map
  `(Fin n → K) → (Fin n → K)` is proper.
* `TauCeti.Sym.coeffHomeomorph`: the **elementary symmetric chart** `Sym K n ≃ₜ (Fin n → K)`.

Lane F4.1 of the analytic Heegaard Floer roadmap opens with "`Sym^g(Σ)` geometry: smooth complex
structure (elementary symmetric functions)", after Ozsváth--Szabó
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1): a holomorphic coordinate on the
surface identifies a neighbourhood in `Sym^g(Σ)` with an open subset of `Sym^g(ℂ)`, and the chart
below is what makes that a chart on a topological manifold. The complex structure itself, and the
totally real tori `T_α`, `T_β`, are separate later steps.
-/

public section

namespace TauCeti

open Filter Polynomial

namespace Sym

/-! ### Continuity of the coefficients -/

section Continuity

variable {ι R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The coefficients of `∏ i ∈ s, (X - C (f i))` depend continuously on the tuple `f` of roots.

This is the elementary half of the chart: each coefficient is, up to sign, an elementary symmetric
function of the roots, so continuity of the ring operations is all that is used. -/
theorem continuous_coeff_prod_X_sub_C (s : Finset ι) (k : ℕ) :
    Continuous fun f : ι → R => (∏ i ∈ s, (X - C (f i))).coeff k := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simpa using continuous_const
  | @insert a s ha ih =>
    cases k with
    | zero =>
      have hpt : (fun f : ι → R => (∏ i ∈ insert a s, (X - C (f i))).coeff 0) =
          fun f => -f a * (∏ i ∈ s, (X - C (f i))).coeff 0 := by
        funext f
        rw [Finset.prod_insert ha, mul_coeff_zero]
        simp
      rw [hpt]
      exact (continuous_apply a).neg.mul (ih 0)
    | succ k =>
      have hpt : (fun f : ι → R => (∏ i ∈ insert a s, (X - C (f i))).coeff (k + 1)) =
          fun f => (∏ i ∈ s, (X - C (f i))).coeff k
            - f a * (∏ i ∈ s, (X - C (f i))).coeff (k + 1) := by
        funext f
        rw [Finset.prod_insert ha, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
      rw [hpt]
      exact (ih k).sub ((continuous_apply a).mul (ih (k + 1)))

end Continuity

section Chart

variable {K : Type*} [NormedField K] [IsAlgClosed K] {n : ℕ}

/-- The coefficient map `(Fin n → K) → (Fin n → K)`, the elementary symmetric chart read on ordered
tuples, is continuous. -/
@[continuity, fun_prop]
theorem continuous_coeffEquiv_comp_ofFn :
    Continuous fun f : Fin n → K => coeffEquiv K n (ofFn f) := by
  refine continuous_pi fun i => ?_
  simp only [coeffEquiv_ofFn_apply]
  exact continuous_coeff_prod_X_sub_C Finset.univ i

/-- **Cauchy's bound** on the symmetric power: the points of an unordered tuple are bounded by one
more than the sup-norm of its elementary symmetric chart, because each of them is a root of the
monic polynomial those coordinates present. -/
theorem norm_le_norm_coeffEquiv_ofFn_add_one (f : Fin n → K) :
    ‖f‖ ≤ ‖coeffEquiv K n (ofFn f)‖ + 1 := by
  have hnonneg : (0 : ℝ) ≤ ‖coeffEquiv K n (ofFn f)‖ + 1 := by positivity
  refine (pi_norm_le_iff_of_nonneg hnonneg).2 fun j => ?_
  have hmonic : (toMonic (ofFn f) : K[X]).Monic := monic_toMonic _
  have hroot : (toMonic (ofFn f) : K[X]).IsRoot (f j) :=
    mem_iff_isRoot.1 (_root_.Sym.mem_coe.2 (mem_ofFn.2 ⟨j, rfl⟩))
  have hcauchy := hroot.norm_lt_cauchyBound hmonic.ne_zero
  have hbound : cauchyBound (toMonic (ofFn f) : K[X]) ≤ ‖coeffEquiv K n (ofFn f)‖₊ + 1 := by
    have hsup : ((Finset.range n).sup fun i => ‖(toMonic (ofFn f) : K[X]).coeff i‖₊)
        ≤ ‖coeffEquiv K n (ofFn f)‖₊ := by
      refine Finset.sup_le fun i hi => ?_
      rw [Finset.mem_range] at hi
      have hcoord := nnnorm_le_pi_nnnorm (coeffEquiv K n (ofFn f)) ⟨i, hi⟩
      rwa [coeffEquiv_apply_eq_coeff] at hcoord
    rw [cauchyBound, hmonic.leadingCoeff, nnnorm_one, div_one, natDegree_toMonic]
    exact add_le_add hsup le_rfl
  have : ‖f j‖₊ < ‖coeffEquiv K n (ofFn f)‖₊ + 1 := hcauchy.trans_le hbound
  simpa using (NNReal.coe_lt_coe.2 this).le

variable [ProperSpace K]

/-- The coefficient map is proper: bounded coefficients force bounded roots, by Cauchy's bound. -/
theorem isProperMap_coeffEquiv_comp_ofFn :
    IsProperMap fun f : Fin n → K => coeffEquiv K n (ofFn f) := by
  rw [isProperMap_iff_tendsto_cocompact]
  refine ⟨continuous_coeffEquiv_comp_ofFn, ?_⟩
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  refine tendsto_atTop_mono (fun f => ?_)
    (tendsto_atTop_add_const_right _ (-1) tendsto_norm_cobounded_atTop)
  have := norm_le_norm_coeffEquiv_ofFn_add_one f
  linarith

/-- The elementary symmetric chart is a closed map. -/
theorem isClosedMap_coeffEquiv : IsClosedMap (coeffEquiv K n) := by
  intro C hC
  have himage : coeffEquiv K n '' C =
      (fun f : Fin n → K => coeffEquiv K n (ofFn f)) '' (ofFn ⁻¹' C) := by
    rw [← Set.image_image (coeffEquiv K n) ofFn (ofFn ⁻¹' C),
      Set.image_preimage_eq _ ofFn_surjective]
  rw [himage]
  exact isProperMap_coeffEquiv_comp_ofFn.isClosedMap _ (hC.preimage continuous_ofFn)

variable (K n)

/-- The **elementary symmetric chart** on the `n`-th symmetric power of a proper algebraically
closed normed field is a homeomorphism onto affine `n`-space: an unordered `n`-tuple is determined,
continuously and with continuous inverse, by the lower coefficients of its monic polynomial.

Continuity of the inverse is the classical continuity of the roots of a monic polynomial in its
coefficients; it comes from `TauCeti.Sym.isProperMap_coeffEquiv_comp_ofFn`, and hence from Cauchy's
bound. -/
noncomputable def coeffHomeomorph : Sym K n ≃ₜ (Fin n → K) :=
  (coeffEquiv K n).toHomeomorphOfContinuousClosed
    (continuous_iff_comp_ofFn.2 continuous_coeffEquiv_comp_ofFn) isClosedMap_coeffEquiv

/-- The chart homeomorphism is the chart equivalence. -/
@[simp]
theorem coeffHomeomorph_apply (s : Sym K n) : coeffHomeomorph K n s = coeffEquiv K n s := by
  simp [coeffHomeomorph]

/-- The inverse chart homeomorphism is the inverse chart equivalence. -/
@[simp]
theorem coeffHomeomorph_symm_apply (f : Fin n → K) :
    ((coeffHomeomorph K n).symm f : Sym K n) = (coeffEquiv K n).symm f := by
  simp [coeffHomeomorph]

end Chart

end Sym

end TauCeti
