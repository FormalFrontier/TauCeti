/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.DriftMaximumPrinciple

/-!
# Maximum principles with drift and a nonnegative zeroth-order term

This file combines the two lower-order extensions of the Laplacian maximum principle.  For the
operator `-Δ - b·∇ + c`, a nonnegative zeroth-order coefficient and a bounded drift preserve the
weak maximum principle.  The sign condition on `c` and the nonnegativity of the frontier bound are
explicit, as required for the standard estimate `sup u ≤ sup (u⁺|∂Ω)`.

Following Gilbarg--Trudinger, *Elliptic Partial Differential Equations of Second Order*, Chapter 3,
the proof adapts the weak-principle argument from `DriftMaximumPrinciple`: it perturbs a subsolution
by the same positive exponential barrier. At a positive interior maximum, its derivative vanishes
and its Laplacian is nonpositive, while the subsolution inequality, `c ≥ 0`, and strict positivity
of the barrier give the opposite strict inequality.

## Main declarations

* `TauCeti.le_of_mul_le_laplacian_add_fderiv_le_frontier`: the weak maximum principle for
  `-Δ - b·∇ + c`.
* `TauCeti.ge_of_laplacian_add_fderiv_le_mul_ge_frontier` and
  `TauCeti.abs_le_of_laplacian_add_fderiv_eq_mul_abs_le_frontier`: its lower and two-sided forms.
* `TauCeti.le_of_laplacian_add_fderiv_sub_mul_le_laplacian_add_fderiv_sub_mul_of_le_frontier`:
  the corresponding comparison principle.
* `TauCeti.eqOn_of_laplacian_add_fderiv_sub_mul_eq_of_eqOn_frontier`: Dirichlet uniqueness for
  equal operator values.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E]

/-- **Weak maximum principle for `-Δ - b·∇ + c`.**

If `c` is nonnegative, `b` has norm at most `β` on the interior of a compact set, and
`c x * f x ≤ Δ f x + fderiv ℝ f x (b x)`, then every nonnegative frontier bound for `f` is a
bound on the whole set. -/
theorem le_of_mul_le_laplacian_add_fderiv_le_frontier {K : Set E} (hK : IsCompact K)
    {c f : E → ℝ} {b : E → E} {β m : ℝ} (hm : 0 ≤ m) (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hsub : ∀ ⦃x⦄, x ∈ interior K → c x * f x ≤ Δ f x + fderiv ℝ f x (b x))
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ m := by
  intro x hxK
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
  let α : ℝ := β + 1
  let w : E → ℝ := fun y => Real.exp (α * ⟪u, y⟫)
  have hwpos (y : E) : 0 < w y := Real.exp_pos _
  have hwcd : ContDiff ℝ 2 w := by
    have hi : ContDiff ℝ 2 (fun y : E => (⟪u, y⟫ : ℝ)) := by
      simpa only [coe_innerSL_apply] using (innerSL ℝ u).contDiff
    exact (by simpa only [smul_eq_mul] using hi.const_smul α : ContDiff ℝ 2 _).exp
  obtain ⟨C, hC⟩ := hK.bddAbove_image hwcd.continuous.continuousOn
  have hC0 : 0 ≤ C := (hwpos x).le.trans (hC (Set.mem_image_of_mem w hxK))
  apply le_of_forall_pos_mul_le hC0
  intro ε hε
  let g : E → ℝ := fun y => f y + ε • w y
  have hgcont : ContinuousOn g K := hcont.add (hwcd.continuous.continuousOn.const_smul ε)
  obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn ⟨x, hxK⟩ hgcont
  have hfz : f z ≤ m := by
    by_cases hzint : z ∈ interior K
    · by_contra hn
      have hfz0 : 0 ≤ f z := hm.trans (not_le.mp hn).le
      have hgcd : ContDiffAt ℝ 2 g z := (hcd hzint).add (hwcd.contDiffAt.const_smul ε)
      have hloc : IsLocalMax g z := hzmax.isLocalMax (mem_interior_iff_mem_nhds.mp hzint)
      have hLgnonpos : Δ g z + fderiv ℝ g z (b z) ≤ 0 := by
        rw [hloc.fderiv_eq_zero]
        simpa using laplacian_nonpos_of_isLocalMax hgcd hloc
      have hLwpos : 0 < Δ w z + fderiv ℝ w z (b z) := by
        simpa only [w, α] using
          laplacian_add_fderiv_exp_inner_pos_of_norm_le hu (hb hzint) z
      have hLg : Δ g z + fderiv ℝ g z (b z) =
          (Δ f z + fderiv ℝ f z (b z)) +
            ε * (Δ w z + fderiv ℝ w z (b z)) := by
        simpa only [g] using laplacian_add_fderiv_add_const_smul f w (b z) ε z
          (hcd hzint) hwcd.contDiffAt
      have hLf0 : 0 ≤ Δ f z + fderiv ℝ f z (b z) :=
        (mul_nonneg (hc hzint) hfz0).trans (hsub hzint)
      rw [hLg] at hLgnonpos
      nlinarith [mul_pos hε hLwpos]
    · exact hbdry ⟨subset_closure hzK, hzint⟩
  have hxle : f x + ε * w x ≤ f z + ε * w z := by
    simpa [g, smul_eq_mul] using hzmax hxK
  have hwzC : ε * w z ≤ ε * C :=
    mul_le_mul_of_nonneg_left (hC (Set.mem_image_of_mem w hzK)) hε.le
  nlinarith [mul_nonneg hε.le (hwpos x).le]

/-- **Weak minimum principle for `-Δ - b·∇ + c`.** This is the negation-dual of
`le_of_mul_le_laplacian_add_fderiv_le_frontier`. -/
theorem ge_of_laplacian_add_fderiv_le_mul_ge_frontier {K : Set E} (hK : IsCompact K)
    {c f : E → ℝ} {b : E → E} {β m : ℝ} (hm : m ≤ 0) (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hsuper : ∀ ⦃x⦄, x ∈ interior K →
      Δ f x + fderiv ℝ f x (b x) ≤ c x * f x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → m ≤ f x) :
    ∀ ⦃x⦄, x ∈ K → m ≤ f x := by
  intro x hx
  have h := le_of_mul_le_laplacian_add_fderiv_le_frontier (c := c) (f := -f) (b := b)
    (β := β) (m := -m) hK (neg_nonneg.mpr hm) hcont.neg
    (fun y hy => (hcd hy).neg) hc hb (fun y hy => by
      have h1 : Δ (-f) y = -Δ f y := by rw [congrFun laplacian_neg y, Pi.neg_apply]
      have h2 : fderiv ℝ (-f) y (b y) = -fderiv ℝ f y (b y) := by
        rw [fderiv_neg, neg_apply]
      rw [h1, h2, Pi.neg_apply, mul_neg]
      linarith [hsuper hy]) (fun y hy => by simpa using neg_le_neg (hbdry hy)) hx
  simpa using neg_le_neg h

/-- A solution of `-Δ f - b·∇f + c f = 0` is bounded in absolute value by every
nonnegative bound for its absolute value on the frontier. -/
theorem abs_le_of_laplacian_add_fderiv_eq_mul_abs_le_frontier {K : Set E} (hK : IsCompact K)
    {c f : E → ℝ} {b : E → E} {β M : ℝ} (hM : 0 ≤ M) (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hsol : ∀ ⦃x⦄, x ∈ interior K →
      Δ f x + fderiv ℝ f x (b x) = c x * f x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → |f x| ≤ M) :
    ∀ ⦃x⦄, x ∈ K → |f x| ≤ M := by
  intro x hx
  rw [abs_le]
  constructor
  · exact ge_of_laplacian_add_fderiv_le_mul_ge_frontier hK (neg_nonpos.mpr hM) hcont hcd hc hb
      (fun y hy => (hsol hy).le) (fun y hy => (abs_le.mp (hbdry hy)).1) hx
  · exact le_of_mul_le_laplacian_add_fderiv_le_frontier hK hM hcont hcd hc hb
      (fun y hy => (hsol hy).ge) (fun y hy => (abs_le.mp (hbdry hy)).2) hx

/-- **Comparison principle for `-Δ - b·∇ + c`.** Functions acted on by the same lower-order
coefficients are ordered on a compact set when their operator values and frontier values are
ordered. -/
theorem le_of_laplacian_add_fderiv_sub_mul_le_laplacian_add_fderiv_sub_mul_of_le_frontier
    {K : Set E} (hK : IsCompact K) {c f g : E → ℝ}
    {b : E → E} {β : ℝ} (hfcont : ContinuousOn f K) (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hL : ∀ ⦃x⦄, x ∈ interior K →
      Δ g x + fderiv ℝ g x (b x) - c x * g x ≤
        Δ f x + fderiv ℝ f x (b x) - c x * f x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ g x) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ g x := by
  intro x hx
  have h := le_of_mul_le_laplacian_add_fderiv_le_frontier (c := c) (f := f - g) (b := b)
    (β := β) (m := 0) hK le_rfl (hfcont.sub hgcont)
    (fun y hy => (hfcd hy).sub (hgcd hy)) hc hb (fun y hy => by
      rw [(hfcd hy).laplacian_sub (hgcd hy), fderiv_sub
        ((hfcd hy).differentiableAt (by norm_num)) ((hgcd hy).differentiableAt (by norm_num))]
      simp only [Pi.sub_apply, sub_apply]
      linarith [hL hy]) (fun y hy => sub_nonpos.mpr (hbdry hy)) hx
  exact sub_nonpos.mp h

/-- **Dirichlet uniqueness for `-Δ - b·∇ + c`.** Equal operator values and equal frontier data
force two functions to agree throughout the compact set. -/
theorem eqOn_of_laplacian_add_fderiv_sub_mul_eq_of_eqOn_frontier {K : Set E} (hK : IsCompact K)
    {c f g : E → ℝ} {b : E → E} {β : ℝ} (hfcont : ContinuousOn f K)
    (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hL : ∀ ⦃x⦄, x ∈ interior K →
      Δ f x + fderiv ℝ f x (b x) - c x * f x =
        Δ g x + fderiv ℝ g x (b x) - c x * g x)
    (hbdry : Set.EqOn f g (frontier K)) : Set.EqOn f g K := by
  intro x hx
  apply le_antisymm
  · exact le_of_laplacian_add_fderiv_sub_mul_le_laplacian_add_fderiv_sub_mul_of_le_frontier
      hK hfcont hgcont hfcd hgcd hc hb
      (fun y hy => (hL hy).ge) (fun y hy => (hbdry hy).le) hx
  · exact le_of_laplacian_add_fderiv_sub_mul_le_laplacian_add_fderiv_sub_mul_of_le_frontier
      hK hgcont hfcont hgcd hfcd hc hb
      (fun y hy => (hL hy).le) (fun y hy => (hbdry hy).ge) hx

end TauCeti

end
