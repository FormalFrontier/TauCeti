/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple

/-!
# Necessity of the zeroth-order sign condition in the maximum principle

The weak maximum principle for `-Δ + c` in
`TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple` assumes that the
zeroth-order coefficient is nonnegative. This file records that the assumption is essential.

On the interval `[0, π]`, the function `u(x) = sin x` is positive in the interior, vanishes on
the frontier, and satisfies

`Δ u = -u`.

Thus `u` and the zero function are distinct solutions of the homogeneous Dirichlet problem for
`-Δ - 1`, and the boundary estimate `u ≤ 0` fails in the interior. In particular, both the weak
maximum principle and Dirichlet uniqueness can fail when the zeroth-order coefficient is negative.
This is the first Dirichlet eigenfunction counterexample singled out by the maximum-principle
acceptance criterion in the PDE roadmap.

## Main declarations

* `TauCeti.laplacian_sin`: the one-dimensional identity `Δ sin x = -sin x`.
* `TauCeti.sin_eq_zero_on_frontier_Icc_zero_pi`: `sin` vanishes on the frontier of `[0, π]`.
* `TauCeti.sin_pos_on_interior_Icc_zero_pi`: `sin` is positive in the interior of `[0, π]`.
* `TauCeti.exists_neg_constant_laplacian_eq_mul_eq_zero_on_frontier_pos`: a fully quantified
  counterexample to dropping the nonnegativity assumption from the zeroth-order maximum principle.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Set

/-- On the real line, `sin` is an eigenfunction of the Laplacian with eigenvalue `-1`. -/
theorem laplacian_sin (x : ℝ) : Δ Real.sin x = -Real.sin x := by
  rw [laplacian_eq_iteratedDeriv_real]
  simp

/-- The sine function vanishes on the frontier of the interval `[0, π]`. -/
theorem sin_eq_zero_on_frontier_Icc_zero_pi :
    Set.EqOn Real.sin 0 (frontier (Icc (0 : ℝ) Real.pi)) := by
  rw [frontier_Icc Real.pi_pos.le]
  rintro x (rfl | rfl) <;> simp

/-- The sine function is strictly positive in the interior of the interval `[0, π]`. -/
theorem sin_pos_on_interior_Icc_zero_pi :
    ∀ ⦃x : ℝ⦄, x ∈ interior (Icc (0 : ℝ) Real.pi) → 0 < Real.sin x := by
  rw [interior_Icc]
  exact fun _ hx => Real.sin_pos_of_mem_Ioo hx

/-- The function `sin` is not bounded above by its zero frontier values on `[0, π]`. -/
theorem not_sin_le_zero_on_Icc_zero_pi :
    ¬∀ ⦃x : ℝ⦄, x ∈ Icc (0 : ℝ) Real.pi → Real.sin x ≤ 0 := by
  intro h
  have hmem : Real.pi / 2 ∈ Icc (0 : ℝ) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have := h hmem
  norm_num at this

/-- A negative constant zeroth-order coefficient can violate the weak maximum principle.

There are a compact set `K`, a negative constant `c`, and a function `f`, continuous on `K` and
`C²` on its interior, such that `Δ f = c f` in the interior and `f = 0` on the frontier, but `f`
is positive somewhere in `K`. The witnesses are `K = [0, π]`, `c = -1`, and `f = sin`.

Consequently, the nonnegativity hypothesis on `c` in
`TauCeti.le_of_mul_le_laplacian_le_frontier` and
`TauCeti.eqOn_of_laplacian_sub_mul_eq_of_eqOn_frontier` cannot simply be omitted. -/
theorem exists_neg_constant_laplacian_eq_mul_eq_zero_on_frontier_pos :
    ∃ (K : Set ℝ) (c : ℝ) (f : ℝ → ℝ), IsCompact K ∧ c < 0 ∧ ContinuousOn f K ∧
      (∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x) ∧
      (∀ ⦃x⦄, x ∈ interior K → Δ f x = c * f x) ∧ Set.EqOn f 0 (frontier K) ∧
      ∃ x ∈ K, 0 < f x := by
  refine ⟨Icc 0 Real.pi, -1, Real.sin, isCompact_Icc, by norm_num,
    Real.continuous_sin.continuousOn, ?_, ?_, sin_eq_zero_on_frontier_Icc_zero_pi, ?_⟩
  · exact fun _ _ => (Real.contDiff_sin (n := 2)).contDiffAt
  · intro x _
    rw [laplacian_sin]
    ring
  · refine ⟨Real.pi / 2, ?_, ?_⟩
    · constructor <;> linarith [Real.pi_pos]
    · simp

end TauCeti

end
