/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# A uniform time of existence for autonomous ODEs

Picard–Lindelöf produces a solution of `x' = g x` through a single initial point. Extending an
integral curve past a finite endpoint of its interval of definition needs more: a *single* time
`ε > 0` that works for **every** initial point near a given one, together with control on where the
resulting solutions go. This file supplies both by shrinking Mathlib's Picard–Lindelöf solution
space until all of its curves lie in a prescribed neighbourhood.

## Main results

* `ODE.exists_forall_mem_ball_exists_eq_forall_mem_Ioo_hasDerivAt_and_mem`: for a `C^1`
  autonomous vector field and a neighbourhood `u` of `c`, there are a radius `r > 0` and a time
  `ε > 0` such that every initial point of `ball c r` carries a solution on
  `Ioo (t₀ - ε) (t₀ + ε)` staying in `u`.

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Finite-endpoint extension criterion".
-/

public section

open Filter Metric Set
open scoped NNReal Topology

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {g : E → E} {c : E}

/-- **Uniform time of existence.** For an autonomous vector field `g` that is `C^1` at `c` and a
neighbourhood `u` of `c`, there are a radius `r > 0` and a time `ε > 0` such that every initial
point in `ball c r` carries a solution of `f' t = g (f t)` on all of `Ioo (t₀ - ε) (t₀ + ε)`,
which moreover stays inside `u`.

Picard–Lindelöf alone gives a time of existence depending on the initial point; the content here
is that it can be chosen uniformly, and that the solutions do not escape a prescribed
neighbourhood. -/
theorem exists_forall_mem_ball_exists_eq_forall_mem_Ioo_hasDerivAt_and_mem [CompleteSpace E]
    (hg : ContDiffAt ℝ 1 g c) {u : Set E} (hu : u ∈ 𝓝 c) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ ball c r, ∃ f : ℝ → E, f t₀ = x ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt f (g (f t)) t ∧ f t ∈ u := by
  obtain ⟨ε₀, hε₀, a, r₀, L, K, hr₀, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hg
  obtain ⟨ρ, hρ, hρu⟩ := Metric.mem_nhds_iff.mp hu
  -- the ball of radius `a` on which the Picard–Lindelöf data lives is nondegenerate
  have hapos : (0 : ℝ) < a := by
    have h := (hpl t₀).mul_max_le
    simp only [add_sub_cancel_left, sub_sub_cancel, max_self] at h
    have : (0 : ℝ) ≤ L * ε₀ := mul_nonneg L.coe_nonneg hε₀.le
    have : (0 : ℝ) < r₀ := hr₀
    linarith
  -- shrink the ball so that it sits inside `u`, and shrink the time accordingly
  set ρ' : ℝ≥0 := ⟨ρ / 2, by positivity⟩ with hρ'
  have hρ'pos : 0 < ρ' := by rw [← NNReal.coe_pos]; exact half_pos hρ
  set a' : ℝ≥0 := min a ρ' with ha'
  have ha'pos : 0 < a' := lt_min (by exact_mod_cast hapos) hρ'pos
  have ha'u : closedBall c (a' : ℝ) ⊆ u := by
    refine subset_trans (closedBall_subset_ball ?_) hρu
    calc (a' : ℝ) ≤ (ρ' : ℝ) := by exact_mod_cast min_le_right a ρ'
      _ = ρ / 2 := rfl
      _ < ρ := by linarith
  set r' : ℝ≥0 := a' / 2 with hr'def
  have hr'lt : r' < a' := NNReal.half_lt_self ha'pos.ne'
  obtain ⟨ε, hε, hpl'⟩ := (hpl t₀).exists_shrink_radius hε₀ (min_le_left a ρ') hr'lt
  have ha'coe_pos : (0 : ℝ) < (a' : ℝ) := by exact_mod_cast ha'pos
  have hr'pos : (0 : ℝ) < r' := by
    simpa [hr'def] using half_pos ha'coe_pos
  refine ⟨r', hr'pos, ε, hε, fun x hx ↦ ?_⟩
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hpl' (ball_subset_closedBall hx)
  have ht₀ : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := by simp [hε.le]
  refine ⟨α.compProj, ?_, fun t ht ↦ ⟨?_, ha'u (α.compProj_mem_closedBall hpl'.mul_max_le)⟩⟩
  · rw [FunSpace.compProj_of_mem ht₀, ← hα, FunSpace.next_apply₀]
  · apply (hasDerivWithinAt_picard_Icc ht₀ hpl'.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ ↦ α.compProj_mem_closedBall hpl'.mul_max_le) x (Ioo_subset_Icc_self ht)
      |>.congr_of_mem _ (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    intro t' ht'
    nth_rw 1 [← hα]
    rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]

end ODE
