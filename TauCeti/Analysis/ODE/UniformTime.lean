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
resulting solutions go. This file supplies both.

The mechanism is an a priori bound: a solution whose vector field is bounded by `L` on a closed
ball around `c` cannot leave that ball before time `(R - ‖x - c‖) / L`, because it never had time
to travel that far. Combined with `IsPicardLindelof.exists_shrink_radius`, which trades the radius
of the ball for a shorter time interval, this confines all the solutions produced by
Picard–Lindelöf to a prescribed neighbourhood of `c`.

## Main results

* `ODE.norm_sub_le_of_hasDerivWithinAt_Icc`: the a priori speed bound on a closed interval whose
  left endpoint carries the initial condition.
* `ODE.mem_closedBall_of_hasDerivWithinAt_Icc`: the resulting confinement to a closed ball, on an
  interval centred at the initial time.
* `ODE.exists_forall_mem_ball_exists_forall_mem_Ioo_hasDerivAt`: for a `C^1` autonomous vector
  field and a neighbourhood `u` of `c`, there are a radius `r > 0` and a time `ε > 0` such that
  every initial point of `ball c r` carries a solution on `Ioo (t₀ - ε) (t₀ + ε)` staying in `u`.

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Finite-endpoint extension criterion".
-/

public section

open Filter Metric Set
open scoped NNReal Topology

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {g : E → E} {f : ℝ → E} {c : E} {L R : ℝ}

/-- **A priori speed bound.** If a solution of the autonomous equation `f' t = g (f t)` on
`Icc a b` starts close enough to `c` that the total distance `L * (b - a)` it could travel at
speed `L` keeps it inside `closedBall c R`, where `g` is bounded by `L`, then it indeed travels at
speed at most `L`.

The point is that the bound on `g` is only assumed on the ball, so this is a genuine a priori
estimate: it is proved by continuous induction along the interval. -/
theorem norm_sub_le_of_hasDerivWithinAt_Icc {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (g (f t)) (Icc a b) t)
    (hg : ∀ y ∈ closedBall c R, ‖g y‖ ≤ L) (hL : 0 ≤ L)
    (hstart : ‖f a - c‖ + L * (b - a) < R) :
    ∀ t ∈ Icc a b, ‖f t - f a‖ ≤ L * (t - a) := by
  have hcont : ContinuousOn f (Icc a b) := fun t ht ↦ (hf t ht).continuousWithinAt
  set S : Set ℝ := {t | ‖f t - f a‖ ≤ L * (t - a)} with hS
  have hclosed : IsClosed (S ∩ Icc a b) := by
    have hc : ContinuousOn (fun t ↦ ‖f t - f a‖ - L * (t - a)) (Icc a b) :=
      ((hcont.sub continuousOn_const).norm).sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    have h : IsClosed (Icc a b ∩ (fun t ↦ ‖f t - f a‖ - L * (t - a)) ⁻¹' Iic (0 : ℝ)) :=
      hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hset : S ∩ Icc a b = Icc a b ∩ (fun t ↦ ‖f t - f a‖ - L * (t - a)) ⁻¹' Iic 0 := by
      ext t
      simp only [hS, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Iic, sub_nonpos]
      tauto
    rw [hset]
    exact h
  have hsub : Icc a b ⊆ S := by
    refine hclosed.Icc_subset_of_forall_exists_gt (by simp [hS]) ?_
    rintro t ⟨htS, hta, htb⟩ y hy
    simp only [hS, mem_ofPred_eq] at htS
    have htab : t ∈ Icc a b := ⟨hta, htb.le⟩
    -- the solution is still strictly inside the ball at time `t`
    have hballt : f t ∈ ball c R := by
      have htri : ‖f t - c‖ ≤ ‖f t - f a‖ + ‖f a - c‖ := by
        rw [← sub_add_sub_cancel (f t) (f a) c]
        exact norm_add_le _ _
      have hmono : L * (t - a) ≤ L * (b - a) := by
        have : t - a ≤ b - a := by linarith
        exact mul_le_mul_of_nonneg_left this hL
      rw [mem_ball_iff_norm]
      linarith
    -- so it stays inside for a little longer, and the mean value theorem applies there
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp
      ((hcont t htab).preimage_mem_nhdsWithin (isOpen_ball.mem_nhds hballt))
    set z : ℝ := min (min y b) (t + δ / 2) with hz
    have htz : t < z := lt_min (lt_min hy htb) (by linarith)
    have hzy : z ≤ y := (min_le_left _ _).trans (min_le_left _ _)
    have hzb : z ≤ b := (min_le_left _ _).trans (min_le_right _ _)
    have hIccsub : Icc t z ⊆ Icc a b := fun s hs ↦ ⟨hta.trans hs.1, hs.2.trans hzb⟩
    have hIccball : ∀ s ∈ Icc t z, f s ∈ closedBall c R := by
      intro s hs
      have hsδ : s ∈ ball t δ := by
        rw [mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
        have : z ≤ t + δ / 2 := min_le_right _ _
        linarith [hs.2]
      exact ball_subset_closedBall (hδsub ⟨hsδ, hIccsub hs⟩)
    have hmvt : ‖f z - f t‖ ≤ L * ‖z - t‖ :=
      (convex_Icc t z).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun s hs ↦ (hf s (hIccsub hs)).mono hIccsub)
        (fun s hs ↦ hg _ (hIccball s hs)) (left_mem_Icc.2 htz.le) (right_mem_Icc.2 htz.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hmvt
    refine ⟨z, ?_, htz, hzy⟩
    simp only [hS, mem_ofPred_eq]
    calc ‖f z - f a‖ ≤ ‖f z - f t‖ + ‖f t - f a‖ := by
          rw [← sub_add_sub_cancel (f z) (f t) (f a)]; exact norm_add_le _ _
      _ ≤ L * (z - t) + L * (t - a) := add_le_add hmvt htS
      _ = L * (z - a) := by ring
  exact fun t ht ↦ hsub ht

/-- **A priori confinement.** A solution of `f' t = g (f t)` on a symmetric interval around `t₀`
stays inside `closedBall c R` as soon as `g` is bounded by `L` there and the initial point leaves
room `L * ε` inside the ball. -/
theorem mem_closedBall_of_hasDerivWithinAt_Icc {t₀ ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), HasDerivWithinAt f (g (f t)) (Icc (t₀ - ε) (t₀ + ε)) t)
    (hg : ∀ y ∈ closedBall c R, ‖g y‖ ≤ L) (hL : 0 ≤ L)
    (hstart : ‖f t₀ - c‖ + L * ε < R) :
    ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), f t ∈ closedBall c R := by
  -- the right half is the a priori bound applied on `Icc t₀ (t₀ + ε)`
  have hright : ∀ t ∈ Icc t₀ (t₀ + ε), f t ∈ closedBall c R := by
    have hsub : Icc t₀ (t₀ + ε) ⊆ Icc (t₀ - ε) (t₀ + ε) := fun s hs ↦ ⟨by linarith [hs.1], hs.2⟩
    have := norm_sub_le_of_hasDerivWithinAt_Icc (f := f) (g := g) (c := c)
      (fun t ht ↦ (hf t (hsub ht)).mono hsub) hg hL (by simpa using hstart)
    intro t ht
    have h1 := this t ht
    have h2 : ‖f t - c‖ ≤ ‖f t - f t₀‖ + ‖f t₀ - c‖ := by
      rw [← sub_add_sub_cancel (f t) (f t₀) c]; exact norm_add_le _ _
    have h3 : L * (t - t₀) ≤ L * ε := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hL
    rw [mem_closedBall_iff_norm]
    linarith
  -- the left half follows by reflecting the time variable, which negates the vector field
  have hleft : ∀ t ∈ Icc (t₀ - ε) t₀, f t ∈ closedBall c R := by
    have hreflect_t₀ : 2 * t₀ - t₀ = t₀ := by ring
    have hsub : ∀ s ∈ Icc t₀ (t₀ + ε), 2 * t₀ - s ∈ Icc (t₀ - ε) (t₀ + ε) := by
      intro s hs; constructor <;> [linarith [hs.2]; linarith [hs.1]]
    have hF : ∀ s ∈ Icc t₀ (t₀ + ε),
        HasDerivWithinAt (fun s ↦ f (2 * t₀ - s)) ((fun y ↦ -g y) (f (2 * t₀ - s)))
          (Icc t₀ (t₀ + ε)) s := by
      intro s hs
      have hφ : HasDerivWithinAt (fun s : ℝ ↦ 2 * t₀ - s) (-1) (Icc t₀ (t₀ + ε)) s :=
        ((hasDerivWithinAt_id s _).const_sub (2 * t₀)).congr_deriv (by ring)
      have := (hf _ (hsub s hs)).scomp s hφ (fun r hr ↦ hsub r hr)
      simpa [Function.comp_def] using this
    have hG : ∀ y ∈ closedBall c R, ‖(fun y ↦ -g y) y‖ ≤ L := by
      intro y hy; simpa using hg y hy
    have hstart' : ‖(fun s ↦ f (2 * t₀ - s)) t₀ - c‖ + L * ε < R := by
      simpa [hreflect_t₀] using hstart
    have := norm_sub_le_of_hasDerivWithinAt_Icc (f := fun s ↦ f (2 * t₀ - s)) (g := fun y ↦ -g y)
      (c := c) hF hG hL (by simpa using hstart')
    intro t ht
    have hs : 2 * t₀ - t ∈ Icc t₀ (t₀ + ε) := by
      constructor <;> [linarith [ht.2]; linarith [ht.1]]
    have h1 := this _ hs
    have hreflect_t : 2 * t₀ - (2 * t₀ - t) = t := by ring
    simp only [hreflect_t, hreflect_t₀] at h1
    have h2 : ‖f t - c‖ ≤ ‖f t - f t₀‖ + ‖f t₀ - c‖ := by
      rw [← sub_add_sub_cancel (f t) (f t₀) c]; exact norm_add_le _ _
    have h3 : L * (2 * t₀ - t - t₀) ≤ L * ε := mul_le_mul_of_nonneg_left (by linarith [ht.1]) hL
    rw [mem_closedBall_iff_norm]
    linarith
  intro t ht
  rcases le_total t t₀ with h | h
  · exact hleft t ⟨ht.1, h⟩
  · exact hright t ⟨h, ht.2⟩

/-- **Uniform time of existence.** For an autonomous vector field `g` that is `C^1` at `c` and a
neighbourhood `u` of `c`, there are a radius `r > 0` and a time `ε > 0` such that every initial
point in `ball c r` carries a solution of `f' t = g (f t)` on all of `Ioo (t₀ - ε) (t₀ + ε)`,
which moreover stays inside `u`.

Picard–Lindelöf alone gives a time of existence depending on the initial point; the content here
is that it can be chosen uniformly, and that the solutions do not escape a prescribed
neighbourhood. -/
theorem exists_forall_mem_ball_exists_forall_mem_Ioo_hasDerivAt [CompleteSpace E]
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
  have hρ'coe : (ρ' : ℝ) = ρ / 2 := rfl
  have hρ'pos : 0 < ρ' := by rw [← NNReal.coe_pos, hρ'coe]; linarith
  set a' : ℝ≥0 := min a ρ' with ha'
  have ha'pos : 0 < a' := lt_min (by exact_mod_cast hapos) hρ'pos
  have ha'u : closedBall c (a' : ℝ) ⊆ u := by
    refine subset_trans (closedBall_subset_ball ?_) hρu
    calc (a' : ℝ) ≤ (ρ' : ℝ) := by exact_mod_cast min_le_right a ρ'
      _ = ρ / 2 := hρ'coe
      _ < ρ := by linarith
  set r' : ℝ≥0 := a' / 2 with hr'def
  have hr'lt : r' < a' := NNReal.half_lt_self ha'pos.ne'
  obtain ⟨ε, hε, hpl'⟩ := (hpl t₀).exists_shrink_radius hε₀ (min_le_left a ρ') hr'lt
  have ha'coe_pos : (0 : ℝ) < (a' : ℝ) := by exact_mod_cast ha'pos
  have hr'pos : (0 : ℝ) < r' := by
    simpa [hr'def] using half_pos ha'coe_pos
  refine ⟨r', hr'pos, ε, hε, fun x hx ↦ ?_⟩
  obtain ⟨α, hα0, hα⟩ := hpl'.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (ball_subset_closedBall hx)
  have hα0' : α t₀ = x := hα0
  have hbound : ∀ y ∈ closedBall c (a' : ℝ), ‖g y‖ ≤ (L : ℝ) := fun y hy ↦
    hpl'.norm_le t₀ ⟨by linarith, by linarith⟩ y hy
  have hmax : (L : ℝ) * ε ≤ (a' : ℝ) - r' := by
    have h := hpl'.mul_max_le
    simpa only [add_sub_cancel_left, sub_sub_cancel, max_self] using h
  have hstart : ‖α t₀ - c‖ + (L : ℝ) * ε < a' := by
    have : ‖x - c‖ < (r' : ℝ) := mem_ball_iff_norm.mp hx
    rw [hα0']
    linarith
  have hconf := mem_closedBall_of_hasDerivWithinAt_Icc (f := α) (g := g) (c := c)
    (R := (a' : ℝ)) (L := (L : ℝ)) hε.le hα hbound L.coe_nonneg hstart
  refine ⟨α, hα0', fun t ht ↦ ⟨?_, ha'u (hconf t (Ioo_subset_Icc_self ht))⟩⟩
  exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end ODE
