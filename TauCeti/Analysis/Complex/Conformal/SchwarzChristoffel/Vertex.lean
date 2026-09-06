/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive
public import TauCeti.Analysis.Complex.SegmentDistIntegral
public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# The vertices of the Schwarz--Christoffel map

The Schwarz--Christoffel primitive is holomorphic on the open upper half-plane, but the polygon
it is meant to parametrize is read off from its *boundary* values: the vertices of that polygon
are the limits of the primitive at the real prevertices.  This file shows those limits exist.

Write `p = a j` for a prevertex and `t` for the total turning exponent carried by it, that is
the sum of the `e i` over all `i` with `a i = p`.  Near `p` the integrand has norm
`∏ i, dist z (a i) ^ e i`, which is `dist z p ^ t` times a factor that stays bounded, so it is
dominated by `C * dist z p ^ t`.  When `-1 < t` — the classical range, since a polygon with
interior angle `α` at the vertex has `t = α / π - 1 > -1` — this dominating function is
integrable along any segment ending at `p`, uniformly enough that the primitive satisfies the
Cauchy criterion at `p`.  Completeness of `ℂ` then produces the limit.

The quantitative heart is the segment estimate `TauCeti.integral_dist_rpow_segment_le`:
integrating `dist ⬝ p ^ u` along a segment of length `L` gives at most `2 / (u + 1) * L ^ (u + 1)`
for `-1 < u ≤ 0`.  Fed into Mathlib's displacement bound
`norm_sub_le_integral_of_norm_deriv_le_of_le` it turns into a Hölder bound
`‖F z - F w‖ ≤ C * (2 / (u + 1)) * ‖z - w‖ ^ (u + 1)` for `z, w` in a small half-disc, which is
what forces the Cauchy criterion.

## Main definitions

* `TauCeti.schwarzChristoffelVertex` -- the boundary value of the Schwarz--Christoffel primitive
  at a prevertex.

## Main results

* `TauCeti.exists_norm_schwarzChristoffelIntegrand_le` -- near a prevertex the integrand is
  dominated by a constant times the corresponding real power of the distance to it.
* `TauCeti.exists_tendsto_schwarzChristoffelPrimitive` -- the Schwarz--Christoffel primitive has
  a limit at a prevertex whose total turning exponent exceeds `-1`.
* `TauCeti.tendsto_schwarzChristoffelPrimitive` -- that limit is `schwarzChristoffelVertex`.
* `TauCeti.schwarzChristoffelVertex_congr` -- coincident prevertices carry the same vertex.
* `TauCeti.schwarzChristoffelVertex_change_base` -- changing the base point translates every
  vertex by the same amount, so the shape of the polygon does not depend on it.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

-- `open` before `namespace TauCeti`: inside it, `UpperHalfPlane` would resolve to the imported
-- `TauCeti.UpperHalfPlane` namespace instead of the root one.
open Complex Filter MeasureTheory Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-! ### The local bound at a prevertex -/

/-- Near a real prevertex `p`, the Schwarz--Christoffel integrand is dominated by a constant
multiple of `dist z p ^ t`, where `t = ∑ i with a i = p, e i` is the total turning exponent
carried by the indices sitting at `p`.  The prevertex itself is excluded because both sides are
totalized there and carry no analytic information. -/
theorem exists_norm_schwarzChristoffelIntegrand_le (a e : ι → ℝ) (p : ℝ) :
    ∃ C > 0, ∀ᶠ z in 𝓝[≠] ((p : ℂ)), ‖schwarzChristoffelIntegrand a e z‖
      ≤ C * dist z (p : ℂ) ^ ∑ i with a i = p, e i := by
  classical
  set s : Finset ι := {i | a i = p} with hsdef
  have hs : ∀ i, i ∈ s ↔ a i = p := by simp [hsdef]
  set g : ℂ → ℝ := fun z => ∏ i ∈ Finset.univ \ s, dist z (a i : ℂ) ^ e i with hg
  have hgcont : ContinuousAt g (p : ℂ) := by
    refine tendsto_finsetProd _ fun i hi => ?_
    have hne : ((a i : ℂ)) ≠ (p : ℂ) := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
      exact_mod_cast fun h => hi ((hs i).mpr (by exact_mod_cast h))
    exact ContinuousAt.rpow_const (continuousAt_id.dist continuousAt_const)
      (Or.inl fun h => hne (dist_eq_zero.mp h).symm)
  have hgnn : 0 ≤ g (p : ℂ) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg dist_nonneg _
  refine ⟨g (p : ℂ) + 1, by linarith, ?_⟩
  have hev : ∀ᶠ z in 𝓝 ((p : ℂ)), g z ≤ g (p : ℂ) + 1 :=
    hgcont.eventually_le_const (lt_add_one _)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z hz hzne
  have hd : 0 < dist z (p : ℂ) := dist_pos.mpr hzne
  have hsplit : ∏ i, dist z (a i : ℂ) ^ e i = dist z (p : ℂ) ^ (∑ i ∈ s, e i) * g z := by
    rw [hg, ← Finset.prod_sdiff (Finset.subset_univ s), Real.rpow_sum_of_pos hd,
      mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by rw [(hs i).mp hi]
  rw [norm_schwarzChristoffelIntegrand, hsplit, mul_comm]
  exact mul_le_mul_of_nonneg_right hz (Real.rpow_nonneg dist_nonneg _)

/-! ### A Hölder estimate near a prevertex -/

/-- Where the Schwarz--Christoffel integrand is dominated by `C * dist ⬝ p ^ u` with `-1 < u ≤ 0`,
its primitive is Hölder of exponent `u + 1` on the part of the half-plane inside a disc about the
boundary point `p`. -/
private theorem dist_schwarzChristoffelPrimitive_le (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p : ℂ} {C u ρ : ℝ} (hu : -1 < u) (hu0 : u ≤ 0) (hC : 0 ≤ C) (hp : p.im ≤ 0)
    (hbd : ∀ y ∈ Metric.ball p ρ ∩ upperHalfPlaneSet,
      ‖schwarzChristoffelIntegrand a e y‖ ≤ C * dist y p ^ u)
    {z w : ℂ} (hz : z ∈ Metric.ball p ρ ∩ upperHalfPlaneSet)
    (hw : w ∈ Metric.ball p ρ ∩ upperHalfPlaneSet) :
    dist (schwarzChristoffelPrimitive a e z₀ z) (schwarzChristoffelPrimitive a e z₀ w)
      ≤ C * (2 / (u + 1)) * ‖z - w‖ ^ (u + 1) := by
  have hconv : Convex ℝ (Metric.ball p ρ ∩ upperHalfPlaneSet) :=
    (convex_ball p ρ).inter (convex_halfSpace_im_gt 0)
  have hγcont : Continuous fun s : ℝ => w + (s : ℂ) * (z - w) := by fun_prop
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1,
      w + (s : ℂ) * (z - w) ∈ Metric.ball p ρ ∩ upperHalfPlaneSet := by
    intro s hs
    have hmix := hconv hw hz (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s) hs.1 (by ring)
    have heq : (1 - s) • w + s • z = w + (s : ℂ) * (z - w) := by
      simp only [Complex.real_smul]
      push_cast
      ring
    rwa [heq] at hmix
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, w + (s : ℂ) * (z - w) ≠ p := by
    intro s hs hcon
    have him := (hmem s hs).2
    rw [hcon] at him
    exact absurd him (not_lt.mpr hp)
  -- the primitive restricted to the segment, and its derivative
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => schwarzChristoffelPrimitive a e z₀ (w + (s : ℂ) * (z - w)))
        ((z - w) * schwarzChristoffelIntegrand a e (w + (s : ℂ) * (z - w))) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => w + (s : ℂ) * (z - w)) (z - w) s := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (z - w)).const_add w
    have h2 := hasDerivAt_schwarzChristoffelPrimitive a e z₀ (hmem s hs).2
    simpa [Function.comp_def, smul_eq_mul] using h2.scomp s h1
  have hfc : ContinuousOn
      (fun s : ℝ => schwarzChristoffelPrimitive a e z₀ (w + (s : ℂ) * (z - w))) (Icc 0 1) :=
    fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
  have hfd : DifferentiableOn ℝ
      (fun s : ℝ => schwarzChristoffelPrimitive a e z₀ (w + (s : ℂ) * (z - w))) (Ioo 0 1) :=
    fun s hs => (hderiv s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
  have hfB : ∀ᵐ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ‖deriv (fun s : ℝ => schwarzChristoffelPrimitive a e z₀ (w + (s : ℂ) * (z - w))) t‖
        ≤ ‖z - w‖ * (C * dist (w + (t : ℂ) * (z - w)) p ^ u) :=
    .of_forall fun t ht => by
      rw [(hderiv t (Ioo_subset_Icc_self ht)).deriv, norm_mul]
      exact mul_le_mul_of_nonneg_left (hbd _ (hmem t (Ioo_subset_Icc_self ht))) (norm_nonneg _)
  have hBi : IntervalIntegrable
      (fun s : ℝ => ‖z - w‖ * (C * dist (w + (s : ℂ) * (z - w)) p ^ u)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul (continuousOn_const.mul
      ((hγcont.dist continuous_const).continuousOn.rpow_const fun s hs =>
        Or.inl fun h => hne s hs (by rwa [dist_eq_zero] at h)))
  have hkey := norm_sub_le_integral_of_norm_deriv_le_of_le zero_le_one hfc hfd hfB hBi
  have h1 : w + ((1 : ℝ) : ℂ) * (z - w) = z := by push_cast; ring
  have h0 : w + ((0 : ℝ) : ℂ) * (z - w) = w := by push_cast; ring
  simp only [h1, h0] at hkey
  rw [dist_eq_norm]
  refine hkey.trans ?_
  calc (∫ s in (0 : ℝ)..1, ‖z - w‖ * (C * dist (w + (s : ℂ) * (z - w)) p ^ u))
      = C * ((∫ s in (0 : ℝ)..1, dist (w + (s : ℂ) * (z - w)) p ^ u) * ‖z - w‖) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        ring
    _ ≤ C * (2 / (u + 1) * ‖z - w‖ ^ (u + 1)) :=
        mul_le_mul_of_nonneg_left (integral_dist_rpow_segment_le hu hu0 hne) hC
    _ = C * (2 / (u + 1)) * ‖z - w‖ ^ (u + 1) := by ring

/-! ### Existence of the vertex -/

/-- The **Schwarz--Christoffel primitive converges at a prevertex** whose total turning exponent
exceeds `-1`.  The exponent is summed over all indices sitting at the prevertex `a j`, so for a
family of pairwise distinct prevertices the hypothesis reads `-1 < e j`; for the classical
exponents `e i = α i / π - 1` attached to interior angles `α i ∈ (0, 2 π)` it always holds.  The
limit is the polygon vertex the map produces at `a j`. -/
theorem exists_tendsto_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane) (j : ι)
    (he : -1 < ∑ i with a i = a j, e i) :
    ∃ v : ℂ, Tendsto (schwarzChristoffelPrimitive a e z₀)
      (𝓝[upperHalfPlaneSet] ((a j : ℂ))) (𝓝 v) := by
  set p : ℂ := (a j : ℂ) with hpdef
  have hpim : p.im ≤ 0 := by simp [hpdef]
  have hsub : upperHalfPlaneSet ⊆ ({p}ᶜ : Set ℂ) := by
    intro y hy hcon
    rw [mem_singleton_iff] at hcon
    rw [hcon] at hy
    exact absurd hy (not_lt.mpr hpim)
  have hnb : (𝓝[upperHalfPlaneSet] p).NeBot := neBot_nhdsWithin_upperHalfPlaneSet (a j)
  obtain ⟨C, hC, hev⟩ := exists_norm_schwarzChristoffelIntegrand_le a e (a j)
  set T : ℝ := ∑ i with a i = a j, e i with hTdef
  set u : ℝ := min T 0 with hudef
  have hu : -1 < u := lt_min he (by norm_num)
  have hu0 : u ≤ 0 := min_le_right _ _
  have hu1 : (0 : ℝ) < u + 1 := by linarith
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set ρ₀ : ℝ := min r₁ 1 with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min hr₁ zero_lt_one
  have hbd : ∀ y ∈ Metric.ball p ρ₀ ∩ upperHalfPlaneSet,
      ‖schwarzChristoffelIntegrand a e y‖ ≤ C * dist y p ^ u := by
    intro y hy
    have hyne : y ≠ p := hsub hy.2
    have hd : 0 < dist y p := dist_pos.mpr hyne
    have hd1 : dist y p ≤ 1 := by
      have := Metric.mem_ball.mp hy.1
      have h2 : ρ₀ ≤ 1 := min_le_right _ _
      linarith
    have h1 : ‖schwarzChristoffelIntegrand a e y‖ ≤ C * dist y p ^ T := by
      refine hr₁sub ⟨?_, hyne⟩
      exact Metric.mem_ball.mp hy.1 |>.trans_le (min_le_left _ _) |> Metric.mem_ball.mpr
    have hdecomp : T = (T - u) + u := by ring
    have h2 : dist y p ^ T ≤ dist y p ^ u := by
      rw [hdecomp, Real.rpow_add hd]
      have hle1 : dist y p ^ (T - u) ≤ 1 :=
        Real.rpow_le_one dist_nonneg hd1 (by simp [hudef])
      nlinarith [Real.rpow_nonneg (dist_nonneg (x := y) (y := p)) u]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC.le)
  refine CompleteSpace.complete (f := map (schwarzChristoffelPrimitive a e z₀)
    (𝓝[upperHalfPlaneSet] p)) ?_
  rw [Metric.cauchy_iff]
  refine ⟨map_neBot, ?_⟩
  intro ε hε
  set K : ℝ := C * (2 / (u + 1)) with hKdef
  have hK : 0 < K := by positivity
  obtain ⟨ρ, hρpos, hρle, hρε⟩ : ∃ ρ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ K * (2 * ρ) ^ (u + 1) < ε := by
    set τ : ℝ := (ε / (2 * K)) ^ (u + 1)⁻¹ with hτdef
    have hτ : 0 < τ := Real.rpow_pos_of_pos (by positivity) _
    refine ⟨min ρ₀ (τ / 2), lt_min hρ₀ (by positivity), min_le_left _ _, ?_⟩
    have h2ρ : 2 * min ρ₀ (τ / 2) ≤ τ := by
      have := min_le_right ρ₀ (τ / 2)
      linarith
    have hstep : K * (2 * min ρ₀ (τ / 2)) ^ (u + 1) ≤ K * τ ^ (u + 1) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) h2ρ hu1.le) hK.le
    have hval : τ ^ (u + 1) = ε / (2 * K) := by
      rw [hτdef, Real.rpow_inv_rpow (by positivity) hu1.ne']
    rw [hval] at hstep
    have : K * (ε / (2 * K)) = ε / 2 := by field_simp
    rw [this] at hstep
    exact hstep.trans_lt (half_lt_self hε)
  refine ⟨schwarzChristoffelPrimitive a e z₀ '' (Metric.ball p ρ ∩ upperHalfPlaneSet), ?_, ?_⟩
  · refine mem_map.mpr (mem_of_superset ?_ (subset_preimage_image _ _))
    exact inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds p hρpos)) self_mem_nhdsWithin
  rintro x ⟨z, hz, rfl⟩ y ⟨w, hw, rfl⟩
  have hzw : ‖z - w‖ ≤ 2 * ρ := by
    have h1 := Metric.mem_ball.mp hz.1
    have h2 := Metric.mem_ball.mp hw.1
    have := dist_triangle z p w
    rw [dist_comm p w] at this
    rw [← dist_eq_norm]
    linarith
  have hzsub : Metric.ball p ρ ∩ upperHalfPlaneSet ⊆ Metric.ball p ρ₀ ∩ upperHalfPlaneSet :=
    inter_subset_inter_left _ (Metric.ball_subset_ball hρle)
  calc dist (schwarzChristoffelPrimitive a e z₀ z) (schwarzChristoffelPrimitive a e z₀ w)
      ≤ K * ‖z - w‖ ^ (u + 1) :=
        dist_schwarzChristoffelPrimitive_le a e z₀ hu hu0 hC.le hpim hbd (hzsub hz) (hzsub hw)
    _ ≤ K * (2 * ρ) ^ (u + 1) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hzw hu1.le) hK.le
    _ < ε := hρε

/-- The **Schwarz--Christoffel vertex** attached to the prevertex `a j`: the boundary value at
`a j` of the primitive normalized at `z₀`.  It is a genuine limit under the hypotheses of
`TauCeti.exists_tendsto_schwarzChristoffelPrimitive`. -/
def schwarzChristoffelVertex (a e : ι → ℝ) (z₀ : UpperHalfPlane) (j : ι) : ℂ :=
  limUnder (𝓝[upperHalfPlaneSet] ((a j : ℂ))) (schwarzChristoffelPrimitive a e z₀)

/-- Coincident prevertices carry the same vertex: `schwarzChristoffelVertex` depends on the index
`j` only through the prevertex `a j`. -/
theorem schwarzChristoffelVertex_congr (a e : ι → ℝ) (z₀ : UpperHalfPlane) {j k : ι}
    (h : a j = a k) :
    schwarzChristoffelVertex a e z₀ j = schwarzChristoffelVertex a e z₀ k := by
  simp only [schwarzChristoffelVertex, h]

/-- The Schwarz--Christoffel primitive converges to `schwarzChristoffelVertex` at the
prevertex. -/
theorem tendsto_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane) (j : ι)
    (he : -1 < ∑ i with a i = a j, e i) :
    Tendsto (schwarzChristoffelPrimitive a e z₀) (𝓝[upperHalfPlaneSet] ((a j : ℂ)))
      (𝓝 (schwarzChristoffelVertex a e z₀ j)) := by
  have := neBot_nhdsWithin_upperHalfPlaneSet (a j)
  obtain ⟨v, hv⟩ := exists_tendsto_schwarzChristoffelPrimitive a e z₀ j he
  rwa [schwarzChristoffelVertex, hv.limUnder_eq]

/-- Changing the base point translates every Schwarz--Christoffel vertex by the same constant, so
the polygon it spans is determined up to translation. -/
theorem schwarzChristoffelVertex_change_base (a e : ι → ℝ) (b c : UpperHalfPlane) (j : ι)
    (he : -1 < ∑ i with a i = a j, e i) :
    schwarzChristoffelVertex a e b j
      = schwarzChristoffelVertex a e c j - schwarzChristoffelPrimitive a e c b := by
  have := neBot_nhdsWithin_upperHalfPlaneSet (a j)
  refine tendsto_nhds_unique (tendsto_schwarzChristoffelPrimitive a e b j he) ?_
  refine Tendsto.congr' ?_
    ((tendsto_schwarzChristoffelPrimitive a e c j he).sub tendsto_const_nhds)
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (schwarzChristoffelPrimitive_change_base a e b c hz).symm

end TauCeti
