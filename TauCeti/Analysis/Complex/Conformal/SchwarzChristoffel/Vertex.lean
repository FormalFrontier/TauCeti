/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive

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

The quantitative heart is a segment estimate: on a segment of length `L`, the distance to a
fixed point `p` is at least `L` times the distance of the parameter to the (clamped) foot of the
perpendicular, so the integral of `dist ⬝ p ^ u` over the parameter interval is at most
`2 / (u + 1) * L ^ u` for `-1 < u ≤ 0`.  Multiplying by `L` turns the estimate into a Hölder
bound `‖F z - F w‖ ≤ C * (2 / (u + 1)) * ‖z - w‖ ^ (u + 1)` for `z, w` in a small half-disc,
which is what forces the Cauchy criterion.

## Main definitions

* `TauCeti.schwarzChristoffelVertex` -- the boundary value of the Schwarz--Christoffel primitive
  at a prevertex.

## Main results

* `TauCeti.exists_norm_schwarzChristoffelIntegrand_le` -- near a prevertex the integrand is
  dominated by a constant times the corresponding real power of the distance to it.
* `TauCeti.exists_tendsto_schwarzChristoffelPrimitive` -- the Schwarz--Christoffel primitive has
  a limit at a prevertex whose total turning exponent exceeds `-1`.
* `TauCeti.tendsto_schwarzChristoffelVertex` -- that limit is `schwarzChristoffelVertex`.
* `TauCeti.schwarzChristoffelVertex_change_base` -- changing the base point translates every
  vertex by the same amount, so the shape of the polygon does not depend on it.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

namespace TauCeti

open Complex Filter MeasureTheory Set Topology UpperHalfPlane

variable {ι : Type*} [Fintype ι]

/-! ### A segment estimate for negative powers of the distance -/

/-- On the segment from `w` to `z`, the distance to a point `p` is bounded below by the length of
the segment times the distance of the parameter to a fixed parameter `c ∈ [0, 1]`.  Geometrically
`c` is the foot of the perpendicular from `p`, clamped to the parameter interval. -/
private theorem exists_mem_Icc_mul_abs_sub_le_dist (p z w : ℂ) :
    ∃ c ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖z - w‖ * |s - c| ≤ dist (w + (s : ℂ) * (z - w)) p := by
  rcases eq_or_ne z w with rfl | hzw
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun s _ => by simp⟩
  have hL : (0 : ℝ) < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hzw)
  set A : ℂ := w - p with hA
  set B : ℂ := z - w with hB
  set q : ℝ := A.re * B.re + A.im * B.im with hq
  set s₀ : ℝ := -q / ‖B‖ ^ 2 with hs₀
  have key : ∀ t : ℝ, ‖B‖ * |t - s₀| ≤ ‖A + (t : ℂ) * B‖ := by
    intro t
    have hB2 : ‖B‖ ^ 2 = B.re * B.re + B.im * B.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    have hA2 : ‖A‖ ^ 2 = A.re * A.re + A.im * A.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    have hnorm : ‖A + (t : ℂ) * B‖ ^ 2 =
        (A.re + t * B.re) * (A.re + t * B.re) + (A.im + t * B.im) * (A.im + t * B.im) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
    have hdiv : q ^ 2 / ‖B‖ ^ 2 ≤ ‖A‖ ^ 2 := by
      rw [div_le_iff₀ (pow_pos hL 2), hA2, hB2, hq]
      nlinarith [sq_nonneg (A.re * B.im - A.im * B.re)]
    have hsq : (‖B‖ * |t - s₀|) ^ 2 ≤ ‖A + (t : ℂ) * B‖ ^ 2 := by
      have hexp : (‖B‖ * |t - s₀|) ^ 2 =
          ‖B‖ ^ 2 * t ^ 2 + 2 * t * q + q ^ 2 / ‖B‖ ^ 2 := by
        rw [mul_pow, sq_abs, hs₀]
        field_simp
        ring
      rw [hexp, hnorm]
      nlinarith [hdiv, hA2, hB2]
    have := abs_le_of_sq_le_sq' hsq (norm_nonneg _)
    exact this.2
  refine ⟨max 0 (min 1 s₀), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, ?_⟩
  intro s hs
  have hclamp : |s - max 0 (min 1 s₀)| ≤ |s - s₀| := by
    rcases le_or_gt s₀ 0 with h | h
    · rw [min_eq_right (h.trans zero_le_one), max_eq_left h, sub_zero,
        abs_of_nonneg hs.1, abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s - s₀)]
      linarith
    rcases le_or_gt s₀ 1 with h' | h'
    · rw [min_eq_right h', max_eq_right h.le]
    · rw [min_eq_left h'.le, max_eq_right zero_le_one]
      rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith [hs.2])]
      linarith
  have hseg : w + (s : ℂ) * (z - w) - p = A + (s : ℂ) * B := by
    rw [hA, hB]; ring
  calc ‖z - w‖ * |s - max 0 (min 1 s₀)| ≤ ‖B‖ * |s - s₀| := by
        rw [hB]
        exact mul_le_mul_of_nonneg_left hclamp (norm_nonneg _)
    _ ≤ ‖A + (s : ℂ) * B‖ := key s
    _ = dist (w + (s : ℂ) * (z - w)) p := by rw [dist_eq_norm, hseg]

/-- The integral of a negative power of the distance to `p` along the segment from `w` to `z`,
weighted by the length of the segment.  The exponent range `-1 < u ≤ 0` is exactly the one in
which the singularity of `dist ⬝ p ^ u` is integrable. -/
private theorem integral_dist_rpow_segment_le {p : ℂ} {u : ℝ} (hu : -1 < u) (hu0 : u ≤ 0)
    {z w : ℂ} (hne : ∀ s ∈ Icc (0 : ℝ) 1, w + (s : ℂ) * (z - w) ≠ p) :
    (∫ s in (0 : ℝ)..1, dist (w + (s : ℂ) * (z - w)) p ^ u) * ‖z - w‖
      ≤ 2 / (u + 1) * ‖z - w‖ ^ (u + 1) := by
  have hu1 : (0 : ℝ) < u + 1 := by linarith
  have hcontγ : Continuous fun s : ℝ => w + (s : ℂ) * (z - w) := by fun_prop
  have hcontd : Continuous fun s : ℝ => dist (w + (s : ℂ) * (z - w)) p :=
    hcontγ.dist continuous_const
  have hcont : ContinuousOn (fun s : ℝ => dist (w + (s : ℂ) * (z - w)) p ^ u) (Icc 0 1) :=
    hcontd.continuousOn.rpow_const fun s hs =>
      Or.inl (fun h => hne s hs (by rwa [dist_eq_zero] at h))
  rcases eq_or_ne z w with rfl | hzw
  · rw [sub_self, norm_zero, mul_zero, Real.zero_rpow hu1.ne', mul_zero]
  have hL : (0 : ℝ) < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hzw)
  obtain ⟨c, hc, hclamp⟩ := exists_mem_Icc_mul_abs_sub_le_dist p z w
  have hi1 : IntervalIntegrable (fun s : ℝ => dist (w + (s : ℂ) * (z - w)) p ^ u) volume 0 c :=
    (hcont.mono (by rw [uIcc_of_le hc.1]; exact Icc_subset_Icc le_rfl hc.2)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s : ℝ => dist (w + (s : ℂ) * (z - w)) p ^ u) volume c 1 :=
    (hcont.mono (by rw [uIcc_of_le hc.2]; exact Icc_subset_Icc hc.1 le_rfl)).intervalIntegrable
  have hae : ∀ (b : ℝ), ∀ᵐ s ∂(volume.restrict (Icc c b)), s ≠ c := by
    intro b
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp
  have hae' : ∀ (b : ℝ), ∀ᵐ s ∂(volume.restrict (Icc b c)), s ≠ c := by
    intro b
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp
  -- the piece to the right of the foot of the perpendicular
  have hb2 : (∫ s in c..(1 : ℝ), dist (w + (s : ℂ) * (z - w)) p ^ u)
      ≤ ‖z - w‖ ^ u * ((1 - c) ^ (u + 1) / (u + 1)) := by
    have hint2 : IntervalIntegrable
        (fun s : ℝ => ‖z - w‖ ^ u * (s - c) ^ u) volume c 1 := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 - c) hu).comp_sub_right
        c
      simpa using h.const_mul (‖z - w‖ ^ u)
    have hmono := intervalIntegral.integral_mono_ae_restrict hc.2 hi2 hint2 ?_
    · refine hmono.trans_eq ?_
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ u) c, sub_self,
        integral_rpow (Or.inl hu), Real.zero_rpow hu1.ne']
      ring
    · filter_upwards [hae 1, self_mem_ae_restrict (measurableSet_Icc (a := c) (b := 1))]
        with s hsne hsmem
      have hcs : c < s := lt_of_le_of_ne hsmem.1 (Ne.symm hsne)
      have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hc.1.trans hsmem.1, hsmem.2⟩
      have hpos : 0 < ‖z - w‖ * (s - c) := by positivity
      have hle : ‖z - w‖ * (s - c) ≤ dist (w + (s : ℂ) * (z - w)) p := by
        have := hclamp s hs01
        rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - c)] at this
      calc dist (w + (s : ℂ) * (z - w)) p ^ u ≤ (‖z - w‖ * (s - c)) ^ u :=
            Real.rpow_le_rpow_of_nonpos hpos hle hu0
        _ = ‖z - w‖ ^ u * (s - c) ^ u :=
            Real.mul_rpow (norm_nonneg _) (by linarith)
  -- the piece to the left of the foot of the perpendicular
  have hb1 : (∫ s in (0 : ℝ)..c, dist (w + (s : ℂ) * (z - w)) p ^ u)
      ≤ ‖z - w‖ ^ u * (c ^ (u + 1) / (u + 1)) := by
    have hint1 : IntervalIntegrable
        (fun s : ℝ => ‖z - w‖ ^ u * (c - s) ^ u) volume 0 c := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) hu).comp_sub_left c
      simpa using (h.const_mul (‖z - w‖ ^ u)).symm
    have hmono := intervalIntegral.integral_mono_ae_restrict hc.1 hi1 hint1 ?_
    · refine hmono.trans_eq ?_
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ u) c, sub_self, sub_zero,
        integral_rpow (Or.inl hu), Real.zero_rpow hu1.ne']
      ring
    · filter_upwards [hae' 0, self_mem_ae_restrict (measurableSet_Icc (a := 0) (b := c))]
        with s hsne hsmem
      have hsc : s < c := lt_of_le_of_ne hsmem.2 hsne
      have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hsmem.1, hsmem.2.trans hc.2⟩
      have hpos : 0 < ‖z - w‖ * (c - s) := by positivity
      have hle : ‖z - w‖ * (c - s) ≤ dist (w + (s : ℂ) * (z - w)) p := by
        have := hclamp s hs01
        rwa [abs_of_nonpos (by linarith : s - c ≤ (0 : ℝ)), neg_sub] at this
      calc dist (w + (s : ℂ) * (z - w)) p ^ u ≤ (‖z - w‖ * (c - s)) ^ u :=
            Real.rpow_le_rpow_of_nonpos hpos hle hu0
        _ = ‖z - w‖ ^ u * (c - s) ^ u :=
            Real.mul_rpow (norm_nonneg _) (by linarith)
  have hsplit : (∫ s in (0 : ℝ)..1, dist (w + (s : ℂ) * (z - w)) p ^ u)
      = (∫ s in (0 : ℝ)..c, dist (w + (s : ℂ) * (z - w)) p ^ u)
        + ∫ s in c..(1 : ℝ), dist (w + (s : ℂ) * (z - w)) p ^ u :=
    (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  have hc1 : c ^ (u + 1) ≤ 1 := Real.rpow_le_one hc.1 hc.2 hu1.le
  have hc2 : (1 - c) ^ (u + 1) ≤ 1 :=
    Real.rpow_le_one (by linarith [hc.2]) (by linarith [hc.1]) hu1.le
  have hbound : (∫ s in (0 : ℝ)..1, dist (w + (s : ℂ) * (z - w)) p ^ u)
      ≤ ‖z - w‖ ^ u * (2 / (u + 1)) := by
    rw [hsplit]
    have hnn : (0 : ℝ) ≤ ‖z - w‖ ^ u := Real.rpow_nonneg (norm_nonneg _) u
    calc _ ≤ ‖z - w‖ ^ u * (c ^ (u + 1) / (u + 1))
            + ‖z - w‖ ^ u * ((1 - c) ^ (u + 1) / (u + 1)) := add_le_add hb1 hb2
      _ ≤ ‖z - w‖ ^ u * (1 / (u + 1)) + ‖z - w‖ ^ u * (1 / (u + 1)) := by
          gcongr
      _ = ‖z - w‖ ^ u * (2 / (u + 1)) := by ring
  calc (∫ s in (0 : ℝ)..1, dist (w + (s : ℂ) * (z - w)) p ^ u) * ‖z - w‖
      ≤ ‖z - w‖ ^ u * (2 / (u + 1)) * ‖z - w‖ :=
        mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    _ = 2 / (u + 1) * ‖z - w‖ ^ (u + 1) := by
        rw [Real.rpow_add hL, Real.rpow_one]
        ring

/-- Every real point is in the closure of the open upper half-plane, so limits along the
half-plane at a real point are well posed. -/
theorem neBot_nhdsWithin_upperHalfPlaneSet (x : ℝ) :
    (𝓝[upperHalfPlaneSet] ((x : ℂ))).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (by simp [upperHalfPlaneSet])

/-! ### The local bound at a prevertex -/

/-- Near a real prevertex `p`, the Schwarz--Christoffel integrand is dominated by a constant
multiple of `dist z p ^ t`, where `t = ∑ i ∈ s, e i` is the total turning exponent carried by the
indices `s` sitting at `p`.  The prevertex itself is excluded because both sides are totalized
there and carry no analytic information. -/
theorem exists_norm_schwarzChristoffelIntegrand_le (a e : ι → ℝ) (p : ℝ) {s : Finset ι}
    (hs : ∀ i, i ∈ s ↔ a i = p) :
    ∃ C > 0, ∀ᶠ z in 𝓝[≠] ((p : ℂ)), ‖schwarzChristoffelIntegrand a e z‖
      ≤ C * dist z (p : ℂ) ^ ∑ i ∈ s, e i := by
  classical
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
    exact Finset.prod_congr rfl fun i hi => by rw [show a i = p from (hs i).mp hi]
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
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => schwarzChristoffelPrimitive a e z₀ (w + (s : ℂ) * (z - w)))
        ((z - w) * schwarzChristoffelIntegrand a e (w + (s : ℂ) * (z - w))) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h1 : HasDerivAt (fun s : ℝ => w + (s : ℂ) * (z - w)) (z - w) s := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (z - w)).const_add w
    have h2 := hasDerivAt_schwarzChristoffelPrimitive a e z₀ (hmem s hs).2
    simpa [Function.comp_def, smul_eq_mul] using h2.scomp s h1
  have hcontint : ContinuousOn
      (fun s : ℝ => schwarzChristoffelIntegrand a e (w + (s : ℂ) * (z - w))) (Icc 0 1) :=
    ((differentiableOn_schwarzChristoffelIntegrand a e).continuousOn).comp
      hγcont.continuousOn fun s hs => (hmem s hs).2
  have hint : IntervalIntegrable
      (fun s : ℝ => (z - w) * schwarzChristoffelIntegrand a e (w + (s : ℂ) * (z - w)))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul hcontint
  have hFTC : schwarzChristoffelPrimitive a e z₀ z - schwarzChristoffelPrimitive a e z₀ w
      = ∫ s in (0 : ℝ)..1,
          (z - w) * schwarzChristoffelIntegrand a e (w + (s : ℂ) * (z - w)) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    norm_num
  have hi1 : IntervalIntegrable
      (fun s : ℝ => ‖schwarzChristoffelIntegrand a e (w + (s : ℂ) * (z - w))‖) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact hcontint.norm
  have hi2 : IntervalIntegrable
      (fun s : ℝ => C * dist (w + (s : ℂ) * (z - w)) p ^ u) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul
      ((hγcont.dist continuous_const).continuousOn.rpow_const fun s hs =>
        Or.inl fun h => hne s hs (by rwa [dist_eq_zero] at h))
  have hcmp : (∫ s in (0 : ℝ)..1, ‖schwarzChristoffelIntegrand a e (w + (s : ℂ) * (z - w))‖)
      ≤ C * ∫ s in (0 : ℝ)..1, dist (w + (s : ℂ) * (z - w)) p ^ u := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on zero_le_one hi1 hi2 fun s hs => hbd _ (hmem s hs)
  rw [dist_eq_norm, hFTC]
  calc ‖∫ s in (0 : ℝ)..1, (z - w) * schwarzChristoffelIntegrand a e (w + (s : ℂ) * (z - w))‖
      ≤ ∫ s in (0 : ℝ)..1, ‖(z - w) * schwarzChristoffelIntegrand a e (w + (s : ℂ) * (z - w))‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ = ‖z - w‖ * ∫ s in (0 : ℝ)..1,
          ‖schwarzChristoffelIntegrand a e (w + (s : ℂ) * (z - w))‖ := by
        simp_rw [norm_mul]
        rw [intervalIntegral.integral_const_mul]
    _ ≤ ‖z - w‖ * (C * ∫ s in (0 : ℝ)..1, dist (w + (s : ℂ) * (z - w)) p ^ u) :=
        mul_le_mul_of_nonneg_left hcmp (norm_nonneg _)
    _ = C * ((∫ s in (0 : ℝ)..1, dist (w + (s : ℂ) * (z - w)) p ^ u) * ‖z - w‖) := by ring
    _ ≤ C * (2 / (u + 1) * ‖z - w‖ ^ (u + 1)) :=
        mul_le_mul_of_nonneg_left (integral_dist_rpow_segment_le hu hu0 hne) hC
    _ = C * (2 / (u + 1)) * ‖z - w‖ ^ (u + 1) := by ring

/-! ### Existence of the vertex -/

/-- The **Schwarz--Christoffel primitive converges at a prevertex** whose total turning exponent
exceeds `-1`.  The indices sitting at the prevertex `a j` are collected in `s`, so that for a
family of pairwise distinct prevertices `s = {j}` and the hypothesis reads `-1 < e j`; for the
classical exponents `e i = α i / π - 1` attached to interior angles `α i ∈ (0, 2 π)` it always
holds.  The limit is the polygon vertex the map produces at `a j`. -/
theorem exists_tendsto_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane) (j : ι)
    {s : Finset ι} (hs : ∀ i, i ∈ s ↔ a i = a j) (he : -1 < ∑ i ∈ s, e i) :
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
  set u : ℝ := min (∑ i ∈ s, e i) 0 with hudef
  have hu : -1 < u := lt_min he (by norm_num)
  have hu0 : u ≤ 0 := min_le_right _ _
  have hu1 : (0 : ℝ) < u + 1 := by linarith
  obtain ⟨C, hC, hev⟩ := exists_norm_schwarzChristoffelIntegrand_le a e (a j) hs
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
    have h1 : ‖schwarzChristoffelIntegrand a e y‖ ≤ C * dist y p ^ ∑ i ∈ s, e i := by
      refine hr₁sub ⟨?_, hyne⟩
      exact Metric.mem_ball.mp hy.1 |>.trans_le (min_le_left _ _) |> Metric.mem_ball.mpr
    have h2 : dist y p ^ (∑ i ∈ s, e i) ≤ dist y p ^ u := by
      rw [show (∑ i ∈ s, e i) = ((∑ i ∈ s, e i) - u) + u by ring, Real.rpow_add hd]
      have hle1 : dist y p ^ ((∑ i ∈ s, e i) - u) ≤ 1 :=
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
`a j` of the primitive normalized at `z₀`.  It is a genuine limit exactly under the hypotheses of
`TauCeti.exists_tendsto_schwarzChristoffelPrimitive`. -/
def schwarzChristoffelVertex (a e : ι → ℝ) (z₀ : UpperHalfPlane) (j : ι) : ℂ :=
  limUnder (𝓝[upperHalfPlaneSet] ((a j : ℂ))) (schwarzChristoffelPrimitive a e z₀)

/-- The Schwarz--Christoffel primitive converges to `schwarzChristoffelVertex` at the
prevertex. -/
theorem tendsto_schwarzChristoffelVertex (a e : ι → ℝ) (z₀ : UpperHalfPlane) (j : ι)
    {s : Finset ι} (hs : ∀ i, i ∈ s ↔ a i = a j) (he : -1 < ∑ i ∈ s, e i) :
    Tendsto (schwarzChristoffelPrimitive a e z₀) (𝓝[upperHalfPlaneSet] ((a j : ℂ)))
      (𝓝 (schwarzChristoffelVertex a e z₀ j)) := by
  have := neBot_nhdsWithin_upperHalfPlaneSet (a j)
  obtain ⟨v, hv⟩ := exists_tendsto_schwarzChristoffelPrimitive a e z₀ j hs he
  rwa [schwarzChristoffelVertex, hv.limUnder_eq]

/-- Changing the base point translates every Schwarz--Christoffel vertex by the same constant, so
the polygon it spans is determined up to translation. -/
theorem schwarzChristoffelVertex_change_base (a e : ι → ℝ) (b c : UpperHalfPlane) (j : ι)
    {s : Finset ι} (hs : ∀ i, i ∈ s ↔ a i = a j) (he : -1 < ∑ i ∈ s, e i) :
    schwarzChristoffelVertex a e b j
      = schwarzChristoffelVertex a e c j - schwarzChristoffelPrimitive a e c b := by
  have := neBot_nhdsWithin_upperHalfPlaneSet (a j)
  refine tendsto_nhds_unique (tendsto_schwarzChristoffelVertex a e b j hs he) ?_
  refine Tendsto.congr' ?_
    ((tendsto_schwarzChristoffelVertex a e c j hs he).sub tendsto_const_nhds)
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (schwarzChristoffelPrimitive_change_base a e b c hz).symm

end TauCeti
