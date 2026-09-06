/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive

/-!
# Straight image edges of the Schwarz--Christoffel map

The Schwarz--Christoffel map is the primitive on the upper half-plane of the product
`∏ i, (z - a i) ^ (e i)` of principal powers with real prevertices `a i`.  This file proves the
step that makes its image a polygon: on a real interval containing no prevertex, the map extends
continuously and its boundary values run along a straight line, in the direction
`exp (i π ∑_{a i > x} e i)`.

The obstacle is that the principal power is cut along the negative reals, so the integrand itself
is discontinuous across the part of the real axis to the left of a prevertex.  It is only the
branch that is wrong: replacing the factor `(z - a i) ^ (e i)` by `(a i - z) ^ (e i)` for every
prevertex lying to the right of a reference point `c` produces
`schwarzChristoffelContinuedIntegrand`, which differs from the integrand on the upper half-plane
by the unimodular constant `exp (i · schwarzChristoffelEdgeAngle a e c)` and, when `c` is taken to
be the left endpoint of a prevertex-free interval, is holomorphic on the whole vertical strip that
interval cuts out.  On the interval itself it is real and positive, since every factor is then a
positive real raised to a real power.

Integrating the continued integrand over the disc whose diameter is the interval — a disc which
lies in the strip, so Morera's theorem for a disc supplies a primitive there — gives a holomorphic
function agreeing with the Schwarz--Christoffel primitive up to an additive constant on the upper
half of the disc.  Its restriction to the interval is therefore the continuous boundary extension,
and the fundamental theorem of calculus writes an increment of it as a real multiple of the
direction constant.  That is the straight edge.

The turning of the direction at a prevertex is `schwarzChristoffelEdgeAngle_sub`: passing a
prevertex `a i` rotates the edge direction by `-π · e i`, which for the classical choice
`e i = α i / π - 1` is the exterior angle `π - α i` of a polygon with interior angle `α i`.

## Main definitions

* `TauCeti.schwarzChristoffelContinuedIntegrand` -- the Schwarz--Christoffel integrand with the
  branch of every factor to the right of a reference point reflected, so that, as long as no
  prevertex equals that point, it continues holomorphically across the real axis near it.
* `TauCeti.schwarzChristoffelEdgeAngle` -- the argument `π ∑_{a i > c} e i` of the resulting
  edge direction.

## Main results

* `TauCeti.schwarzChristoffelIntegrand_eq_exp_mul_continued` -- on the upper half-plane the
  integrand is the continued integrand times the unimodular edge-direction constant.
* `TauCeti.schwarzChristoffelContinuedIntegrand_ofReal` -- on a prevertex-free real interval the
  continued integrand is the positive real `∏ i, |x - a i| ^ e i`.
* `TauCeti.tendsto_schwarzChristoffelIntegrand_nhdsWithin` -- the boundary value of the integrand
  at a point of such an interval, whose argument is the edge angle.
* `TauCeti.exists_tendsto_schwarzChristoffelPrimitive_sub_eq` -- the Schwarz--Christoffel map
  extends continuously to a prevertex-free real interval, and an increment of the extension is a
  real multiple of the edge direction.
* `TauCeti.exists_tendsto_schwarzChristoffelPrimitive_injOn_collinear` -- consequently the
  interval is carried injectively onto a collinear set: the edge runs along a straight line.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

namespace TauCeti

open Complex Filter MeasureTheory Set Topology UpperHalfPlane

variable {ι : Type*} [Fintype ι]

/-- The **Schwarz--Christoffel integrand continued across a reference point** `c`.

Each factor `(z - a i) ^ (e i)` of `schwarzChristoffelIntegrand` whose prevertex `a i` lies to the
right of `c` is replaced by `(a i - z) ^ (e i)`, moving its branch cut from the real half-line to
the left of `a i` to the one to the right.  Provided no prevertex equals `c`, all the cuts then
avoid a neighbourhood of `c` in the real axis, so the product continues holomorphically across it
(`differentiableAt_schwarzChristoffelContinuedIntegrand`), while on the upper half-plane it still
agrees with the integrand up to the unimodular constant of
`schwarzChristoffelIntegrand_eq_exp_mul_continued`. -/
def schwarzChristoffelContinuedIntegrand (a e : ι → ℝ) (c : ℝ) (z : ℂ) : ℂ :=
  ∏ i, (if a i ≤ c then z - (a i : ℂ) else (a i : ℂ) - z) ^ (e i : ℂ)

/-- The **Schwarz--Christoffel edge angle** at a reference point `c`: the argument `π ∑_{a i > c}
e i` of the direction in which the map runs along the image of the boundary interval containing
`c`. -/
def schwarzChristoffelEdgeAngle (a e : ι → ℝ) (c : ℝ) : ℝ :=
  Real.pi * ∑ i, if c < a i then e i else 0

/-- The continued Schwarz--Christoffel integrand is the product of its reflected principal-power
factors. -/
theorem schwarzChristoffelContinuedIntegrand_def (a e : ι → ℝ) (c : ℝ) (z : ℂ) :
    schwarzChristoffelContinuedIntegrand a e c z =
      ∏ i, (if a i ≤ c then z - (a i : ℂ) else (a i : ℂ) - z) ^ (e i : ℂ) :=
  (rfl)

/-- The Schwarz--Christoffel edge angle as a sum over the prevertices to the right of the
reference point. -/
theorem schwarzChristoffelEdgeAngle_eq_sum_filter (a e : ι → ℝ) (c : ℝ) :
    schwarzChristoffelEdgeAngle a e c =
      Real.pi * ∑ i ∈ Finset.univ.filter fun i => c < a i, e i := by
  rw [schwarzChristoffelEdgeAngle, Finset.sum_filter]

/-- The edge angle drops, as the reference point moves to the right past a set of prevertices, by
`π` times the total of their exponents.  For the classical choice `e i = α i / π - 1` attached to a
polygon with interior angle `α i`, passing a single prevertex therefore turns the edge direction by
`-π * e i = π - α i`, the exterior angle at that vertex. -/
theorem schwarzChristoffelEdgeAngle_sub (a e : ι → ℝ) {c d : ℝ} (hcd : c ≤ d) :
    schwarzChristoffelEdgeAngle a e c - schwarzChristoffelEdgeAngle a e d =
      Real.pi * ∑ i ∈ Finset.univ.filter fun i => a i ∈ Ioc c d, e i := by
  rw [schwarzChristoffelEdgeAngle, schwarzChristoffelEdgeAngle, ← mul_sub, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases le_or_gt (a i) c with h₁ | h₁
  · simp [not_lt.mpr h₁, not_lt.mpr (h₁.trans hcd), Set.mem_Ioc]
  · rcases le_or_gt (a i) d with h₂ | h₂
    · simp [h₁, not_lt.mpr h₂, Set.mem_Ioc, h₂]
    · simp [h₁, h₂, Set.mem_Ioc, not_le.mpr h₂]

/-- On the upper half-plane the Schwarz--Christoffel integrand is its continuation across any real
reference point, times the unimodular constant with argument the edge angle there. -/
theorem schwarzChristoffelIntegrand_eq_exp_mul_continued (a e : ι → ℝ) (c : ℝ) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelIntegrand a e z =
      Complex.exp (schwarzChristoffelEdgeAngle a e c * Complex.I) *
        schwarzChristoffelContinuedIntegrand a e c z := by
  have hz' : 0 < z.im := hz
  have hfac : ∀ i : ι, (z - (a i : ℂ)) ^ (e i : ℂ) =
      Complex.exp (if c < a i then (Real.pi : ℂ) * (e i : ℂ) * Complex.I else 0) *
        (if a i ≤ c then z - (a i : ℂ) else (a i : ℂ) - z) ^ (e i : ℂ) := by
    intro i
    by_cases h : a i ≤ c
    · rw [ite_eq_right (not_lt.mpr h), ite_eq_left h, Complex.exp_zero, one_mul]
    · rw [ite_eq_left (lt_of_not_ge h), ite_eq_right h]
      exact sub_cpow_eq_exp_mul_sub_cpow_of_im_pos hz' (a i) (e i : ℂ)
  rw [schwarzChristoffelIntegrand_def, schwarzChristoffelContinuedIntegrand_def,
    Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  rw [schwarzChristoffelEdgeAngle]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by split <;> simp

/-- The continued Schwarz--Christoffel integrand is holomorphic at any point strictly to the right
of every prevertex not to the right of the reference point, and strictly to the left of every
prevertex that is. -/
theorem differentiableAt_schwarzChristoffelContinuedIntegrand (a e : ι → ℝ) {c : ℝ} {z : ℂ}
    (hlo : ∀ i, a i ≤ c → a i < z.re) (hhi : ∀ i, c < a i → z.re < a i) :
    DifferentiableAt ℂ (schwarzChristoffelContinuedIntegrand a e c) z := by
  have hfun : schwarzChristoffelContinuedIntegrand a e c =
      fun w : ℂ => ∏ i, (if a i ≤ c then w - (a i : ℂ) else (a i : ℂ) - w) ^ (e i : ℂ) :=
    funext (schwarzChristoffelContinuedIntegrand_def a e c)
  rw [hfun]
  refine DifferentiableAt.fun_finsetProd fun i _ => ?_
  by_cases h : a i ≤ c
  · simp only [ite_eq_left h]
    refine (differentiableAt_id.sub_const _).cpow_const (mem_slitPlane_iff.mpr (Or.inl ?_))
    simpa using sub_pos.mpr (hlo i h)
  · simp only [ite_eq_right h]
    refine ((differentiableAt_const _).sub differentiableAt_id).cpow_const
      (mem_slitPlane_iff.mpr (Or.inl ?_))
    simpa using sub_pos.mpr (hhi i (lt_of_not_ge h))

/-- The Schwarz--Christoffel integrand continued across the left endpoint of a prevertex-free
interval is holomorphic on the whole vertical strip over that interval. -/
theorem differentiableOn_schwarzChristoffelContinuedIntegrand (a e : ι → ℝ) {p q : ℝ}
    (ha : ∀ i, a i ∉ Ioo p q) :
    DifferentiableOn ℂ (schwarzChristoffelContinuedIntegrand a e p) {z : ℂ | z.re ∈ Ioo p q} := by
  intro z hz
  refine (differentiableAt_schwarzChristoffelContinuedIntegrand a e (fun i hi => ?_)
    fun i hi => ?_).differentiableWithinAt
  · exact hi.trans_lt hz.1
  · exact hz.2.trans_le (not_lt.mp fun h => ha i ⟨hi, h⟩)

/-- On a prevertex-free real interval the continued Schwarz--Christoffel integrand takes the
positive real value `∏ i, |x - a i| ^ e i`: every factor is a positive real raised to a real
power. -/
theorem schwarzChristoffelContinuedIntegrand_ofReal (a e : ι → ℝ) {c x : ℝ}
    (hlo : ∀ i, a i ≤ c → a i < x) (hhi : ∀ i, c < a i → x < a i) :
    schwarzChristoffelContinuedIntegrand a e c (x : ℂ) = ((∏ i, |x - a i| ^ e i : ℝ) : ℂ) := by
  rw [schwarzChristoffelContinuedIntegrand_def, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : a i ≤ c
  · have hx : 0 < x - a i := sub_pos.mpr (hlo i h)
    have hcast : (x : ℂ) - (a i : ℂ) = ((x - a i : ℝ) : ℂ) := by push_cast; ring
    rw [ite_eq_left h, hcast, ← Complex.ofReal_cpow hx.le, abs_of_pos hx]
  · have hx : 0 < a i - x := sub_pos.mpr (hhi i (lt_of_not_ge h))
    have hcast : (a i : ℂ) - (x : ℂ) = ((a i - x : ℝ) : ℂ) := by push_cast; ring
    rw [ite_eq_right h, hcast, ← Complex.ofReal_cpow hx.le, abs_sub_comm, abs_of_pos hx]

/-- The **boundary value of the Schwarz--Christoffel integrand** at a point of a prevertex-free
real interval: approaching from the upper half-plane, the integrand tends to the positive real
`∏ i, |x - a i| ^ e i` rotated by the edge angle.  In particular its argument is constant along
the interval. -/
theorem tendsto_schwarzChristoffelIntegrand_nhdsWithin (a e : ι → ℝ) {p q x : ℝ}
    (ha : ∀ i, a i ∉ Ioo p q) (hx : x ∈ Ioo p q) :
    Tendsto (schwarzChristoffelIntegrand a e) (𝓝[upperHalfPlaneSet] (x : ℂ))
      (𝓝 (Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) *
        ((∏ i, |x - a i| ^ e i : ℝ) : ℂ))) := by
  have hstrip : IsOpen {z : ℂ | z.re ∈ Ioo p q} :=
    isOpen_Ioo.preimage Complex.continuous_re
  have hmem : (x : ℂ) ∈ {z : ℂ | z.re ∈ Ioo p q} := by simpa using hx
  have hval : schwarzChristoffelContinuedIntegrand a e p (x : ℂ) =
      ((∏ i, |x - a i| ^ e i : ℝ) : ℂ) :=
    schwarzChristoffelContinuedIntegrand_ofReal a e (fun i hi => hi.trans_lt hx.1)
      fun i hi => hx.2.trans_le (not_lt.mp fun h => ha i ⟨hi, h⟩)
  have hcont : ContinuousAt (schwarzChristoffelContinuedIntegrand a e p) (x : ℂ) :=
    ((differentiableOn_schwarzChristoffelContinuedIntegrand a e ha _ hmem).differentiableAt
      (hstrip.mem_nhds hmem)).continuousAt
  have hlim : Tendsto (fun z : ℂ => Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) *
      schwarzChristoffelContinuedIntegrand a e p z) (𝓝[upperHalfPlaneSet] (x : ℂ))
      (𝓝 (Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) *
        ((∏ i, |x - a i| ^ e i : ℝ) : ℂ))) := by
    rw [← hval]
    exact (tendsto_const_nhds.mul hcont.tendsto).mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (schwarzChristoffelIntegrand_eq_exp_mul_continued a e p hz).symm

/-- **The Schwarz--Christoffel map has straight image edges.**  Let the prevertices `a` avoid the
real interval `Ioo p q`.  Then the Schwarz--Christoffel primitive extends continuously from the
upper half-plane to that interval, and any increment of the extension along it is a real multiple
of the unimodular direction with argument `schwarzChristoffelEdgeAngle a e p`.  The image of the
interval is therefore contained in a line with that direction; see
`exists_tendsto_schwarzChristoffelPrimitive_injOn_collinear`. -/
theorem exists_tendsto_schwarzChristoffelPrimitive_sub_eq (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (ha : ∀ i, a i ∉ Ioo p q) :
    ∃ L : ℝ → ℂ,
      (∀ x ∈ Ioo p q, Tendsto (schwarzChristoffelPrimitive a e z₀)
        (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 (L x))) ∧
      ∀ x ∈ Ioo p q, ∀ y ∈ Ioo p q,
        L x - L y = ((∫ t in y..x, ∏ i, |t - a i| ^ e i : ℝ) : ℂ) *
          Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) := by
  set C : ℂ := Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I)
  set g : ℂ → ℂ := fun z => C * schwarzChristoffelContinuedIntegrand a e p z with hg
  have hUre : ∀ z ∈ Metric.ball (((p + q) / 2 : ℝ) : ℂ) ((q - p) / 2), z.re ∈ Ioo p q := by
    intro z hz
    have hnorm : ‖z - (((p + q) / 2 : ℝ) : ℂ)‖ < (q - p) / 2 := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hz
    have h := (Complex.abs_re_le_norm (z - (((p + q) / 2 : ℝ) : ℂ))).trans_lt hnorm
    rw [Complex.sub_re, Complex.ofReal_re, abs_lt] at h
    constructor <;> linarith [h.1, h.2]
  have hUmem : ∀ x ∈ Ioo p q, ((x : ℂ)) ∈ Metric.ball (((p + q) / 2 : ℝ) : ℂ) ((q - p) / 2) := by
    intro x hx
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_lt]
    constructor <;> [linarith [hx.1]; linarith [hx.2]]
  have hgdiff : DifferentiableOn ℂ g (Metric.ball (((p + q) / 2 : ℝ) : ℂ) ((q - p) / 2)) :=
    fun z hz => ((differentiableOn_schwarzChristoffelContinuedIntegrand a e ha z
      (hUre z hz)).differentiableAt ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
        (hUre z hz))).const_mul C |>.differentiableWithinAt
  obtain ⟨P, hP⟩ := hgdiff.isExactOn_ball
  set V := Metric.ball (((p + q) / 2 : ℝ) : ℂ) ((q - p) / 2) ∩ upperHalfPlaneSet
  have hVopen : IsOpen V := Metric.isOpen_ball.inter isOpen_upperHalfPlaneSet
  have hVpre : IsPreconnected V :=
    ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hFd : ∀ z ∈ V, HasDerivAt (schwarzChristoffelPrimitive a e z₀) (g z) z := by
    intro z hz
    have h := hasDerivAt_schwarzChristoffelPrimitive a e z₀ hz.2
    rwa [schwarzChristoffelIntegrand_eq_exp_mul_continued a e p hz.2] at h
  have hPd : ∀ z ∈ V, HasDerivAt P (g z) z := fun z hz => hP z hz.1
  obtain ⟨k, hk⟩ := hVopen.exists_eq_add_of_deriv_eq hVpre
    (fun z hz => (hFd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hPd z hz).differentiableAt.differentiableWithinAt)
    fun z hz => by rw [(hFd z hz).deriv, (hPd z hz).deriv]
  refine ⟨fun x => P (x : ℂ) + k, fun x hx => ?_, fun x hx y hy => ?_⟩
  · have hxU := hUmem x hx
    refine Tendsto.congr' ?_
      (((hP _ hxU).differentiableAt.continuousAt.tendsto.add tendsto_const_nhds).mono_left
        nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hxU)] with z hz₁ hz₂
    exact (hk ⟨hz₂, hz₁⟩).symm
  · have hsub : uIcc y x ⊆ Ioo p q := (Set.ordConnected_Ioo).uIcc_subset hy hx
    have hderiv : ∀ t ∈ uIcc y x, HasDerivAt (fun s : ℝ => P (s : ℂ)) (g (t : ℂ)) t :=
      fun t ht => (hP _ (hUmem t (hsub ht))).comp_ofReal
    have hgcont : ContinuousOn (fun t : ℝ => g (t : ℂ)) (uIcc y x) := by
      have := hgdiff.continuousOn.comp Complex.continuous_ofReal.continuousOn
        fun t ht => hUmem t (hsub ht)
      simpa [Function.comp_def] using this
    have hint : IntervalIntegrable (fun t : ℝ => g (t : ℂ)) volume y x :=
      hgcont.intervalIntegrable
    have hval : EqOn (fun t : ℝ => g (t : ℂ))
        (fun t : ℝ => ((∏ i, |t - a i| ^ e i : ℝ) : ℂ) * C) (uIcc y x) := by
      intro t ht
      have h := schwarzChristoffelContinuedIntegrand_ofReal a e (c := p)
        (fun i hi => hi.trans_lt (hsub ht).1)
        fun i hi => (hsub ht).2.trans_le (not_lt.mp fun h => ha i ⟨hi, h⟩)
      simp only [hg, h]
      ring
    calc P (x : ℂ) + k - (P (y : ℂ) + k) = ∫ t in y..x, g (t : ℂ) := by
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]; ring
      _ = ∫ t in y..x, ((∏ i, |t - a i| ^ e i : ℝ) : ℂ) * C := intervalIntegral.integral_congr hval
      _ = (∫ t in y..x, ((∏ i, |t - a i| ^ e i : ℝ) : ℂ)) * C :=
          intervalIntegral.integral_mul_const _ _
      _ = ((∫ t in y..x, ∏ i, |t - a i| ^ e i : ℝ) : ℂ) * C := by
          rw [intervalIntegral.integral_ofReal]

/-- **The Schwarz--Christoffel map carries a prevertex-free boundary interval injectively into a
line.**  The boundary values of the map along such an interval are collinear, and distinct points
of the interval have distinct boundary values, so the interval is carried injectively onto a subset
of a line — an edge of the image polygon. -/
theorem exists_tendsto_schwarzChristoffelPrimitive_injOn_collinear (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ} (ha : ∀ i, a i ∉ Ioo p q) :
    ∃ L : ℝ → ℂ,
      (∀ x ∈ Ioo p q, Tendsto (schwarzChristoffelPrimitive a e z₀)
        (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 (L x))) ∧
      InjOn L (Ioo p q) ∧ Collinear ℝ (L '' Ioo p q) := by
  obtain ⟨L, hL, hdiff⟩ := exists_tendsto_schwarzChristoffelPrimitive_sub_eq a e z₀ ha
  have hne : ∀ t ∈ Ioo p q, ∀ i, t ≠ a i := fun t ht i h => ha i (h ▸ ht)
  have hfcont : ContinuousOn (fun t : ℝ => ∏ i, |t - a i| ^ e i) (Ioo p q) :=
    continuousOn_finsetProd _ fun i _ t ht =>
      (((continuous_id.sub continuous_const).abs.continuousAt).rpow_const
        (Or.inl (abs_ne_zero.mpr (sub_ne_zero_of_ne (hne t ht i))))).continuousWithinAt
  have hprodpos : ∀ t : ℝ, (∀ i, t ≠ a i) → 0 < ∏ i, |t - a i| ^ e i := fun t ht =>
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero_of_ne (ht i))) _
  have key : ∀ x ∈ Ioo p q, ∀ y ∈ Ioo p q, y < x → L x - L y ≠ 0 := by
    intro x hx y hy hyx
    rw [hdiff x hx y hy]
    have hsub' : uIcc y x ⊆ Ioo p q := Set.ordConnected_Ioo.uIcc_subset hy hx
    have hpos : 0 < ∫ t in y..x, ∏ i, |t - a i| ^ e i :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hfcont.mono hsub').intervalIntegrable
        (fun t ht => hprodpos t
          (hne t (hsub' (Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self ht))))) hyx
    exact mul_ne_zero (mod_cast hpos.ne') (Complex.exp_ne_zero _)
  have hinj : InjOn L (Ioo p q) := by
    intro x hx y hy hxy
    rcases lt_trichotomy x y with h | h | h
    · exact absurd (by simp [hxy]) (key y hy x hx h)
    · exact h
    · exact absurd (by simp [hxy]) (key x hx y hy h)
  refine ⟨L, hL, hinj, ?_⟩
  rcases (Ioo p q).eq_empty_or_nonempty with hempty | ⟨m, hm⟩
  · rw [hempty, Set.image_empty]
    exact collinear_empty ℝ ℂ
  refine (collinear_iff_of_mem (Set.mem_image_of_mem L hm)).mpr
    ⟨Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I), ?_⟩
  rintro - ⟨x, hx, rfl⟩
  refine ⟨∫ t in m..x, ∏ i, |t - a i| ^ e i, ?_⟩
  have := hdiff x hx _ hm
  simp only [Complex.real_smul, vadd_eq_add]
  linear_combination this

end TauCeti
