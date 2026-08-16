/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.Analysis.Contour.PiecewiseC1On
public import Mathlib.Analysis.Convex.Segment
import TauCeti.Analysis.Contour.Winding.UnboundedComponent
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.Compact

/-!
# Proximity invariance of the winding number

Two closed curves that stay closer to each other than the first one stays to `w` have the same
winding number about `w`. This is the "dog on a leash" principle: the leash from `γ₀ t` to `γ₁ t`
is too short to reach `w`, so the two walks encircle `w` the same number of times.

The proof compares the two curves through the quotient `σ t = (γ₁ t - w) / (γ₀ t - w)`. The
hypothesis says exactly that `‖σ t - 1‖ < 1`, so `σ` runs inside the open right half-plane; its own
winding number about `0` therefore vanishes, because the closed left half-plane is an unbounded
connected subset of the complement of its image. Since the index integrands satisfy
`σ' / σ = γ₁' / (γ₁ - w) - γ₀' / (γ₀ - w)` pointwise, that vanishing is the asserted equality.

The Layer 0 item this serves is homotopy invariance of the winding number off the curve. What was
already available (`Contour.windingNumber_eq_of_pathHomotopy`) needs a path homotopy whose
extension to the square is `C²`; the results here need no regularity of the homotopy whatsoever.
In particular `Contour.IsPiecewiseC1On.windingNumber_eq_of_notMem_segment` deduces invariance
along the straight-line homotopy `s ↦ (1 - s) • γ₀ + s • γ₁` from the purely geometric hypothesis
that the segment `[γ₀ t, γ₁ t]` misses `w` for every parameter `t`: the intermediate curves are
piecewise `C¹` because that predicate is stable under affine combinations, and a compactness
estimate lets finitely many of them be chained together by the leash lemma.

## Main results

* `Contour.windingNumber_eq_of_dist_lt_dist` — the raw-hypothesis form: closed curves that are
  continuous, differentiable off a countable set, and have interval-integrable derivatives, with
  `dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w` throughout, have equal winding numbers about `w`.
* `Contour.IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist` — the same for closed piecewise-`C¹`
  curves, whose regularity supplies the raw hypotheses on its own.
* `Contour.IsPiecewiseC1On.windingNumber_eq_of_notMem_segment` — invariance along the
  straight-line homotopy: if `w ∉ [γ₀ t, γ₁ t]` for every `t`, the winding numbers agree.

## Provenance

The comparison-quotient argument is the standard proof of the "dog on a leash" lemma (equivalently,
the homotopy form of Rouché's theorem); see the references in the Contour Integration roadmap,
e.g. L. Ahlfors, *Complex Analysis*, Ch. 4. No formal source is vendored.
-/

public section

noncomputable section

open Bornology MeasureTheory Set

namespace TauCeti.Contour

variable {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {w : ℂ}

/-- The comparison quotient `t ↦ (γ₁ t - w) / (γ₀ t - w)` of two curves relative to the point `w`.
The whole proximity argument is the observation that the leash hypothesis confines this quotient to
the disc of radius `1` about `1`. -/
private def compRatio (γ₀ γ₁ : ℝ → ℂ) (w : ℂ) : ℝ → ℂ := fun t => (γ₁ t - w) / (γ₀ t - w)

private theorem compRatio_apply (γ₀ γ₁ : ℝ → ℂ) (w : ℂ) (t : ℝ) :
    compRatio γ₀ γ₁ w t = (γ₁ t - w) / (γ₀ t - w) := rfl

/-- Under the leash hypothesis at `t`, the base curve misses `w` there. -/
private theorem ne_of_dist_lt_dist {t : ℝ} (h : dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w) :
    γ₀ t ≠ w := fun heq => absurd ((dist_eq_zero.mpr heq) ▸ h) (by simp [dist_nonneg])

/-- The leash hypothesis says exactly that the comparison quotient stays within distance `1`
of `1`. -/
private theorem dist_compRatio_one {t : ℝ} (h : dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w) :
    dist (compRatio γ₀ γ₁ w t) 1 < 1 := by
  have hne : γ₀ t - w ≠ 0 := sub_ne_zero.mpr (ne_of_dist_lt_dist h)
  have hsub : compRatio γ₀ γ₁ w t - 1 = (γ₁ t - γ₀ t) / (γ₀ t - w) := by
    rw [compRatio_apply]
    field_simp
    ring
  rw [dist_eq_norm, hsub, norm_div, div_lt_one (by positivity)]
  simpa [dist_eq_norm] using h

/-- The comparison quotient has positive real part: it lies in the disc of radius `1` about `1`,
which is contained in the open right half-plane. -/
private theorem re_compRatio_pos {t : ℝ} (h : dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w) :
    0 < (compRatio γ₀ γ₁ w t).re := by
  have hd := dist_compRatio_one h
  rw [dist_eq_norm] at hd
  have hre : (1 - compRatio γ₀ γ₁ w t).re ≤ ‖1 - compRatio γ₀ γ₁ w t‖ :=
    Complex.re_le_norm _
  rw [norm_sub_rev] at hre
  simp only [Complex.sub_re, Complex.one_re] at hre
  linarith

/-- Under the leash hypothesis at `t`, the comparison curve also misses `w` there: otherwise the
quotient would be `0`, contradicting the positivity of its real part. -/
private theorem ne_of_dist_lt_dist' {t : ℝ} (h : dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w) :
    γ₁ t ≠ w := by
  intro heq
  have hzero : compRatio γ₀ γ₁ w t = 0 := by rw [compRatio_apply, heq, sub_self, zero_div]
  simpa [hzero] using re_compRatio_pos h

/-- **A set contained in the open right half-plane has `0` in an unbounded component of its
complement**: the closed left half-plane is convex, hence connected, contains `0`, is unbounded,
and misses the set. -/
private theorem not_isBounded_connectedComponentIn_compl {S : Set ℂ} (hS : ∀ z ∈ S, 0 < z.re) :
    ¬IsBounded (connectedComponentIn Sᶜ 0) := by
  have hconv : Convex ℝ {z : ℂ | z.re ≤ 0} := (convex_Iic (0 : ℝ)).linear_preimage Complex.reLm
  have hLS : {z : ℂ | z.re ≤ 0} ⊆ Sᶜ := fun z hz hzS => absurd (hS z hzS) (not_lt.mpr hz)
  have h0 : (0 : ℂ) ∈ {z : ℂ | z.re ≤ 0} := by simp
  have hsub : {z : ℂ | z.re ≤ 0} ⊆ connectedComponentIn Sᶜ 0 :=
    hconv.isPreconnected.subset_connectedComponentIn h0 hLS
  intro hb
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp hb
  have hr0 : 0 ≤ r := by simpa using hr 0 (hsub h0)
  have hmem : ((-(r + 1) : ℝ) : ℂ) ∈ {z : ℂ | z.re ≤ 0} := by
    simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
    linarith
  have hle := hr _ (hsub hmem)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith), neg_neg] at hle
  linarith

/-- **Proximity invariance of the winding number** (the "dog on a leash" lemma). Let `γ₀` and `γ₁`
be closed curves on the oriented interval with endpoints `a`, `b`, each continuous on
`Set.uIcc a b`, differentiable off a common countable set `P`, and with interval-integrable
derivative. If at every parameter the two curves are closer to each other than `γ₀` is to `w`,
then they have the same winding number about `w`.

The comparison quotient `σ = (γ₁ - w) / (γ₀ - w)` is then a closed curve inside the open right
half-plane, so `0` lies in an unbounded component of the complement of its image and
`n_0(σ) = 0`; pointwise `σ' / σ = γ₁' / (γ₁ - w) - γ₀' / (γ₀ - w)`, so `n_0(σ)` is the difference
of the two winding numbers. -/
theorem windingNumber_eq_of_dist_lt_dist {P : Set ℝ} (hP : P.Countable)
    (h₀closed : γ₀ a = γ₀ b) (h₁closed : γ₁ a = γ₁ b)
    (h₀cont : ContinuousOn γ₀ (uIcc a b)) (h₁cont : ContinuousOn γ₁ (uIcc a b))
    (h₀diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ₀ t)
    (h₁diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ₁ t)
    (h₀int : IntervalIntegrable (fun t => deriv γ₀ t) volume a b)
    (h₁int : IntervalIntegrable (fun t => deriv γ₁ t) volume a b)
    (hlt : ∀ t ∈ uIcc a b, dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w) :
    windingNumber γ₁ a b w = windingNumber γ₀ a b w := by
  have hIoo : Ioo (min a b) (max a b) ⊆ uIcc a b := by
    rw [← Icc_min_max]; exact Ioo_subset_Icc_self
  -- Pointwise consequences of the leash hypothesis.
  have h₀ne : ∀ t ∈ uIcc a b, γ₀ t - w ≠ 0 := fun t ht =>
    sub_ne_zero.mpr (ne_of_dist_lt_dist (hlt t ht))
  have h₁ne : ∀ t ∈ uIcc a b, γ₁ t - w ≠ 0 := fun t ht =>
    sub_ne_zero.mpr (ne_of_dist_lt_dist' (hlt t ht))
  have hσne : ∀ t ∈ uIcc a b, compRatio γ₀ γ₁ w t ≠ 0 := fun t ht hzero => by
    simpa [hzero] using re_compRatio_pos (hlt t ht)
  -- Regularity of the comparison quotient.
  have hσcont : ContinuousOn (compRatio γ₀ γ₁ w) (uIcc a b) :=
    (h₁cont.sub continuousOn_const).div (h₀cont.sub continuousOn_const) h₀ne
  have hσclosed : compRatio γ₀ γ₁ w a = compRatio γ₀ γ₁ w b := by
    rw [compRatio_apply, compRatio_apply, h₀closed, h₁closed]
  have hσhas : ∀ t ∈ Ioo (min a b) (max a b) \ P, HasDerivAt (compRatio γ₀ γ₁ w)
      ((deriv γ₁ t * (γ₀ t - w) - (γ₁ t - w) * deriv γ₀ t) / (γ₀ t - w) ^ 2) t := by
    intro t ht
    have hd₀ : HasDerivAt (fun x => γ₀ x - w) (deriv γ₀ t) t :=
      (h₀diff t ht).hasDerivAt.sub_const w
    have hd₁ : HasDerivAt (fun x => γ₁ x - w) (deriv γ₁ t) t :=
      (h₁diff t ht).hasDerivAt.sub_const w
    exact HasDerivAt.div hd₁ hd₀ (h₀ne t (hIoo ht.1))
  have hσdiff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ (compRatio γ₀ γ₁ w) t :=
    fun t ht => (hσhas t ht).differentiableAt
  -- Almost every parameter of `Set.uIoc a b` is an interior non-exceptional parameter.
  have huIoc : Set.uIoc a b = Ioc (min a b) (max a b) := rfl
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → t ∈ Ioo (min a b) (max a b) \ P := by
    filter_upwards [hP.ae_notMem volume,
      (Set.finite_singleton (max a b)).countable.ae_notMem volume] with t htP htmax htI
    rw [huIoc] at htI
    exact ⟨⟨htI.1, lt_of_le_of_ne htI.2 (by simpa using htmax)⟩, htP⟩
  have hae' : ∀ᵐ t ∂volume.restrict (Set.uIoc a b), t ∈ Ioo (min a b) (max a b) \ P :=
    (ae_restrict_iff' measurableSet_uIoc).2 hae
  -- Interval-integrability of `deriv σ`, from the two integrable derivatives and bounded factors.
  have hfac₁ : ContinuousOn (fun t => (γ₀ t - w)⁻¹) (uIcc a b) :=
    (h₀cont.sub continuousOn_const).inv₀ h₀ne
  have hfac₂ : ContinuousOn (fun t => (γ₁ t - w) * ((γ₀ t - w) ^ 2)⁻¹) (uIcc a b) :=
    (h₁cont.sub continuousOn_const).mul
      (((h₀cont.sub continuousOn_const).pow 2).inv₀ fun t ht => pow_ne_zero 2 (h₀ne t ht))
  have hσint : IntervalIntegrable (fun t => deriv (compRatio γ₀ γ₁ w) t) volume a b := by
    refine ((h₁int.continuousOn_mul hfac₁).sub (h₀int.continuousOn_mul hfac₂)).congr_ae ?_
    filter_upwards [hae'] with t ht
    have hne := h₀ne t (hIoo ht.1)
    rw [(hσhas t ht).deriv]
    field_simp
  -- The index integrand of `σ` about `0` is the difference of the two index integrands.
  have hindex : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      (compRatio γ₀ γ₁ w t - 0)⁻¹ * deriv (compRatio γ₀ γ₁ w) t =
        (γ₁ t - w)⁻¹ * deriv γ₁ t - (γ₀ t - w)⁻¹ * deriv γ₀ t := by
    filter_upwards [hae] with t hmem htI
    have ht := hmem htI
    have hne₀ := h₀ne t (hIoo ht.1)
    have hne₁ := h₁ne t (hIoo ht.1)
    rw [(hσhas t ht).deriv, compRatio_apply, sub_zero]
    field_simp
  -- The winding number of `σ` about `0` vanishes, its image lying in the right half-plane.
  have hσzero : windingNumber (compRatio γ₀ γ₁ w) a b 0 = 0 := by
    refine windingNumber_eq_zero_of_unbounded_component hσclosed hP hσcont hσdiff hσint
      (not_isBounded_connectedComponentIn_compl ?_)
    rintro z ⟨t, ht, rfl⟩
    exact re_compRatio_pos (hlt t ht)
  -- Read the vanishing as the difference of the two winding numbers.
  have hint₀ := intervalIntegrable_inv_sub_mul_deriv h₀cont
    (fun t ht => sub_ne_zero.mp (h₀ne t ht)) h₀int
  have hint₁ := intervalIntegrable_inv_sub_mul_deriv h₁cont
    (fun t ht => sub_ne_zero.mp (h₁ne t ht)) h₁int
  have hintσ := intervalIntegrable_inv_sub_mul_deriv hσcont hσne hσint
  rw [windingNumber_eq_integral_of_avoidance hσcont hσne hintσ,
    intervalIntegral.integral_congr_ae hindex, intervalIntegral.integral_sub hint₁ hint₀,
    mul_sub, ← windingNumber_eq_integral_of_avoidance h₁cont
      (fun t ht => sub_ne_zero.mp (h₁ne t ht)) hint₁,
    ← windingNumber_eq_integral_of_avoidance h₀cont
      (fun t ht => sub_ne_zero.mp (h₀ne t ht)) hint₀] at hσzero
  exact sub_eq_zero.mp hσzero

/-- **Proximity invariance for closed piecewise-`C¹` curves.** If two closed piecewise-`C¹` curves
stay closer to each other than the first stays to `w`, they have the same winding number about `w`.
Piecewise-`C¹` regularity supplies the continuity, differentiability and integrability hypotheses
of `windingNumber_eq_of_dist_lt_dist`. -/
theorem IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist (h₀ : IsPiecewiseC1On γ₀ a b)
    (h₁ : IsPiecewiseC1On γ₁ a b) (h₀closed : γ₀ a = γ₀ b) (h₁closed : γ₁ a = γ₁ b)
    (hlt : ∀ t ∈ uIcc a b, dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w) :
    windingNumber γ₁ a b w = windingNumber γ₀ a b w := by
  obtain ⟨P₀, hP₀, hdiff₀⟩ := h₀.exists_countable_differentiableAt
  obtain ⟨P₁, hP₁, hdiff₁⟩ := h₁.exists_countable_differentiableAt
  exact TauCeti.Contour.windingNumber_eq_of_dist_lt_dist (hP₀.union hP₁) h₀closed h₁closed
    h₀.continuousOn h₁.continuousOn
    (fun t ht => hdiff₀ t ⟨ht.1, fun hmem => ht.2 (Or.inl hmem)⟩)
    (fun t ht => hdiff₁ t ⟨ht.1, fun hmem => ht.2 (Or.inr hmem)⟩)
    h₀.intervalIntegrable_deriv h₁.intervalIntegrable_deriv hlt

/-- The stage at time `s` of the straight-line homotopy `(1 - s) • γ₀ + s • γ₁`. -/
private def lineHomotopy (γ₀ γ₁ : ℝ → ℂ) (s : ℝ) : ℝ → ℂ := fun t => (1 - s) • γ₀ t + s • γ₁ t

private theorem lineHomotopy_apply (γ₀ γ₁ : ℝ → ℂ) (s t : ℝ) :
    lineHomotopy γ₀ γ₁ s t = (1 - s) • γ₀ t + s • γ₁ t := rfl

/-- Two stages of the straight-line homotopy differ by the scaled displacement of its ends. -/
private theorem lineHomotopy_sub (γ₀ γ₁ : ℝ → ℂ) (s s' t : ℝ) :
    lineHomotopy γ₀ γ₁ s' t - lineHomotopy γ₀ γ₁ s t = (s' - s) • (γ₁ t - γ₀ t) := by
  simp only [lineHomotopy_apply]
  module

/-- **Invariance of the winding number along a straight-line homotopy.** If for every parameter `t`
the segment from `γ₀ t` to `γ₁ t` misses `w`, then the two closed piecewise-`C¹` curves have the
same winding number about `w`.

No regularity of the homotopy is assumed. The intermediate curves `(1 - s) • γ₀ + s • γ₁` are
piecewise `C¹` because that predicate is stable under affine combinations; a compactness argument
bounds their distance to `w` below by a positive `m` and the displacement `‖γ₁ - γ₀‖` above by
some `M`; and the `N + 1` stages `k / N` with `M / N < m` are then chained together by
`IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist`. -/
theorem IsPiecewiseC1On.windingNumber_eq_of_notMem_segment (h₀ : IsPiecewiseC1On γ₀ a b)
    (h₁ : IsPiecewiseC1On γ₁ a b) (h₀closed : γ₀ a = γ₀ b) (h₁closed : γ₁ a = γ₁ b)
    (hseg : ∀ t ∈ uIcc a b, w ∉ segment ℝ (γ₀ t) (γ₁ t)) :
    windingNumber γ₁ a b w = windingNumber γ₀ a b w := by
  have hHne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ uIcc a b, lineHomotopy γ₀ γ₁ s t - w ≠ 0 := by
    intro s hs t ht
    refine sub_ne_zero.mpr fun heq => hseg t ht ?_
    exact heq ▸ ⟨1 - s, s, by linarith [hs.2], hs.1, by ring, rfl⟩
  have hHpw : ∀ s : ℝ, IsPiecewiseC1On (lineHomotopy γ₀ γ₁ s) a b := fun s =>
    (h₀.const_smul (1 - s)).add (h₁.const_smul s)
  have hHclosed : ∀ s : ℝ, lineHomotopy γ₀ γ₁ s a = lineHomotopy γ₀ γ₁ s b := fun s => by
    rw [lineHomotopy_apply, lineHomotopy_apply, h₀closed, h₁closed]
  -- A positive lower bound for the distance from the homotopy to `w`, by compactness.
  have hKcompact : IsCompact (Icc (0 : ℝ) 1 ×ˢ uIcc a b) := isCompact_Icc.prod isCompact_uIcc
  have hKne : (Icc (0 : ℝ) 1 ×ˢ uIcc a b).Nonempty := ⟨(0, a), ⟨by norm_num, left_mem_uIcc⟩⟩
  have hcont₀ : ContinuousOn (fun p : ℝ × ℝ => γ₀ p.2) (Icc (0 : ℝ) 1 ×ˢ uIcc a b) :=
    h₀.continuousOn.comp continuousOn_snd fun p hp => hp.2
  have hcont₁ : ContinuousOn (fun p : ℝ × ℝ => γ₁ p.2) (Icc (0 : ℝ) 1 ×ˢ uIcc a b) :=
    h₁.continuousOn.comp continuousOn_snd fun p hp => hp.2
  have hcontF : ContinuousOn (fun p : ℝ × ℝ => ‖lineHomotopy γ₀ γ₁ p.1 p.2 - w‖)
      (Icc (0 : ℝ) 1 ×ˢ uIcc a b) := by
    simp only [lineHomotopy_apply]
    exact ((((continuousOn_const.sub continuousOn_fst).smul hcont₀).add
      (continuousOn_fst.smul hcont₁)).sub continuousOn_const).norm
  obtain ⟨q, hqK, hqmin⟩ := hKcompact.exists_isMinOn hKne hcontF
  have hm : 0 < ‖lineHomotopy γ₀ γ₁ q.1 q.2 - w‖ :=
    norm_pos_iff.mpr (hHne q.1 hqK.1 q.2 hqK.2)
  have hmle : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ uIcc a b,
      ‖lineHomotopy γ₀ γ₁ q.1 q.2 - w‖ ≤ ‖lineHomotopy γ₀ γ₁ s t - w‖ :=
    fun s hs t ht => isMinOn_iff.mp hqmin (s, t) ⟨hs, ht⟩
  -- An upper bound for the displacement between the two curves.
  obtain ⟨M, hM⟩ :=
    isCompact_uIcc.exists_bound_of_continuousOn (h₁.continuousOn.sub h₀.continuousOn)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a left_mem_uIcc)
  obtain ⟨N, hN⟩ := exists_nat_gt (M / ‖lineHomotopy γ₀ γ₁ q.1 q.2 - w‖)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hstep : M / N < ‖lineHomotopy γ₀ γ₁ q.1 q.2 - w‖ := by
    rw [div_lt_iff₀ hNpos, mul_comm]
    exact (div_lt_iff₀ hm).mp hN
  -- Chain the stages `k / N` together with the leash lemma.
  have key : ∀ k : ℕ, k ≤ N → windingNumber (lineHomotopy γ₀ γ₁ (k / N)) a b w =
      windingNumber (lineHomotopy γ₀ γ₁ 0) a b w := by
    intro k
    induction k with
    | zero => intro _; norm_num
    | succ k ih =>
      intro hk
      have hkN : k ≤ N := Nat.le_of_succ_le hk
      rw [← ih hkN]
      refine IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist (hHpw _) (hHpw _)
        (hHclosed _) (hHclosed _) fun t ht => ?_
      have hmem : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
        refine ⟨by positivity, ?_⟩
        rw [div_le_one hNpos]
        exact_mod_cast hkN
      have hdisp : ‖lineHomotopy γ₀ γ₁ ((k + 1 : ℕ) / N) t
          - lineHomotopy γ₀ γ₁ ((k : ℝ) / N) t‖ = ‖γ₁ t - γ₀ t‖ / N := by
        rw [lineHomotopy_sub, norm_smul, Real.norm_eq_abs,
          show ((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N = 1 / N by push_cast; ring,
          abs_of_pos (by positivity)]
        ring
      rw [dist_eq_norm, dist_eq_norm, hdisp]
      calc ‖γ₁ t - γ₀ t‖ / N ≤ M / N := by gcongr; exact hM t ht
        _ < ‖lineHomotopy γ₀ γ₁ q.1 q.2 - w‖ := hstep
        _ ≤ ‖lineHomotopy γ₀ γ₁ ((k : ℝ) / N) t - w‖ := hmle _ hmem t ht
  have hfinal := key N le_rfl
  rw [div_self (ne_of_gt hNpos)] at hfinal
  have hH0 : lineHomotopy γ₀ γ₁ 0 = γ₀ := by
    funext t; rw [lineHomotopy_apply]; simp
  have hH1 : lineHomotopy γ₀ γ₁ 1 = γ₁ := by
    funext t; rw [lineHomotopy_apply]; simp
  rwa [hH0, hH1] at hfinal

end TauCeti.Contour

end

end
