/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Sard's lemma on the flat stratum

This file proves the case of finite-dimensional Sard's theorem carried by the higher derivatives:
if `f` is `C^{k+1}` and every iterated derivative of order `1 ≤ i ≤ k` vanishes on a set `s`, then
`f '' s` is null as soon as `finrank ℝ E < (k + 1) * finrank ℝ F`. In Morse's proof of the
Morse--Sard theorem this is the estimate for the innermost stratum `Σ_k` of the critical set, the
one place where regularity beyond `C¹` is genuinely needed; the two slices already available,
`TauCeti.addHaar_image_eq_zero_of_not_surjective_fderivWithin` (equal dimensions, `C¹`) and
`TauCeti.Differentiable.addHaar_image_eq_zero_of_finrank_lt_finrank` (smaller source,
differentiable), neither says anything when the source dimension exceeds the target dimension.

The argument is the classical one, but the covering estimate is replaced by Hausdorff dimension.
Iterating the mean value inequality down the tower of derivatives turns the vanishing hypothesis
into the Taylor-type bound `‖f y - f x‖ ≤ M * ‖y - x‖ ^ (k + 1)`, valid for `x` in the stratum and
`y` in a convex set on which `‖D^{k+1} f‖ ≤ M`. On the stratum this bound *is* a Hölder condition
with exponent `k + 1`, so Mathlib's `dimH_image_le_of_locally_holder_on` divides the Hausdorff
dimension of the source by `k + 1`, and `measure_zero_of_dimH_lt` finishes.

When `[Nontrivial F]`, a point of the stratum with `1 ≤ k` has vanishing first derivative, so the
stratum consists of critical points and this is a statement about critical values; see
`TauCeti.not_surjective_fderiv_of_iteratedFDeriv_one_eq_zero`.

This is Lane F0 of the analytic Heegaard Floer roadmap, where finite-dimensional Sard is the
prerequisite for Sard--Smale and hence for every transversality argument downstream.

## Main results

* `TauCeti.norm_sub_le_pow_of_iteratedFDeriv_eq_zero`: the Taylor-type estimate obtained from the
  vanishing of the derivatives of order `1 ≤ i ≤ k` at a point.
* `TauCeti.holderOnWith_of_iteratedFDeriv_eq_zero`: a map is Hölder of exponent `k + 1` on any set
  of such points inside a convex set with bounded `(k+1)`-st derivative.
* `TauCeti.dimH_image_le_of_iteratedFDeriv_eq_zero`: such a set has its Hausdorff dimension divided
  by `k + 1` under `f`.
* `TauCeti.addHaar_image_eq_zero_of_iteratedFDeriv_eq_zero`: the resulting nullity statement, and
  `TauCeti.ContDiff.addHaar_image_flatStratum_eq_zero` its global form on the whole stratum.
* `TauCeti.ContDiff.dense_compl_image_flatStratum`: the complement of the image of the stratum is
  dense.

## References

The proof is the first step of Morse's argument as presented in J. Milnor, *Topology from the
Differentiable Viewpoint*, §3, and in M. Hirsch, *Differential Topology*, Chapter 3.
The Hausdorff-dimension proof architecture is adapted from the sibling module
`TauCeti/Analysis/Calculus/Sard/LowDimension.lean`.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set

open scoped NNReal ENNReal Topology

namespace TauCeti

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} {k : ℕ} {s : Set E}

/-- On a segment, the distance to the initial point is bounded by the length of the segment. -/
private theorem norm_sub_le_of_mem_segment {x y z : E} (hz : z ∈ segment ℝ x y) :
    ‖z - x‖ ≤ ‖y - x‖ := by
  have h : dist x z + dist z y = dist x y := dist_add_dist_of_mem_segment hz
  have h' : dist x z ≤ dist x y := by linarith [dist_nonneg (x := z) (y := y)]
  simpa only [dist_eq_norm'] using h'

/-- A Hölder bound stated with `dist` upgrades to `HolderOnWith`, which is phrased with `edist`. -/
private theorem holderOnWith_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C r : ℝ≥0} {g : X → Y} {t : Set X}
    (h : ∀ x ∈ t, ∀ y ∈ t, dist (g x) (g y) ≤ C * dist x y ^ (r : ℝ)) :
    HolderOnWith C r g t := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- The descending induction behind `TauCeti.norm_sub_le_pow_of_iteratedFDeriv_eq_zero`: if the
derivatives of order `1 ≤ i ≤ k` vanish at `x`, then the derivative of order `k - j` grows at most
like `‖y - x‖ ^ (j + 1)`. Each step is one application of the mean value inequality along the
segment from `x` to `y`. -/
private theorem norm_iteratedFDeriv_sub_le_of_iteratedFDeriv_eq_zero {M : ℝ} {x : E}
    (hf : ∀ y ∈ s, ContDiffAt ℝ (k + 1 : ℕ) f y) (hs : Convex ℝ s) (hx : x ∈ s)
    (hM : ∀ y ∈ s, ‖iteratedFDeriv ℝ (k + 1) f y‖ ≤ M)
    (hzero : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0) :
    ∀ j ≤ k, ∀ y ∈ s, ‖iteratedFDeriv ℝ (k - j) f y - iteratedFDeriv ℝ (k - j) f x‖
      ≤ M * ‖y - x‖ ^ (j + 1) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx)
  have hdiff : ∀ i ≤ k, ∀ y ∈ s, DifferentiableAt ℝ (iteratedFDeriv ℝ i f) y := fun i hi y hy ↦
    (hf y hy).differentiableAt_iteratedFDeriv (mod_cast Nat.lt_succ_of_le hi)
  intro j
  induction j with
  | zero =>
    intro _ y hy
    simpa using hs.norm_image_sub_le_of_norm_fderiv_le (fun z hz ↦ hdiff k le_rfl z hz)
      (fun z hz ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hM z hz) hx hy
  | succ j ih =>
    intro hjk y hy
    have hj : j ≤ k := by omega
    have hstep : k - (j + 1) + 1 = k - j := by omega
    have hvanish : ∀ z ∈ s, ‖iteratedFDeriv ℝ (k - j) f z‖ ≤ M * ‖z - x‖ ^ (j + 1) := by
      intro z hz
      simpa [hzero (k - j) (by omega) (by omega)] using ih hj z hz
    have hseg : segment ℝ x y ⊆ s := hs.segment_subset hx hy
    have hbound : ∀ z ∈ segment ℝ x y,
        ‖fderiv ℝ (iteratedFDeriv ℝ (k - (j + 1)) f) z‖ ≤ M * ‖y - x‖ ^ (j + 1) := by
      intro z hz
      rw [norm_fderiv_iteratedFDeriv, hstep]
      refine (hvanish z (hseg hz)).trans ?_
      gcongr
      exact norm_sub_le_of_mem_segment hz
    have := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz ↦ hdiff _ (by omega) z (hseg hz)) hbound (left_mem_segment ℝ x y)
      (right_mem_segment ℝ x y)
    calc ‖iteratedFDeriv ℝ (k - (j + 1)) f y - iteratedFDeriv ℝ (k - (j + 1)) f x‖
        ≤ M * ‖y - x‖ ^ (j + 1) * ‖y - x‖ := this
      _ = M * ‖y - x‖ ^ (j + 1 + 1) := by rw [mul_assoc, ← pow_succ]

/-- **The Taylor-type estimate on the flat stratum.** If `f` is `C^{k+1}` on a convex set `s` whose
`(k+1)`-st derivative is bounded by `M`, and if all iterated derivatives of order `1 ≤ i ≤ k`
vanish at `x ∈ s`, then `f` moves points of `s` by at most `M * ‖y - x‖ ^ (k + 1)`.

No factorials appear because the bound is obtained by applying the mean value inequality `k + 1`
times rather than by integrating a Taylor remainder. -/
theorem norm_sub_le_pow_of_iteratedFDeriv_eq_zero {M : ℝ} {x y : E}
    (hf : ∀ z ∈ s, ContDiffAt ℝ (k + 1 : ℕ) f z) (hs : Convex ℝ s) (hx : x ∈ s) (hy : y ∈ s)
    (hM : ∀ z ∈ s, ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤ M)
    (hzero : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0) :
    ‖f y - f x‖ ≤ M * ‖y - x‖ ^ (k + 1) := by
  have key := norm_iteratedFDeriv_sub_le_of_iteratedFDeriv_eq_zero hf hs hx hM hzero k le_rfl y hy
  rw [Nat.sub_self] at key
  rwa [iteratedFDeriv_zero_eq_comp, comp_apply, comp_apply, ← LinearIsometryEquiv.map_sub,
    LinearIsometryEquiv.norm_map] at key

/-- **The flat stratum is a Hölder set of exponent `k + 1`.** On a set `A` of points at which all
iterated derivatives of order `1 ≤ i ≤ k` vanish, sitting inside a convex set `V` on which `f` is
`C^{k+1}` with `‖D^{k+1} f‖ ≤ C`, the map `f` is Hölder continuous with exponent `k + 1`.

This is where the vanishing of the derivatives is converted into a statement about how much `f`
can spread out a set, which is what controls Hausdorff dimension. -/
theorem holderOnWith_of_iteratedFDeriv_eq_zero {A V : Set E} {C : ℝ≥0}
    (hf : ∀ y ∈ V, ContDiffAt ℝ (k + 1 : ℕ) f y) (hV : Convex ℝ V)
    (hC : ∀ y ∈ V, ‖iteratedFDeriv ℝ (k + 1) f y‖ ≤ C) (hAV : A ⊆ V)
    (hzero : ∀ x ∈ A, ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0) :
    HolderOnWith C (k + 1) f A := by
  refine holderOnWith_of_dist_le fun x hx y hy ↦ ?_
  have hcast : (((k : ℝ≥0) + 1 : ℝ≥0) : ℝ) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [dist_eq_norm, dist_eq_norm, hcast, Real.rpow_natCast]
  exact norm_sub_le_pow_of_iteratedFDeriv_eq_zero hf hV (hAV hy) (hAV hx) hC (hzero y hy)

section Dimension

variable [SecondCountableTopology E] {U : Set E}

/-- **Sard's lemma on the flat stratum, in Hausdorff dimension.** A `C^{k+1}` map divides the
Hausdorff dimension of a set of points at which all iterated derivatives of order `1 ≤ i ≤ k`
vanish by `k + 1`.

The Hölder bound of `TauCeti.holderOnWith_of_iteratedFDeriv_eq_zero` only holds near a given point,
where the `(k+1)`-st derivative is bounded, so the countably stable local form
`dimH_image_le_of_locally_holder_on` is what applies. -/
theorem dimH_image_le_of_iteratedFDeriv_eq_zero (hU : IsOpen U)
    (hf : ContDiffOn ℝ (k + 1 : ℕ) f U) (hsU : s ⊆ U)
    (hzero : ∀ x ∈ s, ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0) :
    dimH (f '' s) ≤ dimH s / (k + 1 : ℝ≥0∞) := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ (k + 1) f) U :=
    (hf.continuousOn_iteratedFDerivWithin le_rfl hU.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) (k + 1) hU).symm
  have key : dimH (f '' s) ≤ dimH s / (((k : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) := by
    refine dimH_image_le_of_locally_holder_on (by positivity) fun a ha ↦ ?_
    have hM0 : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ (k + 1) f a‖ + 1 := by positivity
    have hUa : U ∈ 𝓝 a := hU.mem_nhds (hsU ha)
    have hlt : ∀ᶠ y in 𝓝 a,
        ‖iteratedFDeriv ℝ (k + 1) f y‖ < ‖iteratedFDeriv ℝ (k + 1) f a‖ + 1 :=
      ((hcont.continuousAt hUa).norm).eventually_lt_const (lt_add_one _)
    have hnhds : {y | ‖iteratedFDeriv ℝ (k + 1) f y‖ ≤ ‖iteratedFDeriv ℝ (k + 1) f a‖ + 1} ∈ 𝓝 a :=
      hlt.mono fun y hy ↦ hy.le
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hUa hnhds)
    refine ⟨(‖iteratedFDeriv ℝ (k + 1) f a‖ + 1).toNNReal, s ∩ Metric.ball a r,
      inter_mem_nhdsWithin s (Metric.ball_mem_nhds a hr), ?_⟩
    refine holderOnWith_of_iteratedFDeriv_eq_zero (V := Metric.ball a r)
      (fun y hy ↦ hf.contDiffAt (hU.mem_nhds (hball hy).1)) (convex_ball a r)
      (fun y hy ↦ ?_) inter_subset_right fun x hx ↦ hzero x hx.1
    rw [Real.coe_toNNReal _ hM0]
    exact (hball hy).2
  simpa using key

end Dimension

section Measure

variable [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  (ν : Measure F) [IsAddHaarMeasure ν] {U : Set E}

/-- **Sard's lemma on the flat stratum.** Let `f` be `C^{k+1}` on an open set `U` of a
finite-dimensional real normed space, and let `s ⊆ U` be a set at each point of which every
iterated derivative of order `1 ≤ i ≤ k` vanishes. If `finrank ℝ E < (k + 1) * finrank ℝ F`, then
`f '' s` has additive Haar measure zero.

This is the slice of finite-dimensional Sard that higher regularity buys: for a fixed pair of
dimensions with positive-dimensional target, the hypothesis holds as soon as `k` is large enough.
-/
theorem addHaar_image_eq_zero_of_iteratedFDeriv_eq_zero (hU : IsOpen U)
    (hf : ContDiffOn ℝ (k + 1 : ℕ) f U) (hsU : s ⊆ U)
    (hzero : ∀ x ∈ s, ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0)
    (hdim : finrank ℝ E < (k + 1) * finrank ℝ F) :
    ν (f '' s) = 0 := by
  have hν : ν ≪ (μH[(finrank ℝ F : ℝ)] : Measure F) := absolutelyContinuous_isAddHaarMeasure ν _
  refine measure_zero_of_dimH_lt (d := (finrank ℝ F : ℝ≥0)) hν ?_
  refine (dimH_image_le_of_iteratedFDeriv_eq_zero hU hf hsU hzero).trans_lt ?_
  have hs : dimH s ≤ (finrank ℝ E : ℝ≥0∞) := by
    simpa only [Real.dimH_univ_eq_finrank] using dimH_mono (subset_univ s)
  refine lt_of_le_of_lt (ENNReal.div_le_div_right hs _) ?_
  rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), ENNReal.coe_natCast, mul_comm]
  exact_mod_cast hdim

/-- **Sard's lemma on the flat stratum**, global form: the image of the whole set of points at
which all iterated derivatives of order `1 ≤ i ≤ k` vanish is null, provided
`finrank ℝ E < (k + 1) * finrank ℝ F`. -/
theorem ContDiff.addHaar_image_flatStratum_eq_zero (hf : ContDiff ℝ (k + 1 : ℕ) f)
    (hdim : finrank ℝ E < (k + 1) * finrank ℝ F) :
    ν (f '' {x | ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0}) = 0 :=
  addHaar_image_eq_zero_of_iteratedFDeriv_eq_zero ν isOpen_univ hf.contDiffOn (subset_univ _)
    (fun _ hx ↦ hx) hdim

/-- The complement of the image of the flat stratum of a `C^{k+1}` map is dense, provided
`finrank ℝ E < (k + 1) * finrank ℝ F`. -/
theorem ContDiff.dense_compl_image_flatStratum (hf : ContDiff ℝ (k + 1 : ℕ) f)
    (hdim : finrank ℝ E < (k + 1) * finrank ℝ F) :
    Dense (f '' {x | ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0})ᶜ := by
  let t : Set F := f '' {x | ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0}
  have ht : (addHaar : Measure F) t = 0 :=
    ContDiff.addHaar_image_flatStratum_eq_zero (ν := addHaar) hf hdim
  have htc : ∀ᵐ x ∂(addHaar : Measure F), x ∈ tᶜ := ae_iff.mpr (by simpa using ht)
  simpa only [ofPred_mem_eq, t] using Measure.dense_of_ae htc

end Measure

/-- A point at which the first derivative vanishes is a critical point, as long as the target is
nontrivial. In particular the flat stratum of `f` for `1 ≤ k` consists of critical points, so
`TauCeti.addHaar_image_eq_zero_of_iteratedFDeriv_eq_zero` is a statement about critical values. -/
theorem not_surjective_fderiv_of_iteratedFDeriv_one_eq_zero [Nontrivial F] {x : E}
    (hx : iteratedFDeriv ℝ 1 f x = 0) : ¬ Surjective (fderiv ℝ f x) := by
  have hzero : fderiv ℝ f x = 0 := by
    ext v
    have := congrFun (congrArg DFunLike.coe hx) (fun _ ↦ v)
    simpa [iteratedFDeriv_one_apply] using this
  intro hsurj
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  obtain ⟨v, hv⟩ := hsurj y
  exact hy (by rw [← hv, hzero]; simp)

end TauCeti

end
