/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.Analysis.PositiveDefinite.FourierAtom
public import TauCeti.Analysis.PositiveDefinite.Kernel.Basic
-- The remaining imports are proof-only: the Fejér averaging argument uses dominated convergence,
-- Fubini, simple-function approximation, the Haar ball formulas and negation invariance, the
-- Fourier atom kernel, and the kernel Cauchy–Schwarz bound.
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.PositiveDefinite.Kernel.Bounds

/-!
# Nonnegativity of the Fourier transform of a positive-definite function

For a continuous, integrable function `F : V → ℂ` on a finite-dimensional real inner-product
space whose subtraction kernel `(a, b) ↦ F (a - b)` is positive definite, the Fourier transform
`𝓕 F` is real and nonnegative: its real part is nonnegative at every frequency and its imaginary
part vanishes. This is the analytic half of Bochner's theorem.

The real-part nonnegativity is proved by Fejér ball averaging. For a fixed frequency `ξ`, the
twisted function `ψ = fourierAtom ξ * F` is still positive definite (Schur product with the
Fourier atom kernel), continuous, and integrable, and `𝓕 F ξ = ∫ ψ`. For `R > 0` the averaged
double integral `J_R = vol(B_R)⁻¹ ∬_{B_R × B_R} ψ (x - y)` has nonnegative real part because it
is a limit of positive-definite double sums (simple-function approximation of the identity),
while Fubini rewrites `J_R = ∫ ψ · overlapRatio R` whose dominated limit as `R → ∞` is `∫ ψ`.

Adapted from the Bochner–Minlos formalization (`Bochner/FejerPD.lean` in our bochner project);
the Fejér averaging argument is ported with the positive-definiteness hypothesis restated
through `IsPositiveDefiniteKernel`.

## Main declarations

* `TauCeti.fourierIntegral_re_nonneg_of_isPositiveDefiniteKernel`: the Fourier transform of a
  continuous integrable positive-definite function has nonnegative real part.
* `TauCeti.fourierIntegral_im_eq_zero_of_isPositiveDefiniteKernel`: its imaginary part vanishes.
* `TauCeti.fourierIntegral_eq_re_of_isPositiveDefiniteKernel`: it equals its own real part.

## References

* W. Rudin, *Fourier Analysis on Groups* (1962), Theorem 1.4.3.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, §4.2, Lemma 4.8.
* Roadmap: TauCetiRoadmap/OneParameterSemigroups/README.md, Part C (Bochner milestone).
-/

public section

open Complex ComplexConjugate Filter MeasureTheory
open scoped ComplexOrder FourierTransform

namespace TauCeti

/-! ### A simple-function expansion for integrals of compositions -/

section SimpleFuncExpansion

variable {α : Type*} [MeasurableSpace α]

/-- For a simple function `sn : α → α` and any `g : α → ℂ`,
`∫ g (sn x) ∂μ = ∑ u ∈ sn.range, μ (sn ⁻¹' {u}).toReal • g u`. -/
private theorem integral_simpleFunc_comp (sn : SimpleFunc α α) (g : α → ℂ)
    (μ : Measure α) [IsFiniteMeasure μ] :
    ∫ x, g (sn x) ∂μ = ∑ u ∈ sn.range, (μ (⇑sn ⁻¹' {u})).toReal • g u := by
  classical
  have hpw : ∀ x, g (sn x) =
      ∑ u ∈ sn.range, (⇑sn ⁻¹' {u}).indicator (fun _ => g u) x := by
    intro x
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    simp_rw [eq_comm (a := sn x)]
    rw [Finset.sum_ite_eq' sn.range (sn x) (fun u => g u)]
    simp
  simp_rw [hpw]
  rw [integral_finsetSum _ (fun u _ => (integrable_const _).indicator
    (sn.measurableSet_preimage _))]
  congr 1
  ext u
  rw [integral_indicator (sn.measurableSet_preimage _), setIntegral_const, measureReal_def]

end SimpleFuncExpansion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ### Consequences of positive definiteness for a subtraction kernel -/

section KernelConsequences

variable {ψ : V → ℂ}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The positive-definite double sum attached to a subtraction kernel has nonnegative real
part. -/
private theorem re_sum_nonneg_of_kernel
    (hpd : IsPositiveDefiniteKernel fun a b : V => ψ (a - b)) {n : ℕ}
    (x : Fin n → V) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, conj (c i) * c j * ψ (x i - x j)).re := by
  have h := (isPositiveDefiniteKernel_iff.mp hpd).2 x c
  exact (Complex.nonneg_iff.mp h).1

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The value at `0` of a function with positive-definite subtraction kernel has nonnegative
real part. -/
theorem re_map_zero_nonneg_of_isPositiveDefiniteKernel
    (hpd : IsPositiveDefiniteKernel fun a b : V => ψ (a - b)) :
    0 ≤ (ψ 0).re := by
  have h : (0 : ℂ) ≤ ψ 0 := by
    simpa using isPositiveDefiniteKernel_apply_self_nonneg hpd 0
  exact (Complex.nonneg_iff.mp h).1

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A function with positive-definite subtraction kernel is uniformly bounded by the real part
of its value at `0`. -/
theorem norm_le_re_map_zero_of_isPositiveDefiniteKernel
    (hpd : IsPositiveDefiniteKernel fun a b : V => ψ (a - b)) (z : V) :
    ‖ψ z‖ ≤ (ψ 0).re := by
  have h := isPositiveDefiniteKernel_normSq_le hpd z 0
  simp only [sub_zero, sub_self, RCLike.normSq_eq_def', RCLike.re_to_complex] at h
  refine le_of_sq_le_sq ?_ (re_map_zero_nonneg_of_isPositiveDefiniteKernel hpd)
  calc ‖ψ z‖ ^ 2 ≤ (ψ 0).re * (ψ 0).re := h
    _ = (ψ 0).re ^ 2 := (sq ((ψ 0).re)).symm

end KernelConsequences

/-! ### Step A: the positive-definite double integral has nonnegative real part -/

/-- The double integral of a positive-definite function over `S × S` has nonnegative real part.

Approximate `id : V → V` by simple functions `sₙ`. For each `sₙ`, the double integral
`∬ ψ (sₙ x - sₙ y) ∂μ ∂μ` expands as `∑ᵢⱼ μ(Aᵢ) μ(Aⱼ) ψ (uᵢ - uⱼ)`, a positive-definite double
sum with real coefficients, so its real part is nonnegative. The sums converge to
`∬ ψ (x - y) ∂μ ∂μ` by dominated convergence, so nonnegativity passes to the limit.
See Rudin, *Fourier Analysis on Groups*, proof of Theorem 1.4.3, step 1. -/
private theorem pd_double_integral_re_nonneg (ψ : V → ℂ)
    (hpd : IsPositiveDefiniteKernel fun a b : V => ψ (a - b))
    (hcont : Continuous ψ) (S : Set V) (_hSmeas : MeasurableSet S)
    (hSbdd : Bornology.IsBounded S) :
    0 ≤ (∫ x in S, ∫ y in S, ψ (x - y)).re := by
  classical
  let μ := (volume : Measure V).restrict S
  -- 1. Approximate `id` by simple functions; show the double integral converges.
  have h_approx : ∃ (s : ℕ → SimpleFunc V V),
      Tendsto (fun n => ∫ x, ∫ y, ψ (s n x - s n y) ∂μ ∂μ)
        atTop (nhds (∫ x, ∫ y, ψ (x - y) ∂μ ∂μ)) := by
    have hid : StronglyMeasurable (id : V → V) := stronglyMeasurable_id
    refine ⟨hid.approx, ?_⟩
    have h_ptwise : ∀ x, Tendsto (fun n => hid.approx n x) atTop (nhds x) :=
      fun x => by simpa using hid.tendsto_approx x
    -- Uniform bound from positive definiteness: `‖ψ z‖ ≤ (ψ 0).re` for all `z`.
    have hbound : ∀ z, ‖ψ z‖ ≤ (ψ 0).re := norm_le_re_map_zero_of_isPositiveDefiniteKernel hpd
    have hfm : IsFiniteMeasure μ :=
      ⟨by simpa [μ] using hSbdd.measure_lt_top⟩
    -- The inner integral converges for each `x` by dominated convergence.
    have h_inner_conv : ∀ x, Tendsto
        (fun n => ∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ)
        atTop (nhds (∫ y, ψ (x - y) ∂μ)) := by
      intro x
      have hmeas : ∀ n, AEStronglyMeasurable
          (fun y => ψ (hid.approx n x - hid.approx n y)) μ := by
        intro n
        have hsf : (fun y => ψ (hid.approx n x - hid.approx n y)) =
            ⇑((hid.approx n).map (fun v => ψ (hid.approx n x - v))) := by
          ext y
          simp [SimpleFunc.map_apply]
        rw [hsf]
        exact (SimpleFunc.map _ _).aestronglyMeasurable
      have hbd : ∀ n, ∀ᵐ y ∂μ, ‖ψ (hid.approx n x - hid.approx n y)‖ ≤ (ψ 0).re :=
        fun n => ae_of_all _ (fun y => hbound _)
      have hlim : ∀ᵐ y ∂μ, Tendsto
          (fun n => ψ (hid.approx n x - hid.approx n y))
          atTop (nhds (ψ (x - y))) :=
        ae_of_all _ (fun y =>
          (hcont.continuousAt.tendsto.comp ((h_ptwise x).sub (h_ptwise y))))
      exact tendsto_integral_of_dominated_convergence
        (fun _ => (ψ 0).re) hmeas (integrable_const _) hbd hlim
    -- The outer integral converges by dominated convergence.
    have hmeas2 : ∀ n, AEStronglyMeasurable
        (fun x => ∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ) μ := by
      intro n
      have hsf : (fun x => ∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ) =
          ⇑((hid.approx n).map
            (fun u => ∫ y, ψ (u - hid.approx n y) ∂μ)) := by
        ext x
        simp [SimpleFunc.map_apply]
      rw [hsf]
      exact (SimpleFunc.map _ _).aestronglyMeasurable
    have hbd2 : ∀ n, ∀ᵐ x ∂μ,
        ‖∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ‖ ≤
          (ψ 0).re * (μ Set.univ).toReal := by
      intro n
      refine ae_of_all _ (fun x => ?_)
      calc ‖∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ‖
          ≤ ∫ y, ‖ψ (hid.approx n x - hid.approx n y)‖ ∂μ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ _, (ψ 0).re ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
              (integrable_const _) (ae_of_all _ (fun _ => hbound _))
        _ = (ψ 0).re * (μ Set.univ).toReal := by
            rw [integral_const, smul_eq_mul, mul_comm, measureReal_def]
    exact tendsto_integral_of_dominated_convergence
      (fun _ => (ψ 0).re * (μ Set.univ).toReal)
      hmeas2 (integrable_const _) hbd2 (ae_of_all _ h_inner_conv)
  rcases h_approx with ⟨s, hs_tendsto⟩
  -- 2. For a simple function, the double integral expands to a positive-definite sum.
  have h_sum : ∀ n, 0 ≤ (∫ x, ∫ y, ψ (s n x - s n y) ∂μ ∂μ).re := by
    intro n
    let sn := s n
    let R := sn.range
    have hfm : IsFiniteMeasure μ :=
      ⟨by simpa [μ] using hSbdd.measure_lt_top⟩
    have h_double_integral : (∫ x, ∫ y, ψ (sn x - sn y) ∂μ ∂μ) =
        ∑ u ∈ R, ∑ v ∈ R,
          ((μ (sn ⁻¹' {u})).toReal : ℂ) *
          ((μ (sn ⁻¹' {v})).toReal : ℂ) * ψ (u - v) := by
      have h_inner : ∀ x, ∫ y, ψ (sn x - sn y) ∂μ =
          ∑ v ∈ R, (μ (⇑sn ⁻¹' {v})).toReal • ψ (sn x - v) :=
        fun x => integral_simpleFunc_comp sn (fun v => ψ (sn x - v)) μ
      simp_rw [h_inner, Complex.real_smul]
      rw [integral_finsetSum _ (fun v _ => ?_)]
      · -- Expand the outer integral via `integral_simpleFunc_comp`.
        have h_expand : ∀ v, ∫ a, (↑(μ (⇑sn ⁻¹' {v})).toReal : ℂ) * ψ (sn a - v) ∂μ =
            ∑ u ∈ R, (μ (⇑sn ⁻¹' {u})).toReal •
              ((↑(μ (⇑sn ⁻¹' {v})).toReal : ℂ) * ψ (u - v)) := fun v =>
          integral_simpleFunc_comp sn
            (fun w => (↑(μ (⇑sn ⁻¹' {v})).toReal : ℂ) * ψ (w - v)) μ
        simp_rw [h_expand]
        rw [Finset.sum_comm]
        congr 1
        ext u
        congr 1
        ext v
        rw [Complex.real_smul]
        ring
      · -- `c * ψ (sn · - v)` is integrable for the finite measure `μ`.
        refine Integrable.const_mul ?_ _
        have hsf : (fun x => ψ (sn x - v)) = ⇑(sn.map (fun u => ψ (u - v))) := by
          ext x
          simp [SimpleFunc.map_apply]
        rw [hsf]
        exact SimpleFunc.integrable_of_isFiniteMeasure _
    rw [h_double_integral]
    -- Reindex the `Finset` sum to `Fin m` and apply positive definiteness.
    let m := R.card
    have ⟨e, _⟩ : ∃ e : Fin m ≃ R, True := ⟨R.equivFin.symm, trivial⟩
    have h_reindex : (∑ u ∈ R, ∑ v ∈ R,
        ((μ (sn ⁻¹' {u})).toReal : ℂ) *
        ((μ (sn ⁻¹' {v})).toReal : ℂ) * ψ (u - v)) =
      ∑ i : Fin m, ∑ j : Fin m,
        ((μ (sn ⁻¹' {(e i : V)})).toReal : ℂ) *
        ((μ (sn ⁻¹' {(e j : V)})).toReal : ℂ) * ψ ((e i : V) - (e j : V)) := by
      rw [← Finset.sum_coe_sort R]
      exact Fintype.sum_equiv e.symm _ _ (fun i => by
        rw [← Finset.sum_coe_sort R]
        exact Fintype.sum_equiv e.symm _ _ (fun j => by simp))
    rw [h_reindex]
    let c : Fin m → ℂ := fun i => ((μ (sn ⁻¹' {(e i : V)})).toReal : ℂ)
    let x_pts : Fin m → V := fun i => (e i : V)
    have hpd_eval := re_sum_nonneg_of_kernel hpd x_pts c
    -- The coefficients are real, so the conjugation is the identity.
    have hpd_match : (∑ i : Fin m, ∑ j : Fin m,
        conj (c i) * c j * ψ (x_pts i - x_pts j)) =
      ∑ i : Fin m, ∑ j : Fin m, c i * c j * ψ (x_pts i - x_pts j) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      simp only [c, Complex.conj_ofReal]
    rwa [hpd_match] at hpd_eval
  -- 3. Pass to the limit.
  have h_re_tendsto : Tendsto
      (fun n => (∫ x, ∫ y, ψ (s n x - s n y) ∂μ ∂μ).re)
      atTop (nhds (∫ x, ∫ y, ψ (x - y) ∂μ ∂μ).re) :=
    (Complex.continuous_re.tendsto _).comp hs_tendsto
  exact ge_of_tendsto' h_re_tendsto h_sum

/-! ### The Fejér overlap ratio -/

/-- The overlap ratio `vol (B_R ∩ B_R(v)) / vol B_R` appearing in the Fejér average. -/
private noncomputable def overlapRatio (R : ℝ) (v : V) : ℝ :=
  if (volume (Metric.closedBall (0 : V) R)).toReal = 0 then 0
  else (volume (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R)).toReal /
       (volume (Metric.closedBall (0 : V) R)).toReal

/-- The overlap ratio is at most one. -/
private theorem overlapRatio_le_one (R : ℝ) (v : V) : overlapRatio R v ≤ 1 := by
  unfold overlapRatio
  split_ifs with h
  · exact zero_le_one
  · exact div_le_one_of_le₀
      (ENNReal.toReal_mono (ne_of_lt measure_closedBall_lt_top)
        (measure_mono Set.inter_subset_left))
      ENNReal.toReal_nonneg

/-- The overlap ratio is nonnegative. -/
private theorem overlapRatio_nonneg (R : ℝ) (v : V) : 0 ≤ overlapRatio R v := by
  unfold overlapRatio
  split_ifs
  · exact le_refl 0
  · exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- The overlap ratio is measurable in the translation variable. -/
private theorem measurable_overlapRatio (R : ℝ) : Measurable (overlapRatio R : V → ℝ) := by
  unfold overlapRatio
  split_ifs with h
  · exact measurable_const
  · apply Measurable.div_const
    let E := {p : V × V | p.2 ∈ Metric.closedBall (0 : V) R ∧ dist p.2 p.1 ≤ R}
    have hE : MeasurableSet E :=
      .inter (measurableSet_closedBall.preimage measurable_snd)
        ((isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet)
    have hfib : ∀ v : V, Prod.mk v ⁻¹' E =
        Metric.closedBall (0 : V) R ∩ Metric.closedBall v R := by
      intro v
      ext x
      simp [E, Metric.mem_closedBall, Set.mem_inter_iff, dist_comm x v]
    change Measurable fun v => (volume (Metric.closedBall (0 : V) R ∩
        Metric.closedBall v R)).toReal
    simp_rw [← hfib]
    exact (measurable_measure_prodMk_left hE (ν := volume)).ennreal_toReal

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Ball containment: `closedBall 0 (R - ‖v‖) ⊆ closedBall 0 R ∩ closedBall v R`. -/
private theorem closedBall_sub_norm_subset (v : V) (R : ℝ) :
    Metric.closedBall (0 : V) (R - ‖v‖) ⊆
    Metric.closedBall (0 : V) R ∩ Metric.closedBall v R := by
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right] at hx
  constructor
  · exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; linarith [norm_nonneg v])
  · refine Metric.mem_closedBall.mpr ?_
    have h1 : dist x v ≤ dist x 0 + dist 0 v := dist_triangle x 0 v
    simp only [dist_zero_right, dist_zero_left] at h1
    linarith

/-- The overlap ratio tends to one along integer radii, for a fixed translation.

Since `closedBall 0 (R - ‖v‖) ⊆ closedBall 0 R ∩ closedBall v R`, the ratio is at least
`((R - ‖v‖) / R) ^ d → 1` by the Haar ball formula, and it is at most `1`; squeeze. -/
private theorem overlapRatio_tendsto_one (v : V) :
    Tendsto (fun n : ℕ => overlapRatio (n : ℝ) v) atTop (nhds 1) := by
  set d := Module.finrank ℝ V
  apply Filter.Tendsto.squeeze'
    -- Lower bound: `((n - ‖v‖) / n) ^ d → 1`.
    (show Tendsto (fun n : ℕ =>
        ((↑n - ‖v‖) / ↑n) ^ d) atTop (nhds 1) by
      have h : Tendsto (fun n : ℕ => (↑n - ‖v‖) / (↑n : ℝ)) atTop (nhds 1) := by
        have h1 : ∀ᶠ n : ℕ in atTop, (↑n - ‖v‖) / (↑n : ℝ) = 1 - ‖v‖ / ↑n := by
          filter_upwards [Filter.eventually_gt_atTop 0] with n hn
          field_simp
        have hc : Tendsto (fun n : ℕ => ‖v‖ / (↑n : ℝ)) atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
        exact Tendsto.congr' (EventuallyEq.symm h1)
          (by simpa using Tendsto.sub tendsto_const_nhds hc)
      simpa using h.pow (n := d))
    -- Upper bound: the constant `1`.
    tendsto_const_nhds
    -- The ratio dominates the lower bound eventually.
    (by filter_upwards [Filter.eventually_gt_atTop (⌈‖v‖⌉₊)] with n hn
        have hn_gt : ‖v‖ < (n : ℝ) :=
          lt_of_le_of_lt (Nat.le_ceil _) (Nat.cast_lt.mpr hn)
        have hn_pos : (0 : ℝ) < n := by linarith [norm_nonneg v]
        have hsub_nn : (0 : ℝ) ≤ ↑n - ‖v‖ := by linarith
        have hvol_pos := Metric.measure_closedBall_pos (volume : Measure V) 0 hn_pos
        have hvol_ne_top : volume (Metric.closedBall (0 : V) (↑n)) ≠ ⊤ :=
          ne_of_lt measure_closedBall_lt_top
        have hvol_toReal_pos : 0 < (volume (Metric.closedBall (0 : V) (↑n))).toReal :=
          ENNReal.toReal_pos (ne_of_gt hvol_pos) hvol_ne_top
        unfold overlapRatio
        rw [if_neg (ne_of_gt hvol_toReal_pos)]
        have hball_pos : 0 < (volume (Metric.ball (0 : V) 1)).toReal :=
          ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 one_pos))
            (ne_of_lt measure_ball_lt_top)
        have hvol_sub : (volume (Metric.closedBall (0 : V) (↑n - ‖v‖))).toReal =
            (↑n - ‖v‖) ^ d * (volume (Metric.ball (0 : V) 1)).toReal := by
          rw [Measure.addHaar_closedBall volume (0 : V) hsub_nn, ENNReal.toReal_mul,
              ENNReal.toReal_ofReal (by positivity)]
        have hvol_n : (volume (Metric.closedBall (0 : V) (↑n))).toReal =
            (↑n) ^ d * (volume (Metric.ball (0 : V) 1)).toReal := by
          rw [Measure.addHaar_closedBall volume (0 : V) hn_pos.le, ENNReal.toReal_mul,
              ENNReal.toReal_ofReal (by positivity)]
        calc ((↑n - ‖v‖) / ↑n) ^ d
            = (↑n - ‖v‖) ^ d / (↑n) ^ d := by rw [div_pow]
          _ = ((↑n - ‖v‖) ^ d * (volume (Metric.ball (0 : V) 1)).toReal) /
              ((↑n) ^ d * (volume (Metric.ball (0 : V) 1)).toReal) := by
              rw [mul_div_mul_right _ _ (ne_of_gt hball_pos)]
          _ = (volume (Metric.closedBall (0 : V) (↑n - ‖v‖))).toReal /
              (volume (Metric.closedBall (0 : V) (↑n))).toReal := by
              rw [hvol_sub, hvol_n]
          _ ≤ (volume (Metric.closedBall (0 : V) (↑n) ∩ Metric.closedBall v (↑n))).toReal /
              (volume (Metric.closedBall (0 : V) (↑n))).toReal :=
              div_le_div_of_nonneg_right
                (ENNReal.toReal_mono
                  (ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
                    measure_closedBall_lt_top))
                  (measure_mono (closedBall_sub_norm_subset v ↑n)))
                hvol_toReal_pos.le)
    -- The ratio is at most `1`.
    (Filter.Eventually.of_forall (fun n => overlapRatio_le_one (n : ℝ) v))

/-! ### Step B: the Fubini identity for the Fejér average -/

/-- Inner integral substitution via Haar invariance:
`∫ y in closedBall 0 R, ψ (x - y) = ∫ v in closedBall x R, ψ v`. -/
private theorem inner_integral_sub (ψ : V → ℂ) (x : V) (R : ℝ) :
    ∫ y in Metric.closedBall (0 : V) R, ψ (x - y) =
    ∫ v in Metric.closedBall x R, ψ v := by
  rw [← integral_indicator measurableSet_closedBall,
      ← integral_indicator measurableSet_closedBall]
  have hind : ∀ y : V, (Metric.closedBall (0 : V) R).indicator (fun y => ψ (x - y)) y =
      (Metric.closedBall x R).indicator ψ (x - y) := by
    intro y
    simp only [Set.indicator, Metric.mem_closedBall]
    have : dist (x - y) x = dist y 0 := by simp [dist_eq_norm]
    rw [this]
  simp_rw [hind, sub_eq_add_neg]
  have h1 : ∫ y : V, (Metric.closedBall x R).indicator ψ (x + -y) =
      ∫ y : V, (Metric.closedBall x R).indicator ψ (x + y) :=
    integral_neg_eq_self (fun y : V => (Metric.closedBall x R).indicator ψ (x + y)) volume
  rw [h1]
  exact integral_add_left_eq_self ((Metric.closedBall x R).indicator ψ) x

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Indicator equivalence: for the nested ball indicators, membership `v ∈ closedBall x R` can be
transposed to `x ∈ closedBall v R` by `dist_comm`. -/
private theorem indicator_closedBall_inter (ψ : V → ℂ) (R : ℝ) (x v : V) :
    (Metric.closedBall (0 : V) R).indicator
      (fun x => (Metric.closedBall x R).indicator ψ v) x =
    (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
      (fun _ => ψ v) x := by
  simp only [Set.indicator, Metric.mem_closedBall, Set.mem_inter_iff, dist_comm v x]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- The Fejér integrand is integrable on `V × V`: it is the indicator of a compact set applied
to the continuous function `ψ ∘ snd`. -/
private theorem integrable_indicator_prod (ψ : V → ℂ) (hcont : Continuous ψ) (R : ℝ) :
    Integrable (Function.uncurry fun x v =>
      (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
        (fun _ => ψ v) x)
      (Measure.prod volume volume) := by
  set S := {p : V × V | p.1 ∈ Metric.closedBall (0 : V) R ∧ dist p.1 p.2 ≤ R}
  have hfeq : (Function.uncurry fun x v =>
      (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
        (fun _ => ψ v) x) = S.indicator (ψ ∘ Prod.snd) := by
    ext ⟨x, v⟩
    simp only [Function.uncurry, Set.indicator,
      Metric.mem_closedBall, Set.mem_inter_iff, Function.comp, dist_zero_right, S,
      Set.mem_ofPred_eq]
  rw [hfeq]
  have hS_closed : IsClosed S :=
    (Metric.isClosed_closedBall.preimage continuous_fst).inter
      (isClosed_le (Continuous.dist continuous_fst continuous_snd) continuous_const)
  have hS_bdd : Bornology.IsBounded S := by
    apply Metric.isBounded_closedBall (x := (0 : V × V)) (r := |R| + |R|) |>.subset
    intro ⟨x, v⟩ ⟨hx, hdist⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hx
    simp only [Metric.mem_closedBall, Prod.dist_eq] at hdist ⊢
    simp only [Prod.fst_zero, Prod.snd_zero, dist_zero_right]
    apply max_le
    · linarith [le_abs_self R, abs_nonneg R]
    · have hv : ‖v‖ ≤ ‖x‖ + ‖v - x‖ := norm_le_insert' v x
      rw [← dist_eq_norm, dist_comm] at hv
      linarith [le_abs_self R]
  exact ((hcont.comp continuous_snd).continuousOn.integrableOn_compact
    (Metric.isCompact_of_isClosed_isBounded hS_closed hS_bdd)).integrable_indicator
    hS_closed.measurableSet

/-- Conversion of the nested set integrals of the Fejér average to indicator form on `V × V`. -/
private theorem fejer_indicator_form (ψ : V → ℂ) (R : ℝ) :
    ∫ x in Metric.closedBall (0 : V) R, ∫ v in Metric.closedBall x R, ψ v =
      ∫ x, ∫ v, (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
        (fun _ => ψ v) x := by
  set B := Metric.closedBall (0 : V) R
  trans ∫ x, B.indicator (fun x => ∫ v, (Metric.closedBall x R).indicator ψ v) x
  · rw [integral_indicator measurableSet_closedBall]
    congr 1
    funext x
    exact (integral_indicator measurableSet_closedBall).symm
  · congr 1
    funext x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      congr 1
      funext v
      rw [← indicator_closedBall_inter ψ R x v, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      rw [show (fun v => (B ∩ Metric.closedBall v R).indicator (fun _ => ψ v) x) = 0 from by
        funext v
        exact Set.indicator_of_notMem (fun h => hx h.1) _]
      simp

/-- Fubini for the Fejér average: swapping the order of integration evaluates the inner integral
to the overlap volume. See Folland, *A Course in Abstract Harmonic Analysis*, §4.2. -/
private theorem fejer_fubini_eval (ψ : V → ℂ) (hcont : Continuous ψ) (R : ℝ) :
    ∫ x, ∫ v, (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
        (fun _ => ψ v) x =
      ∫ v, (volume (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R)).toReal • ψ v := by
  rw [integral_integral_swap (integrable_indicator_prod ψ hcont R)]
  congr 1
  funext v
  rw [integral_indicator (measurableSet_closedBall.inter measurableSet_closedBall),
      setIntegral_const, measureReal_def]

/-- The Fubini identity: the normalized Fejér double integral equals `∫ ψ · overlapRatio`. -/
private theorem fejer_avg_eq_integral (ψ : V → ℂ) (hcont : Continuous ψ)
    (R : ℝ) (hR : 0 < R) :
    (volume (Metric.closedBall (0 : V) R)).toReal⁻¹ •
      ∫ x in Metric.closedBall (0 : V) R,
        ∫ y in Metric.closedBall (0 : V) R, ψ (x - y) =
    ∫ v, (overlapRatio R v : ℂ) * ψ v := by
  have hvol_ne : (volume (Metric.closedBall (0 : V) R)).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt (Metric.measure_closedBall_pos volume 0 hR))
      (ne_of_lt measure_closedBall_lt_top))
  rw [setIntegral_congr_fun measurableSet_closedBall
    (fun x _ => inner_integral_sub ψ x R)]
  rw [fejer_indicator_form ψ R, fejer_fubini_eval ψ hcont R]
  calc (volume (Metric.closedBall (0 : V) R)).toReal⁻¹ •
      ∫ v, (volume (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R)).toReal • ψ v
    = ∫ v, (volume (Metric.closedBall (0 : V) R)).toReal⁻¹ •
        ((volume (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R)).toReal • ψ v) :=
        (integral_smul _ _).symm
    _ = ∫ v, (overlapRatio R v : ℂ) * ψ v := by
        congr 1
        funext v
        rw [smul_comm, ← smul_assoc, Complex.real_smul]
        congr 1
        rw [Complex.ofReal_inj]
        rw [overlapRatio, if_neg hvol_ne, div_eq_mul_inv, smul_eq_mul]

/-! ### Step C: the integral of a positive-definite function has nonnegative real part -/

/-- For a continuous integrable positive-definite function `ψ`, the integral `∫ ψ` has
nonnegative real part: the Fejér-averaged double integral `J_R` converges to `∫ ψ` and has
nonnegative real part for each radius `R`. -/
private theorem pd_integral_re_nonneg (ψ : V → ℂ)
    (hpd : IsPositiveDefiniteKernel fun a b : V => ψ (a - b))
    (hint : Integrable ψ) (hcont : Continuous ψ) :
    0 ≤ (∫ x, ψ x).re := by
  -- Define `J n = vol(B_n)⁻¹ • ∬_{B_n × B_n} ψ (x - y)`.
  set J : ℕ → ℂ := fun n =>
    if n = 0 then ψ 0
    else (volume (Metric.closedBall (0 : V) (n : ℝ))).toReal⁻¹ •
      ∫ x in Metric.closedBall (0 : V) (n : ℝ),
        ∫ y in Metric.closedBall (0 : V) (n : ℝ), ψ (x - y)
  -- `Re (J n) ≥ 0` for each `n`.
  have hnn : ∀ n : ℕ, 0 ≤ (J n).re := by
    intro n
    simp only [J]
    split_ifs with h
    · exact re_map_zero_nonneg_of_isPositiveDefiniteKernel hpd
    · rw [Complex.smul_re]
      apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      exact pd_double_integral_re_nonneg ψ hpd hcont _ measurableSet_closedBall
        Metric.isBounded_closedBall
  -- `J n → ∫ ψ` via the Fubini identity and dominated convergence.
  have hconv : Tendsto J atTop (nhds (∫ x, ψ x)) := by
    suffices h : Tendsto
        (fun n : ℕ => ∫ v, (overlapRatio (n : ℝ) v : ℂ) * ψ v)
        atTop (nhds (∫ x, ψ x)) by
      apply h.congr'
      filter_upwards [Filter.eventually_ne_atTop 0] with n hn
      simp only [J, if_neg hn]
      exact (fejer_avg_eq_integral ψ hcont n (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).symm
    rw [show (∫ x, ψ x) = ∫ x, (1 : ℂ) * ψ x by simp]
    apply tendsto_integral_of_dominated_convergence (fun v => ‖ψ v‖)
    · intro n
      exact (continuous_ofReal.measurable.comp
        (measurable_overlapRatio n)).aestronglyMeasurable.mul
        hcont.aestronglyMeasurable
    · exact hint.norm
    · intro n
      filter_upwards with v
      rw [norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (abs_le.mpr ⟨by linarith [overlapRatio_nonneg (n : ℝ) v],
          overlapRatio_le_one (n : ℝ) v⟩)
    · filter_upwards with v
      have h2 : Tendsto (fun n : ℕ => (overlapRatio (n : ℝ) v : ℂ))
          atTop (nhds (1 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 1).comp (overlapRatio_tendsto_one v)
      exact h2.mul tendsto_const_nhds
  exact ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp hconv) hnn

/-! ### The main theorems -/

/-- The Fourier transform written as the integral against the Fourier atom. -/
theorem fourierIntegral_eq_integral_fourierAtom_mul (F : V → ℂ) (ξ : V) :
    𝓕 F ξ = ∫ v, fourierAtom ξ v * F v := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul, fourierAtom_eq_fourierChar]

/-- The Fourier transform of a continuous integrable positive-definite function on a
finite-dimensional real inner-product space has nonnegative real part.

Rudin, *Fourier Analysis on Groups*, Theorem 1.4.3; Folland, *A Course in Abstract Harmonic
Analysis*, §4.2, Lemma 4.8. -/
theorem fourierIntegral_re_nonneg_of_isPositiveDefiniteKernel (F : V → ℂ)
    (hpd : IsPositiveDefiniteKernel fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) (ξ : V) :
    0 ≤ (𝓕 F ξ).re := by
  -- Step 1: `𝓕 F ξ = ∫ v, fourierAtom ξ v * F v`.
  rw [fourierIntegral_eq_integral_fourierAtom_mul F ξ]
  -- Step 2: the twisted function is positive definite (Schur product with the Fourier atom).
  have hψ_pd : IsPositiveDefiniteKernel
      fun a b : V => (fun v => fourierAtom ξ v * F v) (a - b) :=
    isPositiveDefiniteKernel_mul (isPositiveDefiniteKernel_fourierAtom ξ) hpd
  -- Step 3: the twisted function is continuous and integrable.
  have hψ_cont : Continuous fun v => fourierAtom ξ v * F v :=
    (continuous_fourierAtom ξ).mul hcont
  have hψ_int : Integrable fun v => fourierAtom ξ v * F v := by
    refine Integrable.mono hint hψ_cont.aestronglyMeasurable ?_
    filter_upwards with v
    rw [norm_mul, fourierAtom_eq_fourierChar, Circle.norm_coe, one_mul]
  -- Step 4: apply the Fejér average bound.
  exact pd_integral_re_nonneg _ hψ_pd hψ_int hψ_cont

/-- The Fourier transform of a positive-definite function on a finite-dimensional real
inner-product space has vanishing imaginary part, by Hermitian symmetry and the negation
invariance of Haar measure. -/
theorem fourierIntegral_im_eq_zero_of_isPositiveDefiniteKernel (F : V → ℂ)
    (hpd : IsPositiveDefiniteKernel fun a b : V => F (a - b)) (ξ : V) :
    (𝓕 F ξ).im = 0 := by
  rw [fourierIntegral_eq_integral_fourierAtom_mul F ξ]
  have hconj : conj (∫ v, fourierAtom ξ v * F v) = ∫ v, fourierAtom ξ v * F v := by
    rw [← integral_conj]
    have hpt : ∀ v : V, conj (fourierAtom ξ v * F v) = fourierAtom ξ (-v) * F (-v) := by
      intro v
      rw [map_mul, (fun v => by simpa using isPositiveDefiniteKernel_conj_symm hpd v 0 :
    ∀ v, conj (F v) = F (-v)) v]
      congr 1
      rw [fourierAtom_eq_fourierChar, fourierAtom_eq_fourierChar,
        Circle.starRingEnd_addChar]
      simp [inner_neg_left]
    simp_rw [hpt]
    exact integral_neg_eq_self (fun v => fourierAtom ξ v * F v) volume
  have him := congrArg Complex.im hconj
  simp only [Complex.conj_im] at him
  linarith

/-- The Fourier transform of a positive-definite function on a finite-dimensional real
inner-product space is real: it equals the coercion of its own real part. -/
theorem fourierIntegral_eq_re_of_isPositiveDefiniteKernel (F : V → ℂ)
    (hpd : IsPositiveDefiniteKernel fun a b : V => F (a - b)) (ξ : V) :
    𝓕 F ξ = ((𝓕 F ξ).re : ℂ) := by
  refine Complex.ext (by simp) ?_
  simp [fourierIntegral_im_eq_zero_of_isPositiveDefiniteKernel F hpd ξ]

end TauCeti
