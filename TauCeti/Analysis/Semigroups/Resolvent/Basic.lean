/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generator.Basic
public import TauCeti.Analysis.Semigroups.ExponentialShift
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Laplace-transform resolvents of strongly continuous semigroups

This file develops the pointwise Bochner-integral resolvent for a C₀-semigroup with a
growth bound, proves that it maps into the generator domain, and establishes the
right-inverse identity and norm estimate.

## References
Ported and adapted (Apache 2.0) from `mrdouglasny/hille-yosida`; references include
Engel--Nagel, Linares, Pazy, Hille, and Yosida.
-/

public section

noncomputable section

open scoped Topology NNReal
open MeasureTheory

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-! ## The Resolvent (general growth bound) -/

open MeasureTheory

omit [CompleteSpace X] in
/-- The growth-bound estimate for the Laplace-transform integrand:
`‖e^{-λt} S(t) x‖ ≤ M ‖x‖ e^{-(λ-ω)t}` for `t > 0`. -/
private lemma StronglyContinuousSemigroup.norm_resolvent_integrand_le
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (x : X) {t : ℝ} (ht : 0 < t) :
    ‖Real.exp (-(lambda * t)) • S.realOperator t x‖ ≤
      M * ‖x‖ * Real.exp (-(lambda - ω) * t) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-(lambda * t)) * ‖(S.realOperator t) x‖
      ≤ Real.exp (-(lambda * t)) * (M * Real.exp (ω * t) * ‖x‖) := by
        gcongr
        exact le_trans (ContinuousLinearMap.le_opNorm _ _)
          (by gcongr; exact hb.bound t ht.le)
    _ = M * ‖x‖ * Real.exp (-(lambda - ω) * t) := by
        have h_exp_exponent : -(lambda - ω) * t = -(lambda * t) + ω * t := by ring
        rw [h_exp_exponent, Real.exp_add]
        ring

/-- The Laplace-transform integrand `e^{-λt} S(t) x` is integrable on `(0, ∞)` for
`ω < λ`. -/
lemma StronglyContinuousSemigroup.integrable_resolvent_integrand
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) :
    IntegrableOn (fun t => Real.exp (-(lambda * t)) • S.realOperator t x) (Set.Ioi 0) := by
  have hpos : 0 < lambda - ω := by linarith
  unfold MeasureTheory.IntegrableOn
  apply MeasureTheory.Integrable.mono'
    ((exp_neg_integrableOn_Ioi 0 hpos).smul (M * ‖x‖))
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.smul
    · exact (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg)).continuousOn
    · have h_cont : ContinuousOn (fun t => S.realOperator t x) (Set.Ici 0) :=
        fun t₀ ht₀ => S.realOperator_continuousWithinAt x t₀ ht₀
      exact h_cont.mono Set.Ioi_subset_Ici_self
  · apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t (ht : 0 < t)
    simpa only [Pi.smul_apply, smul_eq_mul] using
      S.norm_resolvent_integrand_le hb lambda x ht

/-- The resolvent `R(λ) x = ∫₀^∞ e^{-λt} S(t)x dt` of a C₀-semigroup with growth bound
`(ω, M)`, for `λ > ω`. A pointwise `X`-valued Bochner integral (so it is well-defined for
the merely strongly continuous `t ↦ S t`), with built-in norm bound `‖R λ‖ ≤ M/(λ-ω)`. -/
noncomputable def StronglyContinuousSemigroup.resolvent
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) : X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := fun x =>
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(lambda * t)) • S.realOperator t x
      map_add' := fun x y => by
        simp only [ContinuousLinearMap.map_add, smul_add]
        exact integral_add
          (S.integrable_resolvent_integrand hb lambda hlam x)
          (S.integrable_resolvent_integrand hb lambda hlam y)
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, map_smul]
        have h : ∀ t : ℝ, Real.exp (-(lambda * t)) • c • (S.realOperator t) x =
            c • (Real.exp (-(lambda * t)) • (S.realOperator t) x) :=
          fun t => smul_comm _ c _
        simp_rw [h]
        exact integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ))) c
          (fun t => Real.exp (-(lambda * t)) • (S.realOperator t) x) }
    (M / (lambda - ω))
    (by
      have hpos : 0 < lambda - ω := by linarith
      intro x; simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ t in Set.Ioi 0, Real.exp (-(lambda * t)) • (S.realOperator t) x‖
          ≤ ∫ t in Set.Ioi 0, M * ‖x‖ * Real.exp (-(lambda - ω) * t) := by
            apply MeasureTheory.norm_integral_le_of_norm_le
            · exact (exp_neg_integrableOn_Ioi 0 hpos).integrable.const_mul (M * ‖x‖)
            · apply (ae_restrict_mem measurableSet_Ioi).mono
              intro t (ht : 0 < t)
              exact S.norm_resolvent_integrand_le hb lambda x ht
        _ = M / (lambda - ω) * ‖x‖ := by
            rw [MeasureTheory.integral_const_mul]
            have h_eval :
                ∫ t in Set.Ioi 0, Real.exp (-(lambda - ω) * t) = (lambda - ω)⁻¹ := by
              have h := integral_comp_mul_left_Ioi (fun t => Real.exp (-t)) 0 hpos
              simp only [mul_zero] at h
              simp only [neg_mul]
              rw [h, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one]
            rw [h_eval, div_eq_mul_inv]; ring)

/-- The resolvent in integral form (characteristic lemma). -/
theorem StronglyContinuousSemigroup.resolvent_apply
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) :
    S.resolvent hb lambda hlam x
      = ∫ t in Set.Ioi 0, Real.exp (-(lambda * t)) • S.realOperator t x := by
  rfl

/-! ## Resolvent-Generator Interface

The resolvent maps into the generator domain and satisfies the right-inverse identity
from [EN] Thm. II.1.10(i) / [Linares] eq. 0.15. -/

omit [CompleteSpace X] in
/-- Translation of set integral: `∫_{Ioi 0} f(t + h) = ∫_{Ioi h} f(u)`. -/
private lemma integral_comp_add_right_Ioi (f : ℝ → X) (h : ℝ) :
    ∫ t in Set.Ioi 0, f (t + h) = ∫ u in Set.Ioi h, f u := by
  -- Express set integrals as full integrals with indicators
  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  -- Key: indicator_{Ioi 0}(fun t => f(t+h))(t) = indicator_{Ioi h}(f)(t+h)
  have key : ∀ t, Set.indicator (Set.Ioi 0) (fun t => f (t + h)) t =
      Set.indicator (Set.Ioi h) f (t + h) := by
    intro t; simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h1 h2 h2 <;> [rfl; linarith; linarith; rfl]
  simp_rw [key]
  -- Apply translation invariance of Lebesgue measure
  exact MeasureTheory.integral_add_right_eq_self _ h

omit [CompleteSpace X] in
/-- Splitting `∫_{Ioi 0} = ∫_{Ioc 0 h} + ∫_{Ioi h}` for `h > 0`. -/
private lemma integral_Ioi_eq_Ioc_add_Ioi (f : ℝ → X) {h : ℝ} (hh : 0 < h)
    (hf : IntegrableOn f (Set.Ioi 0) volume) :
    ∫ t in Set.Ioi 0, f t = (∫ t in Set.Ioc 0 h, f t) + ∫ t in Set.Ioi h, f t := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hh)]
  have hd : Disjoint (Set.Ioc 0 h) (Set.Ioi h) :=
    Set.disjoint_left.mpr (fun _ ht1 ht2 => not_le.mpr ht2 ht1.2)
  exact MeasureTheory.setIntegral_union hd measurableSet_Ioi
    (hf.mono_set Set.Ioc_subset_Ioi_self)
    (hf.mono_set (Set.Ioi_subset_Ioi (le_of_lt hh)))

/-- The resolvent shift identity for a positive time increment. -/
private theorem StronglyContinuousSemigroup.resolvent_shift_identity
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) {h : ℝ} (hh : 0 < h) :
    S.realOperator h (S.resolvent hb lambda hlam x) - S.resolvent hb lambda hlam x =
      (Real.exp (lambda * h) - 1) • S.resolvent hb lambda hlam x -
      Real.exp (lambda * h) •
        ∫ u in Set.Ioc 0 h, Real.exp (-(lambda * u)) • S.realOperator u x := by
  set Rlx := S.resolvent hb lambda hlam x
  set f := fun t => Real.exp (-(lambda * t)) • S.realOperator t x
  have h_push : S.realOperator h Rlx = Real.exp (lambda * h) • ∫ u in Set.Ioi h, f u := by
    have hRlx : Rlx = ∫ t in Set.Ioi 0, f t := S.resolvent_apply hb lambda hlam x
    rw [hRlx, ← ContinuousLinearMap.integral_comp_comm _
      (S.integrable_resolvent_integrand hb lambda hlam x)]
    have h_eq : ∀ t ∈ Set.Ioi (0 : ℝ),
        (S.realOperator h) (f t) = Real.exp (lambda * h) • f (t + h) := by
      intro t ht
      simp only [f, ContinuousLinearMap.map_smul]
      have h_time_add_comm : h + t = t + h := add_comm h t
      rw [← ContinuousLinearMap.comp_apply,
          ← S.realOperator_add h t (le_of_lt hh) (le_of_lt (Set.mem_Ioi.mp ht)),
          h_time_add_comm]
      symm; rw [← mul_smul, ← Real.exp_add]; congr 1; ring_nf
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_eq]
    rw [integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ)))]
    congr 1
    exact integral_comp_add_right_Ioi f h
  -- Step 2: split `∫_{Ioi h} = Rlx - ∫_{Ioc 0 h} f`
  have h_split : ∫ u in Set.Ioi h, f u = Rlx - ∫ u in Set.Ioc 0 h, f u := by
    have hsplit := integral_Ioi_eq_Ioc_add_Ioi f hh
      (S.integrable_resolvent_integrand hb lambda hlam x)
    have hRlx : Rlx = ∫ t in Set.Ioi 0, f t := S.resolvent_apply hb lambda hlam x
    rw [hRlx, hsplit]; abel
  -- Step 3: combine into the key identity
  rw [h_push, h_split]
  simp only [smul_sub, sub_smul, one_smul]
  abel

/-- The integral average `(1/t) • ∫_{(0,t]} e^{-λu} S(u)x du` of the resolvent integrand
tends to `x` as `t → 0⁺`. -/
private theorem StronglyContinuousSemigroup.tendsto_average_resolvent_integrand
    (S : StronglyContinuousSemigroup X) (lambda : ℝ) (x : X) :
    Filter.Tendsto
      (fun t => (1 / t) • ∫ u in Set.Ioc 0 t, Real.exp (-(lambda * u)) • S.realOperator u x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
  let T := S.expShift lambda
  have h := T.tendsto_average_orbit_zero x
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have hu_nonneg : 0 ≤ u := hu.1.le
  exact S.expShift_realOperator_apply_of_nonneg lambda u hu_nonneg x


/-- The generator difference quotient for `R(λ)x` converges to `λ R(λ)x - x`. -/
private theorem StronglyContinuousSemigroup.resolvent_generator_tendsto
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) :
    Filter.Tendsto (fun t => (1 / t) • (S.realOperator t (S.resolvent hb lambda hlam x) -
      S.resolvent hb lambda hlam x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (lambda • S.resolvent hb lambda hlam x - x)) := by
  -- the slope `(e^{λt}-1)/t → λ` from the derivative of `exp` at `0`
  have hderiv : HasDerivAt (fun t => Real.exp (lambda * t)) lambda 0 := by
    have h := (Real.hasDerivAt_exp (lambda * 0)).comp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_mul lambda)
    simp only [Real.exp_zero, mul_zero, one_mul, mul_one, Function.comp_def] at h
    exact h
  -- rewrite via the shift identity, then take the limit term by term
  apply Filter.Tendsto.congr'
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [S.resolvent_shift_identity hb lambda hlam x ht, smul_sub, smul_smul, smul_smul]
  · set Rlx := S.resolvent hb lambda hlam x
    set f := fun t => Real.exp (-(lambda * t)) • S.realOperator t x
    apply Filter.Tendsto.sub
    · -- `(1/t * (e^{λt}-1)) • Rlx → λ • Rlx`
      apply Filter.Tendsto.smul _ tendsto_const_nhds
      have := hderiv.tendsto_slope_zero_right
      simp only [zero_add, Real.exp_zero, mul_zero] at this
      exact this.congr (fun t => by simp only [smul_eq_mul]; ring)
    · -- `(1/t * e^{λt}) • ∫_{Ioc 0 t} f → 1 • x = x`
      have h_one_smul_x : x = (1 : ℝ) • x := (one_smul ℝ x).symm
      rw [h_one_smul_x]
      have h_average_scale : ∀ t,
          (1 / t * Real.exp (lambda * t)) • ∫ u in Set.Ioc 0 t, f u =
            Real.exp (lambda * t) • ((1 / t) • ∫ u in Set.Ioc 0 t, f u) := by
        intro t
        have h_scale_comm : 1 / t * Real.exp (lambda * t) =
            Real.exp (lambda * t) * (1 / t) := by ring
        rw [h_scale_comm, mul_smul]
      simp_rw [h_average_scale]
      apply Filter.Tendsto.smul
      · have hexp_cont : Filter.Tendsto (fun t => Real.exp (lambda * t))
            (nhds 0) (nhds 1) := by
          have := hderiv.continuousAt.tendsto
          simpa using this
        exact hexp_cont.mono_left nhdsWithin_le_nhds
      · exact S.tendsto_average_resolvent_integrand lambda x

/-- The resolvent maps all of `X` into the domain of the generator
([EN] Thm. II.1.10(i), [Linares] eq. 0.15). -/
theorem StronglyContinuousSemigroup.resolvent_mem_domain
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) :
    (S.resolvent hb lambda hlam x) ∈ S.domain :=
  (S.mem_domain_iff_tendsto _).mpr ⟨_, S.resolvent_generator_tendsto hb lambda hlam x⟩

/-- The fundamental resolvent identity: `(λI - A) R(λ) x = x`. -/
theorem StronglyContinuousSemigroup.resolventRightInv
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) :
    lambda • S.resolvent hb lambda hlam x
      - S.generator
          ⟨S.resolvent hb lambda hlam x, by
            rw [S.generator_domain]
            exact S.resolvent_mem_domain hb lambda hlam x⟩ = x := by
  -- `A (R λ x) = λ • R λ x - x` reads off the generator value from the known limit.
  rw [S.generator_eq_of_tendsto (S.resolvent_mem_domain hb lambda hlam x)
    (S.resolvent_generator_tendsto hb lambda hlam x)]
  abel

/-- **Hille–Yosida resolvent bound**: `‖R λ‖ ≤ M/(λ-ω)` for a C₀ semigroup with
growth bound `(ω, M)` and `λ > ω` (Hille 1948, Yosida 1948; Engel–Nagel Ch. II). -/
theorem StronglyContinuousSemigroup.resolvent_norm_le
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) :
    ‖S.resolvent hb lambda hlam‖ ≤ M / (lambda - ω) :=
  LinearMap.mkContinuous_norm_le _
    (div_nonneg (by linarith [hb.one_le]) (by linarith)) _

/-! ## Contraction-semigroup specializations (`M = 1`, `ω = 0`) -/

/-- The resolvent of a contraction semigroup, the `(0, 1)` case. -/
noncomputable def ContractionSemigroup.resolvent (S : ContractionSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) : X →L[ℝ] X :=
  S.toStronglyContinuousSemigroup.resolvent S.hasGrowthBound lambda (by simpa using hlam)

/-- The contraction resolvent unfolds to the Laplace-transform integral
`R(λ) x = ∫₀^∞ e^{-λt} S(t)x dt`, the `(0, 1)` case. -/
theorem ContractionSemigroup.resolvent_apply (S : ContractionSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) (x : X) :
    S.resolvent lambda hlam x
      = ∫ t in Set.Ioi 0, Real.exp (-(lambda * t)) • S.realOperator t x := by
  rfl

/-- The contraction resolvent maps into the generator domain. -/
theorem ContractionSemigroup.resolvent_mem_domain (S : ContractionSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) (x : X) :
    (S.resolvent lambda hlam x) ∈ S.toStronglyContinuousSemigroup.domain :=
  S.toStronglyContinuousSemigroup.resolvent_mem_domain S.hasGrowthBound lambda
    (by simpa using hlam) x

/-- The contraction resolvent right-inverse identity `(λI - A) R(λ) x = x`, the `(0, 1)` case
(cf. `StronglyContinuousSemigroup.resolventRightInv`). -/
theorem ContractionSemigroup.resolventRightInv (S : ContractionSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) (x : X) :
    lambda • S.resolvent lambda hlam x
      - S.toStronglyContinuousSemigroup.generator
          ⟨S.resolvent lambda hlam x, by
            rw [StronglyContinuousSemigroup.generator_domain]
            exact S.resolvent_mem_domain lambda hlam x⟩ = x :=
  S.toStronglyContinuousSemigroup.resolventRightInv S.hasGrowthBound lambda
    (by simpa using hlam) x

/-- The contraction resolvent bound `‖R λ‖ ≤ 1/λ`, the `(0, 1)` case. -/
theorem ContractionSemigroup.resolvent_norm_le (S : ContractionSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) :
    ‖S.resolvent lambda hlam‖ ≤ 1 / lambda := by
  have h := S.toStronglyContinuousSemigroup.resolvent_norm_le S.hasGrowthBound lambda
    (by simpa using hlam)
  rw [sub_zero] at h
  exact h

end TauCeti.Semigroups

end
