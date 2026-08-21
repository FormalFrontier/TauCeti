/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generator.Basic
public import TauCeti.Analysis.Semigroups.ExponentialShift
import TauCeti.Analysis.Calculus.ExponentialSlope
import TauCeti.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Laplace-transform resolvents of strongly continuous semigroups

This file develops the pointwise Bochner-integral resolvent for a C₀-semigroup with a
growth bound, proves that it maps into the generator domain, and establishes the
right-inverse identity and norm estimate. It also packages the resolvent as a function of
the spectral parameter alone (`resolventFun`, extended by the junk value `0` below the
growth exponent), the form in which it is differentiated in
`TauCeti/Analysis/Semigroups/Resolvent/Deriv.lean`.

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
/-- The growth-bound estimate for a polynomially weighted Laplace-transform integrand:
`‖t^n e^{-λt} S(t) x‖ ≤ M ‖x‖ t^n e^{-(λ-ω)t}` for `t ≥ 0`. -/
lemma StronglyContinuousSemigroup.norm_pow_mul_resolvent_integrand_le
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (n : ℕ) (lambda : ℝ) (x : X) {t : ℝ} (ht : 0 ≤ t) :
    ‖(t ^ n * Real.exp (-(lambda * t))) • S.realOperator t x‖ ≤
      M * ‖x‖ * (t ^ n * Real.exp (-((lambda - ω) * t))) := by
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg ht n) (Real.exp_pos _).le)]
  calc
    t ^ n * Real.exp (-(lambda * t)) * ‖S.realOperator t x‖
        ≤ t ^ n * Real.exp (-(lambda * t)) *
            (M * Real.exp (ω * t) * ‖x‖) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (pow_nonneg ht _) (Real.exp_pos _).le)
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hb.bound t ht) (norm_nonneg x))
    _ = M * ‖x‖ * (t ^ n * Real.exp (-((lambda - ω) * t))) := by
        have h_exp_exponent : -((lambda - ω) * t) = -(lambda * t) + ω * t := by ring
        rw [h_exp_exponent, Real.exp_add]
        ring

omit [CompleteSpace X] in
/-- The growth-bound estimate for the integrand in the defining resolvent integral. -/
lemma StronglyContinuousSemigroup.norm_resolvent_integrand_le
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (x : X) {t : ℝ} (ht : 0 < t) :
    ‖Real.exp (-(lambda * t)) • S.realOperator t x‖ ≤
      M * ‖x‖ * Real.exp (-(lambda - ω) * t) := by
  simpa only [pow_zero, one_mul, neg_mul] using
    S.norm_pow_mul_resolvent_integrand_le hb 0 lambda x ht.le

private lemma StronglyContinuousSemigroup.aestronglyMeasurable_pow_mul_resolvent_integrand
    (S : StronglyContinuousSemigroup X) (n : ℕ) (lambda : ℝ) (x : X) :
    AEStronglyMeasurable
      (fun t : ℝ => (t ^ n * Real.exp (-(lambda * t))) • S.realOperator t x)
      (volume.restrict (Set.Ioi 0)) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  exact (by fun_prop : Continuous (fun t : ℝ => t ^ n * Real.exp (-(lambda * t)))).continuousOn.smul
    ((S.realOperator_continuousOn_Ici x).mono Set.Ioi_subset_Ici_self)

/-- The polynomially weighted Laplace-transform integrand `t^n e^{-λt} S(t) x` is integrable
on `(0, ∞)` for `ω < λ`. -/
lemma StronglyContinuousSemigroup.integrableOn_pow_mul_resolvent_integrand
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (n : ℕ) (lambda : ℝ) (hlam : ω < lambda) (x : X) :
    IntegrableOn
      (fun t => (t ^ n * Real.exp (-(lambda * t))) • S.realOperator t x) (Set.Ioi 0) := by
  have hpos : 0 < lambda - ω := by linarith
  unfold MeasureTheory.IntegrableOn
  apply MeasureTheory.Integrable.mono'
    ((integrableOn_pow_mul_exp_neg_mul_Ioi n hpos).integrable.const_mul (M * ‖x‖))
  · exact S.aestronglyMeasurable_pow_mul_resolvent_integrand n lambda x
  · apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t (ht : 0 < t)
    exact S.norm_pow_mul_resolvent_integrand_le hb n lambda x ht.le

/-- The integrand in the defining resolvent integral is integrable on `(0, ∞)` for `ω < λ`. -/
lemma StronglyContinuousSemigroup.integrableOn_resolvent_integrand
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) :
    IntegrableOn (fun t => Real.exp (-(lambda * t)) • S.realOperator t x) (Set.Ioi 0) := by
  simpa only [pow_zero, one_mul] using
    S.integrableOn_pow_mul_resolvent_integrand hb 0 lambda hlam x

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
          (S.integrableOn_resolvent_integrand hb lambda hlam x).integrable
          (S.integrableOn_resolvent_integrand hb lambda hlam y).integrable
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
              simpa only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, pow_one,
                one_div, neg_mul, zero_add] using integral_pow_mul_exp_neg_mul_Ioi 0 hpos
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
      (S.integrableOn_resolvent_integrand hb lambda hlam x).integrable]
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
      (S.integrableOn_resolvent_integrand hb lambda hlam x)
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
  -- rewrite via the shift identity, then take the limit term by term
  apply Filter.Tendsto.congr'
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [S.resolvent_shift_identity hb lambda hlam x ht, smul_sub, smul_smul, smul_smul]
  · set Rlx := S.resolvent hb lambda hlam x
    set f := fun t => Real.exp (-(lambda * t)) • S.realOperator t x
    apply Filter.Tendsto.sub
    · -- `(1/t * (e^{λt}-1)) • Rlx → λ • Rlx`
      apply Filter.Tendsto.smul _ tendsto_const_nhds
      exact (tendsto_exp_mul_sub_one_div lambda).congr
        (fun t => by ring)
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
          have hcont : ContinuousAt (fun t : ℝ => Real.exp (lambda * t)) 0 := by fun_prop
          simpa using hcont.tendsto
        exact hexp_cont.mono_left nhdsWithin_le_nhds
      · exact S.tendsto_average_resolvent_integrand lambda x

/-- The resolvent maps all of `X` into the domain of the generator
([EN] Thm. II.1.10(i), [Linares] eq. 0.15). -/
theorem StronglyContinuousSemigroup.resolvent_mem_domain
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (lambda : ℝ) (hlam : ω < lambda) (x : X) : (S.resolvent hb lambda hlam x) ∈ S.domain :=
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

/-! ## The resolvent as a function of the spectral parameter

`StronglyContinuousSemigroup.resolvent` carries the proof `ω < λ` as an argument, so it is not
a function of `λ` alone. The variant below drops that argument, extending the resolvent by the
junk value `0` on `λ ≤ ω`, which is what lets one speak of its limits, derivatives and
integrals in `λ`. -/

/-- The Laplace-transform resolvent of `S` as a function of the spectral parameter alone,
extended by the junk value `0` on `λ ≤ ω`. Unlike `StronglyContinuousSemigroup.resolvent` it
does not carry the proof `ω < λ`, so it can be differentiated in `λ`. -/
noncomputable def StronglyContinuousSemigroup.resolventFun
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M) (lambda : ℝ) :
    X →L[ℝ] X :=
  if h : ω < lambda then S.resolvent hb lambda h else 0

/-- Above the growth exponent, `resolventFun` is the Laplace-transform resolvent. -/
@[simp] theorem StronglyContinuousSemigroup.resolventFun_of_lt
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M) {lambda : ℝ}
    (h : ω < lambda) : S.resolventFun hb lambda = S.resolvent hb lambda h :=
  dite_eq_left h

/-- Below the growth exponent, `resolventFun` takes its junk value `0`. -/
@[simp] theorem StronglyContinuousSemigroup.resolventFun_of_le
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M) {lambda : ℝ}
    (h : lambda ≤ ω) : S.resolventFun hb lambda = 0 :=
  dite_eq_right (not_lt.mpr h)

/-- `resolventFun` in integral form. -/
theorem StronglyContinuousSemigroup.resolventFun_apply
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M) {lambda : ℝ}
    (h : ω < lambda) (x : X) :
    S.resolventFun hb lambda x
      = ∫ t in Set.Ioi 0, Real.exp (-(lambda * t)) • S.realOperator t x := by
  rw [S.resolventFun_of_lt hb h, S.resolvent_apply]

/-- The Hille--Yosida bound `‖R λ‖ ≤ M/(λ-ω)` for `resolventFun`. -/
theorem StronglyContinuousSemigroup.resolventFun_norm_le
    (S : StronglyContinuousSemigroup X) {ω M : ℝ} (hb : S.HasGrowthBound ω M) {lambda : ℝ}
    (h : ω < lambda) : ‖S.resolventFun hb lambda‖ ≤ M / (lambda - ω) := by
  rw [S.resolventFun_of_lt hb h]
  exact S.resolvent_norm_le hb lambda h

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

/-- The contraction resolvent is the `(0, 1)` case of the general semigroup resolvent. -/
theorem ContractionSemigroup.resolvent_eq_stronglyContinuousSemigroup_resolvent
    (S : ContractionSemigroup X) (lambda : ℝ) (hlambda : 0 < lambda) :
    S.resolvent lambda hlambda =
      S.toStronglyContinuousSemigroup.resolvent S.hasGrowthBound lambda
        (by simpa using hlambda) := by
  ext x
  rw [ContractionSemigroup.resolvent_apply,
    StronglyContinuousSemigroup.resolvent_apply]

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

/-- The resolvent of a contraction semigroup as a function of the spectral parameter alone,
the `(ω, M) = (0, 1)` case of `StronglyContinuousSemigroup.resolventFun`. -/
noncomputable def ContractionSemigroup.resolventFun (S : ContractionSemigroup X)
    (lambda : ℝ) : X →L[ℝ] X :=
  S.toStronglyContinuousSemigroup.resolventFun S.hasGrowthBound lambda

/-- The contraction resolvent function is the `(ω, M) = (0, 1)` case of
`StronglyContinuousSemigroup.resolventFun`. -/
theorem ContractionSemigroup.resolventFun_eq (S : ContractionSemigroup X) :
    S.resolventFun = S.toStronglyContinuousSemigroup.resolventFun S.hasGrowthBound :=
  -- the parentheses suppress the automatic `@[defeq]` tag, which an exported theorem may not
  -- carry when its proof unfolds an unexposed definition
  (rfl)

/-- For a positive parameter, `resolventFun` is the contraction resolvent. -/
@[simp] theorem ContractionSemigroup.resolventFun_of_pos (S : ContractionSemigroup X)
    {lambda : ℝ} (h : 0 < lambda) : S.resolventFun lambda = S.resolvent lambda h := by
  ext x
  rw [S.resolventFun_eq, S.toStronglyContinuousSemigroup.resolventFun_of_lt S.hasGrowthBound h,
    S.toStronglyContinuousSemigroup.resolvent_apply, S.resolvent_apply]

/-- For a nonpositive parameter, `resolventFun` takes its junk value `0`. -/
@[simp] theorem ContractionSemigroup.resolventFun_of_nonpos (S : ContractionSemigroup X)
    {lambda : ℝ} (h : lambda ≤ 0) : S.resolventFun lambda = 0 :=
  S.toStronglyContinuousSemigroup.resolventFun_of_le S.hasGrowthBound h

end TauCeti.Semigroups

end
