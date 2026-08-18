/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import TauCeti.Analysis.PositiveDefinite.FourierAtom
-- The remaining imports are proof-only: Fourier inversion, the characteristic-function API, the
-- Lévy continuity theorem, Prokhorov's theorem with the Lévy–Prokhorov metrizability of the
-- space of probability measures, sequential compactness, the Fourier-convention bridge with its
-- uniqueness theorem, the nonnegativity and integrability of the Fourier transform of a
-- positive-definite function, Gaussian regularization, and the kernel Cauchy–Schwarz bounds.
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences
import TauCeti.Analysis.Bochner.Fourier.Convention
import TauCeti.Analysis.Bochner.Fourier.Nonneg
import TauCeti.Analysis.Bochner.Gaussian.Regularization
import TauCeti.Analysis.PositiveDefinite.Kernel.Bounds

/-!
# Bochner's theorem

A function `F : V → ℂ` on a finite-dimensional real inner-product space is continuous and
positive definite if and only if it is the Fourier-convention transform
`v ↦ ∫ q, fourierAtom v q ∂μ` of a unique finite Borel measure `μ` on `V`. This file assembles
the final statement from the two analytic predecessors, names the representing measure
`TauCeti.bochnerMeasure`, and records its transform, total mass, scaling, and normalization.

Positive definiteness is `TauCeti.IsPositiveDefiniteSub`, the classical subtraction-form
predicate on an additive commutative group; the equivalent positive-semidefiniteness of the
subtraction kernel `(a, b) ↦ F (a - b)` is available through
`TauCeti.isPositiveDefiniteSub_iff_posSemidef` and is the hypothesis of the kernel-form
statement `TauCeti.bochner_posSemidef`.

The `L¹` case comes first: for a continuous *integrable* positive-definite `F`, the finite
measure with density `(𝓕⁻ F).re` against Lebesgue measure recovers `F` as the
Fourier-convention transform `∫ q, fourierAtom · q` of the measure, by Fourier inversion; this
is the representing measure of Bochner's theorem, given explicitly.

Existence is proved by Gaussian regularization and a compactness argument. If `F 0 = 0` the
kernel Cauchy–Schwarz inequality forces `F = 0` and the zero measure represents. Otherwise,
after normalizing to `G 0 = 1`, the regularizations `G_n = G · exp (-‖·‖²/(n+1))` are
integrable positive-definite functions, each represented by an explicit probability measure
`ν_n` with density `(𝓕⁻ G_n).re` (`integral_fourierAtom_withDensity_re_fourierInv`).
The characteristic functions of the `ν_n` converge pointwise to a rescaling of `G`, which is
continuous at `0`, so the family is tight by the Lévy continuity theorem; Prokhorov's theorem
and the metrizability of the space of probability measures extract a weakly convergent
subsequence, whose limit represents `G` by passing to the limit in the characteristic
functions. Uniqueness is `Measure.ext_of_forall_integral_fourierAtom_eq` from
`Fourier/Convention.lean`.

Adapted (Apache 2.0) from the Bochner–Minlos formalization by Michael R. Douglas
(https://github.com/mrdouglasny/bochner, revision `08eb302`), source file `Bochner/Main.lean`;
the positive-definiteness hypotheses are restated through `TauCeti.IsPositiveDefiniteSub` and
`Matrix.PosSemidef`, and the representation is stated in the `fourierAtom` convention rather
than through `MeasureTheory.charFun`.

## Main declarations

* `TauCeti.integral_fourierAtom_withDensity_re_fourierInv`: the measure
  `volume.withDensity (ENNReal.ofReal (𝓕⁻ F ·).re)` recovers `F` through the Fourier atom — the
  `L¹` case of Bochner's theorem.
* `TauCeti.exists_isFiniteMeasure_integral_fourierAtom_eq`:
  existence of a finite representing measure for a continuous positive-definite function.
* `TauCeti.bochner`, with the Euclidean specialization
  `TauCeti.bochner_euclideanSpace`:
  **Bochner's theorem**, the equivalence between continuity together with positive definiteness
  and the unique Fourier representation.
* `TauCeti.bochner_posSemidef`: the same equivalence with positive definiteness written as
  positive semidefiniteness of the subtraction kernel.
* `TauCeti.bochner_probabilityMeasure`: the normalized form — a positive-definite function with
  `F 0 = 1` is the transform of a unique probability measure.
* `TauCeti.bochnerMeasure`: the representing measure itself, with
  `TauCeti.integral_fourierAtom_bochnerMeasure` (its transform),
  `TauCeti.eq_bochnerMeasure` (uniqueness),
  `TauCeti.bochnerMeasure_eq_zero_of_not` (the fallback branch),
  `TauCeti.bochnerMeasure_univ` and
  `TauCeti.bochnerMeasure_real_univ` (total mass),
  `TauCeti.bochnerMeasure_const_mul` and `TauCeti.bochnerMeasure_add` (nonnegative real scaling
  and additivity), and `TauCeti.isProbabilityMeasure_bochnerMeasure` (normalization).

## References

* S. Bochner, *Vorlesungen über Fouriersche Integrale*, Akademische Verlagsgesellschaft (1932).
* W. Rudin, *Fourier Analysis on Groups* (1962), Theorem 1.4.3.
* Roadmap: TauCetiRoadmap/OneParameterSemigroups/README.md, Part C (Bochner milestone).
-/

public section

open Filter MeasureTheory
open scoped ComplexOrder FourierTransform Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ### The L¹ representing measure -/

/-- **Bochner recovery for `L¹` positive-definite functions.** A continuous integrable function
`F` with positive-definite subtraction kernel is the Fourier-convention transform
`v ↦ ∫ q, fourierAtom v q ∂μ` of the finite measure `μ` with density `(𝓕⁻ F).re` against
Lebesgue measure. The identity is Fourier inversion `𝓕 (𝓕⁻ F) = F`, using that `𝓕⁻ F` is real
and nonnegative. Rudin, *Fourier Analysis on Groups*, §1.4; Folland, §4.2. -/
theorem integral_fourierAtom_withDensity_re_fourierInv (F : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) (v : V) :
    ∫ q, fourierAtom v q ∂(volume.withDensity fun ξ => ENNReal.ofReal (𝓕⁻ F ξ).re) = F v := by
  have hft_int : Integrable (𝓕 F) :=
    integrable_fourier_of_posSemidef F hpd hint hcont
  have hre : ∀ ξ, 0 ≤ (𝓕⁻ F ξ).re :=
    fourierInv_re_nonneg_of_posSemidef F hpd hint hcont
  have hreal : ∀ ξ, 𝓕⁻ F ξ = ((𝓕⁻ F ξ).re : ℂ) :=
    fourierInv_eq_re_of_posSemidef F hpd hint
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (measurable_ofReal_re_fourierInv hint).aemeasurable
    (ae_of_all _ fun ξ => ENNReal.ofReal_lt_top) _]
  calc ∫ q, (ENNReal.ofReal (𝓕⁻ F q).re).toReal • fourierAtom v q
      = ∫ q, fourierAtom v q * 𝓕⁻ F q := by
        refine integral_congr_ae (ae_of_all _ fun q => ?_)
        simp only [ENNReal.toReal_ofReal (hre q), Complex.real_smul]
        rw [← hreal q, mul_comm]
    _ = 𝓕 (𝓕⁻ F) v := (fourier_eq_integral_fourierAtom_mul (𝓕⁻ F) v).symm
    _ = F v := by rw [hcont.fourier_fourierInv_eq hint hft_int]

/-! ### The normalized existence argument -/

/-- **Existence, normalized case.** A continuous function `G` with positive-definite
subtraction kernel and `G 0 = 1` is the Fourier-convention transform of a probability
measure: Gaussian regularization, tightness via Lévy continuity, and Prokhorov compactness. -/
private theorem exists_probabilityMeasure_integral_fourierAtom_eq {G : V → ℂ}
    (hpd : Matrix.PosSemidef fun a b : V => G (a - b))
    (hcont : Continuous G) (hG0 : G 0 = 1) :
    ∃ μ : Measure V, IsProbabilityMeasure μ ∧ ∀ v, ∫ q, fourierAtom v q ∂μ = G v := by
  -- the regularization parameters `ε n → 0⁺`
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε_pos : ∀ n, 0 < ε n := fun n => by positivity
  have hε_lim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- the explicit representing measures of the regularizations
  set ν : ℕ → Measure V := fun n =>
    volume.withDensity fun ξ => ENNReal.ofReal (𝓕⁻ (gaussianRegularize G (ε n)) ξ).re
  have hGn_pd : ∀ n, Matrix.PosSemidef
      fun a b : V => gaussianRegularize G (ε n) (a - b) := fun n =>
    posSemidef_gaussianRegularize hpd (hε_pos n).le
  have hGn_int : ∀ n, Integrable (gaussianRegularize G (ε n)) := fun n =>
    integrable_gaussianRegularize (norm_apply_le_map_zero_re_of_posSemidef hpd)
      hcont.aestronglyMeasurable (hε_pos n)
  have hGn_cont : ∀ n, Continuous (gaussianRegularize G (ε n)) := fun n =>
    continuous_gaussianRegularize hcont (ε n)
  have hν_rep : ∀ n v, ∫ q, fourierAtom v q ∂(ν n) = gaussianRegularize G (ε n) v := fun n v =>
    integral_fourierAtom_withDensity_re_fourierInv _ (hGn_pd n) (hGn_int n) (hGn_cont n) v
  have hν_prob : ∀ n, IsProbabilityMeasure (ν n) := by
    intro n
    have : IsFiniteMeasure (ν n) := isFiniteMeasure_withDensity_ofReal
      (integrable_fourierInv_of_posSemidef _ (hGn_pd n) (hGn_int n)
        (hGn_cont n)).re.2
    -- at `v = 0` the Fourier atom is `1` and the regularization keeps `G 0 = 1`, so the
    -- representation reads `μ.real univ = 1`
    have h0 := hν_rep n 0
    simp only [fourierAtom_zero_left, gaussianRegularize_apply_zero, hG0, integral_const,
      Complex.real_smul, mul_one, Complex.ofReal_eq_one] at h0
    exact isProbabilityMeasure_iff_real.mpr h0
  -- the pointwise limit of the characteristic functions
  set f : V → ℂ := fun t => G ((-2 * Real.pi)⁻¹ • t) with hf_def
  have hchar : ∀ n t, charFun (ν n) t =
      gaussianRegularize G (ε n) ((-2 * Real.pi)⁻¹ • t) := by
    intro n t
    have h := integral_fourierAtom_eq_charFun_neg_two_pi_smul (μ := ν n)
      ((-2 * Real.pi)⁻¹ • t)
    rw [hν_rep n, smul_smul, mul_inv_cancel₀ neg_two_pi_ne_zero, one_smul] at h
    exact h.symm
  have hconv : ∀ t, Tendsto (fun n => charFun (ν n) t) atTop (𝓝 (f t)) := by
    intro t
    simp only [hchar]
    exact (tendsto_gaussianRegularize G ((-2 * Real.pi)⁻¹ • t)).comp hε_lim
  -- tightness, Prokhorov compactness, and a weakly convergent subsequence
  have hf_cont : ContinuousAt f 0 := (hcont.comp (continuous_const_smul _)).continuousAt
  have htight : IsTightMeasureSet (Set.range ν) :=
    isTightMeasureSet_of_tendsto_charFun hf_cont hconv
  set P : ℕ → ProbabilityMeasure V := fun n => ⟨ν n, hν_prob n⟩
  have hcompact : IsCompact (closure (Set.range P)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1
    ext m
    constructor
    · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨P n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨μ₀, -, φ, hφ, hlim⟩ :=
    hcompact.tendsto_subseq fun n => subset_closure (Set.mem_range_self n)
  -- identify the characteristic function of the limit
  have hsub := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim
  have hcharlim : ∀ t, charFun (μ₀ : Measure V) t = f t := fun t =>
    tendsto_nhds_unique (hsub t) ((hconv t).comp hφ.tendsto_atTop)
  refine ⟨(μ₀ : Measure V), μ₀.prop, fun v => ?_⟩
  rw [integral_fourierAtom_eq_charFun_neg_two_pi_smul, hcharlim]
  simp only [hf_def]
  rw [smul_smul, inv_mul_cancel₀ neg_two_pi_ne_zero, one_smul]

/-! ### Bochner's theorem -/

/-- **Existence half of Bochner's theorem.** A continuous positive-definite function `F` on a
finite-dimensional real inner-product space is the Fourier-convention transform
`v ↦ ∫ q, fourierAtom v q ∂μ` of a finite Borel measure `μ`. Rudin, *Fourier Analysis on Groups*,
Theorem 1.4.3. -/
theorem exists_isFiniteMeasure_integral_fourierAtom_eq
    (F : V → ℂ) (hcont : Continuous F) (hpd : IsPositiveDefiniteSub F) :
    ∃ μ : Measure V, IsFiniteMeasure μ ∧ ∀ v, F v = ∫ q, fourierAtom v q ∂μ := by
  have h0re : 0 ≤ (F 0).re := hpd.map_zero_re_nonneg
  have h0eq : F 0 = ((F 0).re : ℂ) := hpd.map_zero_eq_ofReal_re
  rcases h0re.eq_or_lt with hzero | hpos
  · -- degenerate case: `F 0 = 0` forces `F = 0`, represented by the zero measure
    have hFv : ∀ v : V, F v = 0 :=
      hpd.apply_eq_zero_of_map_zero_re_eq_zero hzero.symm
    exact ⟨0, inferInstance, fun v => by simp [hFv v]⟩
  · -- main case: normalize to value `1` at the origin and scale the measure back
    set c : ℝ := (F 0).re
    have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hF0 : F 0 ≠ 0 := by
      rw [h0eq]
      exact hcne
    set G : V → ℂ := fun v => (c : ℂ)⁻¹ * F v with hG_def
    have hG_pd : IsPositiveDefiniteSub G := hpd.normalize
    have hG_cont : Continuous G := continuous_const.mul hcont
    have hG0 : G 0 = 1 := hpd.normalize_apply_zero hF0
    obtain ⟨μ, hμ_prob, hμ_rep⟩ :=
      exists_probabilityMeasure_integral_fourierAtom_eq hG_pd.posSemidef hG_cont hG0
    refine ⟨ENNReal.ofReal c • μ, Measure.smul_finite _ ENNReal.ofReal_ne_top, fun v => ?_⟩
    rw [integral_smul_measure, ENNReal.toReal_ofReal hpos.le, hμ_rep v, hG_def,
      Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]

/-- **Converse half of Bochner's theorem.** The Fourier-convention transform of a finite Borel
measure is continuous and positive definite. -/
theorem continuous_and_isPositiveDefiniteSub_of_integral_fourierAtom_eq {F : V → ℂ}
    (μ : Measure V) [IsFiniteMeasure μ] (hrep : ∀ v, F v = ∫ q, fourierAtom v q ∂μ) :
    Continuous F ∧ IsPositiveDefiniteSub F := by
  refine ⟨?_, IsPositiveDefiniteSub.of_posSemidef ?_⟩
  · rw [funext hrep]
    exact continuous_fourierConventionCharFun
  · have hfun : (fun a b : V => F (a - b)) =
        fun a b : V => ∫ q, fourierAtom (a - b) q ∂μ := by
      funext a b
      exact hrep (a - b)
    rw [hfun]
    exact posSemidef_fourierConventionCharFun_sub

/-- **Bochner's theorem.** A function `F` on a finite-dimensional real inner-product space is
continuous and positive definite if and only if it is the Fourier-convention transform
`v ↦ ∫ q, fourierAtom v q ∂μ` of a unique finite Borel measure `μ`. Bochner (1932); Rudin,
*Fourier Analysis on Groups*, Theorem 1.4.3. -/
theorem bochner (F : V → ℂ) :
    (Continuous F ∧ IsPositiveDefiniteSub F) ↔
      ∃! μ : Measure V, IsFiniteMeasure μ ∧ ∀ v, F v = ∫ q, fourierAtom v q ∂μ := by
  constructor
  · rintro ⟨hcont, hpd⟩
    obtain ⟨μ, hfin, hrep⟩ := exists_isFiniteMeasure_integral_fourierAtom_eq F hcont hpd
    refine ⟨μ, ⟨hfin, hrep⟩, ?_⟩
    rintro ν ⟨hνfin, hνrep⟩
    have := hfin
    have := hνfin
    exact Measure.ext_of_forall_integral_fourierAtom_eq
      fun v => (hνrep v).symm.trans (hrep v)
  · rintro ⟨μ, ⟨hfin, hrep⟩, -⟩
    have := hfin
    exact continuous_and_isPositiveDefiniteSub_of_integral_fourierAtom_eq μ hrep

/-- **Bochner's theorem, kernel form.** The subtraction kernel `(a, b) ↦ F (a - b)` of a
continuous function is positive semidefinite if and only if `F` is the Fourier-convention
transform of a unique finite Borel measure. This is `TauCeti.bochner` read through the
PD-function ↔ PD-kernel correspondence `TauCeti.isPositiveDefiniteSub_iff_posSemidef`. -/
theorem bochner_posSemidef (F : V → ℂ) :
    (Continuous F ∧ Matrix.PosSemidef fun a b : V => F (a - b)) ↔
      ∃! μ : Measure V, IsFiniteMeasure μ ∧ ∀ v, F v = ∫ q, fourierAtom v q ∂μ :=
  (and_congr_right fun _ => isPositiveDefiniteSub_iff_posSemidef.symm).trans (bochner F)

/-- **Bochner's theorem on `ℝᵈ`**: the specialization of `bochner` to Euclidean space. A
function on `EuclideanSpace ℝ (Fin d)` is continuous and positive definite if and only if it is
the Fourier transform of a unique finite positive measure. -/
theorem bochner_euclideanSpace (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℂ) :
    (Continuous F ∧ IsPositiveDefiniteSub F) ↔
      ∃! μ : Measure (EuclideanSpace ℝ (Fin d)), IsFiniteMeasure μ ∧
        ∀ v, F v = ∫ q, fourierAtom v q ∂μ :=
  bochner F

/-- **Bochner's theorem for normalized functions.** A function is continuous, positive definite
and normalized by `F 0 = 1` if and only if it is the Fourier-convention transform of a unique
*probability* measure; this is the characteristic-function form of the theorem. Normalization is
part of the equivalence: a probability representation forces `F 0 = 1`. -/
theorem bochner_probabilityMeasure (F : V → ℂ) :
    (Continuous F ∧ IsPositiveDefiniteSub F ∧ F 0 = 1) ↔
      ∃! μ : Measure V, IsProbabilityMeasure μ ∧ ∀ v, F v = ∫ q, fourierAtom v q ∂μ := by
  constructor
  · rintro ⟨hcont, hpd, hF0⟩
    obtain ⟨μ, hprob, hrep⟩ :=
      exists_probabilityMeasure_integral_fourierAtom_eq hpd.posSemidef hcont hF0
    refine ⟨μ, ⟨hprob, fun v => (hrep v).symm⟩, ?_⟩
    rintro ν ⟨hνprob, hνrep⟩
    have := hprob
    have := hνprob
    exact Measure.ext_of_forall_integral_fourierAtom_eq
      fun v => (hνrep v).symm.trans (hrep v).symm
  · rintro ⟨μ, ⟨hprob, hrep⟩, -⟩
    have := hprob
    obtain ⟨hcont, hpd⟩ := continuous_and_isPositiveDefiniteSub_of_integral_fourierAtom_eq μ hrep
    refine ⟨hcont, hpd, ?_⟩
    rw [hrep 0]
    simp

/-! ### The representing measure -/

open Classical in
/-- **The representing measure of Bochner's theorem**: the unique finite Borel measure whose
Fourier-convention transform is `F`, when `F` is continuous and positive definite, and the zero
measure otherwise. -/
noncomputable def bochnerMeasure (F : V → ℂ) : Measure V :=
  if h : Continuous F ∧ IsPositiveDefiniteSub F then ((bochner F).mp h).exists.choose else 0

variable {F : V → ℂ}

private theorem bochnerMeasure_rep (hcont : Continuous F) (hpd : IsPositiveDefiniteSub F) (v : V) :
    F v = ∫ q, fourierAtom v q ∂(bochnerMeasure F) := by
  classical
  rw [bochnerMeasure, dite_eq_left ⟨hcont, hpd⟩]
  exact ((bochner F).mp ⟨hcont, hpd⟩).exists.choose_spec.2 v

/-- Outside the hypotheses of Bochner's theorem the Bochner measure is `0`. -/
theorem bochnerMeasure_eq_zero_of_not (h : ¬(Continuous F ∧ IsPositiveDefiniteSub F)) :
    bochnerMeasure F = 0 := by
  classical
  rw [bochnerMeasure, dite_eq_right h]

/-- The Bochner measure of any function is finite: for a continuous positive-definite function
this is the finiteness of its representing measure, and otherwise the measure is `0`. -/
instance isFiniteMeasure_bochnerMeasure (F : V → ℂ) : IsFiniteMeasure (bochnerMeasure F) := by
  classical
  rw [bochnerMeasure]
  split
  · rename_i h
    exact ((bochner F).mp h).exists.choose_spec.1
  · infer_instance

/-- **The Bochner measure represents its function.** -/
theorem integral_fourierAtom_bochnerMeasure (hcont : Continuous F) (hpd : IsPositiveDefiniteSub F)
    (v : V) : ∫ q, fourierAtom v q ∂(bochnerMeasure F) = F v :=
  (bochnerMeasure_rep hcont hpd v).symm

/-- **Uniqueness of the Bochner measure.** Any finite Borel measure whose Fourier-convention
transform is `F` is the Bochner measure of `F`; no hypothesis on `F` is needed, since a function
represented by a finite measure is automatically continuous and positive definite. -/
theorem eq_bochnerMeasure (μ : Measure V) [IsFiniteMeasure μ]
    (hrep : ∀ v, F v = ∫ q, fourierAtom v q ∂μ) : μ = bochnerMeasure F := by
  obtain ⟨hcont, hpd⟩ := continuous_and_isPositiveDefiniteSub_of_integral_fourierAtom_eq μ hrep
  exact Measure.ext_of_forall_integral_fourierAtom_eq
    fun v => (hrep v).symm.trans (bochnerMeasure_rep hcont hpd v)

/-- The total mass of the Bochner measure is the value of the function at the origin. -/
theorem bochnerMeasure_real_univ (hcont : Continuous F) (hpd : IsPositiveDefiniteSub F) :
    (bochnerMeasure F).real Set.univ = (F 0).re := by
  have h0 := bochnerMeasure_rep hcont hpd 0
  simp only [fourierAtom_zero_left, integral_const, Complex.real_smul, mul_one] at h0
  rw [h0, Complex.ofReal_re]

/-- The total mass of the Bochner measure, as an extended nonnegative real. -/
theorem bochnerMeasure_univ (hcont : Continuous F) (hpd : IsPositiveDefiniteSub F) :
    bochnerMeasure F Set.univ = ENNReal.ofReal (F 0).re := by
  rw [← bochnerMeasure_real_univ hcont hpd, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **The normalized case.** The Bochner measure of a positive-definite function with `F 0 = 1`
is a probability measure. -/
theorem isProbabilityMeasure_bochnerMeasure (hcont : Continuous F)
    (hpd : IsPositiveDefiniteSub F) (hF0 : F 0 = 1) :
    IsProbabilityMeasure (bochnerMeasure F) :=
  isProbabilityMeasure_iff_real.mpr <| by
    rw [bochnerMeasure_real_univ hcont hpd, hF0, Complex.one_re]

/-- The Bochner measure of the zero function is the zero measure. -/
@[simp]
theorem bochnerMeasure_zero : bochnerMeasure (fun _ : V => (0 : ℂ)) = 0 :=
  (eq_bochnerMeasure 0 fun v => by simp).symm

/-- Scaling a function by a nonnegative real scales its Bochner measure by the same factor. No
hypothesis on `F` is needed: for a positive factor the two sides are simultaneously outside the
hypotheses of Bochner's theorem, where both are `0`. -/
theorem bochnerMeasure_const_mul (F : V → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    bochnerMeasure (fun v => (r : ℂ) * F v) = ENNReal.ofReal r • bochnerMeasure F := by
  rcases hr.eq_or_lt with rfl | hpos
  · simp
  by_cases h : Continuous F ∧ IsPositiveDefiniteSub F
  · have hfin : IsFiniteMeasure (ENNReal.ofReal r • bochnerMeasure F) :=
      Measure.smul_finite _ ENNReal.ofReal_ne_top
    refine (eq_bochnerMeasure (F := fun v => (r : ℂ) * F v) _ fun v => ?_).symm
    rw [integral_smul_measure, ENNReal.toReal_ofReal hpos.le, Complex.real_smul,
      integral_fourierAtom_bochnerMeasure h.1 h.2]
  · -- rescaling by `r > 0` is invertible, so `r • F` fails Bochner's hypotheses along with `F`
    rw [bochnerMeasure_eq_zero_of_not h, smul_zero, bochnerMeasure_eq_zero_of_not]
    rintro ⟨hrcont, hrpd⟩
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hFeq : (fun v => ((r : ℂ)⁻¹ * ((r : ℂ) * F v))) = F := by
      funext v
      rw [← mul_assoc, inv_mul_cancel₀ hrne, one_mul]
    have hcont : Continuous fun v => (r : ℂ)⁻¹ * ((r : ℂ) * F v) := continuous_const.mul hrcont
    have hpd : IsPositiveDefiniteSub fun v => (r : ℂ)⁻¹ * ((r : ℂ) * F v) :=
      hrpd.const_mul (inv_nonneg.mpr ((RCLike.ofReal_nonneg (K := ℂ)).mpr hpos.le))
    rw [hFeq] at hcont hpd
    exact h ⟨hcont, hpd⟩

/-- The Bochner measure of a sum of continuous positive-definite functions is the sum of their
Bochner measures. -/
theorem bochnerMeasure_add {H : V → ℂ} (hFcont : Continuous F) (hFpd : IsPositiveDefiniteSub F)
    (hHcont : Continuous H) (hHpd : IsPositiveDefiniteSub H) :
    bochnerMeasure (fun v => F v + H v) = bochnerMeasure F + bochnerMeasure H := by
  refine (eq_bochnerMeasure (F := fun v => F v + H v) _ fun v => ?_).symm
  rw [integral_add_measure (integrable_fourierAtom _ v) (integrable_fourierAtom _ v),
    integral_fourierAtom_bochnerMeasure hFcont hFpd,
    integral_fourierAtom_bochnerMeasure hHcont hHpd]

end TauCeti
