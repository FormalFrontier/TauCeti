/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Contractability

/-!
# The covariance structure of a contractable L² sequence

This file opens the Layer 3 (L²) lane of the Exchangeability roadmap
(`TauCetiRoadmap/Exchangeability/README.md`, "Layer 3: L² averaging library and the
standard-Borel de Finetti route"), whose first analytic input is the *uniform covariance
structure of a contractable L² sequence* (`contractable_covariance_structure`). It also
supplies the two Layer 3 preliminaries listed before it — "equality of means and integrals
from equal one-dimensional laws" and "equality of pair covariances from equal two-dimensional
laws".

For a real-valued contractable sequence, the one- and two-coordinate `IdentDistrib` facts in
`TauCeti.Probability.Exchangeability.Contractability` give the uniform first- and second-moment
structure:

* `Contractable.integral_coord_eq`: all coordinate means agree;
* `Contractable.variance_coord_eq`: all coordinate variances agree;
* `Contractable.covariance_eq_of_ne`: any two off-diagonal covariances agree,
  `cov[X i, X j; μ] = cov[X k, X l; μ]` for `i ≠ j` and `k ≠ l`.

The `IdentDistrib` and moment machinery is Mathlib's (`ProbabilityTheory.IdentDistrib`,
`ProbabilityTheory.covariance`, `ProbabilityTheory.variance`); the contractability input is
the Layer 0 API in `TauCeti.Probability.Exchangeability.Contractability`. No material from
`cameronfreer/exchangeability` is used: the source's L² lane carries the real-valued
statement through block averages, whereas this file records only the elementary
moment-uniformity that seeds it.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

variable {γ : Type*} [MeasurableSpace γ] [NormedAddCommGroup γ] [NormedSpace ℝ γ]
  [BorelSpace γ] {Z : ℕ → Ω → γ}

/-- **Equal means from contractability.** For a contractable process with values in a normed
real vector space, all coordinate expectations agree. -/
theorem Contractable.integral_coord_eq (hZ : Contractable μ Z)
    {i j : ℕ} (hi_meas : AEMeasurable (Z i) μ) (hj_meas : AEMeasurable (Z j) μ) :
    μ[Z i] = μ[Z j] :=
  (hZ.identDistrib_coord hi_meas hj_meas).integral_eq

section Real

variable {X : ℕ → Ω → ℝ}

/-- **Equal variances from contractability.** For a contractable real-valued process, all
coordinate variances agree. -/
theorem Contractable.variance_coord_eq (hX : Contractable μ X)
    {i j : ℕ} (hi_meas : AEMeasurable (X i) μ) (hj_meas : AEMeasurable (X j) μ) :
    Var[X i; μ] = Var[X j; μ] :=
  (hX.identDistrib_coord hi_meas hj_meas).variance_eq

/-- **Uniform covariances from contractability.** For a contractable real-valued process with
a.e. measurable coordinates, any two off-diagonal covariances agree:
`cov[X i, X j; μ] = cov[X k, X l; μ]` whenever `i < j` and `k < l`. -/
theorem Contractable.covariance_eq_of_lt (hX : Contractable μ X)
    {i j k l : ℕ} (hi_meas : AEMeasurable (X i) μ) (hj_meas : AEMeasurable (X j) μ)
    (hk_meas : AEMeasurable (X k) μ) (hl_meas : AEMeasurable (X l) μ)
    (hij : i < j) (hkl : k < l) :
    cov[X i, X j; μ] = cov[X k, X l; μ] := by
  let F : Ω → ℝ × ℝ := fun ω => (X i ω, X j ω)
  let G : Ω → ℝ × ℝ := fun ω => (X k ω, X l ω)
  have hpair : IdentDistrib F G μ μ :=
    hX.identDistrib_pair hi_meas hj_meas hk_meas hl_meas hij hkl
  have hF : HasLaw F (μ.map F) μ := ⟨hpair.aemeasurable_fst, rfl⟩
  have hG : HasLaw G (μ.map F) μ := hpair.hasLaw hF
  calc
    cov[X i, X j; μ] = cov[Prod.fst, Prod.snd; μ.map F] := by
      simpa [F] using
        hF.covariance_fun_comp measurable_fst.aemeasurable measurable_snd.aemeasurable
    _ = cov[X k, X l; μ] := by
      symm
      simpa [G] using
        hG.covariance_fun_comp measurable_fst.aemeasurable measurable_snd.aemeasurable

/-- **Uniform off-diagonal covariances from contractability.** For a contractable real-valued
process with a.e. measurable coordinates, any two off-diagonal covariances agree:
`cov[X i, X j; μ] = cov[X k, X l; μ]` whenever `i ≠ j` and `k ≠ l`. -/
theorem Contractable.covariance_eq_of_ne (hX : Contractable μ X)
    {i j k l : ℕ} (hi_meas : AEMeasurable (X i) μ) (hj_meas : AEMeasurable (X j) μ)
    (hk_meas : AEMeasurable (X k) μ) (hl_meas : AEMeasurable (X l) μ)
    (hij : i ≠ j) (hkl : k ≠ l) :
    cov[X i, X j; μ] = cov[X k, X l; μ] := by
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · rcases lt_or_gt_of_ne hkl with hkl_lt | hlk_lt
    · exact hX.covariance_eq_of_lt hi_meas hj_meas hk_meas hl_meas hij_lt hkl_lt
    · rw [covariance_comm (X k) (X l)]
      exact hX.covariance_eq_of_lt hi_meas hj_meas hl_meas hk_meas hij_lt hlk_lt
  · rw [covariance_comm (X i) (X j)]
    rcases lt_or_gt_of_ne hkl with hkl_lt | hlk_lt
    · exact hX.covariance_eq_of_lt hj_meas hi_meas hk_meas hl_meas hji_lt hkl_lt
    · rw [covariance_comm (X k) (X l)]
      exact hX.covariance_eq_of_lt hj_meas hi_meas hl_meas hk_meas hji_lt hlk_lt

/-- **The uniform covariance structure of a contractable L² sequence.** A contractable
real-valued process with `L²` coordinates has constant coordinate means and variances, and a
single common off-diagonal covariance: any two unequal-index pairs have equal covariance. This
is the seed of the Layer 3 L² route to de Finetti. -/
theorem contractable_covariance_structure (hX : Contractable μ X) (hX_L2 : ∀ n, MemLp (X n) 2 μ) :
    (∀ i j, μ[X i] = μ[X j]) ∧ (∀ i j, Var[X i; μ] = Var[X j; μ]) ∧
      (∀ i j k l, i ≠ j → k ≠ l → cov[X i, X j; μ] = cov[X k, X l; μ]) := by
  have hmeas : ∀ n, AEMeasurable (X n) μ := fun n => (hX_L2 n).aestronglyMeasurable.aemeasurable
  exact ⟨fun i j => hX.integral_coord_eq (hmeas i) (hmeas j),
    fun i j => hX.variance_coord_eq (hmeas i) (hmeas j),
    fun i j k l hij hkl => hX.covariance_eq_of_ne (hmeas i) (hmeas j) (hmeas k) (hmeas l)
      hij hkl⟩

end Real

end Probability

end TauCeti
