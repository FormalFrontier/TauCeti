/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.ChiSquared
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
public import TauCeti.Probability.Distributions.Gamma.Beta

/-!
# Fisher's F law as a ratio of independent chi-squared variables

Fisher's F law is defined in `TauCeti/Probability/Distributions/FisherSnedecor/Basic.lean` as the
image of `betaMeasure (m / 2) (n / 2)` under the beta-to-F transformation
`u ↦ (n / m) * u / (1 - u)`.  This file justifies that definition by identifying the law with the
classical ratio it is named for: for independent chi-squared variables `U` and `V` with `m` and
`n` degrees of freedom, the variance ratio `(U / m) / (V / n)` has the law
`fisherSnedecorMeasure m n`.

The identification is stated in two parametrizations.  A chi-squared law with `k` degrees of
freedom is the gamma law of shape `k / 2` and rate `1 / 2`, and a ratio is unchanged by a common
scaling of its two arguments, so the gamma form `map_scaled_div_gammaMeasure` covers all gamma
variables with a common rate, at the price of writing the degrees of freedom as `2 * a` and
`2 * b`.  The chi-squared form `map_scaled_div_chiSquaredMeasure` is its specialisation to the
classical parameters, and is the statement to use for a variance ratio.

## Main results

* `TauCeti.Probability.map_scaled_div_gammaMeasure` — the pushforward of a product of gamma laws
  with a common rate along the scaled quotient is Fisher's F law;
* `TauCeti.Probability.map_scaled_div_chiSquaredMeasure` — the same statement for chi-squared
  laws, in the classical degrees-of-freedom parametrization;
* `TauCeti.Probability.hasLaw_fisherSnedecor_of_gammaMeasure` and
  `TauCeti.Probability.hasLaw_fisherSnedecor_of_chiSquared` — the random-variable forms.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 27.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

namespace Probability

variable {m n : ℝ}

/-! ### The pushforward of a product of gamma laws -/

/-- The variance ratio of two independent gamma variables with a common positive rate has Fisher's
F law with twice their shape parameters as degrees of freedom.  The common rate cancels, so it
does not appear in the conclusion. -/
theorem map_scaled_div_gammaMeasure {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map
        (fun z ↦ z.1 / (2 * a) / (z.2 / (2 * b))) =
      fisherSnedecorMeasure (2 * a) (2 * b) := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hb hr
  have ha2 : (0 : ℝ) < 2 * a := by linarith
  have hb2 : (0 : ℝ) < 2 * b := by linarith
  calc ((gammaMeasure a r).prod (gammaMeasure b r)).map
        (fun z ↦ z.1 / (2 * a) / (z.2 / (2 * b)))
      = ((gammaMeasure a r).prod (gammaMeasure b r)).map
        (fun z ↦ fisherSnedecorMap (2 * a) (2 * b) (z.1 / (z.1 + z.2))) := by
        refine (Measure.map_congr ?_).symm
        filter_upwards [ae_mem_prod_Ioi_gammaMeasure ha hb hr hr] with z hz
        exact fisherSnedecorMap_div_add ha2 hb2 hz.1 hz.2
    _ = (((gammaMeasure a r).prod (gammaMeasure b r)).map (fun z ↦ z.1 / (z.1 + z.2))).map
          (fisherSnedecorMap (2 * a) (2 * b)) := by
        rw [Measure.map_map (measurable_fisherSnedecorMap _ _) (by fun_prop)]
        rfl
    _ = fisherSnedecorMeasure (2 * a) (2 * b) := by
        have h2a : 2 * a / 2 = a := by ring
        have h2b : 2 * b / 2 = b := by ring
        rw [map_div_add_gammaMeasure ha hb hr, fisherSnedecorMeasure_eq_map ha2 hb2, h2a, h2b]

/-- The variance ratio of two independent chi-squared variables with positive degrees of freedom
`m` and `n` has the law `fisherSnedecorMeasure m n`.

This is the classical description of Fisher's F law, and the reason for the name of
`TauCeti.Probability.fisherSnedecorMeasure`. -/
theorem map_scaled_div_chiSquaredMeasure (hm : 0 < m) (hn : 0 < n) :
    ((chiSquaredMeasure m).prod (chiSquaredMeasure n)).map (fun z ↦ z.1 / m / (z.2 / n)) =
      fisherSnedecorMeasure m n := by
  have hm2 : 2 * (m / 2) = m := by ring
  have hn2 : 2 * (n / 2) = n := by ring
  have h := map_scaled_div_gammaMeasure (a := m / 2) (b := n / 2) (r := 1 / 2)
    (by linarith) (by linarith) (by norm_num)
  rw [hm2, hn2] at h
  rw [chiSquaredMeasure_eq_gammaMeasure hm, chiSquaredMeasure_eq_gammaMeasure hn]
  exact h

/-! ### Random-variable forms -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : Ω → ℝ}

/-- If `X` and `Y` are independent gamma variables with a common positive rate and shapes `a` and
`b`, then `(X / (2 * a)) / (Y / (2 * b))` has Fisher's F law with `2 * a` and `2 * b` degrees of
freedom. -/
theorem hasLaw_fisherSnedecor_of_gammaMeasure {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hXY : IndepFun X Y P) (hX : HasLaw X (gammaMeasure a r) P)
    (hY : HasLaw Y (gammaMeasure b r) P) :
    HasLaw (fun ω ↦ X ω / (2 * a) / (Y ω / (2 * b))) (fisherSnedecorMeasure (2 * a) (2 * b)) P := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hb hr
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hpair : HasLaw (fun ω ↦ (X ω, Y ω)) ((gammaMeasure a r).prod (gammaMeasure b r)) P :=
    hXY.hasLaw_prod hX hY
  have hratio : HasLaw (fun z : ℝ × ℝ ↦ z.1 / (2 * a) / (z.2 / (2 * b)))
      (fisherSnedecorMeasure (2 * a) (2 * b))
      ((gammaMeasure a r).prod (gammaMeasure b r)) :=
    ⟨by fun_prop, map_scaled_div_gammaMeasure ha hb hr⟩
  exact hratio.fun_comp hpair

/-- If `X` and `Y` are independent chi-squared variables with positive degrees of freedom `m` and
`n`, then the variance ratio `(X / m) / (Y / n)` has the law `fisherSnedecorMeasure m n`. -/
theorem hasLaw_fisherSnedecor_of_chiSquared (hm : 0 < m) (hn : 0 < n) (hXY : IndepFun X Y P)
    (hX : HasLaw X (chiSquaredMeasure m) P) (hY : HasLaw Y (chiSquaredMeasure n) P) :
    HasLaw (fun ω ↦ X ω / m / (Y ω / n)) (fisherSnedecorMeasure m n) P := by
  rw [chiSquaredMeasure_eq_gammaMeasure hm] at hX
  rw [chiSquaredMeasure_eq_gammaMeasure hn] at hY
  have hm2 : 2 * (m / 2) = m := by ring
  have hn2 : 2 * (n / 2) = n := by ring
  have h := hasLaw_fisherSnedecor_of_gammaMeasure (a := m / 2) (b := n / 2) (r := 1 / 2)
    (by linarith) (by linarith) (by norm_num) hXY hX hY
  rwa [hm2, hn2] at h

end Probability

end TauCeti
