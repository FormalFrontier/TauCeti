/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Exponential
public import TauCeti.Probability.Distributions.Gamma.Basic
public import TauCeti.Probability.Distributions.Geometric
public import TauCeti.Probability.Distributions.Laplace
public import TauCeti.Probability.Distributions.NegativeBinomial.Basic

/-!
# Sums and differences of standard distributions

This file records three elementary relations between standard probability laws. The difference of
two independent exponentials with the same rate is a centered Laplace variable, a finite sum of
independent geometric variables with nonzero success probability is negative-binomial, and a
nonempty finite sum of independent exponentials is gamma (the Erlang law).

The results include the empty geometric sum: its law is the shape-zero negative-binomial point mass
at zero. The Erlang result assumes a nonempty index type because the gamma family has no analogous
shape-zero probability law.

## Main results

* `TauCeti.Probability.map_sub_prod_expMeasure` identifies the product-measure pushforward under
  subtraction with the centered Laplace law.
* `TauCeti.Probability.hasLaw_sub_expMeasure_of_indepFun` is the corresponding random-variable
  statement.
* `TauCeti.Probability.iIndepFun.hasLaw_sum_geometric` gives the law of a finite independent sum of
  identically distributed geometric variables with nonzero success probability.
* `TauCeti.Probability.iIndepFun.hasLaw_sum_expMeasure` gives the law of a nonempty finite
  independent sum of identically distributed exponential variables.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, chs. 17 and 19.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995, ch. 24.
* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, ch. 5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Omega iota : Type*} [MeasurableSpace Omega] {P : Measure Omega}

/-! ### Differences of exponential variables -/

/-- The pushforward of two independent exponential laws of rate `b⁻¹` under subtraction is the
centered Laplace law of scale `b`. -/
theorem map_sub_prod_expMeasure {b : ℝ} (hb : 0 < b) :
    ((expMeasure b⁻¹).prod (expMeasure b⁻¹)).map (fun z ↦ z.1 - z.2) =
      laplaceMeasure 0 b := by
  have hr : 0 < b⁻¹ := inv_pos.mpr hb
  let _ := isProbabilityMeasure_expMeasure hr
  let _ := isProbabilityMeasure_laplaceMeasure hb 0
  calc
    ((expMeasure b⁻¹).prod (expMeasure b⁻¹)).map (fun z ↦ z.1 - z.2) =
        expMeasure b⁻¹ ∗ (expMeasure b⁻¹).map (fun x ↦ -x) := by
      rw [Measure.conv]
      calc
        ((expMeasure b⁻¹).prod (expMeasure b⁻¹)).map (fun z ↦ z.1 - z.2) =
            ((expMeasure b⁻¹).prod (expMeasure b⁻¹)).map
              ((fun z : ℝ × ℝ ↦ z.1 + z.2) ∘ Prod.map id fun x ↦ -x) := by
          congr 1
        _ = (((expMeasure b⁻¹).prod (expMeasure b⁻¹)).map
              (Prod.map id fun x ↦ -x)).map (fun z ↦ z.1 + z.2) := by
          rw [Measure.map_map]
          all_goals fun_prop
        _ = (((expMeasure b⁻¹).map id).prod
              ((expMeasure b⁻¹).map fun x ↦ -x)).map (fun z ↦ z.1 + z.2) := by
          rw [Measure.map_prod_map]
          all_goals fun_prop
        _ = ((expMeasure b⁻¹).prod ((expMeasure b⁻¹).map fun x ↦ -x)).map
              (fun z ↦ z.1 + z.2) := by
          rw [Measure.map_id]
    _ = laplaceMeasure 0 b := by
      apply Measure.ext_of_charFun
      ext t
      rw [charFun_conv]
      have hneg : (fun x : ℝ ↦ -x) = fun x ↦ -1 * x := by
        funext x
        simp
      rw [hneg, charFun_map_mul, charFun_expMeasure hr, charFun_expMeasure hr,
        charFun_laplaceMeasure hb]
      have hb0 : b ≠ 0 := hb.ne'
      have hminus : ((b⁻¹ : ℝ) : ℂ) - Complex.I * t ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        norm_num at hre
        exact hb0 hre
      have hplus : ((b⁻¹ : ℝ) : ℂ) - Complex.I * (-t) ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        norm_num at hre
        exact hb0 hre
      norm_num
      field_simp
      ring_nf
      simp [Complex.I_sq, hb0]

/-- The difference of two independent exponential variables with rate `b⁻¹` has the centered
Laplace law of scale `b`. -/
theorem hasLaw_sub_expMeasure_of_indepFun {X Y : Omega → ℝ} {b : ℝ} (hb : 0 < b)
    (hindep : IndepFun X Y P)
    (hX : HasLaw X (expMeasure b⁻¹) P) (hY : HasLaw Y (expMeasure b⁻¹) P) :
    HasLaw (fun omega ↦ X omega - Y omega) (laplaceMeasure 0 b) P := by
  have hr : 0 < b⁻¹ := inv_pos.mpr hb
  let _ := isProbabilityMeasure_expMeasure hr
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hpair : HasLaw (fun omega ↦ (X omega, Y omega))
      ((expMeasure b⁻¹).prod (expMeasure b⁻¹)) P := hindep.hasLaw_prod hX hY
  have hsub : HasLaw (fun z : ℝ × ℝ ↦ z.1 - z.2) (laplaceMeasure 0 b)
      ((expMeasure b⁻¹).prod (expMeasure b⁻¹)) :=
    ⟨by fun_prop, map_sub_prod_expMeasure hb⟩
  simpa only [Function.comp_def] using hsub.fun_comp hpair

/-! ### Geometric sums -/

/-- A geometric law with nonzero success probability is the negative-binomial law of shape one. -/
theorem geometricMeasure_eq_negativeBinomialMeasure_one (p : unitInterval) (hp : p ≠ 0) :
    geometricMeasure p = negativeBinomialMeasure 1 (p : ℝ) := by
  have hp_pos : (0 : ℝ) < p := unitInterval.coe_pos.mpr (pos_iff_ne_zero.mpr hp)
  let _ := isProbabilityMeasure_negativeBinomialMeasure zero_le_one hp_pos p.2.2
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [geometricMeasure_real_singleton hp,
    negativeBinomialMeasure_real_singleton zero_le_one hp_pos p.2.2]
  rw [negativeBinomialWeightReal_eq_coeff one_pos, Ring.multichoose_one, one_mul]
  have hp_rpow : Real.rpow (p : ℝ) 1 = p := Real.rpow_one p
  rw [hp_rpow]
  ring

/-- A finite sum of independent geometric variables with common nonzero success probability `p`
has the negative-binomial law whose shape is the number of summands. This includes an empty family
and the point-mass family at `p = 1`. -/
theorem iIndepFun.hasLaw_sum_geometric [Fintype iota] {p : unitInterval}
    {X : iota → Omega → ℕ} (hindep : iIndepFun X P) (hp : p ≠ 0)
    (hlaw : ∀ i, HasLaw (X i) (geometricMeasure p) P) :
    HasLaw (fun omega ↦ Finset.univ.sum fun i ↦ X i omega)
      (negativeBinomialMeasure (Fintype.card iota : ℝ) (p : ℝ)) P := by
  classical
  have hp_pos : (0 : ℝ) < p := unitInterval.coe_pos.mpr (pos_iff_ne_zero.mpr hp)
  have hlawNB (i : iota) :
      HasLaw (X i) (negativeBinomialMeasure 1 (p : ℝ)) P := by
    rw [← geometricMeasure_eq_negativeBinomialMeasure_one p hp]
    exact hlaw i
  let _ : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hsum (s : Finset iota) :
      HasLaw (∑ i ∈ s, X i)
        (negativeBinomialMeasure (s.card : ℝ) (p : ℝ)) P := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
        rw [negativeBinomialMeasure_zero hp_pos p.2.2]
        exact hasLaw_dirac_of_ae_eq (Filter.Eventually.of_forall fun _ ↦ rfl)
    | @insert i s hi ih =>
        let _ : IsProbabilityMeasure (negativeBinomialMeasure 1 (p : ℝ)) :=
          isProbabilityMeasure_negativeBinomialMeasure zero_le_one hp_pos p.2.2
        let _ : IsProbabilityMeasure (negativeBinomialMeasure (s.card : ℝ) (p : ℝ)) :=
          isProbabilityMeasure_negativeBinomialMeasure (by positivity) hp_pos p.2.2
        have hadd :=
          (hindep.indepFun_finsetSum_of_notMem₀
            (fun j ↦ (hlaw j).aemeasurable) hi).symm.hasLaw_add
            (hlawNB i) ih
        rw [negativeBinomialMeasure_conv_negativeBinomialMeasure zero_le_one
          (by positivity)] at hadd
        simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add,
          Nat.cast_one, add_comm (1 : ℝ)] using hadd
  have hX : (fun omega ↦ ∑ i, X i omega) = ∑ i, X i := by
    funext omega
    exact (Fintype.sum_apply omega X).symm
  rw [hX]
  simpa only [Finset.card_univ] using hsum Finset.univ

/-! ### Erlang sums -/

/-- A nonempty finite sum of independent exponential variables with common positive rate `r` has
the gamma law whose shape is the number of summands. -/
theorem iIndepFun.hasLaw_sum_expMeasure [Fintype iota] [Nonempty iota] {r : ℝ}
    {X : iota → Omega → ℝ} (hindep : iIndepFun X P) (hr : 0 < r)
    (hlaw : ∀ i, HasLaw (X i) (expMeasure r) P) :
    HasLaw (fun omega ↦ ∑ i, X i omega) (gammaMeasure (Fintype.card iota : ℝ) r) P := by
  classical
  have hlawGamma (i : iota) : HasLaw (X i) (gammaMeasure 1 r) P := by
    simpa only [expMeasure] using hlaw i
  let _ : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hsum (s : Finset iota) (hs : s.Nonempty) :
      HasLaw (∑ i ∈ s, X i) (gammaMeasure (s.card : ℝ) r) P := by
    induction hs using Finset.Nonempty.cons_induction with
    | singleton i =>
        simpa only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one] using hlawGamma i
    | cons i s hi hs ih =>
        have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
        let _ : IsProbabilityMeasure (gammaMeasure 1 r) :=
          isProbabilityMeasure_gammaMeasure one_pos hr
        let _ : IsProbabilityMeasure (gammaMeasure (s.card : ℝ) r) :=
          isProbabilityMeasure_gammaMeasure hcard hr
        have hadd :=
          (hindep.indepFun_finsetSum_of_notMem₀
            (fun j ↦ (hlaw j).aemeasurable) hi).symm.hasLaw_add
            (hlawGamma i) ih
        rw [gammaMeasure_conv_gammaMeasure one_pos hcard hr] at hadd
        simpa only [Finset.sum_cons, Finset.card_cons, Nat.cast_add, Nat.cast_one, add_comm]
          using hadd
  have hX : (fun omega ↦ ∑ i, X i omega) = ∑ i, X i := by
    funext omega
    exact (Fintype.sum_apply omega X).symm
  rw [hX]
  simpa only [Finset.card_univ] using hsum Finset.univ Finset.univ_nonempty

end Probability

end TauCeti
