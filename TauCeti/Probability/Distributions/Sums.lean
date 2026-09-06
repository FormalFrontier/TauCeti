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
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Sums and differences of classical distributions

This file identifies three laws obtained from independent scalar random variables. The difference
of two exponential variables with common rate `b⁻¹` has the centered Laplace law of scale `b`.
A finite sum of geometric variables with nonzero success probability has a negative-binomial law,
including the empty sum and the success-probability-one boundary. A nonempty finite sum of
exponential variables with common rate has the corresponding Erlang law.

These closure laws identify independent sums and differences directly with members of the standard
distribution families, so consumers can transfer the established APIs of those families to the
resulting random variables.

## Main results

* `TauCeti.Probability.IndepFun.hasLaw_sub_expMeasure` identifies an exponential difference;
* `TauCeti.Probability.iIndepFun.hasLaw_sum_geometricMeasure` identifies a finite geometric sum;
* `TauCeti.Probability.iIndepFun.hasLaw_sum_expMeasure` identifies a finite exponential sum.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapters 19 and 23.
* N. L. Johnson, A. W. Kemp, and S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley
  (2005), chapter 5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### A difference of exponential variables -/

/-- The difference of independent exponential variables with common rate `b⁻¹` has the centered
Laplace law of scale `b`. -/
theorem IndepFun.hasLaw_sub_expMeasure {X Y : Ω → ℝ} {b : ℝ} (hindep : IndepFun X Y P)
    (hb : 0 < b) (hX : HasLaw X (expMeasure b⁻¹) P)
    (hY : HasLaw Y (expMeasure b⁻¹) P) :
    HasLaw (fun ω => X ω - Y ω) (laplaceMeasure 0 b) P := by
  have hr : 0 < b⁻¹ := inv_pos.mpr hb
  let _ : IsProbabilityMeasure (expMeasure b⁻¹) := isProbabilityMeasure_expMeasure hr
  let _ : IsProbabilityMeasure (laplaceMeasure 0 b) :=
    isProbabilityMeasure_laplaceMeasure hb 0
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hindepNeg : IndepFun X (fun ω => -Y ω) P := by
    simpa only [Function.comp_def, id_eq] using
      hindep.comp measurable_id measurable_neg
  refine ⟨hX.aemeasurable.sub hY.aemeasurable, ?_⟩
  apply Measure.ext_of_charFun
  funext t
  have hneg :
      charFun (P.map (-Y)) t = charFun (expMeasure b⁻¹) (-t) := by
    -- `charFun_map_mul_comp` expresses scalar negation as multiplication by `-1`.
    have hneg_eq_mul : (-Y) = fun ω => (-1 : ℝ) * Y ω := by
      funext ω
      simp
    rw [hneg_eq_mul, charFun_map_mul_comp hY.aemeasurable, hY.map_eq]
    congr 1
    ring
  simp only [sub_eq_add_neg]
  have hsum := congrFun
    (hindepNeg.charFun_map_fun_add_eq_mul hX.aemeasurable hY.aemeasurable.neg) t
  simp only [Pi.mul_apply, Pi.neg_apply] at hsum
  rw [hsum, hX.map_eq, hneg, charFun_expMeasure hr, charFun_expMeasure hr,
    charFun_laplaceMeasure hb]
  push_cast
  have hb0 : b ≠ 0 := hb.ne'
  have hden₁ : (b⁻¹ : ℂ) - Complex.I * t ≠ 0 := by
    intro h
    have hreal : b⁻¹ = 0 := by
      simpa using congrArg Complex.re h
    exact inv_ne_zero hb0 hreal
  have hden₂ : (b⁻¹ : ℂ) - Complex.I * (-t) ≠ 0 := by
    intro h
    have hreal : b⁻¹ = 0 := by
      simpa using congrArg Complex.re h
    exact inv_ne_zero hb0 hreal
  simp only [mul_zero, zero_mul, Complex.exp_zero, one_div]
  field_simp [hden₁, hden₂, hb0]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### Sums of geometric variables -/

/-- A finite sum of independent geometric variables with success probability `p ≠ 0` has the
negative-binomial law whose shape is the cardinality of the family. This includes the empty family
and the boundary `p = 1`, when both laws are point masses at zero. -/
theorem iIndepFun.hasLaw_sum_geometricMeasure {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℕ} {p : unitInterval} (hindep : iIndepFun X P) (hp : p ≠ 0)
    (hlaw : ∀ i, HasLaw (X i) (geometricMeasure p) P) :
    HasLaw (fun ω => ∑ i, X i ω)
      (negativeBinomialMeasure (Fintype.card ι) p) P := by
  classical
  have hpR : (0 : ℝ) < p := by grind
  let _ : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hone (i : ι) : HasLaw (X i) (negativeBinomialMeasure 1 p) P := by
    rw [← geometricMeasure_eq_negativeBinomialMeasure_one p hp]
    exact hlaw i
  have hsum (s : Finset ι) :
      HasLaw (∑ i ∈ s, X i) (negativeBinomialMeasure (s.card : ℝ) p) P := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
        rw [negativeBinomialMeasure_zero hpR p.2.2]
        exact hasLaw_dirac_of_ae_eq (Filter.Eventually.of_forall fun _ => rfl)
    | @insert i s hi ih =>
        let _ : IsProbabilityMeasure (negativeBinomialMeasure 1 p) :=
          isProbabilityMeasure_negativeBinomialMeasure zero_le_one hpR p.2.2
        let _ : IsProbabilityMeasure (negativeBinomialMeasure (s.card : ℝ) p) :=
          isProbabilityMeasure_negativeBinomialMeasure (Nat.cast_nonneg _) hpR p.2.2
        have hadd :=
          (hindep.indepFun_finsetSum_of_notMem₀
            (fun j => (hlaw j).aemeasurable) hi).symm.hasLaw_add (hone i) ih
        rw [negativeBinomialMeasure_conv_negativeBinomialMeasure zero_le_one
          (Nat.cast_nonneg s.card)] at hadd
        simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add,
          Nat.cast_one, add_comm] using hadd
  have hX : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω
    exact (Fintype.sum_apply ω X).symm
  rw [hX]
  simpa only [Finset.card_univ] using hsum Finset.univ

/-! ### Sums of exponential variables -/

/-- A nonempty finite sum of independent exponential variables with common positive rate `r` has
the Gamma (Erlang) law whose shape is the cardinality of the family. -/
theorem iIndepFun.hasLaw_sum_expMeasure {ι : Type*} [Fintype ι] [Nonempty ι]
    {X : ι → Ω → ℝ} {r : ℝ} (hindep : iIndepFun X P) (hr : 0 < r)
    (hlaw : ∀ i, HasLaw (X i) (expMeasure r) P) :
    HasLaw (fun ω => ∑ i, X i ω) (gammaMeasure (Fintype.card ι) r) P := by
  classical
  let _ : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hsum (s : Finset ι) (hs : s.Nonempty) :
      HasLaw (∑ i ∈ s, X i) (gammaMeasure (s.card : ℝ) r) P := by
    induction s using Finset.induction_on with
    | empty => simp at hs
    | @insert i s hi ih =>
        rcases s.eq_empty_or_nonempty with rfl | hs'
        · simpa [expMeasure] using hlaw i
        · have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs'.card_pos
          let _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
          let _ : IsProbabilityMeasure (gammaMeasure (s.card : ℝ) r) :=
            isProbabilityMeasure_gammaMeasure hcard hr
          have hadd :=
            (hindep.indepFun_finsetSum_of_notMem₀
              (fun j => (hlaw j).aemeasurable) hi).symm.hasLaw_add (hlaw i) (ih hs')
          rw [expMeasure, gammaMeasure_conv_gammaMeasure zero_lt_one hcard hr] at hadd
          simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add,
            Nat.cast_one, add_comm] using hadd
  have hX : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω
    exact (Fintype.sum_apply ω X).symm
  rw [hX]
  simpa only [Finset.card_univ] using hsum Finset.univ Finset.univ_nonempty

end Probability

end TauCeti
