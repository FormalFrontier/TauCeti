/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Map

/-!
# The evaluation of a weighted restricted series is multiplicative

`TauCeti/RingTheory/Huber/WeightedEval/Map.lean` gives Wedhorn's evaluation its additive API and
its values on constants and variables. This file adds multiplicativity,
`weightedEval (f * g) = weightedEval f * weightedEval g`.

That is the remaining *algebraic* ingredient of Proposition 5.50, but not by itself the universal
property, since it speaks about individual series. The packaging as a ring homomorphism out of
`A⟨X⟩_T` is `TauCeti.Huber.weightedEvalHom` in `WeightedEval/Hom.lean`, which consumes
`weightedEval_mul` below, and its continuity is `TauCeti.Huber.continuous_weightedEvalHom` in
`WeightedEval/Continuous.lean`. The uniqueness of the extension, which is what makes 5.50
*universal*, is `TauCeti.Huber.weightedRestrictedSubring_ringHom_ext_of_continuous` in
`WeightedRestrictedSeries/Basic.lean`, and `WeightedEval/UniversalProperty.lean` states 5.50 itself.

The argument is the Cauchy product, and Mathlib supplies it:
`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` turns a product of sums into a sum over
antidiagonals, and `MvPowerSeries.coeff_mul` says the antidiagonal sum at `ν` is the `ν`-th
coefficient of `f * g`.

## Main results

* `TauCeti.Huber.weightedEval_mul_of_summable`: multiplicativity from summability alone, which is
  all the proof uses.
* `TauCeti.Huber.weightedEval_mul`, with
  `TauCeti.Huber.weightedEval_mul_of_isWeightedVarPowerBounded` and
  `TauCeti.Huber.weightedEval_mul_of_forall_isPowerBounded`: the same for `T`-restricted series,
  under each of the three hypotheses that produce summability.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

section Term

variable {k : ℕ} {A B : Type*} [CommRing A] [CommRing B] {φ : A →+* B} {b : Fin k → B}

/-- The product of the `α`-th term of `f` and the `β`-th term of `g` is what the pair `(α, β)`
contributes to `f * g`: the monomials multiply because `bα · bβ = b(α+β)`. Private: it exists for
the Cauchy product below and says nothing a consumer needs. -/
private theorem weightedEvalTerm_mul_weightedEvalTerm (f g : MvPowerSeries (Fin k) A)
    (α β : Fin k →₀ ℕ) :
    weightedEvalTerm φ b f α * weightedEvalTerm φ b g β
      = φ (MvPowerSeries.coeff α f * MvPowerSeries.coeff β g) * ∏ i, b i ^ (α + β) i := by
  simp only [weightedEvalTerm_def, map_mul, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
  ring

end Term

section Summable

variable {k : ℕ} {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace B] [T3Space B]
  [IsTopologicalRing B] {φ : A →+* B} {b : Fin k → B}

/-- **The evaluation is multiplicative**, at the level where that is true: three summable
families. Nothing topological about `A`, no weights and no restrictedness — those exist only to
*produce* summability, and the results below are this one composed with ways of producing it.

The third hypothesis, summability over *pairs*, is what the Cauchy product needs and does not
follow from the other two in general; in a nonarchimedean target it does, which is how
`TauCeti.Huber.weightedEval_mul` discharges it. -/
theorem weightedEval_mul_of_summable {f g : MvPowerSeries (Fin k) A}
    (hf : Summable (weightedEvalTerm φ b f)) (hg : Summable (weightedEvalTerm φ b g))
    (hfg : Summable fun p : (Fin k →₀ ℕ) × (Fin k →₀ ℕ) ↦
      weightedEvalTerm φ b f p.1 * weightedEvalTerm φ b g p.2) :
    weightedEval φ b (f * g) = weightedEval φ b f * weightedEval φ b g := by
  classical
  rw [weightedEval_def, weightedEval_def, weightedEval_def,
    hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg]
  refine tsum_congr fun ν ↦ ?_
  rw [weightedEvalTerm_def, MvPowerSeries.coeff_mul, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun p hp ↦ by
    rw [weightedEvalTerm_mul_weightedEvalTerm, Finset.mem_antidiagonal.mp hp]

end Summable

section Restricted

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B]
  [T3Space B] {φ : A →+* B} {T : Fin k → Set A} {b : Fin k → B}

/-- **The evaluation is multiplicative on `T`-restricted series.** This is
`TauCeti.Huber.weightedEval_mul_of_summable` with all three summabilities supplied: the factors by
`TauCeti.Huber.summable_weightedEvalTerm`, the pairs by `HasSum.mul_of_nonarchimedean`.

Only `f` and `g` need be `T`-restricted. Restrictedness of `f * g` is not a hypothesis and no
weight-family condition appears: the Cauchy product produces the terms of the product and their
sum whether or not the product is separately known to be restricted. -/
theorem weightedEval_mul (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ T b)
    {f g : MvPowerSeries (Fin k) A} (hf : IsWeightedRestricted T f)
    (hg : IsWeightedRestricted T g) :
    weightedEval φ b (f * g) = weightedEval φ b f * weightedEval φ b g :=
  weightedEval_mul_of_summable (summable_weightedEvalTerm hφ hb hf)
    (summable_weightedEvalTerm hφ hb hg)
    ((hasSum_weightedEval hφ hb hf).mul_of_nonarchimedean (hasSum_weightedEval hφ hb hg)).summable

/-- `TauCeti.Huber.weightedEval_mul` under Wedhorn's coordinatewise hypothesis. -/
theorem weightedEval_mul_of_isWeightedVarPowerBounded (hφ : ContinuousAt φ 0)
    (hb : IsWeightedVarPowerBounded φ T b) {f g : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) (hg : IsWeightedRestricted T g) :
    weightedEval φ b (f * g) = weightedEval φ b f * weightedEval φ b g :=
  weightedEval_mul hφ (isWeightBounded_of_isWeightedVarPowerBounded hb) hf hg

/-- `TauCeti.Huber.weightedEval_mul` at the one-weight family, where the hypothesis is that each
variable is power-bounded. -/
theorem weightedEval_mul_of_forall_isPowerBounded (hφ : ContinuousAt φ 0)
    (hb : ∀ i, IsPowerBounded (b i)) {f g : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) f)
    (hg : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) g) :
    weightedEval φ b (f * g) = weightedEval φ b f * weightedEval φ b g :=
  weightedEval_mul hφ ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).mpr hb) hf hg

end Restricted

end TauCeti.Huber

end
