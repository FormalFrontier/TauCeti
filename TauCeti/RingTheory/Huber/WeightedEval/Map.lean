/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Basic

/-!
# The evaluation of a weighted restricted power series

`TauCeti/RingTheory/Huber/WeightedEval/Basic.lean` proves that the terms `φ(coeff ν f) · bν` of
Wedhorn's evaluation (Proposition 5.50) are summable. This file takes their sum and gives it the
API a universal property needs: the value on a constant series, the value on a variable, and
additivity in the series.

Multiplicativity is **not** proved here. `weightedEval (f * g) = weightedEval f * weightedEval g`
is a Cauchy-product argument — the coefficients of `f * g` are sums over the antidiagonal, so the
statement is a reindexing of a double sum rather than a consequence of anything below — and it is
the remaining step before 5.50 can be stated as a universal property.

## Main definitions

* `TauCeti.Huber.weightedEval`: the sum `∑' ν, φ(coeff ν f) · bν`.

## Main results

* `TauCeti.Huber.weightedEval_monomial`, with `TauCeti.Huber.weightedEval_C` and
  `TauCeti.Huber.weightedEval_X` as its cases at `ν = 0` and `ν = single i 1`: the value on a
  monomial is its own term, which is what makes this *the* evaluation at `b`.
  These, and the value on `0`, are unconditional: each of the three term families is supported on
  at most one index — the zero series gives the family that vanishes identically — so the sum is a
  single term and no summability hypothesis is involved.
* `TauCeti.Huber.hasSum_weightedEval`: under the hypotheses of the summability theorem, the
  terms have `weightedEval` as their sum. This is the consumer-facing statement — it names the sum
  instead of leaving a `tsum` to be manipulated — and is not itself used below.
* `TauCeti.Huber.weightedEval_zero` and `TauCeti.Huber.weightedEval_add_of_summable`: the
  evaluation is additive in the series, the latter stated where additivity is actually true — two
  summable term families, with no weights, completeness or restrictedness in sight.
  `TauCeti.Huber.weightedEval_add` and its corollaries are that composed with a way of producing
  summability.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

section Values

variable {k : ℕ} {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace B]

/-- **Wedhorn's evaluation** of a series at a tuple `b` along `φ`: the sum of the terms
`φ(coeff ν f) · bν`.

Unconditionally a `tsum`, so it is junk when the family is not summable. The results that take a
genuine infinite sum — `TauCeti.Huber.weightedEval_add` and its corollaries — therefore obtain
summability from `TauCeti.Huber.summable_weightedEvalTerm` and pass it to
`TauCeti.Huber.weightedEval_add_of_summable`. The values on `0`, on a constant and on a variable
need none of that: their term families are supported on at most one index, so the sum is read off
that index directly. -/
noncomputable def weightedEval (φ : A →+* B) (b : Fin k → B) (f : MvPowerSeries (Fin k) A) : B :=
  ∑' ν, weightedEvalTerm φ b f ν

/-- Unfolding lemma for `TauCeti.Huber.weightedEval`. -/
theorem weightedEval_def (φ : A →+* B) (b : Fin k → B) (f : MvPowerSeries (Fin k) A) :
    weightedEval φ b f = ∑' ν, weightedEvalTerm φ b f ν := (rfl)

/-- The evaluation of the zero series is zero. -/
@[simp]
theorem weightedEval_zero (φ : A →+* B) (b : Fin k → B) :
    weightedEval φ b (0 : MvPowerSeries (Fin k) A) = 0 := by
  simp [weightedEval_def, weightedEvalTerm_def]

/-- **The evaluation of a monomial is its term.** Every other coefficient of `monomial ν a`
vanishes, so the sum collapses to the index `ν`. The values on a constant and on a variable are
the two special cases below. -/
@[simp]
theorem weightedEval_monomial (φ : A →+* B) (b : Fin k → B) (ν : Fin k →₀ ℕ) (a : A) :
    weightedEval φ b (MvPowerSeries.monomial ν a) = φ a * ∏ i, b i ^ ν i := by
  classical
  rw [weightedEval_def, tsum_eq_single ν ?_]
  · simp [weightedEvalTerm_def]
  · intro μ hμ
    simp [weightedEvalTerm_def, MvPowerSeries.coeff_monomial, hμ]

/-- **The evaluation sends a constant series to its image**, the monomial at `ν = 0`. -/
@[simp]
theorem weightedEval_C (φ : A →+* B) (b : Fin k → B) (a : A) :
    weightedEval φ b (MvPowerSeries.C a) = φ a := by
  rw [← MvPowerSeries.monomial_zero_eq_C_apply, weightedEval_monomial]
  simp

/-- **The evaluation sends a variable to its value**, the monomial at `ν = single i 1`. -/
@[simp]
theorem weightedEval_X (φ : A →+* B) (b : Fin k → B) (i : Fin k) :
    weightedEval φ b (MvPowerSeries.X i) = b i := by
  classical
  rw [MvPowerSeries.X_def, weightedEval_monomial]
  simp [Finsupp.single_apply, Finset.prod_ite_eq]

end Values

section Additive

variable {k : ℕ} {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace B] [ContinuousAdd B]
  [T2Space B] {φ : A →+* B} {b : Fin k → B}

/-- **The evaluation is additive in the series**, at the level where that is actually true: two
summable term families. Nothing topological about `A`, no completeness, no weights and no
restrictedness enter — those hypotheses exist only to *produce* summability, and every additivity
result below is this one composed with a way of producing it.

Both summability hypotheses are needed: a sum of two families is the sum of their sums only when
each converges. -/
theorem weightedEval_add_of_summable {f g : MvPowerSeries (Fin k) A}
    (hf : Summable (weightedEvalTerm φ b f)) (hg : Summable (weightedEvalTerm φ b g)) :
    weightedEval φ b (f + g) = weightedEval φ b f + weightedEval φ b g := by
  have hterm : weightedEvalTerm φ b (f + g)
      = fun ν ↦ weightedEvalTerm φ b f ν + weightedEvalTerm φ b g ν := by
    funext ν
    simp [weightedEvalTerm_def, add_mul]
  rw [weightedEval_def, hterm]
  exact hf.tsum_add hg

end Additive

section Sums

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanAddGroup B] [CompleteSpace B]
  {φ : A →+* B} {T : Fin k → Set A} {b : Fin k → B}

/-- **The terms sum to the evaluation.** This is for consumers: it names the sum, so that a caller
holding the summability hypotheses does not have to manipulate a `tsum`. Nothing in this file uses
it — additivity goes through `TauCeti.Huber.weightedEval_add_of_summable`, which asks only for
`Summable`. -/
theorem hasSum_weightedEval (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ T b)
    {f : MvPowerSeries (Fin k) A} (hf : IsWeightedRestricted T f) :
    HasSum (weightedEvalTerm φ b f) (weightedEval φ b f) := by
  -- `weightedEval` is the `tsum`, but say so through its unfolding lemma rather than relying on
  -- the wrapper being transparent.
  simpa only [weightedEval_def] using (summable_weightedEvalTerm hφ hb hf).hasSum

/-- `TauCeti.Huber.hasSum_weightedEval` under Wedhorn's coordinatewise hypothesis. -/
theorem hasSum_weightedEval_of_isWeightedVarPowerBounded (hφ : ContinuousAt φ 0)
    (hb : IsWeightedVarPowerBounded φ T b) {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) :
    HasSum (weightedEvalTerm φ b f) (weightedEval φ b f) :=
  hasSum_weightedEval hφ (isWeightBounded_of_isWeightedVarPowerBounded hb) hf

/-- `TauCeti.Huber.hasSum_weightedEval` at the one-weight family, where the hypothesis is that
each variable is power-bounded. -/
theorem hasSum_weightedEval_of_forall_isPowerBounded (hφ : ContinuousAt φ 0)
    (hb : ∀ i, IsPowerBounded (b i)) {f : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) f) :
    HasSum (weightedEvalTerm φ b f) (weightedEval φ b f) :=
  hasSum_weightedEval hφ ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).mpr hb) hf

variable [T2Space B]

/-- **The evaluation is additive on `T`-restricted series.** This is
`TauCeti.Huber.weightedEval_add_of_summable` with summability supplied by
`TauCeti.Huber.summable_weightedEvalTerm`. -/
theorem weightedEval_add (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ T b)
    {f g : MvPowerSeries (Fin k) A} (hf : IsWeightedRestricted T f)
    (hg : IsWeightedRestricted T g) :
    weightedEval φ b (f + g) = weightedEval φ b f + weightedEval φ b g :=
  weightedEval_add_of_summable (summable_weightedEvalTerm hφ hb hf)
    (summable_weightedEvalTerm hφ hb hg)

/-- `TauCeti.Huber.weightedEval_add` under Wedhorn's coordinatewise hypothesis. -/
theorem weightedEval_add_of_isWeightedVarPowerBounded (hφ : ContinuousAt φ 0)
    (hb : IsWeightedVarPowerBounded φ T b) {f g : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted T f) (hg : IsWeightedRestricted T g) :
    weightedEval φ b (f + g) = weightedEval φ b f + weightedEval φ b g :=
  weightedEval_add hφ (isWeightBounded_of_isWeightedVarPowerBounded hb) hf hg

/-- `TauCeti.Huber.weightedEval_add` at the one-weight family. -/
theorem weightedEval_add_of_forall_isPowerBounded (hφ : ContinuousAt φ 0)
    (hb : ∀ i, IsPowerBounded (b i)) {f g : MvPowerSeries (Fin k) A}
    (hf : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) f)
    (hg : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) g) :
    weightedEval φ b (f + g) = weightedEval φ b f + weightedEval φ b g :=
  weightedEval_add hφ ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).mpr hb) hf hg

end Sums

end TauCeti.Huber

end
