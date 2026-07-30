/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Construct
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Exchangeable coin flips: the worked example of a random bias

This file discharges the second worked example of the Exchangeability roadmap
(`TauCetiRoadmap/Exchangeability/README.md`, "Worked examples"):

> A `Bool`-valued sequence generated conditionally i.i.d. given a random `θ` (draw `θ`, then flip
> i.i.d. `κ (θ ω)`-coins) is exchangeable, with `ω ↦ κ (θ ω)` (`κ` a two-point kernel) as the
> directing measure — genuinely: the generating construction makes it a witness of
> `ConditionallyIIDWith`, not merely a mixing representative.

The two-point kernel is `coinKernel p = Ber(true, false, p)`, Mathlib's `bernoulliMeasure` bundled
as a `ProbabilityMeasure Bool`; the parameter `θ` is the first coordinate of the canonical space
`I × (ℕ → Bool)` and the bias measure `π` is arbitrary. As the roadmap insists, the directing
measure is the *random probability measure* `ω ↦ coinKernel ω.1`, not the bias `ω ↦ ω.1` itself.

The example carries weight because the sequence is exchangeable without being independent:
`not_iIndepFun_coinFlips` exhibits a two-point bias law for which the coordinates are dependent, so
`ConditionallyIID` really is a wider class than i.i.d. and the constructed directing measure is not
a disguised constant.

## Main results

* `coinKernel` — the two-point kernel `p ↦ Ber(true, false, p)`, with `measurable_coinKernel` and
  the bias readout `coinKernel_apply_true`.
* `conditionallyIIDWith_coinFlips` — the coin-flip sequence is conditionally i.i.d. with directing
  measure `ω ↦ coinKernel ω.1`, hence `exchangeable_coinFlips` and `contractable_coinFlips`.
* `not_iIndepFun_coinFlips` — for a bias that is genuinely random the flips are *not* independent.

The construction it instantiates is `iidMixtureLaw` in
`TauCeti/Probability/Exchangeability/ConditionallyIID/Construct.lean`. Nothing here is adapted from
`cameronfreer/exchangeability`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

/-- **The two-point kernel.** `coinKernel p` is the law of one `Bool`-valued flip of a coin that
comes up `true` with probability `p`.

Phrasing the example through this kernel — rather than through a `Bernoulli` random variable —
keeps it independent of any particular parametrized-distribution API: all it needs is that the
family is measurable in the bias. -/
-- `@[expose]` is forced by the exported `rfl`-unfold `coinKernel_toMeasure` below: a public theorem
-- proved by unfolding the body requires the body to be exposed.
@[expose]
def coinKernel (p : I) : ProbabilityMeasure Bool :=
  ⟨bernoulliMeasure true false p, inferInstance⟩

/-- The measure underlying `coinKernel p` is Mathlib's Bernoulli measure on `Bool`. -/
@[simp]
theorem coinKernel_toMeasure (p : I) :
    (coinKernel p : Measure Bool) = bernoulliMeasure true false p :=
  rfl

-- Not `@[simp]`: with `coinKernel_toMeasure` in the simp set this left-hand side is not
-- simp-normal, and `simp` closes the statement outright — the `simpNF` linter rejects the tag.
/-- The bias is read back off the coin: `coinKernel p` gives mass `p` to `{true}`. -/
theorem coinKernel_apply_true (p : I) :
    (coinKernel p : Measure Bool) {true} = (toNNReal p : ℝ≥0∞) := by
  rw [coinKernel_toMeasure]
  exact bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) rfl (by simp)

/-- The two-point kernel is measurable in the bias, so it can direct a mixture. -/
theorem measurable_coinKernel : Measurable coinKernel := by
  have hp : Measurable fun p : I => (toNNReal p : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp toNNReal_continuous.measurable
  have hσ : Measurable fun p : I => (toNNReal (σ p) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (toNNReal_continuous.comp continuous_symm).measurable
  refine (Measure.measurable_of_measurable_coe _ fun s _ => ?_).subtype_mk
  simp only [bernoulliMeasure_def, Measure.coe_add, Measure.coe_smul, Pi.add_apply,
    Pi.smul_apply]
  exact (hp.mul_const _).add (hσ.mul_const _)

variable (π : Measure I)

/-- **The worked example.** Draw a bias from `π`, then flip i.i.d. coins with that bias: the
resulting `Bool`-valued sequence is conditionally i.i.d. with directing measure
`ω ↦ coinKernel ω.1`.

This is the sharp conditional statement, not just the mixture identity: the generating construction
puts the sequence and its directing measure on one space and pins their joint law. -/
theorem conditionallyIIDWith_coinFlips :
    ConditionallyIIDWith (iidMixtureLaw π coinKernel) (fun n ω => ω.2 n)
      fun ω => coinKernel ω.1 :=
  conditionallyIIDWith_iidMixtureLaw measurable_coinKernel

/-- The coin-flip sequence is conditionally i.i.d. (existential form). -/
theorem conditionallyIID_coinFlips :
    ConditionallyIID (iidMixtureLaw π coinKernel) fun n ω => ω.2 n :=
  conditionallyIID_iidMixtureLaw measurable_coinKernel

/-- The coin-flip sequence is exchangeable. -/
theorem exchangeable_coinFlips :
    Exchangeable (iidMixtureLaw π coinKernel) fun n ω => ω.2 n :=
  exchangeable_iidMixtureLaw measurable_coinKernel

/-- The coin-flip sequence is contractable. -/
theorem contractable_coinFlips :
    Contractable (iidMixtureLaw π coinKernel) fun n ω => ω.2 n :=
  contractable_iidMixtureLaw measurable_coinKernel

/-- **Independent flips force a deterministic bias.** If the coordinates of the coin-flip sequence
are independent, then the law of the bias — pushed forward along `toNNReal` — is a Dirac
measure. -/
theorem exists_map_toNNReal_eq_dirac_of_iIndepFun_coinFlips [IsProbabilityMeasure π]
    (h : iIndepFun (fun n (ω : I × (ℕ → Bool)) => ω.2 n) (iidMixtureLaw π coinKernel)) :
    ∃ c : ℝ≥0∞, π.map (fun p : I => (toNNReal p : ℝ≥0∞)) = Measure.dirac c := by
  have hev : Measurable fun Q : ProbabilityMeasure Bool => (Q : Measure Bool) {true} :=
    (Measure.measurable_coe (measurableSet_singleton true)).comp measurable_subtype_coe
  -- degeneracy of the mixing law, transported along the bias readout `Q ↦ Q {true}`
  obtain ⟨Q, hQ⟩ := exists_map_eq_dirac_of_iIndepFun_iidMixtureLaw measurable_coinKernel h
  refine ⟨(Q : Measure Bool) {true}, ?_⟩
  have hcomp : (fun p : I => (toNNReal p : ℝ≥0∞))
      = (fun Q : ProbabilityMeasure Bool => (Q : Measure Bool) {true}) ∘ coinKernel :=
    funext fun p => (coinKernel_apply_true p).symm
  rw [hcomp, ← Measure.map_map hev measurable_coinKernel, hQ]
  exact Measure.map_dirac' hev Q

/-- The bias-to-mass map `I → ℝ≥0∞` is injective, so a degenerate image law means a degenerate
bias law. -/
private theorem toNNReal_ennreal_injective :
    Function.Injective fun p : I => (toNNReal p : ℝ≥0∞) := by
  intro x y hxy
  exact Subtype.ext (by simpa using congrArg ENNReal.toReal hxy)

/-- **Exchangeable but not independent.** With the bias itself drawn from a nondegenerate two-point
law `Ber(a, b, r)` — two distinct biases `a ≠ b`, each of positive probability — the coin flips are
exchangeable (`exchangeable_coinFlips`) yet dependent.

So `ConditionallyIID` is strictly wider than i.i.d., and the directing measure the construction
supplies is genuinely random rather than an a.e. constant. -/
theorem not_iIndepFun_coinFlips {a b r : I} (hab : a ≠ b) (hr₀ : r ≠ 0) (hr₁ : r ≠ 1) :
    ¬ iIndepFun (fun n (ω : I × (ℕ → Bool)) => ω.2 n)
      (iidMixtureLaw (bernoulliMeasure a b r) coinKernel) := by
  intro h
  have hmeas : Measurable fun p : I => (toNNReal p : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp toNNReal_continuous.measurable
  obtain ⟨c, hc⟩ := exists_map_toNNReal_eq_dirac_of_iIndepFun_coinFlips _ h
  rw [map_bernoulliMeasure' a b hmeas r] at hc
  -- evaluating both sides at the singleton `{a's mass}` gives `r` on the left and `0` or `1`
  -- on the right
  have hne : (toNNReal b : ℝ≥0∞) ≠ (toNNReal a : ℝ≥0∞) := fun hcon =>
    hab (toNNReal_ennreal_injective hcon).symm
  have hval := congrArg (fun m : Measure ℝ≥0∞ => m {(toNNReal a : ℝ≥0∞)}) hc
  rw [bernoulliMeasure_apply_of_mem_of_notMem r (measurableSet_singleton _) rfl hne,
    Measure.dirac_apply' _ (measurableSet_singleton _)] at hval
  -- `r` is neither `0` nor `1`, but the indicator on the right is one of the two
  have hr₀' : (toNNReal r : ℝ≥0∞) ≠ 0 := fun hcon =>
    hr₀ (toNNReal_ennreal_injective (by simpa using hcon))
  have hr₁' : (toNNReal r : ℝ≥0∞) ≠ 1 := fun hcon =>
    hr₁ (toNNReal_ennreal_injective (by simpa using hcon))
  by_cases hmem : c ∈ ({(toNNReal a : ℝ≥0∞)} : Set ℝ≥0∞)
  · exact hr₁' (by simpa [hmem] using hval)
  · exact hr₀' (by simpa [hmem] using hval)

end Probability

end TauCeti
