/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Exchangeable.Ergodic
public import TauCeti.Probability.Exchangeability.PathSpace.Law.ZeroOne
public import TauCeti.Probability.DeFinetti.Correspondence

/-!
# The ergodic correspondence for exchangeable laws

Four characterisations of an exchangeable path law have landed separately: triviality of
`exchangeableSigma`, ergodicity of the finitely supported permutation action, being an i.i.d.
product law, and being an extreme point of the exchangeable probability laws. This module records
the equivalences between them that a user is likely to want, so that the ergodic description is
reachable without chaining through the σ-algebra formulation.

## Main results

* `exchangeable_ergodicSMul_iff_iid` — the finitely supported permutations act ergodically exactly
  on the i.i.d. product laws;
* `exchangeable_ergodicSMul_iff_mem_extremePoints` — equivalently, exactly on the extreme points of
  the exchangeable probability laws;
* `deFinettiBarycenter_ergodicSMul_iff_dirac` — so a de Finetti barycenter is ergodic exactly when
  its mixing law is a point mass.

Together these identify the de Finetti components with the ergodic components of the permutation
action, which is what Layer 8 asks for.

## Nothing new is proved here

Each theorem is a composition of results already in the tree —
`exchangeableSigma_trivial_iff_ergodicSMul`, `exchangeableSigma_trivial_iff_iid`,
`exchangeable_extreme_iff_iid` and `deFinettiBarycenter_mem_extremePoints_iff`. The module exists
because the composite statements are the ones with consumers, not because any step was missing.

⚠ The action here is the finitely supported permutations of the *time index*. Ergodicity for it is
a different statement from ergodicity of the one-sided shift, which concerns the smaller σ-algebra
of shift-invariant events; see `PathSpace/Exchangeable/Ergodic.lean` for that caveat.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 8**, whose Build list asks to
  identify the de Finetti components with the ergodic components of the finitely supported
  permutation action once Layer 6's `ErgodicSMul` interface exists.
-/

public section

open Filter MeasurableSpace MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **The permutation action is ergodic exactly on the i.i.d. laws.** For an exchangeable path law,
ergodicity of the finitely supported permutations of the time index characterises being an i.i.d.
product law — the ergodic form of Hewitt–Savage. -/
theorem exchangeable_ergodicSMul_iff_iid [StandardBorelSpace α]
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] (hρ : ExchangeableLaw ρ) :
    ErgodicSMul TimePerm (ℕ → α) ρ ↔
      ∃ P : ProbabilityMeasure α, ρ = Measure.infinitePi fun _ : ℕ => (P : Measure α) :=
  (exchangeableSigma_trivial_iff_ergodicSMul hρ).symm.trans
    (exchangeableSigma_trivial_iff_iid hρ)

/-- **Ergodic exactly at the extreme points.** Combining the previous characterisation with
`exchangeable_extreme_iff_iid`: the ergodic exchangeable laws are precisely the extreme points of
the exchangeable probability laws, so the de Finetti components are the ergodic components. -/
theorem exchangeable_ergodicSMul_iff_mem_extremePoints [StandardBorelSpace α]
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] (hρ : ExchangeableLaw ρ) :
    ErgodicSMul TimePerm (ℕ → α) ρ ↔
      ρ ∈ extremePoints ℝ≥0∞
        {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν} :=
  (exchangeable_ergodicSMul_iff_iid hρ).trans exchangeable_extreme_iff_iid.symm

/-- **A barycenter is ergodic exactly at a point mass.** The mixing-side form: the de Finetti
barycenter of `π` is ergodic for the permutation action if and only if `π` is a Dirac measure, so
the decomposition is trivial precisely when the mixture is. -/
theorem deFinettiBarycenter_ergodicSMul_iff_dirac [StandardBorelSpace α]
    {π : Measure (ProbabilityMeasure α)} [IsProbabilityMeasure π] :
    ErgodicSMul TimePerm (ℕ → α) (deFinettiBarycenter π) ↔
      ∃ P : ProbabilityMeasure α, π = Measure.dirac P :=
  (exchangeable_ergodicSMul_iff_mem_extremePoints
    exchangeableLaw_deFinettiBarycenter).trans deFinettiBarycenter_mem_extremePoints_iff

end Probability

end TauCeti

end
