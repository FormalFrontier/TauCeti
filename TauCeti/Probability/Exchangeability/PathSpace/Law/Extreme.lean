/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: the de Finetti barycenter, whose mixing law is what extremality pins down; it
-- re-exports the mixture representation `deFinetti_mixture` this file consumes.
public import TauCeti.Probability.DeFinetti.Barycenter
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic
public import Mathlib.Dynamics.Ergodic.Extreme
-- Non-public: the zero-one input for the i.i.d. direction and the comparison between invariant
-- and exchangeable events.
import TauCeti.Probability.Exchangeability.PathSpace.HewittSavage
import TauCeti.Probability.Exchangeability.PathSpace.Invariant.Tail
-- Non-public: exchangeable path laws are shift-preserving.
import TauCeti.Probability.Exchangeability.PathSpace.Exchangeable.ToContractable
-- Non-public: a zero-one law on `ProbabilityMeasure α` is Dirac.
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Ext
-- Non-public: mixture injectivity identifies the conditioned mixing law with `π`.
import TauCeti.MeasureTheory.Measure.MixtureInjective

/-!
# Extreme exchangeable laws

The extreme points of the convex set of exchangeable probability measures on `ℕ → α` are exactly
the i.i.d. product laws. The main theorem `exchangeable_extreme_iff_iid` states this using Mathlib's
`Set.extremePoints` for the natural `ℝ≥0∞`-module structure on measures.

The two directions expose the two classical mechanisms. An i.i.d. product law is ergodic for the
one-sided shift: shift-invariant events are exchangeable events, so the Hewitt–Savage zero-one law
applies. Mathlib's `Ergodic.mem_extremePoints` then makes it extreme among all shift-invariant
probability measures, hence among the smaller set of exchangeable ones. Conversely, de Finetti's
unique mixture representation writes an exchangeable law as

```text
∫ P^{⊗ℕ} dπ(P).
```

If a measurable set has mixing mass strictly between zero and one, conditioning `π` on the set and
its complement gives a nontrivial convex decomposition into exchangeable laws. Extremality rules
this out, mixture injectivity identifies the conditional mixing law with `π`, and therefore `π` is
zero-one. `IsZeroOneMeasure.exists_eq_dirac_probabilityMeasure` turns this into `π = δ_P`.

This proves the Layer 6 extreme-point corollary and the public
`exchangeable_extreme_iff_iid` target in Layer 7 of
`TauCetiRoadmap/Exchangeability/README.md`.

## Main results

* `ergodic_shift_infinitePi_const` — an i.i.d. product law is ergodic for the one-sided shift.
* `infinitePi_mem_extremePoints_exchangeable` — an i.i.d. product law is an extreme exchangeable
  law. This direction needs no standard Borel hypothesis, so it is stated over an arbitrary
  measurable space.
* `exchangeable_extreme_iff_iid` — the extreme exchangeable probability laws are exactly the
  i.i.d. product laws.

## References

* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 1.
* Edwin Hewitt and Leonard J. Savage, *Symmetric measures on Cartesian products*, Transactions of
  the American Mathematical Society **80** (1955), 470–501.

No material is adapted from `cameronfreer/exchangeability`, which does not contain this
extreme-point result. The proof reuses Mathlib's characterization of ergodic measures as extreme
points and Tau Ceti's de Finetti mixture injectivity rather than reproducing either argument.
-/

public section

noncomputable section

open Filter MeasurableSpace MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- An i.i.d. infinite product law is ergodic for the one-sided shift.

The shift-invariant σ-algebra is contained in the exchangeable σ-algebra, and the coordinate
process is independent and identically distributed under the product law, so Hewitt–Savage makes
every shift-invariant event null or conull. -/
theorem ergodic_shift_infinitePi_const (P : ProbabilityMeasure α) :
    Ergodic (shift α) (Measure.infinitePi fun _ : ℕ => (P : Measure α)) := by
  have hexchLaw : ExchangeableLaw (Measure.infinitePi fun _ : ℕ => (P : Measure α)) :=
    exchangeableLaw_infinitePi_const P
  refine { hexchLaw.contractableLaw.measurePreserving_shift with aeconst_set := ?_ }
  intro s hs hs_shift
  have hs_inv : MeasurableSet[MeasurableSpace.invariants (shift α)] s := ⟨hs, hs_shift⟩
  have hzeroOne := exchangeableSigma_trivial_of_infinitePi P
    (invariants_shift_le_exchangeableSigma (α := α) s hs_inv)
  refine eventuallyConst_set.2 ?_
  rcases hzeroOne with hzero | hone
  · exact Or.inr (ae_iff.mpr (by simpa using hzero))
  · exact Or.inl ((_root_.MeasureTheory.mem_ae_iff_prob_eq_one hs).2 hone)

private theorem cond_eq_of_extreme_iidMixture [StandardBorelSpace α]
    {p : Measure (ProbabilityMeasure α)} [IsProbabilityMeasure p]
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ]
    (hρ : ρ ∈ extremePoints ℝ≥0∞
      {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν})
    (hrepr : ρ = deFinettiBarycenter p)
    {s : Set (ProbabilityMeasure α)} (hs : MeasurableSet s) (hs0 : p s ≠ 0)
    (hsc0 : p sᶜ ≠ 0) : p[|s] = p := by
  have : IsProbabilityMeasure (p[|s]) := cond_isProbabilityMeasure hs0
  have : IsProbabilityMeasure (p[|sᶜ]) := cond_isProbabilityMeasure hsc0
  have hs_mem : deFinettiBarycenter (p[|s]) ∈
      {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν} :=
    ⟨exchangeableLaw_deFinettiBarycenter, inferInstance⟩
  have hsc_mem : deFinettiBarycenter (p[|sᶜ]) ∈
      {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν} :=
    ⟨exchangeableLaw_deFinettiBarycenter, inferInstance⟩
  have hp_split : p = p s • p[|s] + p sᶜ • p[|sᶜ] := by
    ext t ht
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    simpa [mul_comm] using (cond_add_cond_compl_eq (μ := p) (t := t) hs).symm
  -- affinity of the barycenter turns the splitting of `p` into a splitting of `ρ`
  have hmix_split : deFinettiBarycenter p =
      p s • deFinettiBarycenter (p[|s]) + p sᶜ • deFinettiBarycenter (p[|sᶜ]) := by
    conv_lhs => rw [hp_split]
    simp only [deFinettiBarycenter_add, deFinettiBarycenter_smul]
  have hopen : ρ ∈
      openSegment ℝ≥0∞ (deFinettiBarycenter (p[|s])) (deFinettiBarycenter (p[|sᶜ])) :=
    ⟨p s, p sᶜ, pos_iff_ne_zero.2 hs0, pos_iff_ne_zero.2 hsc0,
      prob_add_prob_compl hs, hmix_split.symm.trans hrepr.symm⟩
  have hμs : deFinettiBarycenter (p[|s]) = ρ := hρ.2 hs_mem hsc_mem hopen
  have hbary : deFinettiBarycenter (p[|s]) = deFinettiBarycenter p := hμs.trans hrepr
  simp only [deFinettiBarycenter_def] at hbary
  exact TauCeti.MeasureTheory.Measure.ext_of_bind_infinitePi_eq hbary

/-- **An extreme exchangeable law is i.i.d.** De Finetti writes the law as a mixture over
`ProbabilityMeasure α`; extremality forces the mixing measure to be a zero-one law, hence a Dirac
mass, and the mixture collapses to a single infinite product. -/
private theorem exists_eq_infinitePi_of_mem_extremePoints [StandardBorelSpace α]
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ]
    (hρ : ρ ∈ extremePoints ℝ≥0∞
      {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν}) :
    ∃ P : ProbabilityMeasure α,
      ρ = Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
  obtain ⟨π, hrepr, -⟩ := hρ.1.1.existsUnique_mixingLaw
  let p : Measure (ProbabilityMeasure α) := π
  have : IsProbabilityMeasure p := π.2
  have hrepr' : ρ = deFinettiBarycenter p := hrepr
  have hp_zeroOne : IsZeroOneMeasure p := {
    zero_one₀ := fun s hs => by
      by_cases hs0 : p s = 0
      · exact Or.inl hs0
      by_cases hs1 : p s = 1
      · exact Or.inr hs1
      exfalso
      have hsc0 : p sᶜ ≠ 0 := fun h => hs1 ((prob_compl_eq_zero_iff hs).mp h)
      have hps : p[|s] = p := cond_eq_of_extreme_iidMixture hρ hrepr' hs hs0 hsc0
      apply hs1
      rw [← hps]
      exact cond_apply_self hs0 (measure_ne_top p s)
    }
  let : IsZeroOneMeasure p := hp_zeroOne
  obtain ⟨P, hp⟩ :=
    TauCeti.MeasureTheory.IsZeroOneMeasure.exists_eq_dirac_probabilityMeasure (π := p)
  exact ⟨P, by rw [hrepr', hp, deFinettiBarycenter_dirac]⟩

/-- **An i.i.d. law is an extreme exchangeable law.** The infinite product is ergodic for the
shift, hence extreme among the shift-invariant laws; exchangeable laws are shift-invariant, so
extremality survives the passage to that smaller set. -/
theorem infinitePi_mem_extremePoints_exchangeable (P : ProbabilityMeasure α) :
    (Measure.infinitePi fun _ : ℕ => (P : Measure α)) ∈ extremePoints ℝ≥0∞
      {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν} := by
  let ρP := Measure.infinitePi fun _ : ℕ => (P : Measure α)
  have herg : Ergodic (shift α) ρP := ergodic_shift_infinitePi_const P
  have hshiftExtreme : ρP ∈ extremePoints ℝ≥0∞
      {ν : Measure (ℕ → α) |
        MeasurePreserving (shift α) ν ν ∧ IsProbabilityMeasure ν} :=
    herg.mem_extremePoints
  have hsubset :
      {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν} ⊆
        {ν : Measure (ℕ → α) |
          MeasurePreserving (shift α) ν ν ∧ IsProbabilityMeasure ν} := by
    rintro ν ⟨hν, hνprob⟩
    let : IsProbabilityMeasure ν := hνprob
    exact ⟨hν.contractableLaw.measurePreserving_shift, hνprob⟩
  have hρPexch : ExchangeableLaw (Measure.infinitePi fun _ : ℕ => (P : Measure α)) := by
    rw [← deFinettiBarycenter_dirac P]
    exact exchangeableLaw_deFinettiBarycenter
  exact inter_extremePoints_subset_extremePoints_of_subset hsubset
    ⟨⟨hρPexch, inferInstance⟩, hshiftExtreme⟩

/-- **The extreme exchangeable laws are exactly the i.i.d. laws.** For a standard Borel
state space, a probability measure on `ℕ → α` is an extreme point of the set of exchangeable
probability measures if and only if it is an infinite product `P^{⊗ℕ}` for some probability
measure `P` on `α`. -/
theorem exchangeable_extreme_iff_iid [StandardBorelSpace α]
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] :
    ρ ∈ extremePoints ℝ≥0∞
        {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν} ↔
      ∃ P : ProbabilityMeasure α,
        ρ = Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
  exact ⟨exists_eq_infinitePi_of_mem_extremePoints,
    fun ⟨P, hP⟩ => hP ▸ infinitePi_mem_extremePoints_exchangeable P⟩

end Probability

end TauCeti
