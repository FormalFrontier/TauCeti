/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.Representation
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic
public import Mathlib.Dynamics.Ergodic.Extreme
-- Non-public: the zero-one input for the i.i.d. direction and the comparison between invariant
-- and exchangeable events.
import TauCeti.Probability.Exchangeability.PathSpace.HewittSavage
import TauCeti.Probability.Exchangeability.PathSpace.InvariantTail
-- Non-public: exchangeable path laws are shift-preserving.
import TauCeti.Probability.Exchangeability.PathSpace.Exchangeable.ToContractable
import TauCeti.Probability.Exchangeability.ConditionallyIID.Construct
-- Non-public: a zero-one law on `ProbabilityMeasure α` is Dirac.
import TauCeti.MeasureTheory.Measure.ProbabilityMeasureExt
-- Non-public: uniqueness of the mixing law from its mixture of infinite powers.
import TauCeti.MeasureTheory.Measure.MixtureInjective
import Mathlib.Probability.Independence.InfinitePi

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

private theorem exchangeableLaw_bind_infinitePi
    {π : Measure (ProbabilityMeasure α)} [IsProbabilityMeasure π] :
    ExchangeableLaw
      (π.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)) := by
  haveI := isProbabilityMeasure_iidMixtureLaw (π := π) (P := id) measurable_id
  have hX := exchangeable_iidMixtureLaw (π := π) (P := id) measurable_id
  have hcoord : ∀ n, AEMeasurable
      (fun ω : ProbabilityMeasure α × (ℕ → α) => ω.2 n) (iidMixtureLaw π id) :=
    fun n => ((measurable_pi_apply n).comp measurable_snd).aemeasurable
  have hlaw := (exchangeable_iff_exchangeableLaw_pathLaw
    (X := fun n (ω : ProbabilityMeasure α × (ℕ → α)) => ω.2 n) hcoord).mp hX
  rw [pathLaw_iidMixtureLaw (π := π) (P := id) measurable_id] at hlaw
  simpa using hlaw

/-- An i.i.d. infinite product law is ergodic for the one-sided shift.

The shift-invariant σ-algebra is contained in the exchangeable σ-algebra, and the coordinate
process is independent and identically distributed under the product law, so Hewitt–Savage makes
every shift-invariant event null or conull. -/
theorem ergodic_shift_infinitePi_const (P : ProbabilityMeasure α) :
    Ergodic (shift α) (Measure.infinitePi fun _ : ℕ => (P : Measure α)) := by
  let ρ := Measure.infinitePi fun _ : ℕ => (P : Measure α)
  have hindep : iIndepFun (fun n (x : ℕ → α) => x n) ρ :=
    iIndepFun_infinitePi (P := fun _ : ℕ => (P : Measure α))
      (X := fun _ x => x) fun _ => measurable_id
  have hident : ∀ n, IdentDistrib (fun x : ℕ → α => x n) (fun x => x 0) ρ ρ := fun n =>
    ⟨(measurable_pi_apply n).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
      simp [ρ, Measure.infinitePi_map_eval]⟩
  have hexch : Exchangeable ρ (fun n (x : ℕ → α) => x n) :=
    Exchangeable.of_iIndepFun_identDistrib hindep hident
  have hpath : pathLaw ρ (fun n (x : ℕ → α) => x n) = ρ := by simp [pathLaw_def]
  have hexchLaw : ExchangeableLaw ρ :=
    hpath ▸ (exchangeable_iff_exchangeableLaw_pathLaw
      (fun n => (measurable_pi_apply n).aemeasurable)).1 hexch
  refine { hexchLaw.contractableLaw.measurePreserving_shift with aeconst_set := ?_ }
  intro s hs hs_shift
  have hs_inv : MeasurableSet[MeasurableSpace.invariants (shift α)] s := ⟨hs, hs_shift⟩
  have hs_exch : MeasurableSet[exchangeableSigma α] s :=
    invariants_shift_le_exchangeableSigma (α := α) s hs_inv
  have hzeroOne := hewittSavage_trivial_of_iIndep hindep hident hs_exch
  rw [hpath] at hzeroOne
  refine eventuallyConst_set.2 ?_
  rcases hzeroOne with hzero | hone
  · exact Or.inr (ae_iff.mpr (by simpa using hzero))
  · exact Or.inl ((_root_.MeasureTheory.mem_ae_iff_prob_eq_one hs).2 hone)

private theorem cond_eq_of_extreme_iidMixture [StandardBorelSpace α]
    {p : Measure (ProbabilityMeasure α)} [IsProbabilityMeasure p]
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ]
    (hρ : ρ ∈ extremePoints ℝ≥0∞
      {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν})
    (hrepr : ρ = p.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α))
    {s : Set (ProbabilityMeasure α)} (hs : MeasurableSet s) (hs0 : p s ≠ 0)
    (hsc0 : p sᶜ ≠ 0) : p[|s] = p := by
  let ps : Measure (ProbabilityMeasure α) := p[|s]
  let psc : Measure (ProbabilityMeasure α) := p[|sᶜ]
  haveI : IsProbabilityMeasure ps := cond_isProbabilityMeasure hs0
  haveI : IsProbabilityMeasure psc := cond_isProbabilityMeasure hsc0
  let μs : Measure (ℕ → α) :=
    ps.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)
  let μsc : Measure (ℕ → α) :=
    psc.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)
  have hpow : Measurable fun P : ProbabilityMeasure α =>
      Measure.infinitePi fun _ : ℕ => (P : Measure α) :=
    TauCeti.MeasureTheory.measurable_infinitePi_const
  haveI : IsProbabilityMeasure μs := isProbabilityMeasure_bind hpow.aemeasurable
    (ae_of_all _ fun _ => inferInstance)
  haveI : IsProbabilityMeasure μsc := isProbabilityMeasure_bind hpow.aemeasurable
    (ae_of_all _ fun _ => inferInstance)
  have hs_mem : μs ∈
      {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν} :=
    ⟨exchangeableLaw_bind_infinitePi, inferInstance⟩
  have hsc_mem : μsc ∈
      {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν} :=
    ⟨exchangeableLaw_bind_infinitePi, inferInstance⟩
  have hp_split : p = p s • ps + p sᶜ • psc := by
    ext t ht
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    simpa [mul_comm] using (cond_add_cond_compl_eq (μ := p) (t := t) hs).symm
  have hmix_split :
      p.bind (fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)) =
        p s • μs + p sᶜ • μsc := by
    calc
      p.bind (fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)) =
          (p s • ps + p sᶜ • psc).bind
            (fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)) :=
        congrArg
          (fun q : Measure (ProbabilityMeasure α) =>
            q.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)) hp_split
      _ = p s • μs + p sᶜ • μsc := by
        have h := Measure.bind_sum
          (fun b : Bool => if b then p s • ps else p sᶜ • psc)
          (fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)) hpow.aemeasurable
        simpa [Measure.sum_bool, Measure.bind_smul, μs, μsc] using h
  have hopen : ρ ∈ openSegment ℝ≥0∞ μs μsc :=
    ⟨p s, p sᶜ, pos_iff_ne_zero.2 hs0, pos_iff_ne_zero.2 hsc0,
      prob_add_prob_compl hs, hmix_split.symm.trans hrepr.symm⟩
  have hμs : μs = ρ := hρ.2 hs_mem hsc_mem hopen
  exact TauCeti.MeasureTheory.Measure.ext_of_bind_infinitePi_eq (hμs.trans hrepr)

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
  letI : Nonempty α := (nonempty_of_isProbabilityMeasure ρ).map fun x => x 0
  constructor
  · intro hρ
    have hcoord : ∀ n, Measurable (fun x : ℕ → α => x n) := fun n => measurable_pi_apply n
    have hX : Exchangeable ρ (fun n x => x n) :=
      (exchangeable_iff_exchangeableLaw_pathLaw fun n => (hcoord n).aemeasurable).2 (by
        simpa [pathLaw_def] using hρ.1.1)
    obtain ⟨π, hrepr, -⟩ := deFinetti_mixture hX hcoord
    have hrepr' : ρ = (π : Measure (ProbabilityMeasure α)).bind
        fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
      simpa [pathLaw_def] using hrepr
    let p : Measure (ProbabilityMeasure α) := π
    haveI : IsProbabilityMeasure p := π.2
    have hp_zeroOne : IsZeroOneMeasure p := {
      zero_one₀ := fun s hs => by
        by_cases hs0 : p s = 0
        · exact Or.inl hs0
        by_cases hs1 : p s = 1
        · exact Or.inr hs1
        exfalso
        have hsc0 : p sᶜ ≠ 0 := fun h => hs1 ((prob_compl_eq_zero_iff hs).mp h)
        have hps : p[|s] = p := cond_eq_of_extreme_iidMixture hρ (by simpa [p] using hrepr')
          hs hs0 hsc0
        apply hs1
        rw [← hps]
        exact cond_apply_self hs0 (measure_ne_top p s)
      }
    letI : IsZeroOneMeasure p := hp_zeroOne
    obtain ⟨P, hp⟩ :=
      TauCeti.MeasureTheory.IsZeroOneMeasure.exists_eq_dirac_probabilityMeasure (π := p)
    refine ⟨P, ?_⟩
    calc
      ρ = p.bind (fun Q => Measure.infinitePi fun _ : ℕ => (Q : Measure α)) := by
        simpa [p] using hrepr'
      _ = Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
        rw [hp, Measure.dirac_bind TauCeti.MeasureTheory.measurable_infinitePi_const]
  · rintro ⟨P, rfl⟩
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
      letI : IsProbabilityMeasure ν := hνprob
      exact ⟨hν.contractableLaw.measurePreserving_shift, hνprob⟩
    have hρPexch : ExchangeableLaw ρP := by
      have hdirac : ρP = (Measure.dirac P).bind
          (fun Q => Measure.infinitePi fun _ : ℕ => (Q : Measure α)) := by
        rw [Measure.dirac_bind TauCeti.MeasureTheory.measurable_infinitePi_const]
      rw [hdirac]
      exact exchangeableLaw_bind_infinitePi
    exact inter_extremePoints_subset_extremePoints_of_subset hsubset
      ⟨⟨hρPexch, inferInstance⟩, hshiftExtreme⟩

end Probability

end TauCeti
