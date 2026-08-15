/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.Barycenter
-- Public: the correspondence's point masses are characterized by extremality.
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Extreme
-- Non-public: used only inside proofs — injectivity of the mixture is what makes the
-- correspondence injective.
import TauCeti.MeasureTheory.Measure.MixtureInjective

/-!
# The de Finetti correspondence

De Finetti's theorem says that the barycenter map `π ↦ ∫ P^{⊗ℕ} dπ(P)` is a bijection from mixing
laws onto exchangeable path laws. This file packages that bijection as an equivalence

```text
deFinettiEquiv :
  ProbabilityMeasure (ProbabilityMeasure α) ≃ {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw ρ}
```

for a standard Borel state space `α`, and identifies its point masses.

Injectivity is `Measure.ext_of_bind_infinitePi_eq`, surjectivity is
`ExchangeableLaw.existsUnique_mixingLaw` — de Finetti's theorem in path-law form. The inverse
`deFinettiEquiv.symm` is therefore a genuine construction: it reads the mixing law off an
exchangeable law.

The correspondence is affine, `deFinettiBarycenter_add` and `deFinettiBarycenter_smul` giving
the mixture identity on the barycenter side; and it takes the point masses of
`ProbabilityMeasure α` exactly to the extreme exchangeable laws
(`deFinettiBarycenter_mem_extremePoints_iff`, `deFinettiEquiv_dirac`). Reading
`deFinettiBarycenter` as `deFinettiBarycenter_eq_join_map` does, this is the canonical
decomposition of an exchangeable law over the extreme — equivalently the
i.i.d. — exchangeable laws: the mixing law is unique, and the path laws it averages are extreme.

This settles the Layer 8 bullet "the affine and ergodic decomposition of exchangeable laws" in
`TauCetiRoadmap/Exchangeability/README.md`. Together with `exchangeableSigma_trivial_iff_iid`,
`exchangeableSigma_trivial_iff_ergodicSMul` and `exchangeable_extreme_iff_iid`, this correspondence
identifies the product — equivalently extreme — components with the ergodic components for the
finitely supported permutation action, which that bullet sequences after the `ErgodicSMul` interface
of Layer 6. Those equivalences compose directly; no additional correspondence declaration is
required.

⚠ The action is the finitely supported permutations of the *time index*. Ergodicity for it is a
different statement from ergodicity of the one-sided shift, which concerns the smaller σ-algebra of
shift-invariant events; see `PathSpace/Exchangeable/Ergodic.lean`.

## Main results

* `deFinettiEquiv` — mixing laws correspond bijectively to exchangeable path laws.
* `deFinettiEquiv_dirac` — a point mass corresponds to an i.i.d. law.
* `deFinettiBarycenter_mem_extremePoints_iff` — a barycenter is an extreme exchangeable law
  exactly when its mixing law is a point mass.

## References

* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 1, Theorem 1.1.
* David Aldous, *Exchangeability and related topics*, École d'Été de Probabilités de Saint-Flour
  XIII, 1983, §3, for the affine and extreme-point reading of the representation.

No material is adapted from `cameronfreer/exchangeability`, which does not package the
representation as a correspondence.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **The de Finetti correspondence.** Over a standard Borel state space, the de Finetti
barycenter is a bijection from mixing laws — probability measures on `ProbabilityMeasure α` — onto
exchangeable probability measures on `ℕ → α`.

The forward map is `deFinettiBarycenter`; the inverse sends an exchangeable law to its mixing law.
Injectivity is uniqueness of the mixing law and surjectivity is de Finetti's theorem, so the
equivalence is exactly the content of `ExchangeableLaw.existsUnique_mixingLaw` in bijective
form. -/
def deFinettiEquiv [StandardBorelSpace α] :
    ProbabilityMeasure (ProbabilityMeasure α) ≃
      {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw (ρ : Measure (ℕ → α))} :=
  Equiv.ofBijective
    (fun π : ProbabilityMeasure (ProbabilityMeasure α) =>
      ⟨⟨deFinettiBarycenter π.toMeasure, inferInstance⟩, exchangeableLaw_deFinettiBarycenter⟩)
    ⟨fun π₁ π₂ h => by
      have h' : deFinettiBarycenter π₁.toMeasure = deFinettiBarycenter π₂.toMeasure :=
        congrArg (fun r : {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw ρ.toMeasure} =>
          ProbabilityMeasure.toMeasure r.1) h
      simp only [deFinettiBarycenter_def] at h'
      exact ProbabilityMeasure.toMeasure_injective
        (TauCeti.MeasureTheory.Measure.ext_of_bind_infinitePi_eq h'),
      fun ρ => by
        obtain ⟨π, hπ, -⟩ := ρ.2.existsUnique_mixingLaw
        exact ⟨π, Subtype.ext (ProbabilityMeasure.toMeasure_injective hπ.symm)⟩⟩

@[simp]
theorem deFinettiEquiv_apply_coe [StandardBorelSpace α]
    (π : ProbabilityMeasure (ProbabilityMeasure α)) :
    ((deFinettiEquiv π : ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α)) =
      deFinettiBarycenter (π : Measure (ProbabilityMeasure α)) :=
  (rfl)

/-- The inverse of the correspondence really is the mixing law: the barycenter of the mixing law
of an exchangeable law recovers that law. -/
@[simp]
theorem deFinettiBarycenter_deFinettiEquiv_symm [StandardBorelSpace α]
    (ρ : {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw (ρ : Measure (ℕ → α))}) :
    deFinettiBarycenter ((deFinettiEquiv.symm ρ : ProbabilityMeasure (ProbabilityMeasure α)) :
        Measure (ProbabilityMeasure α)) = (ρ : ProbabilityMeasure (ℕ → α)) := by
  rw [← deFinettiEquiv_apply_coe, deFinettiEquiv.apply_symm_apply]

/-- The mixing law is characterized by its barycenter: a mixing law whose barycenter is `ρ` is
*the* mixing law of `ρ`. -/
theorem deFinettiEquiv_symm_eq [StandardBorelSpace α]
    {ρ : {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw (ρ : Measure (ℕ → α))}}
    {π : ProbabilityMeasure (ProbabilityMeasure α)}
    (h : ((ρ : ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α)) =
      deFinettiBarycenter (π : Measure (ProbabilityMeasure α))) :
    deFinettiEquiv.symm ρ = π :=
  deFinettiEquiv.symm_apply_eq.2 (Subtype.ext (Subtype.ext h))

/-- **Point masses correspond to i.i.d. laws.** A mixing law concentrated at `P` corresponds to
the i.i.d. law `P^{⊗ℕ}`. -/
@[simp]
theorem deFinettiEquiv_dirac [StandardBorelSpace α] (P : ProbabilityMeasure α) :
    ((deFinettiEquiv ⟨Measure.dirac P, inferInstance⟩ : ProbabilityMeasure (ℕ → α)) :
        Measure (ℕ → α)) = Measure.infinitePi fun _ : ℕ => (P : Measure α) :=
  deFinettiBarycenter_dirac P

/-- **The extreme fibres of the correspondence are exactly the point masses.** The de Finetti
barycenter of a mixing law is an extreme exchangeable probability law if and only if that mixing
law is a Dirac mass.

Combined with `deFinettiBarycenter_eq_join_map`, this is the canonical decomposition an
exchangeable law admits: it is the barycenter of a unique law on path laws, and that law is
carried by the extreme — equivalently i.i.d. — exchangeable laws
(`infinitePi_mem_extremePoints_exchangeable`), degenerating exactly on the extreme points
themselves. -/
theorem deFinettiBarycenter_mem_extremePoints_iff [StandardBorelSpace α]
    {π : Measure (ProbabilityMeasure α)} [IsProbabilityMeasure π] :
    deFinettiBarycenter π ∈ extremePoints ℝ≥0∞
        {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν} ↔
      ∃ P : ProbabilityMeasure α, π = Measure.dirac P := by
  rw [exchangeable_extreme_iff_iid]
  refine ⟨fun ⟨P, hP⟩ => ⟨P, TauCeti.MeasureTheory.Measure.ext_of_bind_infinitePi_eq ?_⟩,
    fun ⟨P, hP⟩ => ⟨P, ?_⟩⟩
  · simp only [← deFinettiBarycenter_def, hP, deFinettiBarycenter_dirac]
  · rw [hP, deFinettiBarycenter_dirac]

end Probability

end TauCeti
