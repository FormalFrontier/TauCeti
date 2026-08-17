/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.Mixture
public import TauCeti.Probability.DeFinetti.Theorem

/-!
# The unique de Finetti mixture representation

De Finetti's theorem identifies an exchangeable sequence with a unique mixture of i.i.d. sequence
laws. In path-law form, there is a unique probability measure `π` on `ProbabilityMeasure α` such
that

```text
pathLaw μ X = ∫ P^{⊗ℕ} dπ(P).
```

The conditional theorem `conditionallyIID_of_exchangeable` supplies a directing measure, hence a
mixed-i.i.d. witness after integrating out the directing coordinate.
`MixedIID.existsUnique_mixingLaw` then packages the witness's law intrinsically: the injectivity of
the infinite-product mixture makes `π` independent of the chosen directing measure.

This is the `deFinetti_mixture` target from
`TauCetiRoadmap/Exchangeability/README.md`, Layer 6, “directing measures and de Finetti
representation.” It is the mixture-of-product-measures form with the unique law of the directing
measure. Unlike the sample-space-specific `deFinettiMeasure`, the statement needs a standard Borel
structure only on the state space `α`; the sample space `Ω` remains an arbitrary measurable space.

The mathematical statement follows Kallenberg, *Probabilistic Symmetries and Invariance
Principles* (2005), Theorem 1.1. The proof is an assembly of Tau Ceti's conditional de Finetti
theorem, infinite-product mixture representation, and mixing-law injectivity; no formalization is
ported or adapted here.

## Main result

* `deFinetti_mixture` — an exchangeable sequence has a unique mixing law in its infinite-product
  representation.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **De Finetti's theorem, unique mixture form.** An exchangeable process under a probability law,
with a.e. measurable coordinates in a standard Borel state space, has a unique probability mixing
law `π` for which its path law is the `π`-mixture of the i.i.d. infinite product laws.

No nonemptiness hypothesis on `α` is needed, although the directing-measure construction behind the
proof requires one: a probability measure on `Ω` exhibits a point of `Ω`, which `X 0` carries into
`α`. That step is why the coordinates appear here at all — everything else in the statement, both
`pathLaw μ X` and the uniqueness endpoint `MixedIID.existsUnique_mixingLaw`, sees `X` only up to
a.e. equality. -/
theorem deFinetti_mixture [StandardBorelSpace α] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α} (hX : Exchangeable μ X)
    (hX_meas : ∀ n, AEMeasurable (X n) μ) :
    ∃! π : ProbabilityMeasure (ProbabilityMeasure α),
      pathLaw μ X = (π : Measure (ProbabilityMeasure α)).bind
        fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
  have : Nonempty α := (nonempty_of_isProbabilityMeasure μ).map (X 0)
  exact (mixedIID_of_conditionallyIID (conditionallyIID_of_exchangeable hX hX_meas))
    |>.existsUnique_mixingLaw hX_meas

end Probability

end TauCeti
