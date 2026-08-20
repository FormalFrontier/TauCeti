/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Representation
public import Mathlib.Probability.ProductMeasure

/-!
# Randomizing a probability measure by a uniform variable

A probability measure on a standard Borel space is the law of a measurable function of a single
uniform variable, and the function can be chosen to depend measurably on the measure. Packaging
that choice once gives a **coding map**

```text
unitIntervalCoding α : ProbabilityMeasure α → I → α
```

which is jointly measurable and satisfies `volume.map (unitIntervalCoding α P) = P` for every `P`.
Feeding it independent uniform variables therefore realizes any product `P^{⊗ι}` as the law of a
coordinatewise transform of uniform noise, which is `map_infinitePi_volume_unitIntervalCoding`.

This is the "isolation of randomness" step: a random probability measure `ν` and an independent
uniform sequence `ϑ` together generate a sample from `ν`, with all the randomness of the sample
carried by `ϑ`. It is what turns a conditional-distribution statement into a *functional*
representation.

## Main definitions

* `TauCeti.Probability.samplingKernel` — the tautological Markov kernel
  `ProbabilityMeasure α → α`, which samples from its own parameter.
* `TauCeti.Probability.unitIntervalCoding` — the coding map above.

## Main results

* `TauCeti.Probability.map_volume_unitIntervalCoding` — the coding map transports the uniform law
  on `I` to its parameter.
* `TauCeti.Probability.map_infinitePi_volume_unitIntervalCoding` — applying it coordinatewise to
  i.i.d. uniform noise produces the countable power of the parameter.
* `TauCeti.Probability.exists_measurable_uncurry_map_volume_eq` — the same statement for a
  measurable family of probability measures indexed by an arbitrary parameter space.

## Implementation

Mathlib's `ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval` supplies the coding for
an arbitrary Markov kernel into a standard Borel space; the content here is applying it to the
tautological kernel, so that the parameter space is the space of probability measures itself and no
further choice has to be threaded through downstream statements. `unitIntervalCoding` is therefore
a choice: it has no properties beyond the two recorded below, and consumers should use those rather
than unfold it.

## References

* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 4.22.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **The tautological Markov kernel.** It sends a probability measure to itself, viewed as a
random element of `α`; sampling from it is sampling from its own parameter. -/
-- `@[expose]` is forced by the exported `rfl`-unfold `samplingKernel_apply` below.
@[expose]
def samplingKernel (α : Type*) [MeasurableSpace α] : Kernel (ProbabilityMeasure α) α :=
  ⟨fun P => (P : Measure α), measurable_subtype_coe⟩

@[simp]
theorem samplingKernel_apply (P : ProbabilityMeasure α) :
    samplingKernel α P = (P : Measure α) :=
  rfl

instance : IsMarkovKernel (samplingKernel α) :=
  ⟨fun P => P.2⟩

variable (α)

/-- **The coding map of a standard Borel space.** A jointly measurable
`ProbabilityMeasure α → I → α` transporting the uniform law on the unit interval to its parameter,
`map_volume_unitIntervalCoding`.

This is a choice among the maps with that property; the two lemmas below are its entire
specification. -/
def unitIntervalCoding [StandardBorelSpace α] [Nonempty α] : ProbabilityMeasure α → I → α :=
  (Kernel.exists_measurable_map_eq_unitInterval (samplingKernel α)).choose

variable [StandardBorelSpace α] [Nonempty α]

/-- The coding map is jointly measurable in the parameter and the uniform variable. -/
theorem measurable_uncurry_unitIntervalCoding :
    Measurable (Function.uncurry (unitIntervalCoding α)) :=
  (Kernel.exists_measurable_map_eq_unitInterval (samplingKernel α)).choose_spec.1

variable {α}

/-- The coding map is measurable in the uniform variable, for each fixed parameter. -/
theorem measurable_unitIntervalCoding (P : ProbabilityMeasure α) :
    Measurable (unitIntervalCoding α P) :=
  (measurable_uncurry_unitIntervalCoding α).of_uncurry_left

/-- **The defining property of the coding map:** it transports the uniform law on `I` to its
parameter. -/
@[simp]
theorem map_volume_unitIntervalCoding (P : ProbabilityMeasure α) :
    (volume : Measure I).map (unitIntervalCoding α P) = (P : Measure α) :=
  (Kernel.exists_measurable_map_eq_unitInterval (samplingKernel α)).choose_spec.2 P

/-- **Coding a product law by i.i.d. uniform noise.** Applying the coding map coordinatewise to an
i.i.d. uniform family produces the countable power of the parameter. -/
theorem map_infinitePi_volume_unitIntervalCoding {ι : Type*} (P : ProbabilityMeasure α) :
    (Measure.infinitePi fun _ : ι => (volume : Measure I)).map
        (fun u i => unitIntervalCoding α P (u i))
      = Measure.infinitePi fun _ : ι => (P : Measure α) := by
  rw [Measure.infinitePi_map_pi (μ := fun _ : ι => (volume : Measure I))
    (f := fun _ : ι => unitIntervalCoding α P) fun _ => measurable_unitIntervalCoding P]
  simp

/-- **Randomizing a measurable family of probability measures.** Over an arbitrary parameter space,
a measurable family `Q` of probability measures on a standard Borel space is the family of laws of
a single jointly measurable function of the parameter and one uniform variable. -/
theorem exists_measurable_uncurry_map_volume_eq {T : Type*} [MeasurableSpace T]
    {Q : T → ProbabilityMeasure α} (hQ : Measurable Q) :
    ∃ f : T → I → α, Measurable (Function.uncurry f) ∧
      ∀ t, (volume : Measure I).map (f t) = (Q t : Measure α) :=
  ⟨fun t => unitIntervalCoding α (Q t),
    (measurable_uncurry_unitIntervalCoding α).comp (hQ.prodMap measurable_id),
    fun t => map_volume_unitIntervalCoding (Q t)⟩

end Probability

end TauCeti
