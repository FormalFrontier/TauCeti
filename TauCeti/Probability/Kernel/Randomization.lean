/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.ProbabilityMeasure
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

* `TauCeti.Probability.unitIntervalCoding` — the coding map above.

## Main results

* `TauCeti.Probability.map_volume_unitIntervalCoding` — the coding map transports the uniform law
  on `I` to its parameter.
* `TauCeti.Probability.map_infinitePi_volume_unitIntervalCoding` — applying it coordinatewise to
  i.i.d. uniform noise produces the `ι`-fold power of the parameter for an arbitrary index type.

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
@[fun_prop]
theorem measurable_uncurry_unitIntervalCoding :
    Measurable (Function.uncurry (unitIntervalCoding α)) :=
  (Kernel.exists_measurable_map_eq_unitInterval (samplingKernel α)).choose_spec.1

variable {α}

/-- The coding map is measurable in the uniform variable, for each fixed parameter. -/
@[fun_prop]
theorem measurable_unitIntervalCoding (P : ProbabilityMeasure α) :
    Measurable (unitIntervalCoding α P) :=
  (measurable_uncurry_unitIntervalCoding α).of_uncurry_left

/-- **The defining property of the coding map:** it transports the uniform law on `I` to its
parameter. -/
@[simp]
theorem map_volume_unitIntervalCoding (P : ProbabilityMeasure α) :
    (volume : Measure I).map (unitIntervalCoding α P) = (P : Measure α) :=
  calc
    (volume : Measure I).map (unitIntervalCoding α P) = samplingKernel α P :=
      (Kernel.exists_measurable_map_eq_unitInterval (samplingKernel α)).choose_spec.2 P
    _ = (P : Measure α) := samplingKernel_apply P

/-- The coordinatewise coding of an `ι`-indexed uniform family is measurable. -/
theorem measurable_pi_unitIntervalCoding {ι : Type*} (P : ProbabilityMeasure α) :
    Measurable fun u : ι → I => fun i => unitIntervalCoding α P (u i) :=
  measurable_pi_lambda _ fun i =>
    (measurable_unitIntervalCoding P).comp (measurable_pi_apply i)

/-- **Coding a product law by i.i.d. uniform noise.** Applying the coding map coordinatewise to an
i.i.d. uniform family produces the `ι`-fold power of the parameter, for an arbitrary index type. -/
@[simp]
theorem map_infinitePi_volume_unitIntervalCoding {ι : Type*} (P : ProbabilityMeasure α) :
    (Measure.infinitePi fun _ : ι => (volume : Measure I)).map
        (fun u i => unitIntervalCoding α P (u i))
      = Measure.infinitePi fun _ : ι => (P : Measure α) := by
  rw [Measure.infinitePi_map_pi (μ := fun _ : ι => (volume : Measure I))
    (f := fun _ : ι => unitIntervalCoding α P) fun _ => measurable_unitIntervalCoding P]
  simp

end Probability

end TauCeti
