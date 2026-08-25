/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# The measurable structure on lists

Mathlib equips no type of lists with a measurable structure. This file gives `List α` the structure
transported from its length-indexed representation `Σ n, Fin n → α`. Thus each fixed-length stratum
has the finite product structure, and the list space is their countable disjoint union.

When `α` is countable and discrete, this structure is discrete too. In particular, a process whose
values are finite words over a countable alphabet, such as the excursion process of a path, has a
countable discrete value space.

## Main definitions

* `TauCeti.instMeasurableSpaceList`: the measurable structure on `List α` induced by its
  length-indexed representation.
* `TauCeti.instDiscreteMeasurableSpaceList`: discreteness when `α` is countable and discrete.
-/

public section

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

/-- The measurable structure on lists induced through
`List.equivSigmaTuple : List α ≃ Σ n, Fin n → α`. -/
instance instMeasurableSpaceList : MeasurableSpace (List α) :=
  MeasurableSpace.comap List.equivSigmaTuple inferInstance

/-- Lists over a countable discrete measurable space form a discrete measurable space. -/
instance instDiscreteMeasurableSpaceList [Countable α] [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (List α) :=
  ⟨fun s => by
    -- Unfold measurability in the structure pulled back along the list-tuple equivalence.
    change ∃ t : Set (Σ n, Fin n → α), MeasurableSet t ∧
      Set.preimage (List.equivSigmaTuple : List α → Σ n, Fin n → α) t = s
    refine ⟨Set.image List.equivSigmaTuple s, ?_, ?_⟩
    -- The sigma measurable space tests measurability separately on each fixed-length stratum.
    · apply MeasurableSpace.measurableSet_iInf.2
      intro n
      change MeasurableSet (Set.preimage (Sigma.mk n) (Set.image List.equivSigmaTuple s))
      let _ : MeasurableSingletonClass (Fin n → α) := inferInstance
      let _ : DiscreteMeasurableSpace (Fin n → α) := inferInstance
      exact MeasurableSet.of_discrete
    · exact Set.preimage_image_eq s List.equivSigmaTuple.injective⟩

end TauCeti

end
