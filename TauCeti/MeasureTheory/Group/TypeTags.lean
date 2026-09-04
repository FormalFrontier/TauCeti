/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Measure theory on the multiplicative type tag

`Multiplicative α` is the type `α` with its addition renamed to multiplication. Mathlib transports
the algebraic and topological structure of `α` along that renaming, but not the measurable
structure, so an additive group carrying a Haar measure is not usable as a *multiplicative* group
with a Haar measure. This file supplies the missing transport: the measurable space, the Borel
property, the three measure-theoretic size conditions, and left invariance, from which the
`IsHaarMeasure` instance follows.

Everything here is definitional — `Multiplicative α` and `α` are the same type, with the same
topology and the same σ-algebra — so each instance is the corresponding instance on `α`, and
`Measure.IsMulLeftInvariant` is `Measure.IsAddLeftInvariant` read through
`Multiplicative.toAdd`. What the instances add is that typeclass search can find them: a class
whose argument is the *type* `Multiplicative α` (`MeasurableSpace`, `BorelSpace`,
`IsMulLeftInvariant`) is keyed on that head symbol and no instance for `α` will match, and even a
class whose only argument is the measure (`IsProbabilityMeasure`,
`IsFiniteMeasureOnCompacts`, `IsOpenPosMeasure`) is stated with the ambient type fixed by the
measure's spelling, so it must be restated once the measure is read as a measure on
`Multiplicative α`.

Only the `Multiplicative` direction is built, because that is the direction a consumer needs: the
representation theory of a group is stated for a multiplicative group, while Mathlib's circle,
`AddCircle T`, is additive. The `Additive` analogues are the same one-line transports and are
omitted until something asks for them.

## Main definitions

* `TauCeti.instMeasurableSpaceMultiplicative`: the σ-algebra of `Multiplicative α` is that of `α`.
* `TauCeti.instIsMulLeftInvariantMultiplicative`: a left-invariant measure for the addition of `α`
  is left invariant for the multiplication of `Multiplicative α`.
* `TauCeti.instIsHaarMeasureMultiplicative`: an additive Haar measure on `α` is a Haar measure on
  `Multiplicative α`.

## Tags

multiplicative, type tag, Haar measure, measurable space
-/

public section

open MeasureTheory

namespace TauCeti

variable {α : Type*}

/-- `Multiplicative α` carries the σ-algebra of `α`. -/
instance instMeasurableSpaceMultiplicative [m : MeasurableSpace α] :
    MeasurableSpace (Multiplicative α) := m

/-- `Multiplicative α` inherits the Borel property, since it has both the topology and the
σ-algebra of `α`. -/
instance instBorelSpaceMultiplicative [TopologicalSpace α] [MeasurableSpace α] [h : BorelSpace α] :
    BorelSpace (Multiplicative α) := h

/-- A probability measure on `α` is a probability measure on `Multiplicative α`. -/
instance instIsProbabilityMeasureMultiplicative [MeasurableSpace α] (μ : Measure α)
    [h : IsProbabilityMeasure μ] : IsProbabilityMeasure (α := Multiplicative α) μ := h

/-- A measure finite on the compact sets of `α` is finite on the compact sets of
`Multiplicative α`. -/
instance instIsFiniteMeasureOnCompactsMultiplicative [TopologicalSpace α] [MeasurableSpace α]
    (μ : Measure α) [h : IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (α := Multiplicative α) μ := h

/-- A measure positive on the nonempty open sets of `α` is positive on the nonempty open sets of
`Multiplicative α`. -/
instance instIsOpenPosMeasureMultiplicative [TopologicalSpace α] [MeasurableSpace α]
    (μ : Measure α) [h : μ.IsOpenPosMeasure] :
    Measure.IsOpenPosMeasure (X := Multiplicative α) μ := h

/-- Left invariance for the addition of `α` **is** left invariance for the multiplication of
`Multiplicative α`: the two translations are the same map. -/
instance instIsMulLeftInvariantMultiplicative [Add α] [MeasurableSpace α] (μ : Measure α)
    [h : μ.IsAddLeftInvariant] : Measure.IsMulLeftInvariant (G := Multiplicative α) μ :=
  ⟨h.map_add_left_eq_self⟩

/-- **An additive Haar measure is a Haar measure on the multiplicative type tag.** The three
constituents — finiteness on compacts, left invariance, positivity on nonempty opens — are the
instances above; only the assembly into `IsHaarMeasure` is new, because a structure class is not
found from its fields by typeclass search. -/
instance instIsHaarMeasureMultiplicative [TopologicalSpace α] [AddGroup α] [MeasurableSpace α]
    (μ : Measure α) [μ.IsAddHaarMeasure] : Measure.IsHaarMeasure (G := Multiplicative α) μ where

end TauCeti
