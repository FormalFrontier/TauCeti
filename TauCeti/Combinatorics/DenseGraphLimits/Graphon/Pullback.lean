/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.Basic

/-!
# Reading a graphon on another carrier

A graphon on `(Ω, μ)` may be read on any other probability space through a measurable map
`f : Ω' → Ω`, by evaluating it at the images of both arguments:
`W.comap f hf μ' x y = W (f x) (f y)`. Symmetry, measurability and the `[0, 1]` range all survive,
so the result is again a graphon.

This is `SymmKernel.comap` with the range constraint carried along, and it is the object that makes
the cross-carrier theory run: the two graphons compared by the cut distance live on different
spaces, and a coupling `π` of their carriers turns both into graphons on `(Ω₁ × Ω₂, π)` — the
pullbacks along the two coordinate projections, whose difference is
`TauCeti.DenseGraphLimits.overlayDiff`. Nothing here needs `f` to be measure preserving; that
hypothesis enters only where an *integral* is transported, as in
`TauCeti.DenseGraphLimits.homDensity_comap`.

## Main definitions

* `TauCeti.DenseGraphLimits.Graphon.comap` — the pullback of a graphon along a measurable map.

## Main results

* `Graphon.comap_apply` — the eliminator `W.comap f hf μ' x y = W (f x) (f y)`;
* `Graphon.toSymmKernel_comap` — the pullback of a graphon is the pullback of its kernel, which is
  how the cut norm and the kernel algebra see it;
* `Graphon.comap_id`, `Graphon.comap_comap`, `Graphon.comap_const` — functoriality and the constant
  graphon.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 — the basic API of the `Graphon`
  object, and the cross-carrier reading of two graphons through a coupling that the
  coupling-primary `cutDist` rests on.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), §6.
-/

public section

noncomputable section

open MeasureTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

namespace Graphon

variable {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The **pullback of a graphon along a measurable map** `f : Ω' → Ω`, acting on both arguments:
`W.comap f hf μ' x y = W (f x) (f y)`.

The underlying kernel is `SymmKernel.comap`, so symmetry, measurability and boundedness are
inherited from there; the `[0, 1]` range is inherited pointwise. As for kernels, no hypothesis on
either measure is needed — `μ'` only has to be a probability measure for the result to be a
*graphon* at all.

The argument order follows `SymmKernel.comap`: the map first, then its measurability, then the
carrier measure of the result, which the data does not determine. -/
def comap (W : Graphon Ω μ) (f : Ω' → Ω) (hf : Measurable f) (μ' : Measure Ω')
    [IsProbabilityMeasure μ'] : Graphon Ω' μ' where
  toSymmKernel := W.toSymmKernel.comap f hf μ'
  mem01' x y := by
    -- `mem01'` is stated through the inherited raw `toFun` field. Since `SymmKernel.comap` is
    -- opaque, expose its coercion definitionally before applying its public evaluation lemma.
    change W.toSymmKernel.comap f hf μ' x y ∈ Set.Icc 0 1
    simpa only [SymmKernel.comap_apply, coe_toSymmKernel] using W.mem_Icc (f x) (f y)

variable (W : Graphon Ω μ) (f : Ω' → Ω) (hf : Measurable f) (μ' : Measure Ω')
  [IsProbabilityMeasure μ']

/-- Pulling back a graphon evaluates it after applying the map to both arguments. -/
@[simp]
theorem comap_apply (x y : Ω') : W.comap f hf μ' x y = W (f x) (f y) := by
  exact SymmKernel.comap_apply W.toSymmKernel f hf μ' x y

/-- The underlying kernel of a pulled-back graphon is the pullback of its kernel. This is the form
the cut norm and the kernel algebra consume, so it is the bridge between this file and
`TauCeti.Combinatorics.DenseGraphLimits.Kernel.Pullback`. -/
@[simp]
theorem toSymmKernel_comap : (W.comap f hf μ').toSymmKernel = W.toSymmKernel.comap f hf μ' := by
  ext x y
  simp

/-- Pulling back along the identity is the identity. -/
@[simp]
theorem comap_id : W.comap id measurable_id μ = W := by ext; simp

/-- Pullbacks compose contravariantly. -/
@[simp]
theorem comap_comap (g : Ω'' → Ω') (hg : Measurable g) (μ'' : Measure Ω'')
    [IsProbabilityMeasure μ''] :
    (W.comap f hf μ').comap g hg μ'' = W.comap (f ∘ g) (hf.comp hg) μ'' := by ext; simp

/-- The constant graphon pulls back to the constant graphon with the same parameter. -/
@[simp]
theorem comap_const (p : I) : (const μ p).comap f hf μ' = const μ' p := by ext; simp

end Graphon

end DenseGraphLimits

end TauCeti
