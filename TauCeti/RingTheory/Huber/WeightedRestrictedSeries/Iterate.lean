/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

/-!
# From `A⟨X₁,…,X_{k+m}⟩` to `A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩`

Splitting the variables of a completed restricted power-series algebra into a first block of `k`
and a second of `m` presents the algebra in two variables at once as an algebra in `m` variables
over the algebra in `k`. This file constructs the comparison map in one direction,

```text
A⟨X₁,…,X_{k+m}⟩ ⟶ A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩,
```

as the unique continuous homomorphism carrying `Xᵢ` to the `i`-th generator of the iterated
algebra: for `i < k` the `i`-th variable of the inner algebra, read as a constant series of the
outer one, and for `i ≥ k` the corresponding variable of the outer algebra.

It is Wedhorn's Proposition 5.50 for the completed algebra — `weightedEvalHomCompletion` — applied
to that tuple of generators. Two things make the application legitimate and neither is automatic:
the target must be a *complete Hausdorff nonarchimedean* ring, which for an iterated algebra rests
on the completion of a nonarchimedean group being nonarchimedean; and the tuple must be
power-bounded, which is `isPowerBounded_coe_weightedC` and `isPowerBounded_coe_weightedX_one_weight`
of the module on power-boundedness.

## Main definitions

* `TauCeti.Huber.iterateVar`: the generators of `A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩`, indexed by `Fin (k + m)`
  as those of `A⟨X₁,…,X_{k+m}⟩` are.
* `TauCeti.Huber.iterateStructureHom`: the structure map `A → A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩`, the composite
  of the two the iterated algebra is built from.
* `TauCeti.Huber.iterateComparisonHom`: the comparison map itself.

## Main results

* `TauCeti.Huber.isPowerBounded_iterateVar`: every generator of the iterated algebra is
  power-bounded in it, which is what Proposition 5.50 asks of the tuple.
* `TauCeti.Huber.continuous_iterateComparisonHom`, with
  `TauCeti.Huber.iterateComparisonHom_coe_weightedC` and
  `TauCeti.Huber.iterateComparisonHom_coe_weightedX`: the comparison map is a morphism of
  topological rings, and its values on the generators. The body of the definition is not exported,
  so those two are how a consumer computes with it.

## What is not here

The map in the other direction, and that the two are mutually inverse. The roadmap asks for the
isomorphism `A⟨X⟩⟨Y⟩ ≅ A⟨X,Y⟩`; this is the first of its two halves, in the shape the identification
of Wedhorn's Remark 7.55 was built in — the two comparison maps first, then the equivalence.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50, whose
  completed form this applies.
-/

public section

namespace TauCeti.Huber

open UniformSpace

variable (k m : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [IsHuberRing A]

/-- The generators of `A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩`, indexed as those of `A⟨X₁,…,X_{k+m}⟩`. -/
noncomputable def iterateVar (i : Fin (k + m)) :
    restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A) :=
  Fin.addCases
    (fun i ↦ ((weightedC (fun _ : Fin m ↦ ({1} : Set (restrictedMvPowerSeriesCompletion k A)))
        isWeightFamily_one_weight
        ((weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i :
            weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion k A) :
          weightedRestrictedSubring _ _) :
      restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A)))
    (fun j ↦ ((weightedX (fun _ : Fin m ↦ ({1} : Set (restrictedMvPowerSeriesCompletion k A)))
        isWeightFamily_one_weight j : weightedRestrictedSubring _ _) :
      restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A)))
    i

/-- Each generator is power-bounded. -/
theorem isPowerBounded_iterateVar (i : Fin (k + m)) :
    IsPowerBounded (iterateVar k m A i) := by
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i
  · rw [iterateVar, Fin.addCases_left]
    exact isPowerBounded_coe_weightedC isWeightFamily_one_weight
      (isPowerBounded_coe_weightedX_one_weight i)
  · rw [iterateVar, Fin.addCases_right]
    exact isPowerBounded_coe_weightedX_one_weight j

/-- The structure map `A → A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩`, the composite of the two structure maps the
iterated algebra is built from. -/
noncomputable def iterateStructureHom :
    A →+* restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A) :=
  (algebraMap (restrictedMvPowerSeriesCompletion k A)
    (restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A))).comp
    (algebraMap A (restrictedMvPowerSeriesCompletion k A))

omit [IsHuberRing A] in
/-- The structure map of the iterated algebra is continuous. -/
theorem continuous_iterateStructureHom : Continuous (iterateStructureHom k m A) :=
  (continuous_algebraMap_restrictedMvPowerSeriesCompletion m
    (restrictedMvPowerSeriesCompletion k A)).comp
    (continuous_algebraMap_restrictedMvPowerSeriesCompletion k A)

/-- **The comparison map `A⟨X₁,…,X_{k+m}⟩ → A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩`.** -/
noncomputable def iterateComparisonHom :
    restrictedMvPowerSeriesCompletion (k + m) A →+*
      restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A) :=
  weightedEvalHomCompletion isWeightFamily_one_weight
    (continuous_iterateStructureHom k m A).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr
      (isPowerBounded_iterateVar k m A))

/-- The comparison map is continuous. -/
theorem continuous_iterateComparisonHom : Continuous (iterateComparisonHom k m A) :=
  continuous_weightedEvalHomCompletion _ _ _

/-- The comparison map sends a constant to the corresponding constant. -/
@[simp]
theorem iterateComparisonHom_coe_weightedC (a : A) :
    iterateComparisonHom k m A
        ((weightedC (fun _ : Fin (k + m) ↦ ({1} : Set A)) isWeightFamily_one_weight a :
          weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion (k + m) A)
      = iterateStructureHom k m A a := by
  rw [iterateComparisonHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

/-- The comparison map sends `Xᵢ` to the `i`-th generator of the iterated algebra: for `i < k`
the `i`-th variable of the inner algebra, read as a constant of the outer one, and for `i ≥ k`
the variable of the outer algebra. -/
@[simp]
theorem iterateComparisonHom_coe_weightedX (i : Fin (k + m)) :
    iterateComparisonHom k m A
        ((weightedX (fun _ : Fin (k + m) ↦ ({1} : Set A)) isWeightFamily_one_weight i :
          weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion (k + m) A)
      = iterateVar k m A i := by
  rw [iterateComparisonHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

end TauCeti.Huber

end
