/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

/-!
# Comparing `A⟨X₁,…,X_{k+m}⟩` with `A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩`

Splitting the variables of a completed restricted power-series algebra into a first block of `k`
and a second of `m` presents the algebra in `k + m` variables as an algebra in `m` variables over
the algebra in `k`. This file constructs the two comparison maps

```text
A⟨X₁,…,X_{k+m}⟩ ⟶ A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩    and    A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩ ⟶ A⟨X₁,…,X_{k+m}⟩
```

and records their values on the generators. That they are mutually inverse is not proved here.

Each is Wedhorn's Proposition 5.50 for the completed algebra — `weightedEvalHomCompletion` —
applied to a tuple of generators. The first carries `Xᵢ` to the `i`-th variable of the inner
algebra read as a constant series of the outer one when `i < k`, and to the corresponding variable
of the outer algebra when `i ≥ k`. The second is built in two steps: the first block of variables
gives `A⟨X₁,…,Xₖ⟩ → A⟨X₁,…,X_{k+m}⟩`, and over that map the outer variables `Y_j` go to `X_{k+j}`.

Two hypotheses make the applications legitimate and neither is automatic. The target must be a
*complete Hausdorff nonarchimedean* ring, which for an iterated algebra rests on the completion of
a nonarchimedean group being nonarchimedean; and each tuple must be power-bounded, which is
`isPowerBounded_coe_weightedC` and `isPowerBounded_coe_weightedX_one_weight`.

## Main definitions

* `TauCeti.Huber.iterateVar`: the generators of `A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩`, indexed by `Fin (k + m)`
  as those of `A⟨X₁,…,X_{k+m}⟩` are.
* `TauCeti.Huber.iterateStructureHom`: the structure map `A → A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩`, the composite
  of the two the iterated algebra is built from.
* `TauCeti.Huber.iterateSplitHom`: the comparison map that splits the variables.
* `TauCeti.Huber.iterateFirstBlockHom`: the inclusion `A⟨X₁,…,Xₖ⟩ → A⟨X₁,…,X_{k+m}⟩` of the first
  block, which the map below is taken over.
* `TauCeti.Huber.iterateJoinHom`: the comparison map that joins them.

## Main results

* `TauCeti.Huber.isPowerBounded_iterateVar`: every generator of the iterated algebra is
  power-bounded in it, which is what Proposition 5.50 asks of the tuple.
* `TauCeti.Huber.continuous_iterateSplitHom` and `TauCeti.Huber.continuous_iterateJoinHom`, with
  `TauCeti.Huber.continuous_iterateFirstBlockHom`: all three are morphisms of *topological* rings.
* `TauCeti.Huber.iterateSplitHom_coe_weightedC`, `…_coe_weightedX` and their `iterateJoinHom` and
  `iterateFirstBlockHom` counterparts: the values on the generators. The bodies of the definitions
  are not exported, so these are how a consumer computes with the maps.

## What is not here

That the two maps are mutually inverse. The roadmap asks for the isomorphism
`A⟨X⟩⟨Y⟩ ≅ A⟨X,Y⟩`; this file is its two halves, in the shape the identification of Wedhorn's
Remark 7.55 was built in — the two comparison maps first, then the equivalence.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50, whose
  completed form both maps apply.
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
noncomputable def iterateSplitHom :
    restrictedMvPowerSeriesCompletion (k + m) A →+*
      restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A) :=
  weightedEvalHomCompletion isWeightFamily_one_weight
    (continuous_iterateStructureHom k m A).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr
      (isPowerBounded_iterateVar k m A))

/-- The comparison map is continuous. -/
theorem continuous_iterateSplitHom : Continuous (iterateSplitHom k m A) :=
  continuous_weightedEvalHomCompletion _ _ _

/-- The comparison map sends a constant to the corresponding constant. -/
@[simp]
theorem iterateSplitHom_coe_weightedC (a : A) :
    iterateSplitHom k m A
        ((weightedC (fun _ : Fin (k + m) ↦ ({1} : Set A)) isWeightFamily_one_weight a :
          weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion (k + m) A)
      = iterateStructureHom k m A a := by
  rw [iterateSplitHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

/-- The comparison map sends `Xᵢ` to the `i`-th generator of the iterated algebra: for `i < k`
the `i`-th variable of the inner algebra, read as a constant of the outer one, and for `i ≥ k`
the variable of the outer algebra. -/
@[simp]
theorem iterateSplitHom_coe_weightedX (i : Fin (k + m)) :
    iterateSplitHom k m A
        ((weightedX (fun _ : Fin (k + m) ↦ ({1} : Set A)) isWeightFamily_one_weight i :
          weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion (k + m) A)
      = iterateVar k m A i := by
  rw [iterateSplitHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

/-! ### Joining the variables -/

/-- **The inclusion of the first block of variables**, `A⟨X₁,…,Xₖ⟩ → A⟨X₁,…,X_{k+m}⟩`: the unique
continuous homomorphism over `A` carrying `Xᵢ` to `Xᵢ`. -/
noncomputable def iterateFirstBlockHom :
    restrictedMvPowerSeriesCompletion k A →+* restrictedMvPowerSeriesCompletion (k + m) A :=
  weightedEvalHomCompletion isWeightFamily_one_weight
    (continuous_algebraMap_restrictedMvPowerSeriesCompletion (k + m) A).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun i ↦
      isPowerBounded_coe_weightedX_one_weight (Fin.castAdd m i))

/-- The inclusion of the first block of variables is continuous. -/
theorem continuous_iterateFirstBlockHom : Continuous (iterateFirstBlockHom k m A) :=
  continuous_weightedEvalHomCompletion _ _ _

/-- **The comparison map `A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩ → A⟨X₁,…,X_{k+m}⟩`**: the unique continuous
homomorphism over `A⟨X₁,…,Xₖ⟩` — through the inclusion of the first block — carrying `Y_j` to
`X_{k+j}`. -/
noncomputable def iterateJoinHom :
    restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A) →+*
      restrictedMvPowerSeriesCompletion (k + m) A :=
  weightedEvalHomCompletion isWeightFamily_one_weight
    (continuous_iterateFirstBlockHom k m A).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun j ↦
      isPowerBounded_coe_weightedX_one_weight (Fin.natAdd k j))

/-- The join map is continuous. -/
theorem continuous_iterateJoinHom : Continuous (iterateJoinHom k m A) :=
  continuous_weightedEvalHomCompletion _ _ _

/-- The join map sends a constant series of the outer algebra to the image of its value under the
inclusion of the first block. -/
@[simp]
theorem iterateJoinHom_coe_weightedC (c : restrictedMvPowerSeriesCompletion k A) :
    iterateJoinHom k m A
        ((weightedC (fun _ : Fin m ↦ ({1} : Set (restrictedMvPowerSeriesCompletion k A)))
          isWeightFamily_one_weight c : weightedRestrictedSubring _ _) :
          restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A))
      = iterateFirstBlockHom k m A c := by
  rw [iterateJoinHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

/-- The join map sends the `j`-th variable of the outer algebra to `X_{k+j}`. -/
@[simp]
theorem iterateJoinHom_coe_weightedX (j : Fin m) :
    iterateJoinHom k m A
        ((weightedX (fun _ : Fin m ↦ ({1} : Set (restrictedMvPowerSeriesCompletion k A)))
          isWeightFamily_one_weight j : weightedRestrictedSubring _ _) :
          restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A))
      = ((weightedX (fun _ : Fin (k + m) ↦ ({1} : Set A)) isWeightFamily_one_weight
          (Fin.natAdd k j) : weightedRestrictedSubring _ _) :
        restrictedMvPowerSeriesCompletion (k + m) A) := by
  rw [iterateJoinHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

/-- The inclusion of the first block sends `Xᵢ` to `Xᵢ`. -/
@[simp]
theorem iterateFirstBlockHom_coe_weightedX (i : Fin k) :
    iterateFirstBlockHom k m A
        ((weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i :
          weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion k A)
      = ((weightedX (fun _ : Fin (k + m) ↦ ({1} : Set A)) isWeightFamily_one_weight
          (Fin.castAdd m i) : weightedRestrictedSubring _ _) :
        restrictedMvPowerSeriesCompletion (k + m) A) := by
  rw [iterateFirstBlockHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

/-- The inclusion of the first block is a map of `A`-algebras. -/
@[simp]
theorem iterateFirstBlockHom_coe_weightedC (a : A) :
    iterateFirstBlockHom k m A
        ((weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight a :
          weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion k A)
      = algebraMap A (restrictedMvPowerSeriesCompletion (k + m) A) a := by
  rw [iterateFirstBlockHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

end TauCeti.Huber

end
