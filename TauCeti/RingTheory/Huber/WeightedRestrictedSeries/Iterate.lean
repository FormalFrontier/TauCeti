/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Comparing `A⟨X₁,…,X_{k+m}⟩` with `A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩`

Splitting the variables of a completed restricted power-series algebra into a first block of `k`
and a second of `m` presents the algebra in `k + m` variables as an algebra in `m` variables over
the algebra in `k`. This file constructs the two comparison maps

```text
A⟨X₁,…,X_{k+m}⟩ ⟶ A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩    and    A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩ ⟶ A⟨X₁,…,X_{k+m}⟩
```

and proves them mutually inverse, so that `A⟨X⟩⟨Y⟩ ≅ A⟨X,Y⟩`.

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
* `TauCeti.Huber.iterateRingEquiv`: the isomorphism the two assemble into, with
  `TauCeti.Huber.iterateAlgEquiv` its `A`-algebra form.

## Main results

* `TauCeti.Huber.isPowerBounded_iterateVar`: every generator of the iterated algebra is
  power-bounded in it, which is what Proposition 5.50 asks of the tuple.
* `TauCeti.Huber.continuous_iterateSplitHom` and `TauCeti.Huber.continuous_iterateJoinHom`, with
  `TauCeti.Huber.continuous_iterateFirstBlockHom`: all three are morphisms of *topological* rings.
* `TauCeti.Huber.iterateSplitHom_coe_weightedC`, `…_coe_weightedX` and their `iterateJoinHom` and
  `iterateFirstBlockHom` counterparts, with `TauCeti.Huber.iterateVar_castAdd` and
  `TauCeti.Huber.iterateVar_natAdd` for the two blocks of generators: the values on the
  generators. The bodies of the definitions are not exported, so these are how a consumer computes
  with the maps.
* `TauCeti.Huber.iterateJoinHom_comp_iterateSplitHom` and
  `TauCeti.Huber.iterateSplitHom_comp_iterateJoinHom`: the two maps are mutually inverse. Each is
  the uniqueness half of Proposition 5.50 — two continuous homomorphisms out of the completion
  agreeing on the constants and the variables are equal — applied to the composite and the
  identity.
* `TauCeti.Huber.continuous_iterateRingEquiv` and its `symm`, with the `_coe` and `_apply` `@[simp]`
  lemmas: the isomorphism is one of *topological* rings, and it is `iterateSplitHom` with inverse
  `iterateJoinHom`.
* `TauCeti.Huber.iterateSplitHom_comp_algebraMap`: the comparison carries the structure map of
  `A⟨X₁,…,X_{k+m}⟩` to that of the iterate, which is what makes it a map of `A`-algebras. The
  iterate carries no `Algebra A` instance — `Algebra` does not compose transitively — so
  `iterateAlgEquiv` supplies the one its structure map induces, and
  `TauCeti.Huber.iterateAlgEquiv_toRingEquiv` with its two `_apply` forms says that this changes
  nothing but the bundling.

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

omit [IsHuberRing A] in
/-- On the first block the generator is the `i`-th variable of the inner algebra, read as a
constant series of the outer one. -/
@[simp]
theorem iterateVar_castAdd (i : Fin k) :
    iterateVar k m A (Fin.castAdd m i)
      = ((weightedC (fun _ : Fin m ↦ ({1} : Set (restrictedMvPowerSeriesCompletion k A)))
          isWeightFamily_one_weight
          ((weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i :
              weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion k A) :
            weightedRestrictedSubring _ _) :
        restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A)) := by
  rw [iterateVar, Fin.addCases_left]

omit [IsHuberRing A] in
/-- On the second block the generator is the `j`-th variable of the outer algebra. -/
@[simp]
theorem iterateVar_natAdd (j : Fin m) :
    iterateVar k m A (Fin.natAdd k j)
      = ((weightedX (fun _ : Fin m ↦ ({1} : Set (restrictedMvPowerSeriesCompletion k A)))
          isWeightFamily_one_weight j : weightedRestrictedSubring _ _) :
        restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A)) := by
  rw [iterateVar, Fin.addCases_right]

/-- Each generator is power-bounded. -/
theorem isPowerBounded_iterateVar (i : Fin (k + m)) :
    IsPowerBounded (iterateVar k m A i) := by
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i
  · rw [iterateVar_castAdd]
    exact isPowerBounded_completion_coe_of_isPowerBounded
      (isPowerBounded_weightedC isWeightFamily_one_weight
        (isPowerBounded_coe_weightedX_one_weight i))
  · rw [iterateVar_natAdd]
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

/-! ### The two maps are mutually inverse -/

omit [IsHuberRing A] in
/-- The structure map of the iterated algebra is the constant series of a constant series. -/
theorem iterateStructureHom_eq (a : A) :
    iterateStructureHom k m A a
      = ((weightedC (fun _ : Fin m ↦ ({1} : Set (restrictedMvPowerSeriesCompletion k A)))
          isWeightFamily_one_weight
          ((weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight a :
            weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion k A) :
          weightedRestrictedSubring _ _) :
        restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A)) := by
  rw [iterateStructureHom, RingHom.comp_apply,
    algebraMap_completion_weightedRestrictedSubring_apply _ _ isWeightFamily_one_weight,
    algebraMap_completion_weightedRestrictedSubring_apply _ _ isWeightFamily_one_weight]

/-- **Joining after splitting is the identity on `A⟨X₁,…,X_{k+m}⟩`.** -/
theorem iterateJoinHom_comp_iterateSplitHom :
    (iterateJoinHom k m A).comp (iterateSplitHom k m A)
      = RingHom.id (restrictedMvPowerSeriesCompletion (k + m) A) := by
  refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    ((continuous_iterateJoinHom k m A).comp (continuous_iterateSplitHom k m A)) continuous_id
    (fun a ↦ ?_) fun i ↦ ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      iterateSplitHom_coe_weightedC, iterateStructureHom_eq, iterateJoinHom_coe_weightedC,
      iterateFirstBlockHom_coe_weightedC,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ isWeightFamily_one_weight]
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      iterateSplitHom_coe_weightedX]
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i
    · rw [iterateVar_castAdd, iterateJoinHom_coe_weightedC, iterateFirstBlockHom_coe_weightedX]
    · rw [iterateVar_natAdd, iterateJoinHom_coe_weightedX]

/-- Splitting after including the first block is the structure map of the iterated algebra over
`A⟨X₁,…,Xₖ⟩`: the two agree on the constants and on the variables of `A⟨X₁,…,Xₖ⟩`. -/
theorem iterateSplitHom_comp_iterateFirstBlockHom :
    (iterateSplitHom k m A).comp (iterateFirstBlockHom k m A)
      = algebraMap (restrictedMvPowerSeriesCompletion k A)
        (restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A)) := by
  refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    ((continuous_iterateSplitHom k m A).comp (continuous_iterateFirstBlockHom k m A))
    (continuous_algebraMap_restrictedMvPowerSeriesCompletion m
      (restrictedMvPowerSeriesCompletion k A)) (fun a ↦ ?_) fun i ↦ ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, iterateFirstBlockHom_coe_weightedC,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ isWeightFamily_one_weight,
      iterateSplitHom_coe_weightedC, iterateStructureHom_eq]
  · simp only [RingHom.coe_comp, Function.comp_apply, iterateFirstBlockHom_coe_weightedX,
      iterateSplitHom_coe_weightedX, iterateVar_castAdd,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ isWeightFamily_one_weight]

/-- **Splitting after joining is the identity on `A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩`.** -/
theorem iterateSplitHom_comp_iterateJoinHom :
    (iterateSplitHom k m A).comp (iterateJoinHom k m A)
      = RingHom.id
        (restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A)) := by
  refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    ((continuous_iterateSplitHom k m A).comp (continuous_iterateJoinHom k m A)) continuous_id
    (fun c ↦ ?_) fun j ↦ ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      iterateJoinHom_coe_weightedC]
    rw [← RingHom.comp_apply, iterateSplitHom_comp_iterateFirstBlockHom,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ isWeightFamily_one_weight]
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      iterateJoinHom_coe_weightedX, iterateSplitHom_coe_weightedX, iterateVar_natAdd]

/-- **The iteration isomorphism** `A⟨X₁,…,X_{k+m}⟩ ≃+* A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩`. -/
noncomputable def iterateRingEquiv :
    restrictedMvPowerSeriesCompletion (k + m) A ≃+*
      restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A) :=
  RingEquiv.ofRingHom (iterateSplitHom k m A) (iterateJoinHom k m A)
    (iterateSplitHom_comp_iterateJoinHom k m A) (iterateJoinHom_comp_iterateSplitHom k m A)

/-- The iteration isomorphism is `TauCeti.Huber.iterateSplitHom`. -/
@[simp]
theorem iterateRingEquiv_coe :
    ((iterateRingEquiv k m A : restrictedMvPowerSeriesCompletion (k + m) A ≃+*
        restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A)) :
      restrictedMvPowerSeriesCompletion (k + m) A →+*
        restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A))
      = iterateSplitHom k m A := by
  simp only [iterateRingEquiv, RingEquiv.coe_ringHom_ofRingHom]

/-- The pointwise form of `TauCeti.Huber.iterateRingEquiv_coe`. -/
@[simp]
theorem iterateRingEquiv_apply (x : restrictedMvPowerSeriesCompletion (k + m) A) :
    iterateRingEquiv k m A x = iterateSplitHom k m A x :=
  DFunLike.congr_fun (iterateRingEquiv_coe k m A) x

/-- The inverse of the iteration isomorphism is `TauCeti.Huber.iterateJoinHom`. -/
@[simp]
theorem iterateRingEquiv_symm_coe :
    (((iterateRingEquiv k m A).symm : restrictedMvPowerSeriesCompletion m
        (restrictedMvPowerSeriesCompletion k A) ≃+*
          restrictedMvPowerSeriesCompletion (k + m) A) :
      restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A) →+*
        restrictedMvPowerSeriesCompletion (k + m) A)
      = iterateJoinHom k m A := by
  simp only [iterateRingEquiv, RingEquiv.ofRingHom_symm, RingEquiv.coe_ringHom_ofRingHom]

/-- The pointwise form of `TauCeti.Huber.iterateRingEquiv_symm_coe`. -/
@[simp]
theorem iterateRingEquiv_symm_apply
    (x : restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A)) :
    (iterateRingEquiv k m A).symm x = iterateJoinHom k m A x :=
  DFunLike.congr_fun (iterateRingEquiv_symm_coe k m A) x

/-- The iteration isomorphism is an isomorphism of *topological* rings. -/
theorem continuous_iterateRingEquiv : Continuous (iterateRingEquiv k m A) :=
  (continuous_iterateSplitHom k m A).congr fun x ↦ (iterateRingEquiv_apply k m A x).symm

/-- Its inverse is continuous too. -/
theorem continuous_iterateRingEquiv_symm : Continuous (iterateRingEquiv k m A).symm :=
  (continuous_iterateJoinHom k m A).congr fun x ↦ (iterateRingEquiv_symm_apply k m A x).symm

/-! ### As a map of `A`-algebras -/

/-- **The comparison map carries the structure map of `A⟨X₁,…,X_{k+m}⟩` to the structure map of
the iterated algebra**, so it is a map of `A`-algebras. -/
@[simp]
theorem iterateSplitHom_comp_algebraMap :
    (iterateSplitHom k m A).comp (algebraMap A (restrictedMvPowerSeriesCompletion (k + m) A))
      = iterateStructureHom k m A := by
  ext a
  rw [RingHom.comp_apply,
    algebraMap_completion_weightedRestrictedSubring_apply _ _ isWeightFamily_one_weight,
    iterateSplitHom_coe_weightedC]

/-- **The iteration isomorphism as an equivalence of `A`-algebras.**

The algebra structure on the iterate is the one its structure map induces: `Algebra` does not
compose transitively, so `A⟨X₁,…,Xₖ⟩⟨Y₁,…,Y_m⟩` carries no `Algebra A` instance of its own and the
statement supplies it. -/
noncomputable def iterateAlgEquiv :
    letI := (iterateStructureHom k m A).toAlgebra
    restrictedMvPowerSeriesCompletion (k + m) A ≃ₐ[A]
      restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A) :=
  letI := (iterateStructureHom k m A).toAlgebra
  AlgEquiv.ofRingEquiv (f := iterateRingEquiv k m A) fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra, iterateRingEquiv_apply, ← RingHom.comp_apply,
      iterateSplitHom_comp_algebraMap]

/-- The algebra equivalence is the ring equivalence. -/
@[simp]
theorem iterateAlgEquiv_toRingEquiv :
    letI := (iterateStructureHom k m A).toAlgebra
    (iterateAlgEquiv k m A).toRingEquiv = iterateRingEquiv k m A :=
  (rfl)

/-- The pointwise form of `TauCeti.Huber.iterateAlgEquiv_toRingEquiv`. -/
@[simp]
theorem iterateAlgEquiv_apply (x : restrictedMvPowerSeriesCompletion (k + m) A) :
    letI := (iterateStructureHom k m A).toAlgebra
    iterateAlgEquiv k m A x = iterateRingEquiv k m A x :=
  (rfl)

/-- The inverse of the algebra equivalence is the inverse of the ring equivalence. -/
@[simp]
theorem iterateAlgEquiv_symm_apply
    (x : restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k A)) :
    letI := (iterateStructureHom k m A).toAlgebra
    (iterateAlgEquiv k m A).symm x = (iterateRingEquiv k m A).symm x :=
  (rfl)

end TauCeti.Huber

end
