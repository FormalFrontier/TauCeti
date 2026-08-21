/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic
public import Mathlib.Topology.Algebra.UniformRing

/-!
# The completed restricted power-series algebra `A⟨X₁,…,Xₖ⟩`

For a nonarchimedean commutative ring `A`, the separated completion of the ring of restricted
power series in `k` variables — the weighted ring `TauCeti.Huber.weightedRestrictedSubring`
at the trivial weight family `Tᵢ = {1}` (Wedhorn *Adic Spaces*, arXiv:1910.05934v1, Example
5.54). `A` is not assumed complete or Hausdorff; for `k = 0` the construction is the separated
completion of `A` itself.

Being a completion, `A⟨X₁,…,Xₖ⟩` is a complete Hausdorff topological `A`-algebra with all of
that structure found by instance search, so this module fixes the notation and records what
instance search does not supply: continuity of the structure map, and — at `k = 0`, where the
construction degenerates to the separated completion of `A` — the identification of `A⟨⟩` with
`Â` together with its topological API.

The predicate that every `A⟨X₁,…,Xₖ⟩` is noetherian is
`TauCeti.Huber.IsStronglyNoetherian`, in `TauCeti.RingTheory.Huber.StronglyNoetherian`; the
comparison with the plain restricted-series ring, whenever that ring is itself complete and
Hausdorff — over a complete Hausdorff base, and over a discrete one — is
`TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv`, in
`TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete`.

## Main definitions

* `TauCeti.Huber.restrictedMvPowerSeriesCompletion`: the completed restricted power-series
  algebra `A⟨X₁,…,Xₖ⟩`.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionFinZeroEquiv`: at `k = 0`, the identification
  of `A⟨⟩` with the separated completion `Â`, carried across the completions from the
  ring-level `TauCeti.Huber.weightedRestrictedSubringFinZeroEquiv`.

## Main results

* `TauCeti.Huber.continuous_algebraMap_restrictedMvPowerSeriesCompletion`: the structure map
  `A → A⟨X₁,…,Xₖ⟩` is continuous.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionFinZeroEquiv_coe`,
  `…_symm_coe`, `continuous_restrictedMvPowerSeriesCompletionFinZeroEquiv` and its `_symm`: the
  zero-variable identification on canonical images, and its continuity in both directions.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08` formalises restricted power series in
`projects/AdicSpaces/Adic spaces/RestrictedPowerSeries.lean`. It was consulted and not
ported: everything there is stated for the *uncompleted* restricted-series subring, which
matches Wedhorn only for complete Hausdorff rings, whereas the roadmap — and this file —
define `A⟨X₁,…,Xₖ⟩` through the separated completion, so that the object is the intended one
for an arbitrary Tate ring. The two descriptions are identified, where they agree, by
`TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv`. Nothing was copied.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Remark and Definition 5.48, and Example 5.54 for
  the case `Tᵢ = {1}`.
-/

public section

namespace TauCeti.Huber

variable (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- The completed restricted power-series algebra `A⟨X₁,…,Xₖ⟩` of a nonarchimedean commutative
ring `A`: the separated completion of the ring of restricted power series in `k` variables —
the weighted ring `TauCeti.Huber.weightedRestrictedSubring` at the trivial weight family
`Tᵢ = {1}` — with respect to the uniformity of its ring topology. For `k = 0` this is the
separated completion of `A` itself. -/
noncomputable abbrev restrictedMvPowerSeriesCompletion : Type _ :=
  UniformSpace.Completion
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)

/-- The structure map `A → A⟨X₁,…,Xₖ⟩` is continuous. -/
theorem continuous_algebraMap_restrictedMvPowerSeriesCompletion :
    Continuous (algebraMap A (restrictedMvPowerSeriesCompletion k A)) := by
  have h : Continuous (algebraMap A (weightedRestrictedSubring
      (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)) :=
    (continuous_weightedC isWeightFamily_one_weight).congr fun a ↦ Subtype.ext (by simp)
  exact ((UniformSpace.Completion.continuous_coe _).comp h).congr fun a ↦
    (UniformSpace.Completion.algebraMap_def _ _ a).symm

/-! ### Zero variables -/

section ZeroVariables

variable {A}

/-- **`A⟨⟩` is the separated completion of `A`**, as topological rings: the ring isomorphism
between the two completions induced by the zero-variable comparison
`weightedRestrictedSubringFinZeroEquiv`, which is a homeomorphism, through
`UniformSpace.Completion.mapRingEquiv`. -/
noncomputable def restrictedMvPowerSeriesCompletionFinZeroEquiv :
    letI := IsTopologicalAddGroup.rightUniformSpace A
    letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    restrictedMvPowerSeriesCompletion 0 A ≃+* UniformSpace.Completion A :=
  letI := IsTopologicalAddGroup.rightUniformSpace A
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  UniformSpace.Completion.mapRingEquiv
    (weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set A)))
    (continuous_weightedRestrictedSubringFinZeroEquiv _)
    (continuous_weightedRestrictedSubringFinZeroEquiv_symm _)

/-- On the canonical image of a restricted series, the comparison of completions is the
comparison of the rings underneath. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionFinZeroEquiv_coe
    (f : weightedRestrictedSubring (fun _ : Fin 0 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    letI := IsTopologicalAddGroup.rightUniformSpace A
    letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    restrictedMvPowerSeriesCompletionFinZeroEquiv (f : restrictedMvPowerSeriesCompletion 0 A) =
      ((weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set A)) f : A) :
        UniformSpace.Completion A) := by
  let _ := IsTopologicalAddGroup.rightUniformSpace A
  let _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  simp only [restrictedMvPowerSeriesCompletionFinZeroEquiv]
  exact UniformSpace.Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous
    (continuous_weightedRestrictedSubringFinZeroEquiv _)) f

/-- On the canonical image of an element of `A`, the inverse comparison is the canonical image of
the inverse ring comparison. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionFinZeroEquiv_symm_coe (a : A) :
    letI := IsTopologicalAddGroup.rightUniformSpace A
    letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    (restrictedMvPowerSeriesCompletionFinZeroEquiv (A := A)).symm (a : UniformSpace.Completion A) =
      ((weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set A))).symm a :
        restrictedMvPowerSeriesCompletion 0 A) := by
  let _ := IsTopologicalAddGroup.rightUniformSpace A
  let _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  simp only [restrictedMvPowerSeriesCompletionFinZeroEquiv]
  exact UniformSpace.Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous
    (continuous_weightedRestrictedSubringFinZeroEquiv_symm _)) a

/-- The comparison of completions is continuous. -/
theorem continuous_restrictedMvPowerSeriesCompletionFinZeroEquiv :
    letI := IsTopologicalAddGroup.rightUniformSpace A
    letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    Continuous (restrictedMvPowerSeriesCompletionFinZeroEquiv (A := A)) := by
  let _ := IsTopologicalAddGroup.rightUniformSpace A
  let _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  simp only [restrictedMvPowerSeriesCompletionFinZeroEquiv]
  exact UniformSpace.Completion.continuous_map.congr fun x ↦
    (UniformSpace.Completion.mapRingEquiv_apply _ _ _ x).symm

/-- Its inverse is continuous. -/
theorem continuous_restrictedMvPowerSeriesCompletionFinZeroEquiv_symm :
    letI := IsTopologicalAddGroup.rightUniformSpace A
    letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    Continuous (restrictedMvPowerSeriesCompletionFinZeroEquiv (A := A)).symm := by
  let _ := IsTopologicalAddGroup.rightUniformSpace A
  let _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  simp only [restrictedMvPowerSeriesCompletionFinZeroEquiv]
  exact UniformSpace.Completion.continuous_map.congr fun x ↦
    (UniformSpace.Completion.mapRingEquiv_symm_apply _ _ _ x).symm

end ZeroVariables

end TauCeti.Huber
