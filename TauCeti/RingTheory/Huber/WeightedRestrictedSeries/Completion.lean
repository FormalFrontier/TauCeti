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
* `TauCeti.Huber.weightedMapCompletion`: the map `A⟨X⟩_T → B⟨X⟩_S` on completions induced by a
  continuous ring map carrying each weight into the corresponding one — the completion-level
  companion of `TauCeti.Huber.weightedMap`.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionFinZeroEquiv`: at `k = 0`, the identification
  of `A⟨⟩` with the separated completion `Â`, carried across the completions from the
  ring-level `TauCeti.Huber.weightedRestrictedSubringFinZeroEquiv`.

## Main results

* `TauCeti.Huber.continuous_algebraMap_restrictedMvPowerSeriesCompletion`: the structure map
  `A → A⟨X₁,…,Xₖ⟩` is continuous.
* `TauCeti.Huber.weightedMapCompletion_coe` and
  `TauCeti.Huber.continuous_weightedMapCompletion`: the induced map on the image of `A⟨X⟩_T`,
  and its continuity.
* `TauCeti.Huber.weightedMapCompletion_id` and `TauCeti.Huber.weightedMapCompletion_comp`: the
  functor laws.
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

/-! ### Functoriality in the coefficient ring -/

section Functoriality

variable {k} {A}
variable {B : Type*} [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]
  {φ : A →+* B} {T : Fin k → Set A} {S : Fin k → Set B}

/-- **The completed weighted series ring is functorial in the coefficient ring.** A continuous
ring map `φ : A → B` carrying each weight `T i` into `S i` induces `A⟨X⟩_T → B⟨X⟩_S` by
`TauCeti.Huber.weightedMap`; that map is continuous, so it extends to the completions.

This is the completion-level companion of `TauCeti.Huber.weightedMap`. The subring-level map is
not enough on its own: `TauCeti.Huber.restrictedMvPowerSeriesCompletion` — the object
`IsStronglyNoetherian` is stated over, and the one the roadmap writes `A⟨X₁,…,Xₖ⟩` — is a
completion, so any statement natural in `A` has to live here. -/
noncomputable def weightedMapCompletion (hφ : Continuous φ) (hT : IsWeightFamily T)
    (hS : IsWeightFamily S) (hTS : ∀ i, φ '' T i ⊆ S i) :
    UniformSpace.Completion (weightedRestrictedSubring T hT) →+*
      UniformSpace.Completion (weightedRestrictedSubring S hS) :=
  UniformSpace.Completion.mapRingHom (weightedMap hφ hT hS hTS)
    (continuous_weightedMap hφ hT hS hTS)

/-- The value of `TauCeti.Huber.weightedMapCompletion` on the canonical image of a weighted
restricted series: it agrees with `TauCeti.Huber.weightedMap`. -/
@[simp]
theorem weightedMapCompletion_coe (hφ : Continuous φ) (hT : IsWeightFamily T)
    (hS : IsWeightFamily S) (hTS : ∀ i, φ '' T i ⊆ S i) (f : weightedRestrictedSubring T hT) :
    weightedMapCompletion hφ hT hS hTS f = weightedMap hφ hT hS hTS f :=
  UniformSpace.Completion.mapRingHom_coe _ _

/-- `TauCeti.Huber.weightedMapCompletion` is continuous, so it is a morphism of *topological*
rings. -/
theorem continuous_weightedMapCompletion (hφ : Continuous φ) (hT : IsWeightFamily T)
    (hS : IsWeightFamily S) (hTS : ∀ i, φ '' T i ⊆ S i) :
    Continuous (weightedMapCompletion hφ hT hS hTS) :=
  UniformSpace.Completion.continuous_map

/-- **The identity law**: the map induced by `RingHom.id` is the identity. -/
@[simp]
theorem weightedMapCompletion_id (hT : IsWeightFamily T) :
    weightedMapCompletion (φ := RingHom.id A)
        (by simpa only [RingHom.coe_id] using continuous_id) hT hT
        (fun _ ↦ by simpa only [RingHom.coe_id] using (Set.image_id _).subset)
      = RingHom.id (UniformSpace.Completion (weightedRestrictedSubring T hT)) := by
  simp only [weightedMapCompletion, weightedMap_id]
  exact UniformSpace.Completion.mapRingHom_id

/-- **The composition law**: composing the maps induced by `φ` and `ψ` gives the map induced by
`ψ ∘ φ`. Stated in the collapsing direction, matching
`UniformSpace.Completion.mapRingHom_comp`, so that a composite normalizes to a single induced
map. With `TauCeti.Huber.weightedMapCompletion_id` this is what makes `A⟨X⟩_T` functorial in the
pair `(A, T)` at the level of completions — the §0.4 weighted restricted-series functoriality.

This is **not** Remark 8.29's naturality, which varies the *module* with the coefficient ring
fixed.

A caller holding a weight hypothesis in the form `φ '' T i ⊆ S i` converts it with
`Set.image_subset_iff`. -/
@[simp]
theorem weightedMapCompletion_comp {C : Type*} [CommRing C] [TopologicalSpace C]
    [NonarchimedeanRing C] {ψ : B →+* C} {R : Fin k → Set C} (hφ : Continuous φ)
    (hψ : Continuous ψ) (hT : IsWeightFamily T) (hS : IsWeightFamily S) (hR : IsWeightFamily R)
    (hTS : ∀ i, T i ⊆ φ ⁻¹' S i) (hSR : ∀ i, S i ⊆ ψ ⁻¹' R i) :
    (weightedMapCompletion hψ hS hR fun i ↦ Set.image_subset_iff.mpr (hSR i)).comp
        (weightedMapCompletion hφ hT hS fun i ↦ Set.image_subset_iff.mpr (hTS i))
      = weightedMapCompletion (φ := ψ.comp φ)
          (by simpa only [RingHom.coe_comp] using hψ.comp hφ) hT hR
          (fun i ↦ Set.image_subset_iff.mpr ((hTS i).trans (Set.preimage_mono (hSR i)))) := by
  have hTS' : ∀ i, φ '' T i ⊆ S i := fun i ↦ Set.image_subset_iff.mpr (hTS i)
  have hSR' : ∀ i, ψ '' S i ⊆ R i := fun i ↦ Set.image_subset_iff.mpr (hSR i)
  simp only [weightedMapCompletion, weightedMap_comp hφ hψ hT hS hR hTS' hSR']
  exact UniformSpace.Completion.mapRingHom_comp _ _

end Functoriality

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
