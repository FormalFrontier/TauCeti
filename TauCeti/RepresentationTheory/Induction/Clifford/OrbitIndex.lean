/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Induction.Clifford.Orbit
public import TauCeti.RepresentationTheory.Induction.Inertia

/-!
# Inertia cosets index the constituents in Clifford's theorem

This file identifies the orbit of an irreducible constituent in Clifford's theorem with the left
cosets of its inertia group.  Concretely, if `σ` is a minimal subrepresentation of the restriction
of an irreducible finite-dimensional representation `ρ` from `G` to a normal subgroup `N`, then
the isotypic components of the restriction are indexed by

`G ⧸ inertia (FDRep.of σ.toRepresentation)`.

The construction combines the single-orbit theorem from
`TauCeti/RepresentationTheory/Induction/Clifford/Orbit.lean` with Mathlib's generic
`MulAction.orbitEquivQuotientStabilizer`.  The only bridge needed is that translating `σ` inside
`ρ` represents the same isomorphism class as conjugating the abstract `N`-representation carried
by `σ`.

## Main results

* `TauCeti.Representation.isotypicComponentsEquivQuotientInertia`: the equivalence between the
  isotypic components of the restriction and the inertia cosets.
* `TauCeti.Representation.card_isotypicComponents_eq_inertia_index`: the number of irreducible
  constituent classes is the index of the inertia group.

## References

This is the orbit-indexing step in Clifford's theorem from Layer 5 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.  It prepares the remaining
packaged decomposition of the restriction as equal-multiplicity copies of the conjugates indexed
by an inertia-group transversal.

The mathematics is the classical orbit-stabilizer argument in C. W. Curtis and I. Reiner,
*Representation Theory of Finite Groups and Associative Algebras*, §49.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

universe u v

namespace TauCeti

namespace Representation

section OrbitIndex

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {V : Type u} [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

/-- The finite-dimensional representation of `N` carried by a constituent of the restriction. -/
private noncomputable def constituentFDRep [FiniteDimensional k V]
    (σ : Subrepresentation (ρ.comp N.subtype)) : FDRep k N :=
  FDRep.of σ.toRepresentation

/-- The module of a constituent's restricted representation is canonically the same as the
corresponding submodule of the ambient restriction. -/
private noncomputable def asModuleEquivAsSubmodule
    (σ : Subrepresentation (ρ.comp N.subtype)) :
    σ.toRepresentation.asModule ≃ₗ[k[N]] σ.asSubmodule where
  toFun x := ⟨(_root_.Representation.asModuleEquiv (ρ.comp N.subtype)).symm
      (σ.toRepresentation.asModuleEquiv x : V),
    (σ.toRepresentation.asModuleEquiv x).2⟩
  invFun x := σ.toRepresentation.asModuleEquiv.symm
    ⟨_root_.Representation.asModuleEquiv (ρ.comp N.subtype) x.1, x.2⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' x y := by rfl
  map_smul' a x := by
    apply Subtype.ext
    apply (_root_.Representation.asModuleEquiv (ρ.comp N.subtype)).injective
    simp only [LinearEquiv.apply_symm_apply, RingHom.id_apply,
      _root_.Representation.asModuleEquiv_map_smul]
    exact Subrepresentation.coe_toRepresentation_asAlgebraHom_apply σ a
      (σ.toRepresentation.asModuleEquiv x)

/-- Translating a constituent inside the ambient representation agrees, on isomorphism classes,
with conjugating the finite-dimensional representation carried by that constituent. -/
private theorem toSkeleton_constituentFDRep_conjSubrep [FiniteDimensional k V]
    (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    toSkeleton (constituentFDRep ρ (conjSubrep ρ g σ)) =
      g • toSkeleton (constituentFDRep ρ σ) := by
  rw [smul_toSkeleton]
  apply toSkeleton_eq_toSkeleton_iff.2
  rw [nonempty_fdRepIso_iff]
  exact ⟨(conjSubrepEquiv ρ g σ).symm⟩

omit [N.Normal] in
/-- Two constituents determine the same isomorphism class exactly when their associated
`k[N]`-submodules are linearly equivalent. -/
private theorem toSkeleton_constituentFDRep_eq_iff [FiniteDimensional k V]
    (σ τ : Subrepresentation (ρ.comp N.subtype)) :
    toSkeleton (constituentFDRep ρ σ) = toSkeleton (constituentFDRep ρ τ) ↔
      Nonempty (σ.asSubmodule ≃ₗ[k[N]] τ.asSubmodule) := by
  rw [toSkeleton_eq_toSkeleton_iff, nonempty_fdRepIso_iff,
    nonempty_equiv_iff]
  exact Nonempty.congr
    (fun e => (asModuleEquivAsSubmodule ρ σ).symm.trans e |>.trans
      (asModuleEquivAsSubmodule ρ τ))
    (fun e => (asModuleEquivAsSubmodule ρ σ).trans e |>.trans
      (asModuleEquivAsSubmodule ρ τ).symm)

variable [FiniteDimensional k V]

/-- A chosen simple submodule presenting an isotypic component.  This is proof scaffolding for the
equivalence: the final construction is independent of the choice because it lands in isomorphism
classes. -/
private noncomputable def componentRepresentative
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) :=
  c.2.choose

private instance componentRepresentative_isSimple
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    IsSimpleModule k[N] (componentRepresentative ρ c) :=
  c.2.choose_spec.1

omit [N.Normal] [FiniteDimensional k V] in
/-- The chosen representative cuts out the component from which it was chosen. -/
private theorem component_eq_isotypicComponent_componentRepresentative
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    (c : Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype))) =
      isotypicComponent k[N] (_root_.Representation.asModule (ρ.comp N.subtype))
        (componentRepresentative ρ c) :=
  c.2.choose_spec.2

/-- The chosen simple submodule, read as a subrepresentation of the restriction. -/
private noncomputable def componentSubrep
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    Subrepresentation (ρ.comp N.subtype) :=
  Subrepresentation.subrepresentationSubmoduleOrderIso.symm (componentRepresentative ρ c)

omit [N.Normal] [FiniteDimensional k V] in
/-- Reading the chosen representative as a subrepresentation and back changes nothing. -/
@[simp]
private theorem asSubmodule_componentSubrep
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    (componentSubrep ρ c).asSubmodule = componentRepresentative ρ c :=
  Subrepresentation.subrepresentationSubmoduleOrderIso.apply_symm_apply _

omit [N.Normal] [FiniteDimensional k V] in
private theorem isAtom_componentSubrep
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    IsAtom (componentSubrep ρ c) := by
  apply Subrepresentation.isSimpleModule_asSubmodule_iff.mp
  rw [asSubmodule_componentSubrep]
  infer_instance

/-- The isomorphism class of a chosen simple representative of an isotypic component. -/
private noncomputable def componentClass
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    Skeleton (FDRep k N) :=
  toSkeleton (constituentFDRep ρ (componentSubrep ρ c))

/-- Every component class is in the conjugation orbit of a fixed constituent. -/
private theorem componentClass_mem_orbit [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ)
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    componentClass ρ c ∈ MulAction.orbit G (toSkeleton (constituentFDRep ρ σ)) := by
  obtain ⟨g, ⟨e⟩⟩ :=
    exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ (componentRepresentative ρ c)
  rw [MulAction.mem_orbit_iff]
  refine ⟨g, ?_⟩
  rw [← toSkeleton_constituentFDRep_conjSubrep ρ g σ]
  apply (toSkeleton_constituentFDRep_eq_iff ρ _ _).2
  rw [asSubmodule_componentSubrep]
  exact ⟨e.symm⟩

/-- Send an isotypic component to the isomorphism class of any simple submodule presenting it,
viewed in the orbit of a fixed constituent. -/
private noncomputable def componentOrbitMap [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) →
      MulAction.orbit G (toSkeleton (constituentFDRep ρ σ)) :=
  fun c => ⟨componentClass ρ c, componentClass_mem_orbit ρ hσ c⟩

/-- The isotypic component cut out by the translate of a fixed constituent. -/
noncomputable def conjSubrepIsotypicComponent
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) :=
  ⟨isotypicComponent k[N] (_root_.Representation.asModule (ρ.comp N.subtype))
      (conjSubrep ρ g σ).asSubmodule,
    ⟨(conjSubrep ρ g σ).asSubmodule,
      Subrepresentation.isSimpleModule_asSubmodule_iff.mpr (isAtom_conjSubrep_iff.mpr hσ), rfl⟩⟩

omit [FiniteDimensional k V] in
/-- The component of a translated constituent is definitionally the corresponding isotypic
component. -/
@[simp]
theorem coe_conjSubrepIsotypicComponent
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    (conjSubrepIsotypicComponent ρ σ hσ g :
      Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype))) =
      isotypicComponent k[N] (_root_.Representation.asModule (ρ.comp N.subtype))
        (conjSubrep ρ g σ).asSubmodule :=
  (rfl)

private theorem componentClass_conjSubrepIsotypicComponent
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    componentClass ρ (conjSubrepIsotypicComponent ρ σ hσ g) =
      g • toSkeleton (constituentFDRep ρ σ) := by
  let _ : IsSimpleModule k[N] (conjSubrep ρ g σ).asSubmodule :=
    Subrepresentation.isSimpleModule_asSubmodule_iff.mpr (isAtom_conjSubrep_iff.mpr hσ)
  rw [← toSkeleton_constituentFDRep_conjSubrep ρ g σ]
  apply (toSkeleton_constituentFDRep_eq_iff ρ _ _).2
  rw [asSubmodule_componentSubrep]
  have hle : (conjSubrep ρ g σ).asSubmodule ≤ isotypicComponent k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))
        (componentRepresentative ρ (conjSubrepIsotypicComponent ρ σ hσ g)) := by
    rw [← component_eq_isotypicComponent_componentRepresentative ρ]
    exact (conjSubrep ρ g σ).asSubmodule.le_isotypicComponent
  obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))
        (componentRepresentative ρ (conjSubrepIsotypicComponent ρ σ hσ g)))
      (conjSubrep ρ g σ).asSubmodule hle
  exact ⟨e.symm⟩

private theorem componentOrbitMap_injective [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    Function.Injective (componentOrbitMap ρ hσ) := by
  intro c d hcd
  have hclass : componentClass ρ c = componentClass ρ d := congrArg Subtype.val hcd
  -- `componentClass` hides the chosen representatives; expose only their two `toSkeleton` values
  -- so the preceding bridge lemma applies.
  change toSkeleton (constituentFDRep ρ (componentSubrep ρ c)) =
    toSkeleton (constituentFDRep ρ (componentSubrep ρ d)) at hclass
  obtain ⟨e⟩ := (toSkeleton_constituentFDRep_eq_iff ρ _ _).1 hclass
  rw [asSubmodule_componentSubrep, asSubmodule_componentSubrep] at e
  apply Subtype.ext
  rw [component_eq_isotypicComponent_componentRepresentative,
    component_eq_isotypicComponent_componentRepresentative]
  exact e.isotypicComponent_eq

private theorem componentOrbitMap_surjective [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    Function.Surjective (componentOrbitMap ρ hσ) := by
  rintro ⟨x, hx⟩
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hx
  refine ⟨conjSubrepIsotypicComponent ρ σ hσ g, Subtype.ext ?_⟩
  exact (componentClass_conjSubrepIsotypicComponent ρ σ hσ g).trans hg

private noncomputable def componentsEquivOrbit [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) ≃
      MulAction.orbit G (toSkeleton (constituentFDRep ρ σ)) :=
  Equiv.ofBijective (componentOrbitMap ρ hσ)
    ⟨componentOrbitMap_injective ρ hσ, componentOrbitMap_surjective ρ hσ⟩

private theorem stabilizer_constituentClass_eq_inertia
    (σ : Subrepresentation (ρ.comp N.subtype)) :
    MulAction.stabilizer G (toSkeleton (constituentFDRep ρ σ)) =
      inertia (FDRep.of σ.toRepresentation) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, mem_inertia_iff, smul_toSkeleton,
    toSkeleton_eq_toSkeleton_iff]
  rfl

/-- **The inertia cosets index the isotypic components in Clifford's theorem.**  A component is
sent to the conjugation orbit of any simple submodule presenting it, and orbit--stabilizer
identifies that orbit with the left cosets of the constituent's inertia group. -/
noncomputable def isotypicComponentsEquivQuotientInertia [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) ≃
      G ⧸ inertia (FDRep.of σ.toRepresentation) :=
  ((componentsEquivOrbit ρ hσ).trans
    (MulAction.orbitEquivQuotientStabilizer G
      (toSkeleton (constituentFDRep ρ σ)))).trans
    (Subgroup.quotientEquivOfEq (stabilizer_constituentClass_eq_inertia ρ σ))

/-- Under the Clifford orbit equivalence, the component of the translate by `g` corresponds to
the coset of `g`. -/
@[simp]
theorem isotypicComponentsEquivQuotientInertia_apply_conjSubrep [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    isotypicComponentsEquivQuotientInertia ρ σ hσ
        (conjSubrepIsotypicComponent ρ σ hσ g) =
      QuotientGroup.mk g := by
  let eo := MulAction.orbitEquivQuotientStabilizer G
    (toSkeleton (constituentFDRep ρ σ))
  rw [isotypicComponentsEquivQuotientInertia]
  -- The public equivalence is a threefold composite; displaying the composite application makes
  -- the two generic equivalences available through their injectivity and computation lemmas.
  change Subgroup.quotientEquivOfEq (stabilizer_constituentClass_eq_inertia ρ σ)
      (eo (componentsEquivOrbit ρ hσ (conjSubrepIsotypicComponent ρ σ hσ g))) =
    QuotientGroup.mk g
  have horbit : componentsEquivOrbit ρ hσ (conjSubrepIsotypicComponent ρ σ hσ g) =
      eo.symm (QuotientGroup.mk g) := by
    apply Subtype.ext
    -- The source equivalence is built from `componentOrbitMap`; after passing to underlying
    -- skeleton objects its value is `componentClass`.
    change componentClass ρ (conjSubrepIsotypicComponent ρ σ hσ g) = _
    simpa [eo] using componentClass_conjSubrepIsotypicComponent ρ σ hσ g
  calc
    _ = Subgroup.quotientEquivOfEq (stabilizer_constituentClass_eq_inertia ρ σ)
        (QuotientGroup.mk g) := congrArg _
          ((congrArg eo horbit).trans (eo.apply_symm_apply (QuotientGroup.mk g)))
    _ = QuotientGroup.mk g := Subgroup.quotientEquivOfEq_mk _ _

/-- **The number of constituent classes is the inertia index.**  This is the numerical
orbit--stabilizer statement underlying the number of summands in Clifford's decomposition. -/
theorem card_isotypicComponents_eq_inertia_index [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    Nat.card (isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) =
      (inertia (FDRep.of σ.toRepresentation) : Subgroup G).index := by
  exact Nat.card_congr (isotypicComponentsEquivQuotientInertia ρ σ hσ)

end OrbitIndex

end Representation

end TauCeti
