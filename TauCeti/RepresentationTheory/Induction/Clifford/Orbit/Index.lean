/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Induction.Clifford.Orbit.Basic
public import TauCeti.RepresentationTheory.Induction.Inertia
public import TauCeti.RingTheory.Semisimple.RegularIsotypicComponent

/-!
# Inertia cosets index the constituents in Clifford's theorem

This file identifies the orbit of an irreducible constituent in Clifford's theorem with the left
cosets of its inertia group. Concretely, if `σ` is a minimal subrepresentation of the restriction
of an irreducible finite-dimensional representation `ρ` from `G` to a normal subgroup `N`, then
the isotypic components of the restriction are indexed by

`G ⧸ inertia (FDRep.of σ.toRepresentation)`.

The construction combines the single-orbit theorem from
`TauCeti/RepresentationTheory/Induction/Clifford/Orbit/Basic.lean` with Mathlib's generic
`MulAction.orbitEquivQuotientStabilizer`. It uses two dictionary bridges: translating `σ` inside
`ρ` represents the conjugate abstract `N`-representation carried by `σ`, and the module of a
subrepresentation is canonically equivalent to its associated `k[N]`-submodule.

## Main definitions

* `Representation.fdRepIsoConjSubrep`: the finite-dimensional representation carried by a
  translated constituent is isomorphic to the conjugate representation.
* `Representation.isotypicComponentsEquivQuotientInertia`: the equivalence between the isotypic
  components of the restriction and the inertia cosets.

The indexed component `Representation.conjSubrepIsotypicComponent` is defined in `Orbit/Basic.lean`.

## Main results

* `Representation.toSkeleton_fdRepOf_conjSubrep`: translating a constituent inside `ρ` and
  conjugating the abstract `N`-representation it carries agree on isomorphism classes.
* `Representation.mem_inertia_fdRepOf_toRepresentation_iff`: a group element lies in the inertia
  group of a constituent exactly when its translate carries an equivalent `k[N]`-submodule.
* `Representation.isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent`: under the
  equivalence, the component of the translate by `g` corresponds to the coset of `g`.
* `Representation.isotypicComponentsEquivQuotientInertia_symm_mk`: the inverse computation.
* `Representation.conjSubrepIsotypicComponent_eq_iff`: two translates determine the same component
  exactly when their quotient lies in the inertia group.
* `Representation.card_isotypicComponents_eq_inertia_index`: the number of irreducible constituent
  classes is the index of the inertia group.

## Implementation notes

Isotypic components are handled through `TauCeti.simpleSubmoduleClassesEquiv`, rather than by
choosing a simple representative. Isomorphism of subrepresentations is expressed as a
`k[N]`-linear equivalence of their associated submodules; the general bridge to equality in
`Skeleton (FDRep k N)` is `TauCeti.toSkeleton_fdRepOf_toRepresentation_eq_iff`.

## References

This is the orbit-indexing step in Clifford's theorem from Layer 5 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`. It prepares the remaining
packaged decomposition of the restriction as equal-multiplicity copies of the conjugates indexed
by an inertia-group transversal.

The mathematics is the classical orbit-stabilizer argument in C. W. Curtis and I. Reiner,
*Representation Theory of Finite Groups and Associative Algebras*, §49.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

universe u v

namespace Representation

open TauCeti TauCeti.Representation

section OrbitIndex

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {V : Type u} [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

/-- **A translated constituent carries the conjugate finite-dimensional representation.** -/
noncomputable def fdRepIsoConjSubrep [FiniteDimensional k V]
    (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    FDRep.of (conjSubrep ρ g σ).toRepresentation ≅
      conjNormalFDRep g (FDRep.of σ.toRepresentation) :=
  fdRepIsoOfAsModuleLinearEquiv
    (TauCeti.Representation.asModuleLinearEquivOfEquiv (conjSubrepEquiv ρ g σ).symm)

/-- Translating a constituent inside the ambient representation agrees, on isomorphism classes,
with conjugating the finite-dimensional representation carried by that constituent. -/
theorem toSkeleton_fdRepOf_conjSubrep [FiniteDimensional k V]
    (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    toSkeleton (FDRep.of (conjSubrep ρ g σ).toRepresentation) =
      g • toSkeleton (FDRep.of σ.toRepresentation) := by
  rw [smul_toSkeleton]
  exact toSkeleton_eq_toSkeleton_iff.mpr ⟨fdRepIsoConjSubrep ρ g σ⟩

/-- Membership in a constituent's inertia group is equivalence of the translated and original
associated submodules. -/
theorem mem_inertia_fdRepOf_toRepresentation_iff [FiniteDimensional k V]
    (g : G) (σ : Subrepresentation (ρ.comp N.subtype)) :
    g ∈ inertia (FDRep.of σ.toRepresentation) ↔
      Nonempty ((conjSubrep ρ g σ).asSubmodule ≃ₗ[k[N]] σ.asSubmodule) := by
  rw [mem_inertia_iff]
  constructor
  · rintro ⟨i⟩
    apply (toSkeleton_fdRepOf_toRepresentation_eq_iff _ _).mp
    exact toSkeleton_eq_toSkeleton_iff.mpr ⟨fdRepIsoConjSubrep ρ g σ ≪≫ i⟩
  · intro h
    obtain ⟨i⟩ := toSkeleton_eq_toSkeleton_iff.mp
      ((toSkeleton_fdRepOf_toRepresentation_eq_iff _ _).mpr h)
    exact ⟨(fdRepIsoConjSubrep ρ g σ).symm ≪≫ i⟩

variable [FiniteDimensional k V]

/-- Send an isomorphism class of simple submodules to the class of the finite-dimensional
representation carried by any representative. -/
private noncomputable def submoduleClassToSkeleton :
    SimpleSubmoduleClasses k[N]
        (_root_.Representation.asModule (ρ.comp N.subtype)) →
      Skeleton (FDRep k N) :=
  SimpleSubmoduleClasses.lift
    (fun T _ ↦ toSkeleton (FDRep.of
      (Subrepresentation.subrepresentationSubmoduleOrderIso.symm T).toRepresentation))
    (by
      intro T U _ _ e
      apply (toSkeleton_fdRepOf_toRepresentation_eq_iff _ _).mpr
      obtain ⟨e⟩ := e
      exact ⟨(LinearEquiv.ofEq _ _
          (OrderIso.apply_symm_apply
            Subrepresentation.subrepresentationSubmoduleOrderIso T)).trans e
        |>.trans
        (LinearEquiv.ofEq _ _
          (OrderIso.apply_symm_apply
            Subrepresentation.subrepresentationSubmoduleOrderIso U).symm)⟩)

omit [N.Normal] in
@[simp]
private theorem submoduleClassToSkeleton_mk
    (T : Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype)))
    [IsSimpleModule k[N] T] :
    submoduleClassToSkeleton ρ (.mk T) =
      toSkeleton (FDRep.of
        (Subrepresentation.subrepresentationSubmoduleOrderIso.symm T).toRepresentation) :=
  by
    rw [submoduleClassToSkeleton, SimpleSubmoduleClasses.lift_mk]

omit [N.Normal] in
private theorem submoduleClassToSkeleton_injective :
    Function.Injective (submoduleClassToSkeleton (N := N) ρ) := by
  intro C
  induction C using SimpleSubmoduleClasses.ind with
  | mk T hT =>
    intro D
    induction D using SimpleSubmoduleClasses.ind with
    | mk U hU =>
      intro h
      rw [SimpleSubmoduleClasses.mk_eq_mk_iff]
      have h' :
          toSkeleton (FDRep.of
              (Subrepresentation.subrepresentationSubmoduleOrderIso.symm T).toRepresentation) =
            toSkeleton (FDRep.of
              (Subrepresentation.subrepresentationSubmoduleOrderIso.symm U).toRepresentation) := by
        simpa only [submoduleClassToSkeleton_mk] using h
      obtain ⟨e⟩ := (toSkeleton_fdRepOf_toRepresentation_eq_iff _ _).mp h'
      exact ⟨(LinearEquiv.ofEq _ _
          (OrderIso.apply_symm_apply
            Subrepresentation.subrepresentationSubmoduleOrderIso T).symm).trans e
        |>.trans (LinearEquiv.ofEq _ _
          (OrderIso.apply_symm_apply
            Subrepresentation.subrepresentationSubmoduleOrderIso U))⟩

/-- The isomorphism class attached to an isotypic component, obtained through the generic
equivalence between components and simple-submodule classes. -/
private noncomputable def componentClassMap
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    Skeleton (FDRep k N) :=
  submoduleClassToSkeleton ρ
    ((simpleSubmoduleClassesEquiv k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))).symm c)

omit [N.Normal] in
private theorem componentClassMap_injective :
    Function.Injective (componentClassMap (N := N) ρ) := by
  intro c d h
  apply (simpleSubmoduleClassesEquiv k[N]
    (_root_.Representation.asModule (ρ.comp N.subtype))).symm.injective
  exact submoduleClassToSkeleton_injective ρ h

private theorem componentClassMap_conjSubrepIsotypicComponent [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    componentClassMap ρ (conjSubrepIsotypicComponent ρ σ hσ g) =
      g • toSkeleton (FDRep.of σ.toRepresentation) := by
  let _ : IsSimpleModule k[N] (conjSubrep ρ g σ).asSubmodule :=
    Subrepresentation.isSimpleModule_asSubmodule_iff.mpr (isAtom_conjSubrep_iff.mpr hσ)
  let ec := simpleSubmoduleClassesEquiv k[N]
    (_root_.Representation.asModule (ρ.comp N.subtype))
  have hclass :
      ec.symm (conjSubrepIsotypicComponent ρ σ hσ g) =
        SimpleSubmoduleClasses.mk (conjSubrep ρ g σ).asSubmodule := by
    apply ec.injective
    exact (ec.apply_symm_apply _).trans <| by
      apply Subtype.ext
      simp only [ec, coe_conjSubrepIsotypicComponent,
        coe_simpleSubmoduleClassesEquiv_mk]
  rw [componentClassMap, hclass, submoduleClassToSkeleton_mk]
  calc
    _ = toSkeleton (FDRep.of (conjSubrep ρ g σ).toRepresentation) :=
      (toSkeleton_fdRepOf_toRepresentation_eq_iff _ _).mpr <| by
        exact ⟨LinearEquiv.ofEq _ _
          (OrderIso.apply_symm_apply
            Subrepresentation.subrepresentationSubmoduleOrderIso _)⟩
    _ = _ := toSkeleton_fdRepOf_conjSubrep ρ g σ

private theorem submoduleClassToSkeleton_mem_orbit [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ)
    (C : SimpleSubmoduleClasses k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    submoduleClassToSkeleton ρ C ∈
      MulAction.orbit G (toSkeleton (FDRep.of σ.toRepresentation)) := by
  induction C using SimpleSubmoduleClasses.ind with
  | mk T hT =>
    obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ T
    rw [MulAction.mem_orbit_iff]
    refine ⟨g, ?_⟩
    exact (toSkeleton_fdRepOf_conjSubrep ρ g σ).symm.trans <| by
      rw [submoduleClassToSkeleton_mk]
      apply (toSkeleton_fdRepOf_toRepresentation_eq_iff _ _).mpr
      exact ⟨e.symm.trans (LinearEquiv.ofEq _ _
        (OrderIso.apply_symm_apply
          Subrepresentation.subrepresentationSubmoduleOrderIso _).symm)⟩

/-- Every component class is in the conjugation orbit of a fixed constituent. -/
private theorem componentClassMap_mem_orbit [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ)
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    componentClassMap ρ c ∈
      MulAction.orbit G (toSkeleton (FDRep.of σ.toRepresentation)) :=
  submoduleClassToSkeleton_mem_orbit ρ hσ _

private noncomputable def componentOrbitMap [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) →
      MulAction.orbit G (toSkeleton (FDRep.of σ.toRepresentation)) :=
  fun c ↦ ⟨componentClassMap ρ c, componentClassMap_mem_orbit ρ hσ c⟩

private theorem componentOrbitMap_injective [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    Function.Injective (componentOrbitMap ρ hσ) := by
  intro c d h
  apply componentClassMap_injective ρ
  exact congrArg Subtype.val h

private theorem componentOrbitMap_surjective [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    Function.Surjective (componentOrbitMap ρ hσ) := by
  rintro ⟨x, hx⟩
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hx
  refine ⟨conjSubrepIsotypicComponent ρ σ hσ g, Subtype.ext ?_⟩
  exact (componentClassMap_conjSubrepIsotypicComponent ρ σ hσ g).trans hg

private noncomputable def componentsEquivOrbit [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) ≃
      MulAction.orbit G (toSkeleton (FDRep.of σ.toRepresentation)) :=
  Equiv.ofBijective (componentOrbitMap ρ hσ)
    ⟨componentOrbitMap_injective ρ hσ, componentOrbitMap_surjective ρ hσ⟩

@[simp]
private theorem componentsEquivOrbit_apply [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ)
    (c : isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) :
    componentsEquivOrbit ρ hσ c = componentOrbitMap ρ hσ c := by
  rfl

private theorem stabilizer_toSkeleton_fdRepOf_eq_inertia
    (σ : Subrepresentation (ρ.comp N.subtype)) :
    MulAction.stabilizer G (toSkeleton (FDRep.of σ.toRepresentation)) =
      inertia (FDRep.of σ.toRepresentation) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, mem_inertia_iff, smul_toSkeleton,
    toSkeleton_eq_toSkeleton_iff]

/-- **The inertia cosets index the isotypic components in Clifford's theorem.** A component is
sent to the coset of any `g` whose translated constituent cuts out that component, and generic
orbit--stabilizer identifies this with the left cosets of the constituent's inertia group. -/
noncomputable def isotypicComponentsEquivQuotientInertia [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) ≃
      G ⧸ inertia (FDRep.of σ.toRepresentation) :=
  (componentsEquivOrbit ρ hσ).trans
    (MulAction.orbitEquivQuotientStabilizer G
      (toSkeleton (FDRep.of σ.toRepresentation))) |>.trans
    (Subgroup.quotientEquivOfEq (stabilizer_toSkeleton_fdRepOf_eq_inertia ρ σ))

/-- Under the Clifford orbit equivalence, the component of the translate by `g` corresponds to
the coset of `g`. -/
@[simp]
theorem isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent
    [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    isotypicComponentsEquivQuotientInertia ρ σ hσ
        (conjSubrepIsotypicComponent ρ σ hσ g) =
      QuotientGroup.mk g := by
  let eo := MulAction.orbitEquivQuotientStabilizer G
    (toSkeleton (FDRep.of σ.toRepresentation))
  simp only [isotypicComponentsEquivQuotientInertia]
  have horbit :
      componentsEquivOrbit ρ hσ (conjSubrepIsotypicComponent ρ σ hσ g) =
        (MulAction.orbitEquivQuotientStabilizer G
          (toSkeleton (FDRep.of σ.toRepresentation))).symm (QuotientGroup.mk g) := by
    apply Subtype.ext
    rw [componentsEquivOrbit_apply]
    simpa only [componentOrbitMap,
      MulAction.orbitEquivQuotientStabilizer_symm_apply] using
      componentClassMap_conjSubrepIsotypicComponent ρ σ hσ g
  calc
    _ = Subgroup.quotientEquivOfEq (stabilizer_toSkeleton_fdRepOf_eq_inertia ρ σ)
        (QuotientGroup.mk g) := congrArg _ <|
          (congrArg eo horbit).trans (eo.apply_symm_apply (QuotientGroup.mk g))
    _ = QuotientGroup.mk g := Subgroup.quotientEquivOfEq_mk _ _

/-- The coset of `g` is sent back to the component cut out by the translate by `g`. -/
@[simp]
theorem isotypicComponentsEquivQuotientInertia_symm_mk [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    (isotypicComponentsEquivQuotientInertia ρ σ hσ).symm (QuotientGroup.mk g) =
      conjSubrepIsotypicComponent ρ σ hσ g := by
  rw [Equiv.symm_apply_eq]
  exact (isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent ρ σ hσ g).symm

/-- Two translates cut out the same isotypic component exactly when they determine the same
inertia coset. -/
@[simp]
theorem conjSubrepIsotypicComponent_eq_iff [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g h : G) :
    conjSubrepIsotypicComponent ρ σ hσ g = conjSubrepIsotypicComponent ρ σ hσ h ↔
      g⁻¹ * h ∈ inertia (FDRep.of σ.toRepresentation) := by
  constructor
  · intro e
    have he := congrArg (isotypicComponentsEquivQuotientInertia ρ σ hσ) e
    simpa only [isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent,
      QuotientGroup.eq] using he
  · intro e
    apply (isotypicComponentsEquivQuotientInertia ρ σ hσ).injective
    rw [isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent,
      isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent]
    exact QuotientGroup.eq.mpr e

/-- **The number of constituent classes is the inertia index.** This is the numerical
orbit--stabilizer statement underlying the number of summands in Clifford's decomposition. -/
theorem card_isotypicComponents_eq_inertia_index [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    Nat.card (isotypicComponents k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype))) =
      (inertia (FDRep.of σ.toRepresentation) : Subgroup G).index := by
  exact Nat.card_congr (isotypicComponentsEquivQuotientInertia ρ σ hσ)

end OrbitIndex

end Representation
