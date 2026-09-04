/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Compact.Character.Projection
public import Mathlib.RingTheory.SimpleModule.Isotypic
import TauCeti.RepresentationTheory.Continuous.InvariantComplement
import TauCeti.RepresentationTheory.Continuous.Intertwining
import TauCeti.RepresentationTheory.Irreducible

/-!
# Isotypic projections for compact-group representations

Let `rho` be a finite-dimensional unitary representation of a compact group and let `sigma` be an
irreducible subrepresentation. The continuous class function

`dim(sigma) · conj(character sigma)`

acts on `rho` by integration. The character-projection identities show that it is the identity on
every irreducible subrepresentation isomorphic to `sigma` and zero on every other irreducible
subrepresentation. Complete reducibility then identifies its range with Mathlib's
`isotypicComponent` attached to `sigma`.

## Main definitions

* `ContRepresentation.isotypicKernel`: the normalized conjugate-character kernel.
* `ContRepresentation.isotypicProjector`: its integrated action on the ambient
  representation, packaged as a continuous self-intertwiner.

## Main results

* `ContRepresentation.isotypicProjector_apply_subtype_of_equiv`: the projector is the
  identity on an irreducible subrepresentation of the selected isomorphism type.
* `ContRepresentation.isotypicProjector_apply_subtype_of_not_equiv`: it vanishes on an
  irreducible subrepresentation of every other isomorphism type.
* `ContRepresentation.range_isotypicProjector`: the range of the projector is precisely
  Mathlib's `isotypicComponent`.
* `ContRepresentation.isotypicProjector_idempotent`: the projector is idempotent.

## Implementation notes

The selected irreducible is represented by an actual subrepresentation `sigma` of `rho`. This
makes its character and its inclusion into the ambient representation canonical. Isomorphism type
is nevertheless the only datum visible in the answer: the range is Mathlib's sum of all simple
submodules linearly equivalent to `sigma.asSubmodule`.

The bridge from the blockwise character identities to the ambient representation is
`ContRepresentation.comp_integratedOperator`: integration is natural with respect to the
inclusion of an invariant subspace. Complete reducibility is supplied by the invariant orthogonal
complement of a unitary representation.

All declarations sit in the root `ContRepresentation` namespace, so that `rho.isotypicProjector`
and `rho.isotypicKernel` elaborate: `ContRepresentation` is Mathlib's type, and
`scripts/lint-dot-notation.py` asks that new declarations about it not recreate its namespace
inside `TauCeti`.

## References

This constructs the isotypic projector requested in Layer 5 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
using the normalization `dim V_pi · conj chi_pi` specified there. The mathematical development
follows Daniel Bump, *Lie Groups*, second edition, Chapter 2, and T. Bröcker and T. tom Dieck,
*Representations of Compact Lie Groups*, Springer GTM 98 (1985), Chapter II.
-/

public section

open MeasureTheory TauCeti TauCeti.ContRepresentation
open scoped InnerProductSpace MonoidAlgebra

namespace ContRepresentation

section IsotypicProjection

variable {k G V : Type*} [RCLike k] [IsAlgClosed k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace k V] [NormedSpace ℝ V] [SMulCommClass ℝ k V]
  [FiniteDimensional k V]

local instance instCompleteSpaceIsotypicProjection : CompleteSpace V :=
  FiniteDimensional.complete k V

variable (rho : ContRepresentation k G V) (hrho : Continuous rho)

include hrho

/-- The normalized conjugate-character kernel attached to a subrepresentation. When the
subrepresentation is irreducible and the ambient representation is unitary, integrating this
kernel cuts out its entire isotypic component. -/
noncomputable def isotypicKernel (sigma : Subrepresentation rho.toRepresentation) : C(G, k) :=
  let hSigma : ∀ g, ∀ v ∈ sigma.toSubmodule, rho g v ∈ sigma.toSubmodule :=
    fun g _ hv ↦ sigma.apply_mem_toSubmodule g hv
  let rhoSigma := subrepresentation rho sigma.toSubmodule hSigma
  let hSigma := continuous_subrepresentation hrho
  (Module.finrank k sigma.toSubmodule : k) • star (character rhoSigma hSigma)

omit [IsAlgClosed k] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ V] [SMulCommClass ℝ k V] in
/-- The isotypic kernel is constant on conjugacy classes. -/
theorem isotypicKernel_conj (sigma : Subrepresentation rho.toRepresentation) (g h : G) :
    isotypicKernel rho hrho sigma (h * g * h⁻¹) = isotypicKernel rho hrho sigma g := by
  simp only [isotypicKernel, ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.star_apply]
  rw [character_conj]

/-- **The character isotypic projector.** This is the action on `rho` of
`dim(sigma) · conj(character sigma)`, packaged as a continuous self-intertwiner. -/
noncomputable def isotypicProjector (sigma : Subrepresentation rho.toRepresentation) :
    ContIntertwiningMap rho rho where
  __ := integratedOperator rho hrho (isotypicKernel rho hrho sigma)
  isIntertwining' := integratedOperator_comp rho hrho (isotypicKernel_conj rho hrho sigma)

omit [IsAlgClosed k] in
/-- The continuous linear map underlying the isotypic projector is the integrated action of its
normalized conjugate-character kernel. -/
@[simp]
theorem toContinuousLinearMap_isotypicProjector
    (sigma : Subrepresentation rho.toRepresentation) :
    (isotypicProjector rho hrho sigma).toContinuousLinearMap =
      integratedOperator rho hrho (isotypicKernel rho hrho sigma) :=
  (rfl)

omit [IsAlgClosed k] in
/-- The defining integral formula for the isotypic projector. -/
theorem isotypicProjector_apply (sigma : Subrepresentation rho.toRepresentation) (v : V) :
    isotypicProjector rho hrho sigma v =
      ∫ g, isotypicKernel rho hrho sigma g • rho g v ∂haarProb G :=
  calc
    _ = (isotypicProjector rho hrho sigma).toContinuousLinearMap v := (rfl)
    _ = integratedOperator rho hrho (isotypicKernel rho hrho sigma) v := by
      rw [toContinuousLinearMap_isotypicProjector]
    _ = _ := integratedOperator_apply rho hrho _ v

omit hrho in
/-- The inclusion of an invariant subspace, packaged as a continuous intertwiner. -/
private noncomputable def subrepresentationInclusion
    (tau : Subrepresentation rho.toRepresentation) :
    ContIntertwiningMap
      (subrepresentation rho tau.toSubmodule
        (fun g _ hv ↦ tau.apply_mem_toSubmodule g hv)) rho :=
  { toContinuousLinearMap := tau.toSubmodule.subtypeL
    isIntertwining' := fun g ↦ by
      ext v
      exact coe_subrepresentation_apply g v }

omit hrho [IsAlgClosed k] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ V] [SMulCommClass ℝ k V]
  [FiniteDimensional k V] in
@[simp]
private theorem subrepresentationInclusion_apply
    (tau : Subrepresentation rho.toRepresentation) (v : tau.toSubmodule) :
    subrepresentationInclusion rho tau v = (v : V) :=
  (rfl)

omit [IsAlgClosed k] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ V] [SMulCommClass ℝ k V] in
/-- Equivalent subrepresentations determine the same normalized character kernel. -/
private theorem isotypicKernel_eq_of_equiv
    {sigma tau : Subrepresentation rho.toRepresentation}
    (e : tau.asSubmodule ≃ₗ[k[G]] sigma.asSubmodule) :
    isotypicKernel rho hrho sigma = isotypicKernel rho hrho tau := by
  let phi : tau.toRepresentation.Equiv sigma.toRepresentation :=
    Representation.equivOfAsModuleLinearEquiv
      ((tau.asModuleEquivAsSubmodule.trans e).trans sigma.asModuleEquivAsSubmodule.symm)
  have hdim : Module.finrank k tau.toSubmodule = Module.finrank k sigma.toSubmodule :=
    (e.restrictScalars k).finrank_eq
  ext g
  simp only [isotypicKernel, ContinuousMap.smul_apply, ContinuousMap.star_apply, smul_eq_mul,
    coe_character, hdim]
  congr 2
  let hTau : ∀ g, ∀ v ∈ tau.toSubmodule, rho g v ∈ tau.toSubmodule :=
    fun g _ hv ↦ tau.apply_mem_toSubmodule g hv
  let hSigma : ∀ g, ∀ v ∈ sigma.toSubmodule, rho g v ∈ sigma.toSubmodule :=
    fun g _ hv ↦ sigma.apply_mem_toSubmodule g hv
  have hTauRep : (subrepresentation rho tau.toSubmodule hTau).toRepresentation =
      tau.toRepresentation := by
    rw [toRepresentation_subrepresentation]
    ext g v
    rfl
  have hSigmaRep : (subrepresentation rho sigma.toSubmodule hSigma).toRepresentation =
      sigma.toRepresentation := by
    rw [toRepresentation_subrepresentation]
    ext g v
    rfl
  rw [hTauRep, hSigmaRep]
  exact congrFun (Representation.char_iso phi.symm) g

/-- **The isotypic projector is the identity on every equivalent irreducible block.** -/
theorem isotypicProjector_apply_subtype_of_equiv (hunitary : IsUnitary rho)
    {sigma tau : Subrepresentation rho.toRepresentation} (htau : IsAtom tau)
    (e : Nonempty (tau.asSubmodule ≃ₗ[k[G]] sigma.asSubmodule))
    (v : tau.toSubmodule) :
    isotypicProjector rho hrho sigma (v : V) = (v : V) := by
  let hTauInv : ∀ g, ∀ v ∈ tau.toSubmodule, rho g v ∈ tau.toSubmodule :=
    fun g _ hv ↦ tau.apply_mem_toSubmodule g hv
  let rhoTau := subrepresentation rho tau.toSubmodule hTauInv
  let hTau : Continuous rhoTau := continuous_subrepresentation hrho
  let iota : ContIntertwiningMap rhoTau rho := subrepresentationInclusion rho tau
  have hirrTau : Representation.IsIrreducible rhoTau.toRepresentation :=
    by
      dsimp [rhoTau]
      rw [toRepresentation_subrepresentation]
      exact TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom htau
  have hunitaryTau : IsUnitary rhoTau :=
    hunitary.subrepresentation tau.apply_mem_toSubmodule
  have hkernel := isotypicKernel_eq_of_equiv rho hrho e.some
  have hblock : integratedOperator rhoTau hTau (isotypicKernel rho hrho sigma) =
      ContinuousLinearMap.id k tau.toSubmodule := by
    rw [hkernel, isotypicKernel, integratedOperator_smul,
      finrank_smul_integratedOperator_star_character_self rhoTau hTau hunitaryTau hirrTau]
  have hnatural := comp_integratedOperator rhoTau hTau rho hrho iota
    (isotypicKernel rho hrho sigma)
  have happly := congrArg (fun T : tau.toSubmodule →L[k] V ↦ T v) hnatural
  have hiota : iota.toContinuousLinearMap v = (v : V) :=
    subrepresentationInclusion_apply rho tau v
  calc
    isotypicProjector rho hrho sigma (v : V) =
        integratedOperator rho hrho (isotypicKernel rho hrho sigma) (v : V) := by
      exact congrArg (fun T : V →L[k] V ↦ T (v : V))
        (toContinuousLinearMap_isotypicProjector rho hrho sigma)
    _ = integratedOperator rho hrho (isotypicKernel rho hrho sigma)
        (iota.toContinuousLinearMap v) := by rw [hiota]
    _ = iota.toContinuousLinearMap
        (integratedOperator rhoTau hTau (isotypicKernel rho hrho sigma) v) := by
      simpa only [ContinuousLinearMap.comp_apply] using happly.symm
    _ = (v : V) := by rw [hblock, ContinuousLinearMap.id_apply, hiota]

/-- **The isotypic projector vanishes on every inequivalent irreducible block.** -/
theorem isotypicProjector_apply_subtype_of_not_equiv (hunitary : IsUnitary rho)
    {sigma tau : Subrepresentation rho.toRepresentation} (hsigma : IsAtom sigma)
    (htau : IsAtom tau) (hne : IsEmpty (tau.asSubmodule ≃ₗ[k[G]] sigma.asSubmodule))
    (v : tau.toSubmodule) :
    isotypicProjector rho hrho sigma (v : V) = 0 := by
  let hSigmaInv : ∀ g, ∀ v ∈ sigma.toSubmodule, rho g v ∈ sigma.toSubmodule :=
    fun g _ hv ↦ sigma.apply_mem_toSubmodule g hv
  let rhoSigma := subrepresentation rho sigma.toSubmodule hSigmaInv
  let hSigma : Continuous rhoSigma := continuous_subrepresentation hrho
  let hTauInv : ∀ g, ∀ v ∈ tau.toSubmodule, rho g v ∈ tau.toSubmodule :=
    fun g _ hv ↦ tau.apply_mem_toSubmodule g hv
  let rhoTau := subrepresentation rho tau.toSubmodule hTauInv
  let hTau : Continuous rhoTau := continuous_subrepresentation hrho
  let iota : ContIntertwiningMap rhoTau rho := subrepresentationInclusion rho tau
  have hirrSigma : Representation.IsIrreducible rhoSigma.toRepresentation :=
    by
      dsimp [rhoSigma]
      rw [toRepresentation_subrepresentation]
      exact TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom hsigma
  have hirrTau : Representation.IsIrreducible rhoTau.toRepresentation :=
    by
      dsimp [rhoTau]
      rw [toRepresentation_subrepresentation]
      exact TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom htau
  have hunitarySigma : IsUnitary rhoSigma :=
    hunitary.subrepresentation sigma.apply_mem_toSubmodule
  have hTauRep : rhoTau.toRepresentation = tau.toRepresentation := by
    dsimp [rhoTau]
    rw [toRepresentation_subrepresentation]
    ext g v
    rfl
  have hSigmaRep : rhoSigma.toRepresentation = sigma.toRepresentation := by
    dsimp [rhoSigma]
    rw [toRepresentation_subrepresentation]
    ext g v
    rfl
  let hempty : IsEmpty (_root_.ContRepresentation.Equiv rhoTau rhoSigma) :=
    ⟨fun phi ↦ by
      have phi' : tau.toRepresentation.Equiv sigma.toRepresentation := by
        have phi' := (ContRepresentation.nonempty_equiv_iff.mp ⟨phi⟩).some
        rw [hTauRep, hSigmaRep] at phi'
        exact phi'
      exact hne.false ((tau.asModuleEquivAsSubmodule.symm.trans
        (Representation.asModuleLinearEquivOfEquiv phi')).trans
          sigma.asModuleEquivAsSubmodule)⟩
  have hzero : integratedOperator rhoTau hTau
      (star (character rhoSigma hSigma)) = 0 :=
    integratedOperator_star_character_eq_zero rhoSigma hSigma rhoTau hTau hunitarySigma hirrTau
      fun phi ↦ by
        simpa using congrArg ContIntertwiningMap.toContinuousLinearMap
          (eq_zero_of_isEmpty_equiv hirrTau hirrSigma hempty phi)
  have hblock : integratedOperator rhoTau hTau (isotypicKernel rho hrho sigma) = 0 := by
    rw [isotypicKernel, integratedOperator_smul, hzero, smul_zero]
  have hnatural := comp_integratedOperator rhoTau hTau rho hrho iota
    (isotypicKernel rho hrho sigma)
  have happly := congrArg (fun T : tau.toSubmodule →L[k] V ↦ T v) hnatural
  have hiota : iota.toContinuousLinearMap v = (v : V) :=
    subrepresentationInclusion_apply rho tau v
  calc
    isotypicProjector rho hrho sigma (v : V) =
        integratedOperator rho hrho (isotypicKernel rho hrho sigma) (v : V) := by
      exact congrArg (fun T : V →L[k] V ↦ T (v : V))
        (toContinuousLinearMap_isotypicProjector rho hrho sigma)
    _ = integratedOperator rho hrho (isotypicKernel rho hrho sigma)
        (iota.toContinuousLinearMap v) := by rw [hiota]
    _ = iota.toContinuousLinearMap
        (integratedOperator rhoTau hTau (isotypicKernel rho hrho sigma) v) := by
      simpa only [ContinuousLinearMap.comp_apply] using happly.symm
    _ = 0 := by rw [hblock, zero_apply, map_zero]

/-- **The character projector cuts out the isotypic component.** Its range is exactly Mathlib's
sum of the simple `k[G]`-submodules isomorphic to the selected irreducible subrepresentation. -/
theorem range_isotypicProjector (hunitary : IsUnitary rho)
    (sigma : Subrepresentation rho.toRepresentation) (hsigma : IsAtom sigma) :
    (isotypicProjector rho hrho sigma).toIntertwiningMap.range.asSubmodule =
      isotypicComponent k[G] rho.toRepresentation.asModule sigma.asSubmodule := by
  classical
  let P := (isotypicProjector rho hrho sigma).toIntertwiningMap
  let p : Module.End k[G] rho.toRepresentation.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ P
  let C := isotypicComponent k[G] rho.toRepresentation.asModule sigma.asSubmodule
  let _ : IsSimpleModule k[G] sigma.asSubmodule :=
    Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hsigma
  have hsemisimple : IsSemisimpleModule k[G] rho.toRepresentation.asModule :=
    hunitary.isSemisimpleModule_asModule
  let _ := hsemisimple
  have hp_apply (x : rho.toRepresentation.asModule) :
      rho.toRepresentation.asModuleEquiv (p x) =
        P (rho.toRepresentation.asModuleEquiv x) := (rfl)
  have hP_apply (x : V) : P x = isotypicProjector rho hrho sigma x := (rfl)
  have hasModuleEquiv_apply (x : rho.toRepresentation.asModule) :
      rho.toRepresentation.asModuleEquiv x = (x : V) := (rfl)
  have hmaps : ∀ m : Submodule k[G] rho.toRepresentation.asModule,
      IsSimpleModule k[G] m → m ≤ C.comap p := by
    intro m hm x hx
    let tau : Subrepresentation rho.toRepresentation := Subrepresentation.ofSubmodule' m
    have htau : IsAtom tau := Subrepresentation.isSimpleModule_asSubmodule_iff.mp hm
    by_cases he : Nonempty (m ≃ₗ[k[G]] sigma.asSubmodule)
    · have happly := isotypicProjector_apply_subtype_of_equiv rho hrho hunitary htau he
        (⟨x, hx⟩ : tau.toSubmodule)
      have hmC : m ≤ C := le_sSup he
      have hxC : x ∈ C := hmC hx
      change p x ∈ C
      have hP : P (rho.toRepresentation.asModuleEquiv x) =
          rho.toRepresentation.asModuleEquiv x := by
        rw [hP_apply, hasModuleEquiv_apply]
        exact happly
      have hpx : p x = x := by
        apply rho.toRepresentation.asModuleEquiv.injective
        rw [hp_apply, hP]
      rw [hpx]
      exact hxC
    · let hne : IsEmpty (m ≃ₗ[k[G]] sigma.asSubmodule) := ⟨fun e ↦ he ⟨e⟩⟩
      have happly := isotypicProjector_apply_subtype_of_not_equiv rho hrho hunitary hsigma htau
        hne (⟨x, hx⟩ : tau.toSubmodule)
      change p x ∈ C
      have hP : P (rho.toRepresentation.asModuleEquiv x) = 0 := by
        rw [hP_apply, hasModuleEquiv_apply]
        exact happly
      have hpx : p x = 0 := by
        apply rho.toRepresentation.asModuleEquiv.injective
        rw [hp_apply, hP, map_zero]
      rw [hpx]
      exact C.zero_mem
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    have htop : (⊤ : Submodule k[G] rho.toRepresentation.asModule) ≤ C.comap p := by
      rw [← IsSemisimpleModule.sSup_simples_eq_top k[G] rho.toRepresentation.asModule]
      exact sSup_le fun m hm ↦ hmaps m hm
    exact htop Submodule.mem_top
  · rw [isotypicComponent]
    refine sSup_le fun m he ↦ ?_
    intro x hx
    let tau : Subrepresentation rho.toRepresentation := Subrepresentation.ofSubmodule' m
    have htau : IsAtom tau := Subrepresentation.isSimpleModule_asSubmodule_iff.mp
      (IsSimpleModule.congr he.some)
    have happly := isotypicProjector_apply_subtype_of_equiv rho hrho hunitary htau he
      (⟨x, hx⟩ : tau.toSubmodule)
    exact ⟨x, happly⟩

/-- The isotypic projector fixes every vector in the selected isotypic component. -/
theorem isotypicProjector_apply_of_mem_isotypicComponent (hunitary : IsUnitary rho)
    (sigma : Subrepresentation rho.toRepresentation) (hsigma : IsAtom sigma) (v : V)
    (hv : rho.toRepresentation.asModuleEquiv.symm v ∈
      isotypicComponent k[G] rho.toRepresentation.asModule sigma.asSubmodule) :
    isotypicProjector rho hrho sigma v = v := by
  classical
  let _ : IsSimpleModule k[G] sigma.asSubmodule :=
    Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hsigma
  have hfix : ∀ x : rho.toRepresentation.asModule,
      x ∈ isotypicComponent k[G] rho.toRepresentation.asModule sigma.asSubmodule →
        isotypicProjector rho hrho sigma (rho.toRepresentation.asModuleEquiv x) =
          rho.toRepresentation.asModuleEquiv x := by
    intro x hx
    rw [isotypicComponent, sSup_eq_iSup'] at hx
    refine Submodule.iSup_induction
      (motive := fun x ↦ isotypicProjector rho hrho sigma
        (rho.toRepresentation.asModuleEquiv x) = rho.toRepresentation.asModuleEquiv x)
      (fun m : {m : Submodule k[G] rho.toRepresentation.asModule |
        Nonempty (m ≃ₗ[k[G]] sigma.asSubmodule)} ↦ m.1) hx ?_ ?_ ?_
    · intro m x hx
      let tau : Subrepresentation rho.toRepresentation := Subrepresentation.ofSubmodule' m.1
      have htau : IsAtom tau := Subrepresentation.isSimpleModule_asSubmodule_iff.mp
        (IsSimpleModule.congr m.2.some)
      have happly := isotypicProjector_apply_subtype_of_equiv rho hrho hunitary htau m.2
        (⟨x, hx⟩ : tau.toSubmodule)
      have hasModuleEquiv : rho.toRepresentation.asModuleEquiv x = (x : V) := (rfl)
      rw [hasModuleEquiv]
      exact happly
    · simp
    · intro x y hx hy
      simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy
  have h := hfix (rho.toRepresentation.asModuleEquiv.symm v) hv
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- The character isotypic projector is idempotent. -/
theorem isotypicProjector_idempotent (hunitary : IsUnitary rho)
    (sigma : Subrepresentation rho.toRepresentation) (hsigma : IsAtom sigma) :
    (isotypicProjector rho hrho sigma).comp (isotypicProjector rho hrho sigma) =
      isotypicProjector rho hrho sigma := by
  ext v
  change isotypicProjector rho hrho sigma (isotypicProjector rho hrho sigma v) =
    isotypicProjector rho hrho sigma v
  apply isotypicProjector_apply_of_mem_isotypicComponent rho hrho hunitary sigma hsigma
  let P := (isotypicProjector rho hrho sigma).toIntertwiningMap
  let p : Module.End k[G] rho.toRepresentation.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ P
  have hrange : rho.toRepresentation.asModuleEquiv.symm
      (isotypicProjector rho hrho sigma v) ∈
      (isotypicProjector rho hrho sigma).toIntertwiningMap.range.asSubmodule := by
    change _ ∈ LinearMap.range p
    refine ⟨rho.toRepresentation.asModuleEquiv.symm v, ?_⟩
    apply rho.toRepresentation.asModuleEquiv.injective
    change isotypicProjector rho hrho sigma v = isotypicProjector rho hrho sigma v
    rfl
  rwa [range_isotypicProjector rho hrho hunitary sigma hsigma] at hrange

end IsotypicProjection

end ContRepresentation
