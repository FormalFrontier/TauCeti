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
import TauCeti.RepresentationTheory.Compact.UnitaryModel
import TauCeti.RepresentationTheory.Irreducible

/-!
# Isotypic projections for compact-group representations

Let `sigma` be a finite-dimensional continuous representation of a compact group. The continuous
class function

`dim(sigma) · conj(character sigma)`

acts by integration on every finite-dimensional continuous representation `rho`. When `sigma` is
irreducible and `rho` is unitary, the character-projection identities show that this action is the
identity on every irreducible subrepresentation of `rho` isomorphic to `sigma` and zero on every
other irreducible subrepresentation of `rho`. Complete reducibility then identifies its range with
Mathlib's `isotypicComponent` of type `sigma`.

## Main definitions

* `ContRepresentation.isotypicKernel`: the normalized conjugate-character kernel of `sigma`.
* `ContRepresentation.isotypicProjector`: its integrated action on `rho`, packaged as a
  continuous self-intertwiner of `rho`.

## Main results

* `ContRepresentation.isotypicKernel_eq_of_equiv`,
  `ContRepresentation.isotypicProjector_eq_of_equiv`: kernel and projector depend on `sigma` only
  through its isomorphism type.
* `ContRepresentation.isotypicProjector_apply_subtype_of_equiv`: the projector is the identity on
  an irreducible subrepresentation of `rho` of the selected isomorphism type.
* `ContRepresentation.isotypicProjector_apply_subtype_of_not_equiv`: it vanishes on an irreducible
  subrepresentation of `rho` of every other isomorphism type.
* `ContRepresentation.range_isotypicProjector`: the range of the projector is precisely Mathlib's
  `isotypicComponent`.
* `ContRepresentation.isotypicProjector_idempotent`: the projector is idempotent.

## Implementation notes

The selected irreducible `sigma` is an arbitrary continuous representation rather than a
subrepresentation of `rho`: the kernel reads only its dimension and its character, and the
vanishing statement concerns irreducibles that need not occur in `rho` at all. Isomorphism type is
the only datum visible in the answer: the range is Mathlib's sum of the simple `k[G]`-submodules of
`rho.toRepresentation.asModule` isomorphic to `sigma.toRepresentation.asModule`.

The bridge from the blockwise character identities to the ambient representation is
`ContRepresentation.comp_integratedOperator`: integration is natural with respect to the inclusion
of an invariant subspace. Complete reducibility is supplied by the invariant orthogonal complement
of a unitary representation.

## References

The isotypic component is Mathlib's `isotypicComponent`. The mathematical development follows
Daniel Bump, *Lie Groups*, second edition, Chapter 2, and T. Bröcker and T. tom Dieck,
*Representations of Compact Lie Groups*, Springer GTM 98 (1985), Chapter II.
-/

public section

open MeasureTheory TauCeti TauCeti.ContRepresentation
open scoped InnerProductSpace MonoidAlgebra

namespace ContRepresentation

section IsotypicProjection

variable {k G V W W' : Type*} [RCLike k] [IsAlgClosed k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace k V] [NormedSpace ℝ V] [SMulCommClass ℝ k V]
  [FiniteDimensional k V]
  [NormedAddCommGroup W] [InnerProductSpace k W] [NormedSpace ℝ W] [SMulCommClass ℝ k W]
  [FiniteDimensional k W]
  [NormedAddCommGroup W'] [InnerProductSpace k W'] [NormedSpace ℝ W'] [SMulCommClass ℝ k W']
  [FiniteDimensional k W']

local instance instCompleteSpaceIsotypicProjection : CompleteSpace V :=
  FiniteDimensional.complete k V

omit [IsAlgClosed k] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ W] [SMulCommClass ℝ k W] in
/-- The normalized conjugate-character kernel `dim(sigma) · conj(character sigma)` of a
finite-dimensional continuous representation `sigma`. When `sigma` is irreducible, integrating this
kernel on a finite-dimensional unitary representation cuts out its isotypic component of type
`sigma`. -/
noncomputable def isotypicKernel (sigma : ContRepresentation k G W) (hsigma : Continuous sigma) :
    C(G, k) :=
  (Module.finrank k W : k) • star (character sigma hsigma)

omit [IsAlgClosed k] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ W] [SMulCommClass ℝ k W] in
/-- The isotypic kernel is constant on conjugacy classes. -/
theorem isotypicKernel_conj (sigma : ContRepresentation k G W) (hsigma : Continuous sigma)
    (g h : G) :
    isotypicKernel sigma hsigma (h * g * h⁻¹) = isotypicKernel sigma hsigma g := by
  simp only [isotypicKernel, ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.star_apply]
  rw [character_conj]

omit [IsAlgClosed k] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ W] [SMulCommClass ℝ k W] [NormedSpace ℝ W'] [SMulCommClass ℝ k W'] in
/-- **Equivalent representations have the same normalized character kernel.** The kernel sees
`sigma` only through its isomorphism type. -/
theorem isotypicKernel_eq_of_equiv {sigma : ContRepresentation k G W} (hsigma : Continuous sigma)
    {tau : ContRepresentation k G W'} (htau : Continuous tau)
    (e : sigma.toRepresentation.Equiv tau.toRepresentation) :
    isotypicKernel sigma hsigma = isotypicKernel tau htau := by
  have hdim : Module.finrank k W = Module.finrank k W' := e.toLinearEquiv.finrank_eq
  ext g
  simp only [isotypicKernel, ContinuousMap.smul_apply, ContinuousMap.star_apply, smul_eq_mul,
    coe_character, hdim]
  rw [Representation.char_iso e]

variable (rho : ContRepresentation k G V) (hrho : Continuous rho)

include hrho

/-- **The character isotypic projector.** This is the action on `rho` of
`dim(sigma) · conj(character sigma)`, packaged as a continuous self-intertwiner. -/
noncomputable def isotypicProjector (sigma : ContRepresentation k G W)
    (hsigma : Continuous sigma) : ContIntertwiningMap rho rho where
  __ := integratedOperator rho hrho (isotypicKernel sigma hsigma)
  isIntertwining' := integratedOperator_comp rho hrho (isotypicKernel_conj sigma hsigma)

omit [IsAlgClosed k] [NormedSpace ℝ W] [SMulCommClass ℝ k W] in
/-- The continuous linear map underlying the isotypic projector is the integrated action of the
normalized conjugate-character kernel. -/
@[simp]
theorem toContinuousLinearMap_isotypicProjector (sigma : ContRepresentation k G W)
    (hsigma : Continuous sigma) :
    (isotypicProjector rho hrho sigma hsigma).toContinuousLinearMap =
      integratedOperator rho hrho (isotypicKernel sigma hsigma) :=
  (rfl)

omit [IsAlgClosed k] [NormedSpace ℝ W] [SMulCommClass ℝ k W] in
/-- The defining integral formula for the isotypic projector. -/
theorem isotypicProjector_apply (sigma : ContRepresentation k G W) (hsigma : Continuous sigma)
    (v : V) :
    isotypicProjector rho hrho sigma hsigma v =
      ∫ g, isotypicKernel sigma hsigma g • rho g v ∂haarProb G :=
  calc
    _ = (isotypicProjector rho hrho sigma hsigma).toContinuousLinearMap v := (rfl)
    _ = integratedOperator rho hrho (isotypicKernel sigma hsigma) v := by
      rw [toContinuousLinearMap_isotypicProjector]
    _ = _ := integratedOperator_apply rho hrho _ v

omit [IsAlgClosed k] [NormedSpace ℝ W] [SMulCommClass ℝ k W] [NormedSpace ℝ W']
  [SMulCommClass ℝ k W'] in
/-- **Equivalent representations have the same isotypic projector.** The projector sees `sigma`
only through its isomorphism type. -/
theorem isotypicProjector_eq_of_equiv {sigma : ContRepresentation k G W}
    (hsigma : Continuous sigma) {tau : ContRepresentation k G W'} (htau : Continuous tau)
    (e : sigma.toRepresentation.Equiv tau.toRepresentation) :
    isotypicProjector rho hrho sigma hsigma = isotypicProjector rho hrho tau htau := by
  ext v
  simp only [toContinuousLinearMap_isotypicProjector, isotypicKernel_eq_of_equiv hsigma htau e]

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

omit [NormedSpace ℝ W] [SMulCommClass ℝ k W] in
/-- **The isotypic projector is the identity on every equivalent irreducible block.** -/
theorem isotypicProjector_apply_subtype_of_equiv (hunitary : IsUnitary rho)
    (sigma : ContRepresentation k G W) (hsigma : Continuous sigma)
    {tau : Subrepresentation rho.toRepresentation} (htau : IsAtom tau)
    (e : Nonempty (tau.asSubmodule ≃ₗ[k[G]] sigma.toRepresentation.asModule))
    (v : tau.toSubmodule) :
    isotypicProjector rho hrho sigma hsigma (v : V) = (v : V) := by
  let hTauInv : ∀ g, ∀ v ∈ tau.toSubmodule, rho g v ∈ tau.toSubmodule :=
    fun g _ hv ↦ tau.apply_mem_toSubmodule g hv
  let rhoTau := subrepresentation rho tau.toSubmodule hTauInv
  let hTau : Continuous rhoTau := continuous_subrepresentation hrho
  let iota : ContIntertwiningMap rhoTau rho := subrepresentationInclusion rho tau
  have hTauRep : rhoTau.toRepresentation = tau.toRepresentation := by
    dsimp only [rhoTau]
    rw [toRepresentation_subrepresentation]
    ext g v
    rfl
  have hirrTau : Representation.IsIrreducible rhoTau.toRepresentation := by
    rw [hTauRep]
    exact TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom htau
  have hunitaryTau : IsUnitary rhoTau :=
    hunitary.subrepresentation tau.apply_mem_toSubmodule
  have phi : rhoTau.toRepresentation.Equiv sigma.toRepresentation := by
    rw [hTauRep]
    exact Representation.equivOfAsModuleLinearEquiv (tau.asModuleEquivAsSubmodule.trans e.some)
  have hkernel : isotypicKernel rhoTau hTau = isotypicKernel sigma hsigma :=
    isotypicKernel_eq_of_equiv hTau hsigma phi
  have hblock : integratedOperator rhoTau hTau (isotypicKernel sigma hsigma) =
      ContinuousLinearMap.id k tau.toSubmodule := by
    rw [← hkernel, isotypicKernel, integratedOperator_smul,
      finrank_smul_integratedOperator_star_character_self rhoTau hTau hunitaryTau hirrTau]
  have hnatural := comp_integratedOperator rhoTau hTau rho hrho iota
    (isotypicKernel sigma hsigma)
  have happly := congrArg (fun T : tau.toSubmodule →L[k] V ↦ T v) hnatural
  have hiota : iota.toContinuousLinearMap v = (v : V) :=
    subrepresentationInclusion_apply rho tau v
  calc
    isotypicProjector rho hrho sigma hsigma (v : V) =
        integratedOperator rho hrho (isotypicKernel sigma hsigma) (v : V) := by
      exact congrArg (fun T : V →L[k] V ↦ T (v : V))
        (toContinuousLinearMap_isotypicProjector rho hrho sigma hsigma)
    _ = integratedOperator rho hrho (isotypicKernel sigma hsigma)
        (iota.toContinuousLinearMap v) := by rw [hiota]
    _ = iota.toContinuousLinearMap
        (integratedOperator rhoTau hTau (isotypicKernel sigma hsigma) v) := by
      simpa only [ContinuousLinearMap.comp_apply] using happly.symm
    _ = (v : V) := by rw [hblock, ContinuousLinearMap.id_apply, hiota]

private theorem isotypicProjector_apply_subtype_of_not_equiv_of_isUnitary
    (sigma : ContRepresentation k G W) (hsigma : Continuous sigma) (hunitary : IsUnitary sigma)
    (hirr : Representation.IsIrreducible sigma.toRepresentation)
    {tau : Subrepresentation rho.toRepresentation} (htau : IsAtom tau)
    (hne : IsEmpty (tau.asSubmodule ≃ₗ[k[G]] sigma.toRepresentation.asModule))
    (v : tau.toSubmodule) :
    isotypicProjector rho hrho sigma hsigma (v : V) = 0 := by
  let hTauInv : ∀ g, ∀ v ∈ tau.toSubmodule, rho g v ∈ tau.toSubmodule :=
    fun g _ hv ↦ tau.apply_mem_toSubmodule g hv
  let rhoTau := subrepresentation rho tau.toSubmodule hTauInv
  let hTau : Continuous rhoTau := continuous_subrepresentation hrho
  let iota : ContIntertwiningMap rhoTau rho := subrepresentationInclusion rho tau
  have hTauRep : rhoTau.toRepresentation = tau.toRepresentation := by
    dsimp only [rhoTau]
    rw [toRepresentation_subrepresentation]
    ext g v
    rfl
  have hirrTau : Representation.IsIrreducible rhoTau.toRepresentation := by
    rw [hTauRep]
    exact TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom htau
  let hempty : IsEmpty (_root_.ContRepresentation.Equiv rhoTau sigma) :=
    ⟨fun phi ↦ by
      have phi' : tau.toRepresentation.Equiv sigma.toRepresentation := by
        have phi' := (ContRepresentation.nonempty_equiv_iff.mp ⟨phi⟩).some
        rw [hTauRep] at phi'
        exact phi'
      exact hne.false (tau.asModuleEquivAsSubmodule.symm.trans
        (Representation.asModuleLinearEquivOfEquiv phi'))⟩
  have hzero : integratedOperator rhoTau hTau (star (character sigma hsigma)) = 0 :=
    integratedOperator_star_character_eq_zero sigma hsigma rhoTau hTau hunitary hirrTau
      fun phi ↦ by
        simpa using congrArg ContIntertwiningMap.toContinuousLinearMap
          (eq_zero_of_isEmpty_equiv hirrTau hirr hempty phi)
  have hblock : integratedOperator rhoTau hTau (isotypicKernel sigma hsigma) = 0 := by
    rw [isotypicKernel, integratedOperator_smul, hzero, smul_zero]
  have hnatural := comp_integratedOperator rhoTau hTau rho hrho iota
    (isotypicKernel sigma hsigma)
  have happly := congrArg (fun T : tau.toSubmodule →L[k] V ↦ T v) hnatural
  have hiota : iota.toContinuousLinearMap v = (v : V) :=
    subrepresentationInclusion_apply rho tau v
  calc
    isotypicProjector rho hrho sigma hsigma (v : V) =
        integratedOperator rho hrho (isotypicKernel sigma hsigma) (v : V) := by
      exact congrArg (fun T : V →L[k] V ↦ T (v : V))
        (toContinuousLinearMap_isotypicProjector rho hrho sigma hsigma)
    _ = integratedOperator rho hrho (isotypicKernel sigma hsigma)
        (iota.toContinuousLinearMap v) := by rw [hiota]
    _ = iota.toContinuousLinearMap
        (integratedOperator rhoTau hTau (isotypicKernel sigma hsigma) v) := by
      simpa only [ContinuousLinearMap.comp_apply] using happly.symm
    _ = 0 := by rw [hblock, zero_apply, map_zero]

/-- **The isotypic projector vanishes on every inequivalent irreducible block.** -/
theorem isotypicProjector_apply_subtype_of_not_equiv
    (sigma : ContRepresentation k G W) (hsigma : Continuous sigma)
    (hirr : Representation.IsIrreducible sigma.toRepresentation)
    {tau : Subrepresentation rho.toRepresentation} (htau : IsAtom tau)
    (hne : IsEmpty (tau.asSubmodule ≃ₗ[k[G]] sigma.toRepresentation.asModule))
    (v : tau.toSubmodule) :
    isotypicProjector rho hrho sigma hsigma (v : V) = 0 := by
  obtain ⟨e, hunitary⟩ := TauCeti.ContRepresentation.exists_isUnitary_congr sigma hsigma
  let sigma' := TauCeti.ContRepresentation.congr e sigma
  let hsigma' : Continuous sigma' := TauCeti.ContRepresentation.continuous_congr e hsigma
  have hirr' : Representation.IsIrreducible sigma'.toRepresentation :=
    TauCeti.ContRepresentation.isIrreducible_congr e hirr
  have hequiv : sigma.toRepresentation.Equiv sigma'.toRepresentation :=
    (ContRepresentation.nonempty_equiv_iff.mp
      ⟨_root_.ContRepresentation.congrEquiv sigma e⟩).some
  let hne' : IsEmpty (tau.asSubmodule ≃ₗ[k[G]] sigma'.toRepresentation.asModule) :=
    ⟨fun f ↦ hne.false
      (f.trans (Representation.asModuleLinearEquivOfEquiv hequiv).symm)⟩
  rw [isotypicProjector_eq_of_equiv rho hrho hsigma hsigma' hequiv]
  exact isotypicProjector_apply_subtype_of_not_equiv_of_isUnitary rho hrho sigma' hsigma'
    hunitary hirr' htau hne' v

/-- **The character projector cuts out the isotypic component.** Its range is exactly Mathlib's
sum of the simple `k[G]`-submodules isomorphic to the selected irreducible. -/
theorem range_isotypicProjector (hunitary : IsUnitary rho)
    (sigma : ContRepresentation k G W) (hsigma : Continuous sigma)
    (hirr : Representation.IsIrreducible sigma.toRepresentation) :
    (isotypicProjector rho hrho sigma hsigma).toIntertwiningMap.range.asSubmodule =
      isotypicComponent k[G] rho.toRepresentation.asModule sigma.toRepresentation.asModule := by
  classical
  let P := (isotypicProjector rho hrho sigma hsigma).toIntertwiningMap
  let p : Module.End k[G] rho.toRepresentation.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ P
  let C := isotypicComponent k[G] rho.toRepresentation.asModule sigma.toRepresentation.asModule
  let _ : IsSimpleModule k[G] sigma.toRepresentation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr
  have hsemisimple : IsSemisimpleModule k[G] rho.toRepresentation.asModule :=
    hunitary.isSemisimpleModule_asModule
  let _ := hsemisimple
  have hp_apply (x : rho.toRepresentation.asModule) :
      rho.toRepresentation.asModuleEquiv (p x) =
        P (rho.toRepresentation.asModuleEquiv x) := (rfl)
  have hP_apply (x : V) : P x = isotypicProjector rho hrho sigma hsigma x := (rfl)
  have hasModuleEquiv_apply (x : rho.toRepresentation.asModule) :
      rho.toRepresentation.asModuleEquiv x = (x : V) := (rfl)
  have hmaps : ∀ m : Submodule k[G] rho.toRepresentation.asModule,
      IsSimpleModule k[G] m → m ≤ C.comap p := by
    intro m hm x hx
    rw [Submodule.mem_comap]
    let tau : Subrepresentation rho.toRepresentation := Subrepresentation.ofSubmodule' m
    have htau : IsAtom tau := Subrepresentation.isSimpleModule_asSubmodule_iff.mp hm
    by_cases he : Nonempty (m ≃ₗ[k[G]] sigma.toRepresentation.asModule)
    · have happly := isotypicProjector_apply_subtype_of_equiv rho hrho hunitary sigma hsigma htau
        he (⟨x, hx⟩ : tau.toSubmodule)
      have hmC : m ≤ C := le_sSup he
      have hxC : x ∈ C := hmC hx
      have hP : P (rho.toRepresentation.asModuleEquiv x) =
          rho.toRepresentation.asModuleEquiv x := by
        rw [hP_apply, hasModuleEquiv_apply]
        exact happly
      have hpx : p x = x := by
        apply rho.toRepresentation.asModuleEquiv.injective
        rw [hp_apply, hP]
      rw [hpx]
      exact hxC
    · let hne : IsEmpty (m ≃ₗ[k[G]] sigma.toRepresentation.asModule) := ⟨fun e ↦ he ⟨e⟩⟩
      have happly := isotypicProjector_apply_subtype_of_not_equiv rho hrho sigma hsigma
        hirr htau hne (⟨x, hx⟩ : tau.toSubmodule)
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
    have happly := isotypicProjector_apply_subtype_of_equiv rho hrho hunitary sigma hsigma htau he
      (⟨x, hx⟩ : tau.toSubmodule)
    exact ⟨x, happly⟩

omit [NormedSpace ℝ W] [SMulCommClass ℝ k W] in
/-- The isotypic projector fixes every vector in the selected isotypic component. -/
theorem isotypicProjector_apply_of_mem_isotypicComponent (hunitary : IsUnitary rho)
    (sigma : ContRepresentation k G W) (hsigma : Continuous sigma)
    (hirr : Representation.IsIrreducible sigma.toRepresentation) (v : V)
    (hv : rho.toRepresentation.asModuleEquiv.symm v ∈
      isotypicComponent k[G] rho.toRepresentation.asModule sigma.toRepresentation.asModule) :
    isotypicProjector rho hrho sigma hsigma v = v := by
  classical
  let _ : IsSimpleModule k[G] sigma.toRepresentation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr
  have hfix : ∀ x : rho.toRepresentation.asModule,
      x ∈ isotypicComponent k[G] rho.toRepresentation.asModule sigma.toRepresentation.asModule →
        isotypicProjector rho hrho sigma hsigma (rho.toRepresentation.asModuleEquiv x) =
          rho.toRepresentation.asModuleEquiv x := by
    intro x hx
    rw [isotypicComponent, sSup_eq_iSup'] at hx
    refine Submodule.iSup_induction
      (motive := fun x ↦ isotypicProjector rho hrho sigma hsigma
        (rho.toRepresentation.asModuleEquiv x) = rho.toRepresentation.asModuleEquiv x)
      (fun m : {m : Submodule k[G] rho.toRepresentation.asModule |
        Nonempty (m ≃ₗ[k[G]] sigma.toRepresentation.asModule)} ↦ m.1) hx ?_ ?_ ?_
    · intro m x hx
      let tau : Subrepresentation rho.toRepresentation := Subrepresentation.ofSubmodule' m.1
      have htau : IsAtom tau := Subrepresentation.isSimpleModule_asSubmodule_iff.mp
        (IsSimpleModule.congr m.2.some)
      have happly := isotypicProjector_apply_subtype_of_equiv rho hrho hunitary sigma hsigma htau
        m.2 (⟨x, hx⟩ : tau.toSubmodule)
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
    (sigma : ContRepresentation k G W) (hsigma : Continuous sigma)
    (hirr : Representation.IsIrreducible sigma.toRepresentation) :
    (isotypicProjector rho hrho sigma hsigma).comp (isotypicProjector rho hrho sigma hsigma) =
      isotypicProjector rho hrho sigma hsigma := by
  ext v
  simp only [ContIntertwiningMap.toContinuousLinearMap_comp, ContinuousLinearMap.comp_apply,
    ContIntertwiningMap.toContinuousLinearMap_apply]
  apply isotypicProjector_apply_of_mem_isotypicComponent rho hrho hunitary sigma hsigma hirr
  have hmem : isotypicProjector rho hrho sigma hsigma v ∈
      (isotypicProjector rho hrho sigma hsigma).toIntertwiningMap.range :=
    (Representation.IntertwiningMap.mem_range _ _ _ _).mpr ⟨v, rfl⟩
  have hrange : rho.toRepresentation.asModuleEquiv.symm
      (isotypicProjector rho hrho sigma hsigma v) ∈
      (isotypicProjector rho hrho sigma hsigma).toIntertwiningMap.range.asSubmodule :=
    (Subrepresentation.mem_asSubmodule_iff
      (σ := (isotypicProjector rho hrho sigma hsigma).toIntertwiningMap.range)).mpr hmem
  rwa [range_isotypicProjector rho hrho hunitary sigma hsigma hirr] at hrange

end IsotypicProjection

end ContRepresentation
