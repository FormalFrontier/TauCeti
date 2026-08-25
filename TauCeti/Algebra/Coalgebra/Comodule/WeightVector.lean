/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# Weight vectors of a comodule

A **weight vector** of a comodule `M` over a coalgebra `C` is a vector `v` whose coaction is
`v ↦ v ⊗ c` for a single element `c` of `C`; equivalently, the line it spans is a subcomodule.
When `C` is the coordinate Hopf algebra of an affine group, this says that every point of the
group scales `v`, by the value it takes on `c`.

The weight of a nonzero weight vector is automatically group-like: the counit law forces
`ε c = 1` and coassociativity forces `Δ c = c ⊗ c`, because a nonzero vector of a vector space is
detected by a linear functional. So a one-dimensional subcomodule of a comodule over a field is
specified by a group-like element. When `C` is the coordinate Hopf algebra of an affine group,
that group-like element is a character, so there is no need to carry group-likeness as a
hypothesis.

Weight vectors are the eigenvector form of the fixed vectors of
`TauCeti.Algebra.Coalgebra.Comodule.Fixed`: a fixed vector is a weight vector of weight `1`. They
are what the Lie--Kolchin argument produces for a connected solvable group, where fixed vectors
are unavailable, and the flag induction of
`TauCeti.Algebra.Coalgebra.Comodule.Flag.Triangular` turns them into a complete invariant flag.

## Main declarations

* `TauCeti.Comodule.HasNonzeroWeightVector`: a comodule contains a nonzero weight vector.
* `TauCeti.Comodule.isGroupLikeElem_of_coact_eq_tmul`: the weight of a nonzero weight vector is
  group-like.
* `TauCeti.Comodule.eq_of_coact_eq_tmul`: the weight of a nonzero weight vector is unique.
* `TauCeti.Comodule.exists_isGroupLikeElem_coact_eq_tmul_of_toSubmodule_eq_span`: a subcomodule
  spanned by a single nonzero vector exhibits it as a weight vector.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §§2.4 and 6.3.

This is a Layer 5 ingredient of the ReductiveGroups roadmap, for the "Lie--Kolchin; solvable
groups" milestone.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

noncomputable section

variable {k : Type u} {C : Type v} {M : Type w}
variable [Field k] [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]

/-- A comodule has a nonzero weight vector if some nonzero `v` has coaction `v ⊗ c` for a
group-like `c`.

When `C` is the coordinate Hopf algebra of an affine group, this says that the group acts on the
line spanned by `v` through the character corresponding to `c`. -/
def HasNonzeroWeightVector (k : Type u) (C : Type v) (M : Type w)
    [Field k] [AddCommMonoid C] [Module k C] [Coalgebra k C]
    [AddCommGroup M] [Module k M] [Comodule k C M] : Prop :=
  ∃ (v : M) (c : C), v ≠ 0 ∧ IsGroupLikeElem k c ∧
    coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] c

/-- The defining characterization of a nonzero weight vector. -/
@[simp]
theorem hasNonzeroWeightVector_iff :
    HasNonzeroWeightVector k C M ↔
      ∃ (v : M) (c : C), v ≠ 0 ∧ IsGroupLikeElem k c ∧
        coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] c :=
  Iff.rfl

/-- The weight of a nonzero weight vector is a group-like element. -/
theorem isGroupLikeElem_of_coact_eq_tmul {v : M} (hv : v ≠ 0) {c : C}
    (h : coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] c) :
    IsGroupLikeElem k c := by
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_eq_one k hv
  constructor
  · have hcounit := lTensor_counit_coact (R := k) (C := C) v
    rw [h] at hcounit
    have := congrArg (TensorProduct.rid k M) hcounit
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, one_smul] at this
    -- `this : Coalgebra.counit c • v = v`; test it against a functional taking `v` to `1`.
    have hphi' := congrArg phi this
    simpa [hphi] using hphi'
  · have hassoc := coassoc_apply (R := k) (C := C) v
    rw [h] at hassoc
    simp only [LinearMap.rTensor_tmul, h, TensorProduct.assoc_tmul,
      LinearMap.lTensor_tmul] at hassoc
    have hphi' := congrArg
      (fun z ↦ TensorProduct.lid k (C ⊗[k] C)
        (TensorProduct.map phi (LinearMap.id : C ⊗[k] C →ₗ[k] C ⊗[k] C) z)) hassoc
    simpa [hphi] using hphi'.symm

/-- The weight of a nonzero weight vector is unique. -/
theorem eq_of_coact_eq_tmul {v : M} (hv : v ≠ 0) {c d : C}
    (hc : coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] c)
    (hd : coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] d) : c = d := by
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_eq_one k hv
  have h := hc.symm.trans hd
  have hphi' := congrArg
    (fun z ↦ TensorProduct.lid k C
      (TensorProduct.map phi (LinearMap.id : C →ₗ[k] C) z)) h
  simpa [hphi] using hphi'

/-- Every vector of a line spanned by a weight vector is a weight vector of the same weight. -/
theorem coact_eq_tmul_of_mem_span {v : M} {c : C}
    (h : coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] c) {x : M} (hx : x ∈ k ∙ v) :
    coact (R := k) (C := C) (M := M) x = x ⊗ₜ[k] c := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, h, TensorProduct.smul_tmul']

/-- A vector whose coaction lies in the tensor product of the line it spans with the coalgebra is
a weight vector, and its weight is group-like. -/
theorem exists_isGroupLikeElem_coact_eq_tmul_of_mem_range {v : M} (hv : v ≠ 0)
    (h : coact (R := k) (C := C) (M := M) v ∈
      LinearMap.range (TensorProduct.map (k ∙ v).subtype (LinearMap.id : C →ₗ[k] C))) :
    ∃ c : C, IsGroupLikeElem k c ∧ coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] c := by
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_eq_one k hv
  obtain ⟨z, hz⟩ := h
  set contract : (↥(k ∙ v)) ⊗[k] C →ₗ[k] C :=
    (TensorProduct.lid k C).toLinearMap ∘ₗ
      TensorProduct.map (phi ∘ₗ (k ∙ v).subtype) (LinearMap.id : C →ₗ[k] C) with hcontract
  have key : ∀ w : (↥(k ∙ v)) ⊗[k] C,
      TensorProduct.map (k ∙ v).subtype (LinearMap.id : C →ₗ[k] C) w = v ⊗ₜ[k] contract w := by
    intro w
    induction w with
    | zero => simp
    | tmul x c =>
        have hx : (x : M) = phi (x : M) • v := by
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.2
          rw [← ha]
          simp [hphi]
        simp only [hcontract, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
          LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
          LinearEquiv.coe_coe, TensorProduct.lid_tmul]
        conv_lhs => rw [hx]
        exact TensorProduct.smul_tmul _ _ _
    | add x y hx hy => simp [hx, hy, TensorProduct.tmul_add]
  refine ⟨contract z, ?_, ?_⟩
  · exact isGroupLikeElem_of_coact_eq_tmul hv (hz ▸ key z)
  · exact hz ▸ key z

/-- A subcomodule spanned by a single nonzero vector exhibits that vector as a weight vector. -/
theorem exists_isGroupLikeElem_coact_eq_tmul_of_toSubmodule_eq_span
    (N : Subcomodule k C M) {v : M} (hv : v ≠ 0) (hN : N.toSubmodule = k ∙ v) :
    ∃ c : C, IsGroupLikeElem k c ∧ coact (R := k) (C := C) (M := M) v = v ⊗ₜ[k] c := by
  refine exists_isGroupLikeElem_coact_eq_tmul_of_mem_range hv ?_
  have hmem : v ∈ N := by
    rw [← Subcomodule.mem_toSubmodule, hN]
    exact Submodule.mem_span_singleton_self v
  have := N.coact_mem hmem
  rwa [← N.toSubmodule_carrier, hN] at this

/-- A subcomodule spanned by a single nonzero vector makes the ambient comodule have a nonzero
weight vector. -/
theorem hasNonzeroWeightVector_of_toSubmodule_eq_span
    (N : Subcomodule k C M) {v : M} (hv : v ≠ 0) (hN : N.toSubmodule = k ∙ v) :
    HasNonzeroWeightVector k C M := by
  obtain ⟨c, hc, hcoact⟩ :=
    exists_isGroupLikeElem_coact_eq_tmul_of_toSubmodule_eq_span N hv hN
  exact ⟨v, c, hv, hc, hcoact⟩

end

end TauCeti.Comodule
