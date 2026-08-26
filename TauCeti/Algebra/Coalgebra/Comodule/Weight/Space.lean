/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Vector
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

/-!
# Weight spaces of a comodule

Let `M` be a comodule over a coalgebra `C` over a field `k`. For a group-like element `c` of
`C`, its weight space is the subspace of vectors whose coaction is `m ↦ m ⊗ c`. This file
packages that subspace and proves that the weight spaces belonging to distinct group-like
elements are independent. Consequently a finite-dimensional comodule has only finitely many
nonzero weight spaces.

The independence proof reads a coaction through all linear functionals on `C`. The `c`-weight
space is the joint eigenspace of the component endomorphisms
`Comodule.coactComponent φ`, with eigenvalue function `φ ↦ φ c`. Linear functionals separate
points over a field, so distinct group-like elements give distinct joint eigenvalue functions.

Unlike the weight decomposition for a monoid algebra, these weight spaces need not span an
arbitrary comodule. The results here provide exactly the finite family permuted in the
Lie--Kolchin induction: after restricting a representation to the derived subgroup, its nonzero
weight spaces form the finite set that the next step must show is permuted by the ambient group.

## Main declarations

* `TauCeti.Comodule.groupLikeWeightSpace`: the weight space belonging to a group-like element.
* `TauCeti.Comodule.iSupIndep_groupLikeWeightSpace`: distinct group-like weight spaces are
  independent.
* `TauCeti.Comodule.finite_setOf_groupLikeWeightSpace_ne_bot`: a finite-dimensional comodule has
  only finitely many nonzero group-like weight spaces.
* `TauCeti.Comodule.natCard_nonzeroGroupLikeWeights_le_finrank`: the number of nonzero weight
  spaces is at most the dimension of the comodule.
* `TauCeti.Comodule.hasNonzeroWeightVector_iff_exists_groupLikeWeightSpace_ne_bot`: nonzero weight
  vectors are exactly nontrivial group-like weight spaces.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Theorem 6.3.1.

This supplies the finite weight-space package needed by Layer 5, "Lie--Kolchin; solvable groups",
of the ReductiveGroups roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

noncomputable section

section Semiring

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- The weight space of a group-like element `c` consists of the vectors with coaction
`m ↦ m ⊗ c`. -/
def groupLikeWeightSpace (c : GroupLike R C) : Submodule R M where
  carrier := {m | coact (R := R) (C := C) m = m ⊗ₜ[R] c.val}
  zero_mem' := by simp
  add_mem' {m n} hm hn := by
    simp only [Set.mem_ofPred_eq] at hm hn ⊢
    rw [map_add, hm, hn, TensorProduct.add_tmul]
  smul_mem' r m hm := by
    simp only [Set.mem_ofPred_eq] at hm ⊢
    rw [map_smul, hm, TensorProduct.smul_tmul']

/-- Membership in a group-like weight space is the corresponding coaction equation. -/
@[simp]
theorem mem_groupLikeWeightSpace {c : GroupLike R C} {m : M} :
    m ∈ groupLikeWeightSpace (M := M) c ↔
      coact (R := R) (C := C) m = m ⊗ₜ[R] c.val :=
  Iff.rfl

/-- A comodule morphism preserves every group-like weight space. -/
theorem Hom.map_mem_groupLikeWeightSpace (f : Hom R C M N) {c : GroupLike R C} {m : M}
    (hm : m ∈ groupLikeWeightSpace (M := M) c) :
    f m ∈ groupLikeWeightSpace (M := N) c := by
  rw [mem_groupLikeWeightSpace] at hm ⊢
  rw [← f.map_coact_apply, hm, TensorProduct.map_tmul]
  rfl

/-- A comodule morphism maps each group-like weight space into the same weight space. -/
theorem Hom.map_groupLikeWeightSpace_le (f : Hom R C M N) (c : GroupLike R C) :
    (groupLikeWeightSpace (M := M) c).map f.toLinearMap ≤
      groupLikeWeightSpace (M := N) c := by
  rintro _ ⟨m, hm, rfl⟩
  exact f.map_mem_groupLikeWeightSpace hm

/-- A comodule has a nonzero weight vector exactly when one of its group-like weight spaces is
nonzero. -/
theorem hasNonzeroWeightVector_iff_exists_groupLikeWeightSpace_ne_bot :
    HasNonzeroWeightVector R C M ↔
      ∃ c : GroupLike R C, groupLikeWeightSpace (M := M) c ≠ ⊥ := by
  rw [hasNonzeroWeightVector_iff]
  constructor
  · rintro ⟨m, c, hm, hc, hcoact⟩
    refine ⟨⟨c, hc⟩, ?_⟩
    exact (groupLikeWeightSpace (M := M) ⟨c, hc⟩).ne_bot_iff.mpr
      ⟨m, mem_groupLikeWeightSpace.mpr hcoact, hm⟩
  · rintro ⟨c, hc⟩
    obtain ⟨m, hm, hm0⟩ := (groupLikeWeightSpace (M := M) c).ne_bot_iff.mp hc
    exact ⟨m, c.val, hm0, c.isGroupLikeElem_val, mem_groupLikeWeightSpace.mp hm⟩

end Semiring

variable {k : Type u} {C : Type v} {M : Type w}
variable [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]

omit [Coalgebra k C] [Comodule k C M] in
/-- Equality of all contractions against the coalgebra factor detects equality in a tensor
product over a field. -/
private theorem tensor_eq_of_forall_tensorComponent_eq {x y : M ⊗[k] C}
    (h : ∀ φ : Module.Dual k C,
      tensorComponent (R := k) (M := M) φ x = tensorComponent (R := k) (M := M) φ y) :
    x = y := by
  classical
  let b := Module.Free.chooseBasis k C
  apply (TensorProduct.equivFinsuppOfBasisRight b (M := M)).injective
  ext i
  rw [equivFinsuppOfBasisRight_apply, equivFinsuppOfBasisRight_apply]
  exact h (b.coord i)

/-- A vector has weight `c` exactly when every component of its coaction has eigenvalue obtained
by evaluating the component functional at `c`. -/
theorem mem_groupLikeWeightSpace_iff_forall_coactComponent_eq_smul
    {c : GroupLike k C} {m : M} :
    m ∈ groupLikeWeightSpace (M := M) c ↔
      ∀ φ : Module.Dual k C,
        coactComponent (R := k) (C := C) (M := M) φ m = φ c.val • m := by
  constructor
  · intro hm φ
    rw [coactComponent_apply, mem_groupLikeWeightSpace.mp hm, tensorComponent_tmul]
  · intro hm
    rw [mem_groupLikeWeightSpace]
    apply tensor_eq_of_forall_tensorComponent_eq
    intro φ
    rw [← coactComponent_apply, hm φ, tensorComponent_tmul]

/-- A group-like weight space is the joint eigenspace of all components of the coaction. -/
theorem groupLikeWeightSpace_eq_iInf_eigenspace (c : GroupLike k C) :
    groupLikeWeightSpace (M := M) c =
      ⨅ φ : Module.Dual k C,
        Module.End.eigenspace (coactComponent (R := k) (C := C) (M := M) φ) (φ c.val) := by
  ext m
  rw [mem_groupLikeWeightSpace_iff_forall_coactComponent_eq_smul]
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- Distinct group-like elements give distinct eigenvalue functions on the linear dual. -/
private theorem injective_groupLike_eigenvalue :
    Function.Injective (fun c : GroupLike k C ↦ fun φ : Module.Dual k C ↦ φ c.val) := by
  intro c d h
  apply GroupLike.val_injective
  apply Module.eval_apply_injective k
  ext φ
  exact congrFun h φ

/-- The group-like weight spaces of a comodule over a field are supremum-independent. -/
theorem iSupIndep_groupLikeWeightSpace :
    iSupIndep (groupLikeWeightSpace (M := M) : GroupLike k C → Submodule k M) := by
  have h := iSupIndep_iInf_eigenspace
    (fun φ : Module.Dual k C ↦
      (coactComponent (R := k) (C := C) (M := M) φ : Module.End k M))
  have hc := h.comp injective_groupLike_eigenvalue
  have hfamily :
      ((fun χ : Module.Dual k C → k ↦
        ⨅ φ : Module.Dual k C,
          Module.End.eigenspace (coactComponent (R := k) (C := C) (M := M) φ) (χ φ)) ∘
          fun c : GroupLike k C ↦ fun φ : Module.Dual k C ↦ φ c.val) =
        (groupLikeWeightSpace (M := M) : GroupLike k C → Submodule k M) := by
    funext c
    exact (groupLikeWeightSpace_eq_iInf_eigenspace c).symm
  rw [hfamily] at hc
  exact hc

/-- Weight spaces belonging to distinct group-like elements are disjoint. -/
theorem disjoint_groupLikeWeightSpace {c d : GroupLike k C} (hcd : c ≠ d) :
    Disjoint (groupLikeWeightSpace (M := M) c) (groupLikeWeightSpace (M := M) d) :=
  iSupIndep_groupLikeWeightSpace.pairwiseDisjoint hcd

/-- A finite-dimensional comodule has only finitely many nonzero group-like weight spaces. -/
theorem finite_setOf_groupLikeWeightSpace_ne_bot [FiniteDimensional k M] :
    {c : GroupLike k C | groupLikeWeightSpace (M := M) c ≠ ⊥}.Finite :=
  Submodule.finite_ne_bot_of_iSupIndep iSupIndep_groupLikeWeightSpace

/-- The number of nonzero group-like weight spaces of a finite-dimensional comodule is at most
the dimension of the comodule. -/
theorem natCard_nonzeroGroupLikeWeights_le_finrank [FiniteDimensional k M] :
    Nat.card {c : GroupLike k C // groupLikeWeightSpace (M := M) c ≠ ⊥} ≤
      Module.finrank k M := by
  let _ : Fintype {c : GroupLike k C // groupLikeWeightSpace (M := M) c ≠ ⊥} :=
    iSupIndep.fintypeNeBotOfFiniteDimensional (R := k) (M := M)
      iSupIndep_groupLikeWeightSpace
  rw [Nat.card_eq_fintype_card]
  exact iSupIndep.subtype_ne_bot_le_finrank (R := k) (M := M)
    iSupIndep_groupLikeWeightSpace

end

end TauCeti.Comodule
