/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
public import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Subcomodule.Transport
import TauCeti.Algebra.Coalgebra.Subcomodule.Comap

/-!
# Complete reducibility and linear reductivity

An affine group over a field is linearly reductive when every finite-dimensional rational
representation is completely reducible. On coordinate rings, rational representations are
comodules, and complete reducibility says that every subcomodule has a subcomodule complement.

This file introduces that intrinsic comodule formulation, proves that complete reducibility is
invariant under corestriction along a coalgebra equivalence, and proves linear reductivity for
every monoid-algebra coalgebra `k[G]`. The last proof makes an arbitrary linear projection onto a
subcomodule equivariant: decompose a vector into its weights, apply the projection separately on
each weight, and project the result back to that weight. The resulting idempotent comodule
endomorphism has the original subcomodule as its range, so its kernel is an invariant complement.

For an abelian group `G`, `k[G]` is the coordinate Hopf algebra of the diagonalizable group
`D(G)`. Thus every diagonalizable group, and in particular every split torus, is linearly
reductive over an arbitrary field. This is the diagonalizable direction of the linear-reductivity
milestone in Layer 6 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.Comodule.IsCompletelyReducible`: every subcomodule has a subcomodule complement.
* `TauCeti.Comodule.isCompletelyReducible_of_orderIso`: transfer complete reducibility across
  compatible order isomorphisms of subcomodules and underlying submodules.
* `TauCeti.Comodule.isCompletelyReducible_transport_iff`: complete reducibility is invariant
  under transport along a linear equivalence.
* `TauCeti.Coalgebra.IsLinearlyReductive`: every finite-dimensional comodule is completely
  reducible.
* `TauCeti.Coalgebra.IsLinearlyReductive.isCompletelyReducible`: testing finite-dimensional
  comodules in the base-field universe suffices for comodules in every universe.
* `TauCeti.Comodule.isCompletelyReducible_corestrict_iff_of_coalgEquiv`: complete reducibility
  is invariant under a coalgebra equivalence.
* `TauCeti.Coalgebra.isLinearlyReductive_iff_of_coalgEquiv`: linear reductivity is invariant
  under a coalgebra equivalence.
* `TauCeti.Coalgebra.isLinearlyReductive_monoidAlgebra`: monoid-algebra coalgebras are linearly
  reductive over a field.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.2.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace Comodule

variable (k : Type u) (C : Type v) (V : Type w)
variable [CommSemiring k]
variable [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommMonoid V] [Module k V] [Comodule k C V]

/-- A comodule is completely reducible when each subcomodule has a complementary subcomodule.

The complement is taken in the lattice of underlying submodules, so the statement says
both that the two subcomodules intersect trivially and that together they span the whole
comodule. -/
def IsCompletelyReducible : Prop :=
  ∀ W : Subcomodule k C V, ∃ Q : Subcomodule k C V,
    IsCompl W.toSubmodule Q.toSubmodule

end Comodule

namespace Coalgebra

variable (k : Type u) (C : Type v)
variable [Field k]
variable [AddCommMonoid C] [Module k C] [Coalgebra k C]

/-- A coalgebra is linearly reductive in carrier universe `w` when every finite-dimensional
comodule over it whose carrier lies in `Type w` is completely reducible. For a commutative Hopf
algebra representing an affine group, this is the usual complete-reducibility definition of a
linearly reductive group at that universe. -/
def IsLinearlyReductive : Prop :=
  ∀ (V : Type w) [AddCommMonoid V] [Module k V] [Comodule k C V] [Module.Finite k V],
    Comodule.IsCompletelyReducible k C V

end Coalgebra

namespace Comodule

section OrderIso

variable (k : Type u) [CommSemiring k]
variable {C : Type v} {D : Type*} {V : Type w} {W : Type*}
variable [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommMonoid D] [Module k D] [Coalgebra k D]
variable [AddCommMonoid V] [Module k V] [Comodule k C V]
variable [AddCommMonoid W] [Module k W] [Comodule k D W]

/-- Complete reducibility transfers across compatible order isomorphisms of subcomodules and
their underlying submodules. -/
theorem isCompletelyReducible_of_orderIso
    (Φ : Subcomodule k C V ≃o Subcomodule k D W)
    (E : Submodule k V ≃o Submodule k W)
    (hΦ : ∀ A, (Φ A).toSubmodule = E A.toSubmodule)
    (h : IsCompletelyReducible k C V) : IsCompletelyReducible k D W := by
  intro A
  obtain ⟨Q, hQ⟩ := h (Φ.symm A)
  refine ⟨Φ Q, ?_⟩
  have hQ' := E.isCompl_iff.mp hQ
  rw [← hΦ (Φ.symm A), ← hΦ Q, Φ.apply_symm_apply] at hQ'
  exact hQ'

end OrderIso

section Transport

variable (k : Type u) [CommSemiring k]
variable {C : Type v} [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable {V : Type w} {W : Type*}
variable [AddCommMonoid V] [Module k V] [Comodule k C V]
variable [AddCommMonoid W] [Module k W]

/-- Complete reducibility is invariant under transporting a comodule structure along a linear
equivalence. -/
theorem isCompletelyReducible_transport_iff (e : V ≃ₗ[k] W) :
    (letI : Comodule k C W := Transport e;
      IsCompletelyReducible k C W) ↔ IsCompletelyReducible k C V := by
  let _ : Comodule k C W := Transport e
  let Φ : Subcomodule k C V ≃o Subcomodule k C W := Subcomodule.transportOrderIso e
  let E : Submodule k V ≃o Submodule k W := Submodule.orderIsoMapComap e
  constructor
  · exact isCompletelyReducible_of_orderIso k Φ.symm E.symm
      (Subcomodule.transportOrderIso_symm_apply_toSubmodule e)
  · exact isCompletelyReducible_of_orderIso k Φ E
      (Subcomodule.transportOrderIso_apply_toSubmodule e)

end Transport

section Equiv

variable (k : Type u) [CommSemiring k]
variable {C : Type v} {D : Type*}
variable [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommMonoid D] [Module k D] [Coalgebra k D]

/-- Complete reducibility is unchanged by corestricting a comodule along a coalgebra
equivalence. -/
theorem isCompletelyReducible_corestrict_iff_of_coalgEquiv (e : C ≃ₗc[k] D)
    {V : Type w} [AddCommMonoid V] [Module k V] [Comodule k D V] :
    (letI : Comodule k C V := Comodule.Corestrict e.symm.toCoalgHom;
      Comodule.IsCompletelyReducible k C V) ↔
      Comodule.IsCompletelyReducible k D V := by
  let _ : Comodule k C V := Comodule.Corestrict e.symm.toCoalgHom
  let subcomoduleEquiv : Subcomodule k D V ≃o Subcomodule k C V :=
    Subcomodule.corestrictOrderIso e.symm
  constructor
  · exact isCompletelyReducible_of_orderIso k subcomoduleEquiv.symm (OrderIso.refl _)
      (fun A ↦ by simp [subcomoduleEquiv])
  · exact isCompletelyReducible_of_orderIso k subcomoduleEquiv (OrderIso.refl _)
      (fun A ↦ by
        simpa [subcomoduleEquiv] using
          Subcomodule.corestrict_toSubmodule e.symm.toCoalgHom A)

end Equiv

end Comodule

namespace Coalgebra

variable (k : Type u) [Field k]
variable {C : Type v} {D : Type*}
variable [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommMonoid D] [Module k D] [Coalgebra k D]

namespace IsLinearlyReductive

/-- If every finite-dimensional comodule whose carrier is in the base-field universe is
completely reducible, then every finite-dimensional comodule is completely reducible, regardless
of its carrier universe. -/
theorem isCompletelyReducible
    (h : IsLinearlyReductive.{u, v, u} k C)
    {V : Type w} [AddCommMonoid V] [Module k V] [Comodule k C V] [Module.Finite k V] :
    Comodule.IsCompletelyReducible k C V := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let : Module.Free k V := Module.Free.of_divisionRing k V
  let e : V ≃ₗ[k] (Fin (Module.finrank k V) → k) := (Module.finBasis k V).equivFun
  let _ : Comodule k C (Fin (Module.finrank k V) → k) := Comodule.Transport e
  exact (Comodule.isCompletelyReducible_transport_iff k e).mp (h _)

end IsLinearlyReductive

/-- Linear reductivity is invariant under equivalence of coalgebras. -/
theorem isLinearlyReductive_iff_of_coalgEquiv (e : C ≃ₗc[k] D) :
    IsLinearlyReductive.{u, v, w} k C ↔ IsLinearlyReductive.{u, _, w} k D := by
  constructor
  · intro h V _ _ _ _
    let _ : Comodule k C V := Comodule.Corestrict e.symm.toCoalgHom
    exact (Comodule.isCompletelyReducible_corestrict_iff_of_coalgEquiv k e).mp (h V)
  · intro h V _ _ _ _
    let _ : Comodule k D V := Comodule.Corestrict e.toCoalgHom
    exact (Comodule.isCompletelyReducible_corestrict_iff_of_coalgEquiv k e.symm).mp (h V)

end Coalgebra

namespace Comodule

section Projection

variable (k : Type u) (G : Type v) (V : Type w)
variable [Field k]
variable [AddCommMonoid V] [Module k V] [Comodule k (MonoidAlgebra k G) V]

/-- Sum the result of applying `p` weightwise and projecting each result back to its source
weight. -/
private noncomputable def projectedWeightSum (p : V →ₗ[k] V) : (G →₀ V) →ₗ[k] V :=
  Finsupp.lsum k fun g ↦ weightProj k G V g ∘ₗ p

/-- The endomorphism obtained by applying `p` separately to each weight component. -/
private noncomputable def equivariantProjection (p : V →ₗ[k] V) : V →ₗ[k] V :=
  (projectedWeightSum k G V p).comp (weightDecomposition k G V)

private theorem equivariantProjection_apply (p : V →ₗ[k] V) (v : V) :
    equivariantProjection k G V p v =
      (weightDecomposition k G V v).sum fun g w ↦ weightProj k G V g (p w) := by
  classical
  rfl

private theorem equivariantProjection_of_mem_weightSpace (p : V →ₗ[k] V)
    {g : G} {v : V} (hv : v ∈ weightSpace k G V g) :
    equivariantProjection k G V p v = weightProj k G V g (p v) := by
  classical
  rw [equivariantProjection_apply]
  have hdecomp : weightDecomposition k G V v = Finsupp.single g v := by
    apply Finsupp.ext
    intro h
    rw [weightDecomposition_apply]
    by_cases hh : h = g
    · subst h
      simp [weightProj_of_mem hv]
    · simp [hh, weightProj_of_mem_of_ne hh hv]
  rw [hdecomp]
  simp

private theorem equivariantProjection_mem_weightSpace (p : V →ₗ[k] V)
    {g : G} {v : V} (hv : v ∈ weightSpace k G V g) :
    equivariantProjection k G V p v ∈ weightSpace k G V g := by
  rw [equivariantProjection_of_mem_weightSpace k G V p hv]
  exact weightProj_mem_weightSpace g (p v)

/-- The weightwise version of a linear endomorphism, bundled as a comodule morphism. -/
private noncomputable def equivariantProjectionHom (p : V →ₗ[k] V) :
    Hom k (MonoidAlgebra k G) V V :=
  Hom.ofMapWeightSpace (equivariantProjection k G V p)
    (fun g _ hv ↦ equivariantProjection_mem_weightSpace k G V p (g := g) hv)

private theorem equivariantProjection_mem_subcomodule
    (N : Subcomodule k (MonoidAlgebra k G) V) (p : V →ₗ[k] V)
    (hp : ∀ v, p v ∈ N) (v : V) : equivariantProjection k G V p v ∈ N := by
  classical
  rw [equivariantProjection_apply]
  exact Submodule.sum_mem N.toSubmodule fun g _ ↦
    weightProj_mem_subcomodule (R := k) (G := G) (V := V) N g (hp _)

private theorem equivariantProjection_apply_of_mem
    (N : Subcomodule k (MonoidAlgebra k G) V) (p : V →ₗ[k] V)
    (hp : ∀ {v}, v ∈ N → p v = v) {v : V} (hv : v ∈ N) :
    equivariantProjection k G V p v = v := by
  classical
  rw [equivariantProjection_apply]
  have hterm : ∀ g ∈ (weightDecomposition k G V v).support,
      weightProj k G V g (p (weightProj k G V g v)) = weightProj k G V g v := by
    intro g hg
    rw [hp (weightProj_mem_subcomodule (R := k) (G := G) (V := V) N g hv),
      weightProj_weightProj_self]
  rw [Finsupp.sum]
  simp_rw [weightDecomposition_apply]
  rw [Finset.sum_congr rfl hterm]
  simpa only [Finsupp.sum, weightDecomposition_apply] using
    weightDecomposition_sum (R := k) (G := G) (V := V) v

private theorem exists_equivariantProjection
    (N : Subcomodule k (MonoidAlgebra k G) V) :
    ∃ P : Hom k (MonoidAlgebra k G) V V,
      LinearMap.range P.toLinearMap = N.toSubmodule ∧
        IsIdempotentElem P.toLinearMap := by
  classical
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  obtain ⟨Q, hNQ⟩ := Submodule.exists_isCompl N.toSubmodule
  let p : V →ₗ[k] V := N.toSubmodule.projection Q hNQ
  let P := equivariantProjectionHom k G V p
  have hP : P.toLinearMap = equivariantProjection k G V p := by
    simp only [P, equivariantProjectionHom, Hom.ofMapWeightSpace_toLinearMap]
  refine ⟨P, ?_, ?_⟩
  · rw [hP]
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact equivariantProjection_mem_subcomodule k G V N p
        (fun w ↦ Submodule.projection_apply_mem hNQ w) v
    · intro n hn
      refine ⟨n, ?_⟩
      exact equivariantProjection_apply_of_mem k G V N p
        (fun hv ↦ Submodule.projection_apply_of_mem_left hNQ hv) hn
  · unfold IsIdempotentElem
    rw [hP]
    ext v
    apply equivariantProjection_apply_of_mem k G V N p
      (fun hv ↦ Submodule.projection_apply_of_mem_left hNQ hv)
    exact equivariantProjection_mem_subcomodule k G V N p
      (fun w ↦ Submodule.projection_apply_mem hNQ w) v

/-- Every comodule over a monoid-algebra coalgebra over a field is completely reducible. -/
theorem isCompletelyReducible_monoidAlgebra :
    IsCompletelyReducible k (MonoidAlgebra k G) V := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  intro N
  obtain ⟨P, hrange, hidem⟩ := exists_equivariantProjection k G V N
  refine ⟨P.ker, ?_⟩
  rw [Comodule.Hom.ker_toSubmodule, ← hrange]
  exact LinearMap.IsIdempotentElem.isCompl (f := P.toLinearMap) hidem

end Projection

end Comodule

namespace Coalgebra

universe u' v' w'

/-- A monoid-algebra coalgebra over a field is linearly reductive. For a commutative group `G`,
this is the coordinate algebra statement that the diagonalizable group `D(G)` is linearly
reductive. -/
theorem isLinearlyReductive_monoidAlgebra (k : Type u') (G : Type v') [Field k] :
    IsLinearlyReductive.{u', max u' v', w'} k (MonoidAlgebra k G) := by
  intro V _ _ _ _
  exact Comodule.isCompletelyReducible_monoidAlgebra k G V

end Coalgebra

end TauCeti
