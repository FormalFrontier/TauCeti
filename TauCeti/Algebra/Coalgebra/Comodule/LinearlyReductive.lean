/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra
import TauCeti.Algebra.Coalgebra.Subcomodule.Comap
import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Linear reductivity of diagonalizable groups

An affine group over a field is linearly reductive when every finite-dimensional rational
representation is completely reducible. On coordinate rings, rational representations are
comodules, and complete reducibility says that every subcomodule has a subcomodule complement.

This file introduces that intrinsic comodule formulation and proves it for every monoid-algebra
coalgebra `k[G]`. The proof makes an arbitrary linear projection onto a subcomodule equivariant:
decompose a vector into its weights, apply the projection separately on each weight, and project
the result back to that weight. The resulting idempotent comodule endomorphism has the original
subcomodule as its range, so its kernel is an invariant complement.

For an abelian group `G`, `k[G]` is the coordinate Hopf algebra of the diagonalizable group
`D(G)`. Thus every diagonalizable group, and in particular every split torus, is linearly
reductive over an arbitrary field. This is the diagonalizable direction of the linear-reductivity
milestone in Layer 6 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.Comodule.IsCompletelyReducible`: every subcomodule has a subcomodule complement.
* `TauCeti.Coalgebra.IsLinearlyReductive`: every finite-dimensional comodule is completely
  reducible.
* `TauCeti.Coalgebra.isLinearlyReductive_monoidAlgebra`: monoid-algebra coalgebras are linearly
  reductive over a field.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.2.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable (k : Type u) (C : Type v) (V : Type w)
variable [Field k]
variable [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommMonoid V] [Module k V] [Comodule k C V]

/-- A comodule is completely reducible when each subcomodule has a complementary subcomodule.

The complement is taken in the lattice of underlying vector subspaces, so the statement says
both that the two subcomodules intersect trivially and that together they span the whole
comodule. -/
def IsCompletelyReducible : Prop :=
  ∀ W : Subcomodule k C V, ∃ Q : Subcomodule k C V,
    IsCompl W.toSubmodule Q.toSubmodule

/-- Complete reducibility is characterized by invariant complements to all subcomodules. -/
theorem isCompletelyReducible_def :
    IsCompletelyReducible k C V ↔
      ∀ W : Subcomodule k C V, ∃ Q : Subcomodule k C V,
        IsCompl W.toSubmodule Q.toSubmodule :=
  Iff.rfl

end Comodule

namespace Coalgebra

variable (k : Type u) (C : Type v)
variable [Field k]
variable [AddCommMonoid C] [Module k C] [Coalgebra k C]

/-- A coalgebra is linearly reductive when every finite-dimensional comodule over it is
completely reducible. For a commutative Hopf algebra representing an affine group, this is the
usual complete-reducibility definition of a linearly reductive group. -/
def IsLinearlyReductive : Prop :=
  ∀ (V : Type w) [AddCommMonoid V] [Module k V] [Comodule k C V] [Module.Finite k V],
    Comodule.IsCompletelyReducible k C V

/-- Linear reductivity is characterized by complements to subcomodules of every finite
comodule. -/
theorem isLinearlyReductive_def :
    IsLinearlyReductive.{u, v, w} k C ↔
      ∀ (V : Type w) [AddCommMonoid V] [Module k V] [Comodule k C V] [Module.Finite k V]
        (W : Subcomodule k C V), ∃ Q : Subcomodule k C V,
          IsCompl W.toSubmodule Q.toSubmodule :=
  Iff.rfl

end Coalgebra

namespace Comodule

section WeightMaps

variable {k : Type u} {G : Type v} {V : Type w} {W : Type x}
variable [CommSemiring k]
variable [AddCommMonoid V] [Module k V] [Comodule k (MonoidAlgebra k G) V]
variable [AddCommMonoid W] [Module k W] [Comodule k (MonoidAlgebra k G) W]

/-- A linear map between comodules over a monoid algebra is a comodule morphism if it preserves
every weight space. -/
@[expose] noncomputable def Hom.ofMapWeightSpace (f : V →ₗ[k] W)
    (hf : ∀ (g : G) {v : V}, v ∈ weightSpace k G V g → f v ∈ weightSpace k G W g) :
    Hom k (MonoidAlgebra k G) V W where
  toLinearMap := f
  map_coact := by
    apply LinearMap.ext
    intro v
    rw [← weightDecomposition_sum (R := k) (G := G) (V := V) v]
    simp only [Finsupp.sum, map_sum, LinearMap.coe_comp, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro g hg
    rw [weightDecomposition_apply,
      mem_weightSpace.mp (weightProj_mem_weightSpace g v), TensorProduct.map_tmul,
      mem_weightSpace.mp (hf g (weightProj_mem_weightSpace g v))]
    rfl

@[simp]
theorem Hom.ofMapWeightSpace_toLinearMap (f : V →ₗ[k] W)
    (hf : ∀ (g : G) {v : V}, v ∈ weightSpace k G V g → f v ∈ weightSpace k G W g) :
    (Hom.ofMapWeightSpace f hf).toLinearMap = f :=
  rfl

omit [Comodule k (MonoidAlgebra k G) V] [Comodule k (MonoidAlgebra k G) W] in
private theorem tensorComponent_map (f : V →ₗ[k] W) (g : G)
    (t : V ⊗[k] MonoidAlgebra k G) :
    f (tensorComponent k G V g t) =
      tensorComponent k G W g (TensorProduct.map f LinearMap.id t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul v x => simp [tensorComponent_tmul]

/-- A comodule morphism over a monoid algebra commutes with every weight projection. -/
theorem Hom.map_weightProj (f : Hom k (MonoidAlgebra k G) V W) (g : G) (v : V) :
    f (weightProj k G V g v) = weightProj k G W g (f v) := by
  rw [weightProj_apply, weightProj_apply]
  exact (tensorComponent_map f.toLinearMap g _).trans <|
    congrArg (tensorComponent k G W g) (f.map_coact_apply v)

end WeightMaps

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

private theorem weightProj_mem_subcomodule (N : Subcomodule k (MonoidAlgebra k G) V)
    (g : G) {v : V} (hv : v ∈ N) : weightProj k G V g v ∈ N := by
  let _ : Comodule k (MonoidAlgebra k G) N := Subcomodule.instComodule N
  have hmap := (Subcomodule.subtype N).map_weightProj g (⟨v, hv⟩ : N)
  rw [Subcomodule.subtype_apply] at hmap
  have hmap' :
      (weightProj k G N g (⟨v, hv⟩ : N) : V) = weightProj k G V g v := by
    simpa only [Subcomodule.subtype_apply] using hmap
  rw [← hmap']
  exact (weightProj k G N g (⟨v, hv⟩ : N)).2

private theorem equivariantProjection_mem_subcomodule
    (N : Subcomodule k (MonoidAlgebra k G) V) (p : V →ₗ[k] V)
    (hp : ∀ v, p v ∈ N) (v : V) : equivariantProjection k G V p v ∈ N := by
  classical
  rw [equivariantProjection_apply]
  exact Submodule.sum_mem N.toSubmodule fun g _ ↦
    weightProj_mem_subcomodule k G V N g (hp _)

private theorem equivariantProjection_apply_of_mem
    (N : Subcomodule k (MonoidAlgebra k G) V) (p : V →ₗ[k] V)
    (hp : ∀ {v}, v ∈ N → p v = v) {v : V} (hv : v ∈ N) :
    equivariantProjection k G V p v = v := by
  classical
  rw [equivariantProjection_apply]
  have hterm : ∀ g ∈ (weightDecomposition k G V v).support,
      weightProj k G V g (p (weightProj k G V g v)) = weightProj k G V g v := by
    intro g hg
    rw [hp (weightProj_mem_subcomodule k G V N g hv),
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
  refine ⟨P, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact equivariantProjection_mem_subcomodule k G V N p
        (fun w ↦ Submodule.projection_apply_mem hNQ w) v
    · intro n hn
      refine ⟨n, ?_⟩
      exact equivariantProjection_apply_of_mem k G V N p
        (fun hv ↦ Submodule.projection_apply_of_mem_left hNQ hv) hn
  · change P.toLinearMap * P.toLinearMap = P.toLinearMap
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
