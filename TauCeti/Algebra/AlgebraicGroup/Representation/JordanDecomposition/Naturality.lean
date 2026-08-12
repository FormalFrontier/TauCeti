/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Corestrict

/-!
# Naturality of Jordan decomposition for algebraic-group points

A bialgebra morphism `φ : H₁ →ₐc[k] H₂` between coordinate Hopf algebras represents a
homomorphism in the opposite direction between the corresponding affine groups. On points this
homomorphism is precomposition, `TauCeti.AlgHom.mapDomain φ`.

This file proves that point-level Jordan decomposition is natural under these homomorphisms. The
key compatibility is representation-theoretic: acting by the precomposed point on an
`H₁`-comodule is the same as first corestricting that comodule along `φ` and then acting by the
original `H₂`-point. Consequently `mapDomain φ` preserves semisimple points, and uniqueness of
the commuting semisimple--unipotent factorization identifies the images of both Jordan factors.

This is the functoriality-under-homomorphisms part of Layer 4, "Jordan decomposition", in the
ReductiveGroups roadmap.

## Main declarations

* `TauCeti.Comodule.endOfPoint_corestrict`: compatibility of point endomorphisms with
  corestriction and precomposition.
* `TauCeti.Comodule.pointsAction_corestrict`: the corresponding equality of point actions.
* `TauCeti.HopfAlgebra.IsSemisimplePoint.mapDomain`: a homomorphism of affine groups preserves
  semisimple points.
* `TauCeti.HopfAlgebra.Point.jordanDecomposition_mapDomain`: Jordan decomposition commutes with
  a homomorphism of affine groups.
* `TauCeti.HopfAlgebra.Point.semisimplePart_mapDomain` and
  `TauCeti.HopfAlgebra.Point.unipotentPart_mapDomain`: the two component formulas.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable {k : Type u} {H₁ : Type v} {H₂ : Type w} {K : Type x}
variable [CommSemiring k] [Semiring H₁] [Semiring H₂]
variable [CommSemiring K] [Algebra k K]

section Bialgebra

variable [_root_.Bialgebra k H₁] [_root_.Bialgebra k H₂]
variable {V : Type*} [AddCommMonoid V] [Module k V] [Comodule k H₁ V]

/-- Acting on a comodule by a point precomposed with a bialgebra morphism is the same as
corestricting the comodule along that morphism and acting by the original point. -/
theorem endOfPoint_corestrict (φ : H₁ →ₐc[k] H₂)
    (g : WithConv (H₂ →ₐ[k] K)) :
    (letI : Comodule k H₂ V := Corestrict φ.toCoalgHom
     endOfPoint V g.ofConv) = endOfPoint V (AlgHom.mapDomain φ g).ofConv := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  rw [endOfPoint_tmul, endOfPoint_tmul]
  simp only [corestrict_coact_apply, AlgHom.mapDomain_apply,
    AlgHom.comp_toLinearMap]
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply]
  rfl

end Bialgebra

section HopfAlgebra

variable [_root_.HopfAlgebra k H₁] [_root_.HopfAlgebra k H₂]
variable {V : Type*} [AddCommMonoid V] [Module k V] [Comodule k H₁ V]

/-- The linear action of a precomposed point agrees with the action of the original point on
the corestricted comodule. -/
theorem pointsAction_corestrict (φ : H₁ →ₐc[k] H₂)
    (g : WithConv (H₂ →ₐ[k] K)) :
    (letI : Comodule k H₂ V := Corestrict φ.toCoalgHom
     pointsAction V g) = pointsAction V (AlgHom.mapDomain φ g) := by
  let : Comodule k H₂ V := Corestrict φ.toCoalgHom
  apply LinearEquiv.ext
  exact LinearMap.congr_fun <|
    (pointsAction_toLinearMap V g).trans <|
      (endOfPoint_corestrict φ g).trans <|
        (pointsAction_toLinearMap V (AlgHom.mapDomain φ g)).symm

end HopfAlgebra

end Comodule

namespace HopfAlgebra

variable {k H₁ H₂ K : Type u}
variable [Field k] [CommRing H₁] [CommRing H₂]
variable [_root_.HopfAlgebra k H₁] [_root_.HopfAlgebra k H₂]
variable [Field K] [Algebra k K]

/-- A homomorphism of affine groups sends semisimple points to semisimple points. In coordinate
algebras the homomorphism is represented contravariantly by a bialgebra morphism. -/
theorem IsSemisimplePoint.mapDomain {g : WithConv (H₂ →ₐ[k] K)}
    (hg : IsSemisimplePoint g) (φ : H₁ →ₐc[k] H₂) :
    IsSemisimplePoint (AlgHom.mapDomain φ g) := by
  rw [isSemisimplePoint_def] at hg ⊢
  intro M
  rw [← Comodule.pointsAction_corestrict (V := M) φ g]
  exact hg ((FGComoduleCat.corestrict φ.toCoalgHom).obj M)

namespace Point

variable [PerfectField K]

/-- The Jordan decomposition of an algebraic-group point commutes with a homomorphism of affine
groups. The coordinate-algebra morphism points in the opposite direction. -/
theorem jordanDecomposition_mapDomain (φ : H₁ →ₐc[k] H₂)
    (g : WithConv (H₂ →ₐ[k] K)) :
    jordanDecomposition k H₁ K (AlgHom.mapDomain φ g) =
      (AlgHom.mapDomain φ (semisimplePart k H₂ K g),
        AlgHom.mapDomain φ (unipotentPart k H₂ K g)) := by
  symm
  apply (eq_jordanDecomposition_iff k H₁ K (AlgHom.mapDomain φ g) _ _).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M
    rw [← Comodule.pointsAction_corestrict (V := M) φ]
    exact isSemisimple_pointsAction_semisimplePart k H₂ K g
      ((FGComoduleCat.corestrict φ.toCoalgHom).obj M)
  · intro M
    rw [← Comodule.pointsAction_corestrict (V := M) φ]
    exact isUnipotent_pointsAction_unipotentPart k H₂ K g
      ((FGComoduleCat.corestrict φ.toCoalgHom).obj M)
  · exact (commute_semisimplePart_unipotentPart k H₂ K g).map (AlgHom.mapDomain φ)
  · rw [← map_mul, semisimplePart_mul_unipotentPart]

/-- The semisimple part of a point is preserved by homomorphisms of affine groups. -/
@[simp]
theorem semisimplePart_mapDomain (φ : H₁ →ₐc[k] H₂)
    (g : WithConv (H₂ →ₐ[k] K)) :
    semisimplePart k H₁ K (toConv (g.ofConv.comp (φ : H₁ →ₐ[k] H₂))) =
      toConv ((semisimplePart k H₂ K g).ofConv.comp (φ : H₁ →ₐ[k] H₂)) := by
  simpa only [jordanDecomposition_fst, AlgHom.mapDomain_apply] using
      congrArg Prod.fst (jordanDecomposition_mapDomain φ g)

/-- The unipotent part of a point is preserved by homomorphisms of affine groups. -/
@[simp]
theorem unipotentPart_mapDomain (φ : H₁ →ₐc[k] H₂)
    (g : WithConv (H₂ →ₐ[k] K)) :
    unipotentPart k H₁ K (toConv (g.ofConv.comp (φ : H₁ →ₐ[k] H₂))) =
      toConv ((unipotentPart k H₂ K g).ofConv.comp (φ : H₁ →ₐ[k] H₂)) := by
  simpa only [jordanDecomposition_snd, AlgHom.mapDomain_apply] using
      congrArg Prod.snd (jordanDecomposition_mapDomain φ g)

end Point
end HopfAlgebra
end TauCeti
