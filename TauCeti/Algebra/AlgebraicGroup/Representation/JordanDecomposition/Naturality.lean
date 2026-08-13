/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint

/-!
# Naturality of Jordan decomposition for algebraic-group points

A bialgebra morphism `φ : H₁ →ₐc[k] H₂` between coordinate Hopf algebras represents a
homomorphism in the opposite direction between the corresponding affine groups. On points this
homomorphism is precomposition, `TauCeti.AlgHom.mapDomain φ`.

This file proves that point-level Jordan decomposition is natural under these homomorphisms. The
key compatibility is representation-theoretic: acting by the precomposed point on an
`H₁`-comodule is the same as first corestricting that comodule along `φ` and then acting by the
original `H₂`-point. The earlier point-action and semisimple-point APIs provide this compatibility;
uniqueness of the commuting semisimple--unipotent factorization then identifies the images of both
Jordan factors.

This is the functoriality-under-homomorphisms part of Layer 4, "Jordan decomposition", in the
ReductiveGroups roadmap.

## Main declarations

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

universe u

namespace HopfAlgebra

variable {k H₁ H₂ K : Type u}
variable [Field k] [CommRing H₁] [CommRing H₂]
variable [_root_.HopfAlgebra k H₁] [_root_.HopfAlgebra k H₂]
variable [Field K] [Algebra k K]

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
  · rw [← isSemisimplePoint_def]
    apply IsSemisimplePoint.mapDomain ?_ φ
    rw [isSemisimplePoint_def]
    exact fun M ↦ isSemisimple_pointsAction_semisimplePart k H₂ K g M
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
