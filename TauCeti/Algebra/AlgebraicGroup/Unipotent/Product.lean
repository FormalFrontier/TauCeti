/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FiniteType.Product
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic

/-!
# Products of smooth unipotent affine groups

The tensor product of two commutative Hopf algebras is the coordinate algebra of the direct
product of their affine group schemes. This file proves that the representation-theoretic
unipotence condition is preserved and reflected by this product.

For points `g` and `h` of the two factors, the corresponding product point factors as

```text
(g, h) = (g, 1) * (1, h).
```

The two factors commute. Each is unipotent because it is obtained from `g` or `h` by
precomposition with the bialgebra projection that applies the counit to the other tensor factor.
Thus their product is unipotent. Conversely, the two components of a unipotent product point are
unipotent by precomposition with the coordinate inclusions.

Combining this pointwise result with stability of smoothness and finite type under tensor products
shows that direct products of smooth unipotent affine groups are smooth unipotent.

## Main declarations

* `TauCeti.HopfAlgebra.isUnipotentPoint_pointsMulEquiv_iff`: a product point is unipotent exactly
  when both of its components are.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.tensorProduct`: geometric-point
  unipotence is closed under products.
* `TauCeti.smoothUnipotentCommHopfAlgProperty.tensorProduct`: smooth unipotent finite-type affine
  groups are closed under products.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This advances Layer 5, "Unipotent groups", of the ReductiveGroups roadmap by establishing the
basic product closure needed to assemble unipotent groups from simpler factors.
-/

public section

open TensorProduct WithConv

namespace TauCeti

universe u v w

namespace HopfAlgebra

variable {k : Type u} [CommSemiring k]
variable {H K : Type v} [CommSemiring H] [CommSemiring K]
variable [_root_.HopfAlgebra k H] [_root_.HopfAlgebra k K]
variable {A : Type w} [CommRing A] [Algebra k A]

/-- A point of a product affine group is unipotent exactly when both factor points are
unipotent. -/
theorem isUnipotentPoint_pointsMulEquiv_iff
    (g : WithConv ((H ⊗[k] K) →ₐ[k] A)) :
    IsUnipotentPoint g ↔
      IsUnipotentPoint (AffineGroup.Product.pointsMulEquiv g).1 ∧
        IsUnipotentPoint (AffineGroup.Product.pointsMulEquiv g).2 := by
  constructor
  · intro hg
    exact ⟨hg.mapDomain Bialgebra.TensorProduct.includeLeft,
      hg.mapDomain Bialgebra.TensorProduct.includeRight⟩
  · rintro ⟨hleft, hright⟩
    let e := AffineGroup.Product.pointsMulEquiv
      (R := k) (H₁ := H) (H₂ := K) (A := A)
    let gleft := e.symm ((e g).1, 1)
    let gright := e.symm (1, (e g).2)
    have hgleft : IsUnipotentPoint gleft := by
      have h := hleft.mapDomain (Bialgebra.TensorProduct.projectLeft
        (R := k) (H₁ := H) (H₂ := K))
      simpa only [AlgHom.mapDomain_apply, gleft, e,
        AffineGroup.Product.mapDomain_projectLeft] using h
    have hgright : IsUnipotentPoint gright := by
      have h := hright.mapDomain (Bialgebra.TensorProduct.projectRight
        (R := k) (H₁ := H) (H₂ := K))
      simpa only [AlgHom.mapDomain_apply, gright, e,
        AffineGroup.Product.mapDomain_projectRight] using h
    have hfactor : g = gleft * gright := by
      simpa only [e, gleft, gright, map_mul, MulEquiv.symm_apply_apply] using
        congrArg e.symm (Prod.fst_mul_snd (e g)).symm
    rw [hfactor]
    exact hgleft.mul_of_commute hgright <| (MonoidHom.commute_inl_inr _ _).map e.symm

end HopfAlgebra

namespace geometricallyUnipotentPointsCommHopfAlgProperty

variable (k : Type u) [Field k]

/-- The tensor product of two coordinate Hopf algebras with unipotent geometric points again has
only unipotent geometric points. Contravariantly, geometric-point unipotence is closed under
direct products of affine groups. -/
theorem tensorProduct (H K : CommHopfAlgCat.{v} k)
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k H)
    (hK : geometricallyUnipotentPointsCommHopfAlgProperty k K) :
    geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.of k (H ⊗[k] K)) := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff] at hH hK ⊢
  intro g
  rw [HopfAlgebra.isUnipotentPoint_pointsMulEquiv_iff]
  exact ⟨hH _, hK _⟩

end geometricallyUnipotentPointsCommHopfAlgProperty

namespace smoothUnipotentCommHopfAlgProperty

variable (k : Type u) [Field k]

/-- The tensor product of two smooth unipotent finite-type coordinate Hopf algebras is smooth
unipotent. Contravariantly, direct products of smooth unipotent affine groups are smooth
unipotent. -/
theorem tensorProduct (H K : FiniteTypeCommHopfAlgCat.{u, v} k)
    (hH : smoothUnipotentCommHopfAlgProperty k H)
    (hK : smoothUnipotentCommHopfAlgProperty k K) :
    smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.tensorProduct H K) := by
  rw [smoothUnipotentCommHopfAlgProperty_iff] at hH hK ⊢
  let smoothH : Algebra.Smooth k H := hH.1
  let smoothK : Algebra.Smooth k K := hK.1
  let smoothOverH : Algebra.Smooth H (H ⊗[k] K) :=
    @Algebra.Smooth.baseChange k _ K H _ _ _ _ smoothK
  refine ⟨@Algebra.Smooth.comp k _ H (H ⊗[k] K) _ _ _ _ _ _
    smoothH smoothOverH, ?_⟩
  intro g
  rw [HopfAlgebra.isUnipotentPoint_pointsMulEquiv_iff]
  exact ⟨hH.2 _, hK.2 _⟩

end smoothUnipotentCommHopfAlgProperty

end TauCeti
