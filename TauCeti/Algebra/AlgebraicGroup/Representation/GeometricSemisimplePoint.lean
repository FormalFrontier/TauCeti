/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.Algebra.AlgebraicGroup.Product
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint

/-!
# Geometric semisimple points of affine groups

This file packages the condition that every algebraic-closure-valued point of a commutative Hopf
algebra is semisimple. It also establishes the generic transport and product results used to prove
that this object property is invariant under isomorphisms and closed under tensor products.

## Main declarations

* `TauCeti.HopfAlgebra.isSemisimplePoint_mapDomain_iff`: invariance of point semisimplicity under
  bialgebra isomorphisms.
* `TauCeti.HopfAlgebra.isSemisimplePoint_pointsMulEquiv_iff`: over a perfect field, a point of a
  product affine group is semisimple if and only if both component points are semisimple.
* `TauCeti.geometricallySemisimplePointsCommHopfAlgProperty`: the object property asserting that
  every algebraic-closure-valued point is semisimple.
* `TauCeti.geometricallySemisimplePointsCommHopfAlgProperty.tensorProduct`: geometric semisimplicity
  is closed under direct products of affine groups.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* J. S. Milne, *Algebraic Groups* (2017), §12.c.

This supplies generic geometric semisimple-point infrastructure used by Layer 4 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti

universe u v w x

section MapDomain

variable {k : Type u} {H₁ : Type v} {H₂ : Type w} {K : Type x}
variable [CommSemiring k] [Semiring H₁] [Semiring H₂]
variable [_root_.HopfAlgebra k H₁] [_root_.HopfAlgebra k H₂]
variable [Field K] [Algebra k K]

/-- Semisimplicity of points is invariant under precomposition by a bialgebra isomorphism. -/
theorem HopfAlgebra.isSemisimplePoint_mapDomain_iff
    (e : H₁ ≃ₐc[k] H₂) (g : WithConv (H₂ →ₐ[k] K)) :
    IsSemisimplePoint (AlgHom.mapDomain (e : H₁ →ₐc[k] H₂) g) ↔ IsSemisimplePoint g := by
  constructor
  · intro hg
    have h := hg.mapDomain (e.symm : H₂ →ₐc[k] H₁)
    have he : AlgHom.mapDomain (e.symm : H₂ →ₐc[k] H₁)
        (AlgHom.mapDomain (e : H₁ →ₐc[k] H₂) g) = g := by
      rw [← AlgHom.mapDomainMulEquiv_symm_apply e, ← AlgHom.mapDomainMulEquiv_apply e]
      exact (AlgHom.mapDomainMulEquiv (A := K) e).left_inv g
    rwa [he] at h
  · intro hg
    exact hg.mapDomain (e : H₁ →ₐc[k] H₂)

end MapDomain

section Product

variable {k : Type u} [CommSemiring k]
variable {H K' : Type v} [CommSemiring H] [CommSemiring K']
variable [_root_.HopfAlgebra k H] [_root_.HopfAlgebra k K']
variable {A : Type w} [Field A] [Algebra k A] [PerfectField A]

/-- Over a perfect field, a point of a product affine group is semisimple exactly when both factor
points are semisimple. -/
theorem HopfAlgebra.isSemisimplePoint_pointsMulEquiv_iff
    (g : WithConv ((H ⊗[k] K') →ₐ[k] A)) :
    IsSemisimplePoint g ↔
      IsSemisimplePoint (AffineGroup.Product.pointsMulEquiv g).1 ∧
        IsSemisimplePoint (AffineGroup.Product.pointsMulEquiv g).2 := by
  constructor
  · intro hg
    exact ⟨hg.mapDomain Bialgebra.TensorProduct.includeLeft,
      hg.mapDomain Bialgebra.TensorProduct.includeRight⟩
  · rintro ⟨hleft, hright⟩
    let e := AffineGroup.Product.pointsMulEquiv
      (R := k) (H₁ := H) (H₂ := K') (A := A)
    let gleft := e.symm ((e g).1, 1)
    let gright := e.symm (1, (e g).2)
    have hgleft : IsSemisimplePoint gleft := by
      have h := hleft.mapDomain (Bialgebra.TensorProduct.projectLeft
        (R := k) (H₁ := H) (H₂ := K'))
      simpa only [AlgHom.mapDomain_apply, gleft, e,
        AffineGroup.Product.mapDomain_projectLeft] using h
    have hgright : IsSemisimplePoint gright := by
      have h := hright.mapDomain (Bialgebra.TensorProduct.projectRight
        (R := k) (H₁ := H) (H₂ := K'))
      simpa only [AlgHom.mapDomain_apply, gright, e,
        AffineGroup.Product.mapDomain_projectRight] using h
    have hcomm : Commute gleft gright := by
      rw [commute_iff_eq]
      apply e.injective
      simp only [map_mul, e, gleft, gright, MulEquiv.apply_symm_apply]
      ext <;> simp
    have hfactor : g = gleft * gright := by
      apply e.injective
      simp only [map_mul, e, gleft, gright, MulEquiv.apply_symm_apply]
      ext <;> simp
    rw [hfactor]
    exact hgleft.mul_of_commute hgright hcomm

end Product

section ObjectProperty

variable (k : Type u) [Field k]

/-- The object property asserting that every algebraic-closure-valued point of a commutative Hopf
algebra is a semisimple point. -/
def geometricallySemisimplePointsCommHopfAlgProperty :
    ObjectProperty (CommHopfAlgCat.{v} k) :=
  fun H ↦ ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
    HopfAlgebra.IsSemisimplePoint g

/-- Membership in `geometricallySemisimplePointsCommHopfAlgProperty` means that every geometric
point is semisimple. -/
@[simp]
theorem geometricallySemisimplePointsCommHopfAlgProperty_iff
    (H : CommHopfAlgCat.{v} k) :
    geometricallySemisimplePointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.IsSemisimplePoint g :=
  Iff.rfl

/-- The geometric-point semisimplicity property is invariant under isomorphisms of commutative Hopf
algebras. -/
instance :
    (geometricallySemisimplePointsCommHopfAlgProperty k :
      ObjectProperty (CommHopfAlgCat.{v} k)).IsClosedUnderIsomorphisms where
  of_iso {H K} e hH g := by
    let e' : H ≃ₐc[k] K := CommHopfAlgCat.ofIso e
    apply (HopfAlgebra.isSemisimplePoint_mapDomain_iff e' g).mp
    exact hH _

/-- The tensor product of two coordinate Hopf algebras with semisimple geometric points again has
only semisimple geometric points. Contravariantly, geometric-point semisimplicity is closed under
direct products of affine groups. -/
theorem geometricallySemisimplePointsCommHopfAlgProperty.tensorProduct
    (H K : CommHopfAlgCat.{v} k)
    (hH : geometricallySemisimplePointsCommHopfAlgProperty k H)
    (hK : geometricallySemisimplePointsCommHopfAlgProperty k K) :
    geometricallySemisimplePointsCommHopfAlgProperty k
      (CommHopfAlgCat.of k (H ⊗[k] K)) := by
  rw [geometricallySemisimplePointsCommHopfAlgProperty_iff] at hH hK ⊢
  intro g
  rw [HopfAlgebra.isSemisimplePoint_pointsMulEquiv_iff]
  exact ⟨hH _, hK _⟩

/-- Every geometric point is semisimple exactly when the unipotent part of every geometric point is
the identity. -/
theorem geometricallySemisimplePointsCommHopfAlgProperty_iff_forall_unipotentPart_eq_one
    (H : CommHopfAlgCat.{u} k) :
    geometricallySemisimplePointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.Point.unipotentPart k H (AlgebraicClosure k) g = 1 := by
  rw [geometricallySemisimplePointsCommHopfAlgProperty_iff]
  apply forall_congr'
  intro g
  constructor
  · intro hg
    exact HopfAlgebra.Point.unipotentPart_eq_one_of_isSemisimple k H (AlgebraicClosure k)
      (fun M ↦ (HopfAlgebra.isSemisimplePoint_def g).mp hg M)
  · intro hu
    rw [HopfAlgebra.isSemisimplePoint_def]
    intro M
    have hdecomp := HopfAlgebra.Point.jordanDecomposition_spec k H (AlgebraicClosure k) g
    have hs := hdecomp.1 M
    have hg_eq : g = (HopfAlgebra.Point.jordanDecomposition k H (AlgebraicClosure k) g).1 := by
      have hmul := hdecomp.2.2.2
      have h2 : (HopfAlgebra.Point.jordanDecomposition k H (AlgebraicClosure k) g).2 = 1 := by
        rw [HopfAlgebra.Point.jordanDecomposition_snd, hu]
      rw [h2, mul_one] at hmul
      exact hmul
    rw [hg_eq]
    exact hs

/-- Every geometric point is semisimple exactly when the semisimple part of every geometric point
is the point itself. -/
theorem geometricallySemisimplePointsCommHopfAlgProperty_iff_forall_semisimplePart_eq_self
    (H : CommHopfAlgCat.{u} k) :
    geometricallySemisimplePointsCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.Point.semisimplePart k H (AlgebraicClosure k) g = g := by
  rw [geometricallySemisimplePointsCommHopfAlgProperty_iff]
  apply forall_congr'
  intro g
  constructor
  · intro hg
    exact HopfAlgebra.Point.semisimplePart_eq_self k H (AlgebraicClosure k)
      (fun M ↦ (HopfAlgebra.isSemisimplePoint_def g).mp hg M)
  · intro hs
    rw [HopfAlgebra.isSemisimplePoint_def]
    intro M
    have hdecomp := HopfAlgebra.Point.jordanDecomposition_spec k H (AlgebraicClosure k) g
    have hsem := hdecomp.1 M
    have h1 : (HopfAlgebra.Point.jordanDecomposition k H (AlgebraicClosure k) g).1 = g := by
      rw [HopfAlgebra.Point.jordanDecomposition_fst, hs]
    rw [h1] at hsem
    exact hsem

end ObjectProperty

end TauCeti
