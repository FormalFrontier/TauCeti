/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Solvable
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.AlgebraicGroup.Product

/-!
# Geometric solvability of affine groups

For a commutative Hopf algebra `H` over a field `k`, this file records the geometric-points
solvability condition: the convolution group of `AlgebraicClosure k`-valued points of `H` is a
solvable abstract group. Smoothness and finite type are deliberately not built into this property;
consumers must state them separately when interpreting it as the classical notion of a solvable
algebraic group.

The property is invariant under coordinate-Hopf-algebra isomorphisms. It is preserved by closed
subgroups, represented contravariantly by surjective coordinate morphisms, and a product has the
property exactly when both factors do. These are the first subgroup-calculus operations needed for
Lie--Kolchin theory and the construction of the solvable radical.

## Main declarations

* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty`: solvability of the geometric point
  group.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty_of_surjective`: closure under closed
  subgroups.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty_tensorProduct_iff`: solvability of a
  product is equivalent to solvability of both factors.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This begins the "Lie--Kolchin; solvable groups" milestone in Layer 5 of the ReductiveGroups
roadmap. The scheme-theoretic derived subgroup and its comparison with this geometric-points
criterion remain to be constructed.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti

universe u v

/-- The object property asserting that the group of algebraic-closure-valued points of a
commutative Hopf algebra is solvable.

This property packages only the geometric-points condition. In applications to classical
algebraic groups, finite type and smoothness are separate hypotheses. -/
def geometricallySolvablePointsCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (CommHopfAlgCat.{v} k) :=
  fun H ↦ Group.IsSolvable (WithConv (H →ₐ[k] AlgebraicClosure k))

/-- Membership in the geometric-points solvability property means that the convolution group of
points over an algebraic closure is solvable. -/
@[simp]
theorem geometricallySolvablePointsCommHopfAlgProperty_iff
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k) :
    geometricallySolvablePointsCommHopfAlgProperty k H ↔
      Group.IsSolvable (WithConv (H →ₐ[k] AlgebraicClosure k)) :=
  Iff.rfl

/-- Geometric-points solvability is invariant under isomorphisms of commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (geometricallySolvablePointsCommHopfAlgProperty k :
      ObjectProperty (CommHopfAlgCat.{v} k)).IsClosedUnderIsomorphisms where
  of_iso {H K} e hH := by
    rw [geometricallySolvablePointsCommHopfAlgProperty_iff] at hH ⊢
    let e' : H ≃ₐc[k] K := CommHopfAlgCat.ofIso e
    let _ : Group.IsSolvable (WithConv (H →ₐ[k] AlgebraicClosure k)) := hH
    exact Group.isSolvable_of_isSolvable_injective
      (f := (AlgHom.mapDomainMulEquiv (A := AlgebraicClosure k) e').toMonoidHom)
      (AlgHom.mapDomainMulEquiv (A := AlgebraicClosure k) e').injective

/-- Geometric-points solvability descends along a surjective coordinate Hopf-algebra morphism.

Contravariantly, the target coordinate algebra represents a closed subgroup of the source affine
group. Its geometric point group embeds into the solvable point group of the ambient object. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_of_surjective
    (k : Type u) [Field k] {H K : CommHopfAlgCat.{v} k}
    (f : H ⟶ K) (hf : Function.Surjective f.hom)
    (hH : geometricallySolvablePointsCommHopfAlgProperty k H) :
    geometricallySolvablePointsCommHopfAlgProperty k K := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff] at hH ⊢
  let _ : Group.IsSolvable (WithConv (H →ₐ[k] AlgebraicClosure k)) := hH
  exact Group.isSolvable_of_isSolvable_injective
    (f := AlgHom.mapDomain (H₁ := H) (H₂ := K) (A := AlgebraicClosure k) f.hom)
    (CommHopfAlgCat.mapPointsFunctor_app_injective_of_surjective f hf
      (CommAlgCat.of k (AlgebraicClosure k)))

/-- The closed subgroup cut out by a Hopf ideal has solvable geometric points whenever the
ambient affine group does. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_quotient
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k) (I : HopfIdeal k H)
    (hH : geometricallySolvablePointsCommHopfAlgProperty k H) :
    geometricallySolvablePointsCommHopfAlgProperty k (CommHopfAlgCat.quotient H I) := by
  apply geometricallySolvablePointsCommHopfAlgProperty_of_surjective k
    (CommHopfAlgCat.mkQuotient H I) _ hH
  exact Ideal.Quotient.mkₐ_surjective k I.toIdeal

/-- The tensor-product coordinate algebra has solvable geometric points exactly when both
factors do. Contravariantly, this is closure and reflection of solvability by direct products of
affine groups. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_tensorProduct_iff
    (k : Type u) [Field k] (H K : CommHopfAlgCat.{v} k) :
    geometricallySolvablePointsCommHopfAlgProperty k
        (CommHopfAlgCat.of k (H ⊗[k] K)) ↔
      geometricallySolvablePointsCommHopfAlgProperty k H ∧
        geometricallySolvablePointsCommHopfAlgProperty k K := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff,
    geometricallySolvablePointsCommHopfAlgProperty_iff,
    geometricallySolvablePointsCommHopfAlgProperty_iff]
  let e := AffineGroup.Product.pointsMulEquiv
    (R := k) (H₁ := (H : Type v)) (H₂ := (K : Type v))
    (A := AlgebraicClosure k)
  let f :
      WithConv (((H : Type v) ⊗[k] (K : Type v)) →ₐ[k] AlgebraicClosure k) →*
        WithConv (H →ₐ[k] AlgebraicClosure k) ×
          WithConv (K →ₐ[k] AlgebraicClosure k) :=
    e.toMonoidHom
  have hf_injective : Function.Injective f := e.injective
  let finv :
      (WithConv (H →ₐ[k] AlgebraicClosure k) ×
          WithConv (K →ₐ[k] AlgebraicClosure k)) →*
        WithConv (((H : Type v) ⊗[k] (K : Type v)) →ₐ[k] AlgebraicClosure k) :=
    e.symm.toMonoidHom
  have hfinv_injective : Function.Injective finv := e.symm.injective
  constructor
  · intro h
    let _ : Group.IsSolvable
        (WithConv (((H : Type v) ⊗[k] (K : Type v)) →ₐ[k] AlgebraicClosure k)) := h
    let hprod : Group.IsSolvable
        (WithConv (H →ₐ[k] AlgebraicClosure k) ×
          WithConv (K →ₐ[k] AlgebraicClosure k)) :=
      Group.isSolvable_of_isSolvable_injective
        (G := WithConv (H →ₐ[k] AlgebraicClosure k) ×
          WithConv (K →ₐ[k] AlgebraicClosure k))
        (G' := WithConv (((H : Type v) ⊗[k] (K : Type v)) →ₐ[k] AlgebraicClosure k))
        (f := finv) hfinv_injective
    let _ : Group.IsSolvable
        (WithConv (H →ₐ[k] AlgebraicClosure k) ×
          WithConv (K →ₐ[k] AlgebraicClosure k)) := hprod
    constructor
    · exact Group.isSolvable_of_surjective
        (G := WithConv (H →ₐ[k] AlgebraicClosure k) ×
          WithConv (K →ₐ[k] AlgebraicClosure k))
        (G' := WithConv (H →ₐ[k] AlgebraicClosure k))
        (f := MonoidHom.fst _ _) (fun x ↦ ⟨(x, 1), rfl⟩)
    · exact Group.isSolvable_of_surjective
        (G := WithConv (H →ₐ[k] AlgebraicClosure k) ×
          WithConv (K →ₐ[k] AlgebraicClosure k))
        (G' := WithConv (K →ₐ[k] AlgebraicClosure k))
        (f := MonoidHom.snd _ _) (fun x ↦ ⟨(1, x), rfl⟩)
  · rintro ⟨hH, hK⟩
    let _ : Group.IsSolvable (WithConv (H →ₐ[k] AlgebraicClosure k)) := hH
    let _ : Group.IsSolvable (WithConv (K →ₐ[k] AlgebraicClosure k)) := hK
    exact Group.isSolvable_of_isSolvable_injective
      (G := WithConv (((H : Type v) ⊗[k] (K : Type v)) →ₐ[k] AlgebraicClosure k))
      (G' := WithConv (H →ₐ[k] AlgebraicClosure k) ×
        WithConv (K →ₐ[k] AlgebraicClosure k))
      (f := f) hf_injective

end TauCeti
