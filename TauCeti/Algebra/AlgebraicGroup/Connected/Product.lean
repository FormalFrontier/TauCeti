/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SemidirectProduct
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Properties
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Connected
public import TauCeti.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometric connectedness of products of affine groups

The direct product of two affine groups over a field has coordinate Hopf algebra given by the
tensor product of their coordinate algebras. This file applies the affine tensor-product
connectedness theorem to show that geometric connectedness is preserved by this construction.

On the scheme side, the product is the fibre product of the two Hopf spectra over the spectrum of
the ground field. Each projection has geometrically connected fibres by base change, and the
other factor is connected. Structure morphisms to the spectrum of a field are universally open,
so Mathlib's connectedness theorem for pullbacks applies. The standard affine pullback
isomorphism then identifies the result with the spectrum of the tensor product.

## Main declarations

* `TauCeti.geometricallyConnectedCommHopfAlgProperty.tensorProduct`: the tensor product of two
  geometrically connected commutative Hopf algebras is geometrically connected.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.semidirectProduct`: a semidirect product
  associated to an action of geometrically connected affine groups is geometrically connected.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.productOfNormal`: the multiplication image
  of a normal subgroup and another connected subgroup is geometrically connected when both
  factors are.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 1.c and 2.a.

This supplies the connectedness step in Layer 5, "The unipotent radical", of the
ReductiveGroups roadmap. The binary product of two radical candidates is formed as the image of
multiplication from a semidirect product whose underlying scheme is the direct product; the
result below proves that source is geometrically connected.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

open AlgebraicGeometry

universe u

private instance geometricallyConnected_respectsIso :
    MorphismProperty.RespectsIso @GeometricallyConnected :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

variable {k : Type u} [Field k]

namespace geometricallyConnectedCommHopfAlgProperty

/-- The tensor product of two geometrically connected commutative Hopf algebras is geometrically
connected. Contravariantly, direct products of geometrically connected affine groups over a
field are geometrically connected.

The Hopf structure on the tensor product is irrelevant to connectedness, but packages the
coordinate ring as the direct product in the same category used by the functor-of-points and
unipotent-radical constructions. -/
theorem tensorProduct (H K : CommHopfAlgCat.{u} k)
    (hH : geometricallyConnectedCommHopfAlgProperty k H)
    (hK : geometricallyConnectedCommHopfAlgProperty k K) :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.of k (H ⊗[k] K)) := by
  have hf : GeometricallyConnected
      (Spec.map (CommRingCat.ofHom (algebraMap k H))) := by
    rw [← morphismProperty_hopfSpec_obj_X_hom_iff
      (P := @GeometricallyConnected) k H]
    exact (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec k H).mp hH
  have hg : GeometricallyConnected
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [← morphismProperty_hopfSpec_obj_X_hom_iff
      (P := @GeometricallyConnected) k K]
    exact (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec k K).mp hK
  have hspectrum := geometricallyConnected_tensorProduct H K hf hg
  apply (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec
    k (CommHopfAlgCat.of k (H ⊗[k] K))).mpr
  exact (morphismProperty_hopfSpec_obj_X_hom_iff
    (P := @GeometricallyConnected) k (CommHopfAlgCat.of k (H ⊗[k] K))).mpr hspectrum

/-- The semidirect product associated to an action of geometrically connected affine groups is
geometrically connected.

The action changes the group law but not the underlying affine scheme: on coordinate algebras,
the carrier remains the tensor product. This formulation is the one used when multiplication of
two normal closed subgroups is made into a homomorphism by equipping their product with the
conjugation semidirect-product structure. -/
theorem semidirectProduct (H K : CommHopfAlgCat.{u} k)
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H))
    (hH : geometricallyConnectedCommHopfAlgProperty k H)
    (hK : geometricallyConnectedCommHopfAlgProperty k K) :
    geometricallyConnectedCommHopfAlgProperty k A.coordinateHopfAlgebra := by
  have h := tensorProduct H K hH hK
  rw [geometricallyConnectedCommHopfAlgProperty_iff] at h
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro L _ _
  let eL := Algebra.TensorProduct.congr
    A.coordinateAlgEquiv (AlgEquiv.refl : L ≃ₐ[k] L)
  exact (PrimeSpectrum.homeomorphOfRingEquiv eL.toRingEquiv).connectedSpace_iff.mpr (h L)

/-- The scheme-theoretic multiplication image of a normal geometrically connected closed affine
subgroup and another geometrically connected closed affine subgroup is geometrically connected. -/
theorem productOfNormal (H : CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal)
    (hIc : geometricallyConnectedCommHopfAlgProperty k (CommHopfAlgCat.quotient H I))
    (hJc : geometricallyConnectedCommHopfAlgProperty k (CommHopfAlgCat.quotient H J)) :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.productOfNormal H I J hI) := by
  let A := CommHopfAlgCat.quotientNormalConjugation H I J hI
  apply image (CommHopfAlgCat.productMapOfNormal H I J hI)
  exact (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    (CommHopfAlgCat.normalSemidirectProductIso H I J hI).symm
    (semidirectProduct (CommHopfAlgCat.quotient H I)
      (CommHopfAlgCat.quotient H J) A hIc hJc)

end geometricallyConnectedCommHopfAlgProperty

end TauCeti
