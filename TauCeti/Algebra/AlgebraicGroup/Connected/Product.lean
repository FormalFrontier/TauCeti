/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Product
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Connected
public import TauCeti.CategoryTheory.Monoidal.SemidirectProduct.Basic

/-!
# Geometric connectedness of products of affine groups

The direct product of two affine groups over a field has coordinate Hopf algebra given by the
tensor product of their coordinate algebras. This file proves that geometric connectedness is
preserved by this construction.

On the scheme side, the product is the fibre product of the two Hopf spectra over the spectrum of
the ground field. Each projection has geometrically connected fibres by base change, and the
other factor is connected. Structure morphisms to the spectrum of a field are universally open,
so Mathlib's connectedness theorem for pullbacks applies. The standard affine pullback
isomorphism then identifies the result with the spectrum of the tensor product.

## Main declarations

* `TauCeti.geometricallyConnectedCommHopfAlgProperty.tensorProduct`: the tensor product of two
  geometrically connected commutative Hopf algebras is geometrically connected.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.semidirectProduct`: an internal semidirect
  product of geometrically connected affine groups is geometrically connected.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 1.c and 2.a.

This supplies the connectedness step in Layer 5, "The unipotent radical", of the
ReductiveGroups roadmap. The binary product of two radical candidates is formed as the image of
multiplication from a semidirect product whose underlying scheme is the direct product; the
result below proves that source is geometrically connected.
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

namespace TauCeti

open AlgebraicGeometry

universe u

private instance geometricallyConnected_respectsIso :
    MorphismProperty.RespectsIso @GeometricallyConnected :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

namespace geometricallyConnectedCommHopfAlgProperty

variable {k : Type u} [Field k]

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
  let f := Spec.map (CommRingCat.ofHom (algebraMap k H))
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hf : GeometricallyConnected f := by
    rw [← morphismProperty_hopfSpec_obj_X_hom_iff
      (P := @GeometricallyConnected) k H]
    exact (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec k H).mp hH
  have hg : GeometricallyConnected g := by
    rw [← morphismProperty_hopfSpec_obj_X_hom_iff
      (P := @GeometricallyConnected) k K]
    exact (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec k K).mp hK
  let _ : GeometricallyConnected f := hf
  let _ : GeometricallyConnected g := hg
  let _ : UniversallyOpen f := inferInstance
  let _ : UniversallyOpen g := inferInstance
  have hproduct : GeometricallyConnected (pullback.fst f g ≫ f) :=
    GeometricallyConnected.comp (pullback.fst f g) f
  have hspectrum : GeometricallyConnected
      (Spec.map (CommRingCat.ofHom (algebraMap k (H ⊗[k] K)))) := by
    have hproduct' : GeometricallyConnected
        ((pullbackSpecIso k H K).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap k (H ⊗[k] K)))) := by
      rw [pullbackSpecIso_hom_base]
      exact hproduct
    rw [MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyConnected) (pullbackSpecIso k H K).hom] at hproduct'
    exact hproduct'
  apply (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec
    k (CommHopfAlgCat.of k (H ⊗[k] K))).mpr
  exact (morphismProperty_hopfSpec_obj_X_hom_iff
    (P := @GeometricallyConnected) k (CommHopfAlgCat.of k (H ⊗[k] K))).mpr hspectrum

/-- The coordinate algebra underlying a semidirect product is explicitly equivalent to the
tensor product of the two coordinate algebras. -/
private noncomputable def semidirectProductCarrierAlgEquiv
    (H K : CommHopfAlgCat.{u} k)
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H)) :
    (((commHopfAlgCatEquivCogrpCommAlgCat k).inverse.obj
      (Opposite.op A.semidirectProduct) : CommHopfAlgCat.{u} k) : Type u) ≃ₐ[k]
      (H ⊗[k] K) := by
  let _ := A.semidirectProductGrpObj
  exact CommAlgCat.algEquivOfIso
    (A := A.semidirectProduct.X.unop) (B := CommAlgCat.of k (H ⊗[k] K))
    (eqToIso (congrArg Opposite.unop A.semidirectProduct_X))

/-- An internal semidirect product of geometrically connected affine groups is geometrically
connected.

The action changes the group law but not the underlying affine scheme: on coordinate algebras,
the carrier remains the tensor product. This formulation is the one used when multiplication of
two normal closed subgroups is made into a homomorphism by equipping their product with the
conjugation semidirect-product structure. -/
theorem semidirectProduct (H K : CommHopfAlgCat.{u} k)
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H))
    (hH : geometricallyConnectedCommHopfAlgProperty k H)
    (hK : geometricallyConnectedCommHopfAlgProperty k K) :
    geometricallyConnectedCommHopfAlgProperty k
      ((commHopfAlgCatEquivCogrpCommAlgCat k).inverse.obj (Opposite.op A.semidirectProduct)) := by
  let _ := A.semidirectProductGrpObj
  have h := tensorProduct H K hH hK
  rw [geometricallyConnectedCommHopfAlgProperty_iff] at h
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro L _ _
  let eL := Algebra.TensorProduct.congr
    (semidirectProductCarrierAlgEquiv H K A) (AlgEquiv.refl : L ≃ₐ[k] L)
  exact (PrimeSpectrum.homeomorphOfRingEquiv eL.toRingEquiv).connectedSpace_iff.mpr (h L)

end geometricallyConnectedCommHopfAlgProperty

end TauCeti
