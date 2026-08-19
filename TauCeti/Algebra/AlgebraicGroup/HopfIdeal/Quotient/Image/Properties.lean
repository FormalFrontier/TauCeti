/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# Geometric properties of affine group images

Let `f : H ⟶ K` be a morphism of commutative Hopf algebras over a field. Contravariantly,
`f` represents a homomorphism `Spec K ⟶ Spec H`, whose scheme-theoretic image has coordinate
Hopf algebra `CommHopfAlgCat.image f = H / ker f`. The canonical map from this image algebra to
`K` is injective. Tensoring it with any field extension remains injective, so geometric
connectedness and geometric reducedness descend from the source `Spec K` to the image.

The image is also finite type whenever the ambient affine group `Spec H` is finite type, since
its coordinate algebra is a quotient of `H`. Together these facts provide the image-property
part of the subgroup-generation argument used for the unipotent radical: the image of the
multiplication map from two connected geometrically reduced subgroups is again connected and
geometrically reduced.

## Main declarations

* `TauCeti.CommHopfAlgCat.image_finiteType`: a closed image in a finite-type affine group is
  finite type.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty.image`: the image of a geometrically
  connected affine group is geometrically connected.
* `TauCeti.geometricallyReducedCommHopfAlgProperty.image`: the image of a geometrically reduced
  affine group is geometrically reduced.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.a and §6.a.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15--16.

This is image infrastructure for Layer 5, "The unipotent radical", of the ReductiveGroups
roadmap. The maximality construction takes scheme-theoretic images of multiplication maps and
needs connectedness and reducedness to survive that operation.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace CommHopfAlgCat

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}

/-- The coordinate algebra of the scheme-theoretic image is finite type when the ambient
coordinate algebra is finite type.

The assumption is on `H`, the coordinate algebra of the target affine group, because
`image f = H / ker f`. No finiteness assumption on the source coordinate algebra `K` is needed.
-/
theorem image_finiteType (f : H ⟶ K) [Algebra.FiniteType k H] :
    Algebra.FiniteType k (image f) :=
  Algebra.FiniteType.of_surjective (mkImage f).hom.toAlgHom (mkImage_surjective f)

/-- The image coordinate algebra is reduced whenever the source coordinate algebra is reduced.

Contravariantly, the scheme-theoretic image of a morphism from a reduced affine group is
reduced. This is the ground-field form of the geometric result below. -/
theorem image_isReduced (f : H ⟶ K) [IsReduced K] : IsReduced (image f) :=
  isReduced_of_injective (imageι f).hom.toAlgHom.toRingHom (imageι_injective f)

/-- After any extension of the ground field, the canonical inclusion of the image coordinate
algebra into the source coordinate algebra remains injective. -/
private theorem image_baseChange_injective (f : H ⟶ K)
    (L : Type u) [Field L] [Algebra k L] :
    Function.Injective
      (Algebra.TensorProduct.map (imageι f).hom.toAlgHom (AlgHom.id k L)) := by
  change Function.Injective
    (TensorProduct.map (imageι f).hom.toLinearMap (LinearMap.id : L →ₗ[k] L))
  exact TensorProduct.map_injective_of_flat_flat
    (imageι f).hom.toLinearMap (LinearMap.id : L →ₗ[k] L)
      (imageι_injective f) Function.injective_id

end CommHopfAlgCat

namespace geometricallyConnectedCommHopfAlgProperty

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}

/-- The scheme-theoretic image of a geometrically connected affine group is geometrically
connected.

For every field extension, the image coordinate algebra embeds in the source coordinate
algebra. Connectedness of the latter's prime spectrum therefore descends to the former. -/
theorem image (f : H ⟶ K) (hK : geometricallyConnectedCommHopfAlgProperty k K) :
    geometricallyConnectedCommHopfAlgProperty k (CommHopfAlgCat.image f) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff] at hK ⊢
  intro L _ _
  exact connectedSpace_primeSpectrum_of_injective
    (Algebra.TensorProduct.map
      (CommHopfAlgCat.imageι f).hom.toAlgHom (AlgHom.id k L)).toRingHom
    (CommHopfAlgCat.image_baseChange_injective f L)

end geometricallyConnectedCommHopfAlgProperty

namespace geometricallyReducedCommHopfAlgProperty

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}

/-- The scheme-theoretic image of a geometrically reduced affine group is geometrically reduced.

After every field extension, reducedness descends along the injective map from the image
coordinate algebra to the source coordinate algebra. -/
theorem image (f : H ⟶ K) (hK : geometricallyReducedCommHopfAlgProperty k K) :
    geometricallyReducedCommHopfAlgProperty k (CommHopfAlgCat.image f) := by
  rw [geometricallyReducedCommHopfAlgProperty_iff] at hK ⊢
  intro L _ _
  let _ := hK L
  exact isReduced_of_injective
    (Algebra.TensorProduct.map
      (CommHopfAlgCat.imageι f).hom.toAlgHom (AlgHom.id k L)).toRingHom
    (CommHopfAlgCat.image_baseChange_injective f L)

end geometricallyReducedCommHopfAlgProperty

end

end TauCeti
