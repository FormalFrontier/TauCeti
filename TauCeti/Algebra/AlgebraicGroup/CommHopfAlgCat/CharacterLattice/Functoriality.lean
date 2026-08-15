/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Basic
public import TauCeti.Algebra.Bialgebra.GroupLike.Map

/-!
# Functoriality of geometric character groups

A morphism of commutative Hopf algebras sends group-like elements to group-like elements after
extension to an algebraic closure. This gives a morphism between geometric character groups. The
map is equivariant for the absolute-Galois actions because scalar extension applies the Hopf map
only to the second tensor factor.

The resulting additive maps assemble the geometric character groups into a functor from
commutative Hopf algebras to integral representations of the absolute Galois group. Restricting
this functor to coordinate rings of tori is the character-lattice functor used in Galois descent.

## Main declarations

* `TauCeti.CommHopfAlgCat.geometricCharacterMap`: the map on geometric characters induced by a
  Hopf-algebra morphism.
* `TauCeti.CommHopfAlgCat.additiveCharacterMap`: its integral-linear additive form.
* `TauCeti.CommHopfAlgCat.geometricCharacterRepresentation`: the absolute-Galois representation
  on geometric characters.
* `TauCeti.CommHopfAlgCat.geometricCharacterFunctor`: functoriality of that representation.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti

universe u

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

/-- A morphism of commutative Hopf algebras induces a homomorphism of their geometric character
groups by scalar extension and restriction to group-like elements. -/
noncomputable def geometricCharacterMap {H K : _root_.CommHopfAlgCat.{u} k} (f : H ⟶ K) :
    geometricCharacterGroup H →* geometricCharacterGroup K :=
  TauCeti.GroupLike.map (baseChangeMap (K := AlgebraicClosure k) f).hom

/-- The value underlying the image of a geometric character is obtained by applying the
base-changed Hopf-algebra morphism. -/
@[simp]
theorem val_geometricCharacterMap {H K : _root_.CommHopfAlgCat.{u} k} (f : H ⟶ K)
    (x : geometricCharacterGroup H) :
    (geometricCharacterMap f x).val =
      (baseChangeMap (K := AlgebraicClosure k) f).hom x.val := by
  rw [geometricCharacterMap, TauCeti.GroupLike.val_map]

private theorem baseChangeMap_smul {H K : _root_.CommHopfAlgCat.{u} k} (f : H ⟶ K)
    (sigma : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (x : AlgebraicClosure k ⊗[k] H) :
    (baseChangeMap (K := AlgebraicClosure k) f).hom (sigma • x) =
      sigma • (baseChangeMap (K := AlgebraicClosure k) f).hom x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul a x =>
      rw [ScalarAut.smul_tmul, baseChangeMap_apply_tmul, baseChangeMap_apply_tmul,
        ScalarAut.smul_tmul]

/-- The map on geometric characters commutes with the absolute-Galois action. -/
@[simp]
theorem geometricCharacterMap_smul {H K : _root_.CommHopfAlgCat.{u} k} (f : H ⟶ K)
    (sigma : Field.absoluteGaloisGroup k) (x : geometricCharacterGroup H) :
    geometricCharacterMap f (sigma • x) = sigma • geometricCharacterMap f x := by
  apply _root_.GroupLike.val_injective
  simp only [val_geometricCharacterMap, val_smul]
  unfold Field.absoluteGaloisGroup at sigma
  exact baseChangeMap_smul f sigma x.val

/-- Mapping geometric characters along an identity morphism is the identity. -/
@[simp]
theorem geometricCharacterMap_id (H : _root_.CommHopfAlgCat.{u} k) :
    geometricCharacterMap (𝟙 H) = MonoidHom.id (geometricCharacterGroup H) := by
  have h := congrArg (fun q ↦ q.hom)
    ((baseChangeFunctor (K := AlgebraicClosure k)).map_id H)
  change (baseChangeMap (K := AlgebraicClosure k) (𝟙 H)).hom =
    _root_.BialgHom.id (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H) at h
  simp only [geometricCharacterMap]
  rw [h, TauCeti.GroupLike.map_id]

/-- Mapping geometric characters respects composition of Hopf-algebra morphisms. -/
@[simp]
theorem geometricCharacterMap_comp {H K L : _root_.CommHopfAlgCat.{u} k}
    (f : H ⟶ K) (g : K ⟶ L) :
    geometricCharacterMap (f ≫ g) = (geometricCharacterMap g).comp (geometricCharacterMap f) := by
  have h := congrArg (fun q ↦ q.hom)
    ((baseChangeFunctor (K := AlgebraicClosure k)).map_comp f g)
  change (baseChangeMap (K := AlgebraicClosure k) (f ≫ g)).hom =
    (baseChangeMap (K := AlgebraicClosure k) g).hom.comp
      (baseChangeMap (K := AlgebraicClosure k) f).hom at h
  simp only [geometricCharacterMap]
  rw [h, TauCeti.GroupLike.map_comp]

/-- The integral-linear map on additive geometric character groups induced by a Hopf-algebra
morphism. -/
noncomputable def additiveCharacterMap {H K : _root_.CommHopfAlgCat.{u} k} (f : H ⟶ K) :
    additiveCharacterGroup H →ₗ[ℤ] additiveCharacterGroup K :=
  (geometricCharacterMap f).toAdditive.toIntLinearMap

/-- Passing to the underlying multiplicative character identifies `additiveCharacterMap` with
`geometricCharacterMap`. -/
@[simp]
theorem additiveCharacterMap_toMul {H K : _root_.CommHopfAlgCat.{u} k} (f : H ⟶ K)
    (x : additiveCharacterGroup H) :
    (additiveCharacterMap f x).toMul = geometricCharacterMap f x.toMul :=
  by
    rw [additiveCharacterMap]
    rfl

/-- The additive character map is equivariant for the absolute-Galois action. -/
@[simp]
theorem additiveCharacterMap_smul {H K : _root_.CommHopfAlgCat.{u} k} (f : H ⟶ K)
    (sigma : Field.absoluteGaloisGroup k) (x : additiveCharacterGroup H) :
    additiveCharacterMap f (sigma • x) = sigma • additiveCharacterMap f x := by
  apply Additive.toMul.injective
  simp only [additiveCharacterMap_toMul, toMul_smul, geometricCharacterMap_smul]

/-- The additive character map of an identity morphism is the identity linear map. -/
@[simp]
theorem additiveCharacterMap_id (H : _root_.CommHopfAlgCat.{u} k) :
    additiveCharacterMap (𝟙 H) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  rw [additiveCharacterMap_toMul, geometricCharacterMap_id, MonoidHom.id_apply,
    LinearMap.id_apply]

/-- Additive character maps respect composition of Hopf-algebra morphisms. -/
@[simp]
theorem additiveCharacterMap_comp {H K L : _root_.CommHopfAlgCat.{u} k}
    (f : H ⟶ K) (g : K ⟶ L) :
    additiveCharacterMap (f ≫ g) = additiveCharacterMap g ∘ₗ additiveCharacterMap f := by
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  rw [additiveCharacterMap_toMul, LinearMap.comp_apply, additiveCharacterMap_toMul,
    additiveCharacterMap_toMul, geometricCharacterMap_comp, MonoidHom.comp_apply]

/-- The geometric character group as an integral representation of the absolute Galois group. -/
noncomputable abbrev geometricCharacterRepresentation (H : _root_.CommHopfAlgCat.{u} k) :
    Rep.{u} ℤ (Field.absoluteGaloisGroup k) :=
  Rep.ofMulDistribMulAction (Field.absoluteGaloisGroup k) (geometricCharacterGroup H)

/-- The additive character map bundled as an intertwining map between the geometric-character
representations. -/
private noncomputable def additiveCharacterIntertwiningMap
    {H K : _root_.CommHopfAlgCat.{u} k} (f : H ⟶ K) :
    (Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
      (geometricCharacterGroup H)).IntertwiningMap
        (Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
          (geometricCharacterGroup K)) where
  __ := additiveCharacterMap f
  isIntertwining' := fun sigma ↦ by
    apply LinearMap.ext
    intro x
    -- The bundled representation records the same action as the scalar notation used by the
    -- equivariance theorem; expose that representation wrapper at this boundary.
    change additiveCharacterMap f (sigma • x) = sigma • additiveCharacterMap f x
    exact additiveCharacterMap_smul f sigma x

@[simp]
private theorem additiveCharacterIntertwiningMap_apply
    {H K : _root_.CommHopfAlgCat.{u} k} (f : H ⟶ K) (x : additiveCharacterGroup H) :
    additiveCharacterIntertwiningMap f x = additiveCharacterMap f x := by
  rfl

/-- The equivariant morphism of geometric-character representations induced by a Hopf-algebra
morphism. -/
noncomputable def geometricCharacterRepresentationMap
    {H K : _root_.CommHopfAlgCat.{u} k} (f : H ⟶ K) :
    geometricCharacterRepresentation H ⟶ geometricCharacterRepresentation K :=
  Rep.ofHom (additiveCharacterIntertwiningMap f)

/-- Evaluation of the representation morphism induced on geometric characters. -/
@[simp]
theorem geometricCharacterRepresentationMap_apply
    {H K : _root_.CommHopfAlgCat.{u} k} (f : H ⟶ K) (x : additiveCharacterGroup H) :
    (geometricCharacterRepresentationMap f).hom x = additiveCharacterMap f x :=
  by
    -- The categorical morphism is an `ofHom` wrapper around this intertwining map.
    change additiveCharacterIntertwiningMap f x = additiveCharacterMap f x
    exact additiveCharacterIntertwiningMap_apply f x

/-- Geometric character groups and their absolute-Galois actions are functorial in the
coordinate Hopf algebra. -/
noncomputable def geometricCharacterFunctor :
    _root_.CommHopfAlgCat.{u} k ⥤ Rep.{u} ℤ (Field.absoluteGaloisGroup k) where
  obj := geometricCharacterRepresentation
  map := geometricCharacterRepresentationMap
  map_id H := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    -- After forgetting the two categorical wrappers, functoriality is the linear-map identity.
    change additiveCharacterMap (𝟙 H) = LinearMap.id
    exact additiveCharacterMap_id H
  map_comp f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    -- After forgetting the two categorical wrappers, functoriality is linear-map composition.
    change additiveCharacterMap (f ≫ g) = additiveCharacterMap g ∘ₗ additiveCharacterMap f
    exact additiveCharacterMap_comp f g

/-- The object part of `geometricCharacterFunctor` is the geometric-character representation. -/
@[simp]
theorem geometricCharacterFunctor_obj (H : _root_.CommHopfAlgCat.{u} k) :
    (geometricCharacterFunctor (k := k)).obj H = geometricCharacterRepresentation H := by
  rw [geometricCharacterFunctor]

end CommHopfAlgCat

end TauCeti
