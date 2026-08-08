/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Projections of Hopf spectra

This file computes the underlying scheme maps of Mathlib's `AlgebraicGeometry.hopfSpec` on an
arbitrary same-universe commutative Hopf algebra.  It identifies the underlying scheme with the
ordinary spectrum, the structural morphism with the algebra structure map, the multiplication
source with the standard affine fibre product, and the group operations with the counit,
comultiplication, and antipode.

These lemmas provide the common projection boundary used by concrete affine group schemes.  The
same-universe restriction is inherited from Mathlib's current `hopfSpec` construction.

## Main declarations

* `TauCeti.hopfSpec_obj_X_left`: the underlying scheme of a Hopf spectrum.
* `TauCeti.hopfSpec_map_hom_hom_left`: the underlying scheme morphism of a Hopf-spectrum map.
* `TauCeti.hopfSpec_obj_X_hom`: its structural morphism.
* `TauCeti.hopfSpec_obj_eq_asOver`: its bundled identification with the group object on the
  ordinary spectrum.
* `TauCeti.hopfSpec_obj_tensor_X_left`: the source of its multiplication.
* `TauCeti.algSpec_map_left_ofAlgHom`: the underlying spectrum map of an algebra morphism.
* `TauCeti.hopfSpec_obj_one_left`, `TauCeti.hopfSpec_obj_mul_left`, and
  `TauCeti.hopfSpec_obj_inv_left`: its three group operations.
-/

public section

open CategoryTheory

namespace TauCeti

open AlgebraicGeometry MonObj MonoidalCategory

universe u

variable (R : Type u) [CommRing R]

/-- The scheme underlying the Hopf spectrum of `H` is its ordinary spectrum. -/
@[simp↓]
lemma hopfSpec_obj_X_left (H : CommHopfAlgCat.{u} R) :
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X.left = Spec (CommRingCat.of H) :=
  rfl

/-- The structural morphism of a Hopf spectrum is induced by its algebra structure map. -/
@[simp↓]
lemma hopfSpec_obj_X_hom (H : CommHopfAlgCat.{u} R) :
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X.hom =
        eqToHom (hopfSpec_obj_X_left R H) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R H)) := by
  simpa only [eqToHom_refl, Category.comp_id] using
    (conj_eqToHom_iff_heq
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op H)).X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      (hopfSpec_obj_X_left R H) rfl).2 (by
        exact heq_of_eq (AlgebraicGeometry.algSpec_obj_hom
          (R := CommRingCat.of R) (Opposite.op (CommAlgCat.of R H))))

/-- The multiplication source of a Hopf spectrum is the standard affine fibre product of two
copies of its underlying spectrum over the base. -/
@[simp↓]
lemma hopfSpec_obj_tensor_X_left (H : CommHopfAlgCat.{u} R) :
    ((((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X ⊗
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
          (Opposite.op H)).X).left) =
      Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R H)))
        (Spec.map (CommRingCat.ofHom (algebraMap R H))) := by
  rw [Over.tensorObj_left]
  have h : ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X.hom ≍
        Spec.map (CommRingCat.ofHom (algebraMap R H)) := by
    rw [hopfSpec_obj_X_hom]
    exact eqToHom_comp_heq _ _
  cases hopfSpec_obj_X_left R H
  exact congrArg (fun k ↦ Limits.pullback k k) (eq_of_heq h)

/-- Applying `algSpec` to an algebra homomorphism has underlying scheme map `Spec.map` of its
underlying ring homomorphism.

Mathlib's `algSpec_map_left` leaves this map expressed through the `CommAlgCat`/under-category
equivalence, and no public computation lemma exposes the resulting `Under.Hom.right`. The final
reduction is therefore definitional and is localized here. -/
@[simp↓]
lemma algSpec_map_left_ofAlgHom {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    ((AlgebraicGeometry.algSpec (CommRingCat.of R)).map
      (CommAlgCat.ofHom f).op).left =
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [AlgebraicGeometry.algSpec_map_left]
  rfl

/-- The scheme morphism underlying the contravariant `hopfSpec` image of a Hopf-algebra
morphism is the corresponding map of affine spectra. -/
@[simp↓]
lemma hopfSpec_map_hom_hom_left {A B : CommHopfAlgCat.{u} R} (f : A ⟶ B) :
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op).hom.hom.left =
      Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) := by
  rw [Functor.comp_map, Functor.mapGrp_map_hom_hom]
  exact algSpec_map_left_ofAlgHom R f.hom.toAlgHom

/-- Mathlib's `hopfSpec` object is the group object on the ordinary spectrum.

This bundled identification carries the group structure across the two instance paths.
Mathlib's operation computation lemmas are stated for `(Spec H).asOver (Spec R)`, while
`hopfSpec` reaches that group object through the Hopf-algebra/cogroup equivalence. -/
lemma hopfSpec_obj_eq_asOver (H : CommHopfAlgCat.{u} R) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H) =
      Grp.mk ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) :=
  rfl

/-- The unit of a Hopf spectrum is induced by the counit of its coordinate Hopf algebra. -/
@[simp]
lemma hopfSpec_obj_one_left (H : CommHopfAlgCat.{u} R) :
    η[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X].left =
      Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom R H)) ≫
        eqToHom (hopfSpec_obj_X_left R H).symm := by
  simpa only [eqToHom_refl, Category.id_comp] using
    (conj_eqToHom_iff_heq
      η[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op H)).X].left
      (Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom R H)))
      rfl (hopfSpec_obj_X_left R H)).2 (by
        rw [hopfSpec_obj_eq_asOver]
        exact heq_of_eq (AlgebraicGeometry.one_spec_asOver_spec_left
          (R := CommRingCat.of R) (A := CommRingCat.of H)))

/-- Multiplication on a Hopf spectrum is induced by the comultiplication of its coordinate Hopf
algebra. -/
@[simp]
lemma hopfSpec_obj_mul_left (H : CommHopfAlgCat.{u} R) :
    μ[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X].left =
      eqToHom (hopfSpec_obj_tensor_X_left R H) ≫
        (pullbackSpecIso R H H).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R H)) ≫
        eqToHom (hopfSpec_obj_X_left R H).symm := by
  simpa only [Category.assoc] using
    (conj_eqToHom_iff_heq
      μ[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op H)).X].left
      ((pullbackSpecIso R H H).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R H)))
      (hopfSpec_obj_tensor_X_left R H) (hopfSpec_obj_X_left R H)).2 (by
        rw [hopfSpec_obj_eq_asOver]
        exact heq_of_eq (AlgebraicGeometry.mul_spec_asOver_spec_left
          (R := CommRingCat.of R) (A := CommRingCat.of H)))

/-- Inversion on a Hopf spectrum is induced by the antipode of its coordinate Hopf algebra. -/
@[simp]
lemma hopfSpec_obj_inv_left (H : CommHopfAlgCat.{u} R) :
    ι[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X].left =
      eqToHom (hopfSpec_obj_X_left R H) ≫
        Spec.map (CommRingCat.ofHom
          (HopfAlgebra.antipodeAlgHom R H).toRingHom) ≫
        eqToHom (hopfSpec_obj_X_left R H).symm := by
  apply (conj_eqToHom_iff_heq _ _
    (hopfSpec_obj_X_left R H) (hopfSpec_obj_X_left R H)).2
  rw [hopfSpec_obj_eq_asOver]
  exact heq_of_eq (algSpec_map_left_ofAlgHom R
    (HopfAlgebra.antipodeAlgHom R H))

end TauCeti
