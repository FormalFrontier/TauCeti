/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic

/-!
# Centers and isomorphisms of affine groups

An isomorphism of commutative Hopf algebras carries the ideal defining the center to the ideal
defining the center. Equivalently, the induced isomorphism of affine group schemes restricts to
an isomorphism of their centers.

The proof uses the universal property of `centerDefiningIdeal`: the pullback of a central Hopf
ideal along a bialgebra equivalence is central, so minimality gives both inclusions. The resulting
coordinate isomorphism transports the general quotient-by-pullback isomorphism along this ideal
equality and is then carried through `hopfSpec`.

## Main declarations

* `TauCeti.CommHopfAlgCat.comap_centerDefiningIdeal`: center ideals are preserved by
  isomorphisms.
* `TauCeti.CommHopfAlgCat.centerCoordinateMap`: restriction of an isomorphism to the coordinate
  Hopf algebras of the centers.
* `TauCeti.CommHopfAlgCat.centerCoordinateIso`: the resulting coordinate isomorphism.
* `TauCeti.CommHopfAlgCat.centerGroupSchemeIso`: the corresponding isomorphism of center group
  schemes.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.k and §2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This supplies the isomorphism invariance of the center `Z(G)` required by Layer 6, "Reductive and
semisimple groups", of `TauCetiRoadmap/ReductiveGroups/README.md`. It makes the center canonical
for the subsequent central-isogeny and adjoint-form constructions.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k]

section Coordinate

variable {H K : _root_.CommHopfAlgCat.{v} k}

/-- **An isomorphism of commutative Hopf algebras preserves the ideal defining the center.** -/
@[simp]
theorem comap_centerDefiningIdeal (e : H ≅ K) :
    (centerDefiningIdeal K).comap e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 = centerDefiningIdeal H := by
  let he : Function.Bijective e.hom.hom := ConcreteCategory.bijective_of_isIso e.hom
  let he' : Function.Bijective e.inv.hom := ConcreteCategory.bijective_of_isIso e.inv
  have hforward : centerDefiningIdeal H ≤
      (centerDefiningIdeal K).comap e.hom.hom he.2 := by
    rw [centerDefiningIdeal_le_iff]
    exact (isCentral_centerDefiningIdeal K).comap_of_bijective e.hom.hom he.1 he.2
  have hbackward : centerDefiningIdeal K ≤
      (centerDefiningIdeal H).comap e.inv.hom he'.2 := by
    rw [centerDefiningIdeal_le_iff]
    exact (isCentral_centerDefiningIdeal H).comap_of_bijective e.inv.hom he'.1 he'.2
  apply le_antisymm
  · intro x hx
    have hxK : e.hom.hom x ∈ centerDefiningIdeal K := HopfIdeal.mem_comap.mp hx
    have hxH : e.inv.hom (e.hom.hom x) ∈ centerDefiningIdeal H :=
      HopfIdeal.mem_comap.mp (hbackward hxK)
    simpa using hxH
  · exact hforward

/-- The isomorphism on coordinate Hopf algebras obtained by restricting an ambient isomorphism
to the centers. -/
@[expose] noncomputable def centerCoordinateIso (e : H ≅ K) :
    quotient H (centerDefiningIdeal H) ≅ quotient K (centerDefiningIdeal K) :=
  eqToIso (congrArg (quotient H) (comap_centerDefiningIdeal e).symm) ≪≫
    quotientIsoOfIso e (centerDefiningIdeal K)

/-- The coordinate morphism obtained by restricting an ambient isomorphism to the centers. -/
@[expose] noncomputable def centerCoordinateMap (e : H ≅ K) :
    quotient H (centerDefiningIdeal H) ⟶ quotient K (centerDefiningIdeal K) :=
  (centerCoordinateIso e).hom

/-- The forward morphism of the coordinate isomorphism is the restricted coordinate map. -/
@[simp]
theorem centerCoordinateIso_hom (e : H ≅ K) :
    (centerCoordinateIso e).hom = centerCoordinateMap e :=
  rfl

/-- Restriction to centers commutes with the two ambient quotient morphisms. -/
@[simp]
theorem mkQuotient_comp_centerCoordinateMap (e : H ≅ K) :
    mkQuotient H (centerDefiningIdeal H) ≫ centerCoordinateMap e =
      e.hom ≫ mkQuotient K (centerDefiningIdeal K) := by
  rw [centerCoordinateMap, centerCoordinateIso]
  simp

/-- On quotient classes, restriction to the center applies the ambient isomorphism before taking
the target quotient class. -/
@[simp]
theorem centerCoordinateMap_mk (e : H ≅ K) (x : H) :
    (centerCoordinateMap e).hom
        (Ideal.Quotient.mk (centerDefiningIdeal H).toIdeal x) =
      Ideal.Quotient.mkₐ k (centerDefiningIdeal K).toIdeal (e.hom.hom x) := by
  calc
    (centerCoordinateMap e).hom
        (Ideal.Quotient.mk (centerDefiningIdeal H).toIdeal x) =
        (mkQuotient H (centerDefiningIdeal H) ≫ centerCoordinateMap e).hom x := by
      rw [_root_.CommHopfAlgCat.comp_apply, mkQuotient_apply,
        Ideal.Quotient.mkₐ_eq_mk]
    _ = (e.hom ≫ mkQuotient K (centerDefiningIdeal K)).hom x :=
      BialgHom.congr_fun
        (congrArg _root_.CommHopfAlgCat.Hom.hom
          (mkQuotient_comp_centerCoordinateMap e)) x
    _ = Ideal.Quotient.mkₐ k (centerDefiningIdeal K).toIdeal (e.hom.hom x) := by
      rw [_root_.CommHopfAlgCat.comp_apply, mkQuotient_apply]

/-- The map on center coordinates induced by an identity is the identity. -/
@[simp]
theorem centerCoordinateMap_refl (H : _root_.CommHopfAlgCat.{v} k) :
    centerCoordinateMap (Iso.refl H) = 𝟙 (quotient H (centerDefiningIdeal H)) := by
  let _ : Epi (mkQuotient H (centerDefiningIdeal H)) :=
    ConcreteCategory.epi_of_surjective _
      (Ideal.Quotient.mkₐ_surjective k (centerDefiningIdeal H).toIdeal)
  rw [← cancel_epi (mkQuotient H (centerDefiningIdeal H))]
  simp

/-- Restriction to center coordinates is compatible with composition of isomorphisms. -/
@[simp]
theorem centerCoordinateMap_trans {L : _root_.CommHopfAlgCat.{v} k}
    (e : H ≅ K) (f : K ≅ L) :
    centerCoordinateMap (e ≪≫ f) = centerCoordinateMap e ≫ centerCoordinateMap f := by
  let _ : Epi (mkQuotient H (centerDefiningIdeal H)) :=
    ConcreteCategory.epi_of_surjective _
      (Ideal.Quotient.mkₐ_surjective k (centerDefiningIdeal H).toIdeal)
  rw [← cancel_epi (mkQuotient H (centerDefiningIdeal H))]
  calc
    mkQuotient H (centerDefiningIdeal H) ≫ centerCoordinateMap (e ≪≫ f) =
        (e ≪≫ f).hom ≫ mkQuotient L (centerDefiningIdeal L) :=
      mkQuotient_comp_centerCoordinateMap (e ≪≫ f)
    _ = e.hom ≫ (f.hom ≫ mkQuotient L (centerDefiningIdeal L)) := by
      rw [Iso.trans_hom, Category.assoc]
    _ = e.hom ≫ (mkQuotient K (centerDefiningIdeal K) ≫ centerCoordinateMap f) := by
      rw [mkQuotient_comp_centerCoordinateMap]
    _ = (e.hom ≫ mkQuotient K (centerDefiningIdeal K)) ≫ centerCoordinateMap f :=
      (Category.assoc _ _ _).symm
    _ = (mkQuotient H (centerDefiningIdeal H) ≫ centerCoordinateMap e) ≫
        centerCoordinateMap f := by
      rw [mkQuotient_comp_centerCoordinateMap]
    _ = mkQuotient H (centerDefiningIdeal H) ≫
        (centerCoordinateMap e ≫ centerCoordinateMap f) :=
      Category.assoc _ _ _

/-- The inverse morphism of the coordinate isomorphism is restriction along the inverse ambient
isomorphism. -/
@[simp]
theorem centerCoordinateIso_inv (e : H ≅ K) :
    (centerCoordinateIso e).inv = centerCoordinateMap e.symm := by
  rw [← cancel_mono (centerCoordinateIso e).hom]
  rw [Iso.inv_hom_id, centerCoordinateIso_hom, ← centerCoordinateMap_trans,
    Iso.symm_self_id, centerCoordinateMap_refl]

end Coordinate

section Scheme

variable {H K : _root_.CommHopfAlgCat.{u} k}

/-- An isomorphism of affine group schemes represented by commutative Hopf algebras restricts to
an isomorphism of their center group schemes. -/
@[expose] noncomputable def centerGroupSchemeIso (e : H ≅ K) :
    centerGroupScheme H ≅ centerGroupScheme K :=
  ((AlgebraicGeometry.hopfSpec (CommRingCat.of k)).mapIso (centerCoordinateIso e).op).symm

/-- The forward center-scheme isomorphism is induced contravariantly by restriction along the
inverse ambient isomorphism. -/
@[simp]
theorem centerGroupSchemeIso_hom (e : H ≅ K) :
    (centerGroupSchemeIso e).hom =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map
        (centerCoordinateMap e.symm).op := by
  rw [centerGroupSchemeIso]
  simp

/-- The inverse center-scheme isomorphism is induced contravariantly by restriction along the
forward ambient isomorphism. -/
@[simp]
theorem centerGroupSchemeIso_inv (e : H ≅ K) :
    (centerGroupSchemeIso e).inv =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map
        (centerCoordinateMap e).op := by
  rw [centerGroupSchemeIso]
  simp

/-- The isomorphism of centers commutes with their inclusions into the ambient affine group
schemes. -/
theorem centerGroupSchemeIso_hom_comp_centerGroupSchemeι (e : H ≅ K) :
    (centerGroupSchemeIso e).hom ≫ centerGroupSchemeι K =
      centerGroupSchemeι H ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map e.inv.op := by
  rw [centerGroupSchemeIso_hom]
  change (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map
      (centerCoordinateMap e.symm).op ≫ quotientSpecι K (centerDefiningIdeal K) =
    quotientSpecι H (centerDefiningIdeal H) ≫
      (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map e.inv.op
  rw [quotientSpecι_def, quotientSpecι_def,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map_comp,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map_comp,
    ← op_comp, ← op_comp, mkQuotient_comp_centerCoordinateMap, Iso.symm_hom]

/-- The center-scheme isomorphism induced by the identity is the identity. -/
@[simp]
theorem centerGroupSchemeIso_refl (H : _root_.CommHopfAlgCat.{u} k) :
    centerGroupSchemeIso (Iso.refl H) = Iso.refl (centerGroupScheme H) := by
  apply Iso.ext
  simp

/-- Center-scheme isomorphisms induced by ambient isomorphisms respect composition. -/
@[simp]
theorem centerGroupSchemeIso_trans {L : _root_.CommHopfAlgCat.{u} k}
    (e : H ≅ K) (f : K ≅ L) :
    centerGroupSchemeIso (e ≪≫ f) = centerGroupSchemeIso e ≪≫ centerGroupSchemeIso f := by
  apply Iso.ext
  simp

end Scheme

end TauCeti.CommHopfAlgCat
