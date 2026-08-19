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
coordinate isomorphism is constructed with the general quotient-by-pullback isomorphism and is
then transported through `hopfSpec`.

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

universe u

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{u} k}

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

/-- The coordinate morphism obtained by restricting an ambient isomorphism to the centers. -/
noncomputable def centerCoordinateMap (e : H ≅ K) :
    quotient H (centerDefiningIdeal H) ⟶ quotient K (centerDefiningIdeal K) :=
  liftQuotient (centerDefiningIdeal H)
    (e.hom ≫ mkQuotient K (centerDefiningIdeal K)) <| by
      intro x hx
      change (mkQuotient K (centerDefiningIdeal K)).hom (e.hom.hom x) = 0
      rw [mkQuotient_eq_zero_iff]
      apply HopfIdeal.mem_comap.mp
      rwa [comap_centerDefiningIdeal e]

/-- On quotient classes, restriction to the center applies the ambient isomorphism before taking
the target quotient class. -/
@[simp]
theorem centerCoordinateMap_mk (e : H ≅ K) (x : H) :
    (centerCoordinateMap e).hom
        (Ideal.Quotient.mk (centerDefiningIdeal H).toIdeal x) =
      Ideal.Quotient.mkₐ k (centerDefiningIdeal K).toIdeal (e.hom.hom x) := by
  rw [← Ideal.Quotient.mkₐ_eq_mk (R₁ := k)]
  rw [centerCoordinateMap, liftQuotient_mk, _root_.CommHopfAlgCat.comp_apply,
    mkQuotient_apply]

/-- Restriction to centers commutes with the two ambient quotient morphisms. -/
@[simp]
theorem mkQuotient_comp_centerCoordinateMap (e : H ≅ K) :
    mkQuotient H (centerDefiningIdeal H) ≫ centerCoordinateMap e =
      e.hom ≫ mkQuotient K (centerDefiningIdeal K) :=
  mkQuotient_comp_liftQuotient _ _ _

/-- The map on center coordinates induced by an identity is the identity. -/
@[simp]
theorem centerCoordinateMap_id (H : _root_.CommHopfAlgCat.{u} k) :
    centerCoordinateMap (Iso.refl H) = 𝟙 (quotient H (centerDefiningIdeal H)) := by
  ext q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (centerDefiningIdeal H).toIdeal q
  simp only [Ideal.Quotient.mkₐ_eq_mk]
  rw [centerCoordinateMap_mk]
  rfl

/-- Restriction to center coordinates is compatible with composition of isomorphisms. -/
@[simp]
theorem centerCoordinateMap_trans {L : _root_.CommHopfAlgCat.{u} k}
    (e : H ≅ K) (f : K ≅ L) :
    centerCoordinateMap (e ≪≫ f) = centerCoordinateMap e ≫ centerCoordinateMap f := by
  ext q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (centerDefiningIdeal H).toIdeal q
  simp only [Ideal.Quotient.mkₐ_eq_mk]
  rw [centerCoordinateMap_mk, _root_.CommHopfAlgCat.comp_apply,
    centerCoordinateMap_mk]
  simp only [Ideal.Quotient.mkₐ_eq_mk]
  rw [centerCoordinateMap_mk]
  rfl

/-- The isomorphism on coordinate Hopf algebras obtained by restricting an ambient isomorphism
to the centers. -/
noncomputable def centerCoordinateIso (e : H ≅ K) :
    quotient H (centerDefiningIdeal H) ≅ quotient K (centerDefiningIdeal K) where
  hom := centerCoordinateMap e
  inv := centerCoordinateMap e.symm
  hom_inv_id := by
    ext q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (centerDefiningIdeal H).toIdeal q
    simp only [Ideal.Quotient.mkₐ_eq_mk]
    rw [_root_.CommHopfAlgCat.comp_apply, centerCoordinateMap_mk]
    simp only [Ideal.Quotient.mkₐ_eq_mk]
    rw [centerCoordinateMap_mk]
    simp
  inv_hom_id := by
    ext q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (centerDefiningIdeal K).toIdeal q
    simp only [Ideal.Quotient.mkₐ_eq_mk]
    rw [_root_.CommHopfAlgCat.comp_apply, centerCoordinateMap_mk]
    simp only [Ideal.Quotient.mkₐ_eq_mk]
    rw [centerCoordinateMap_mk]
    simp

/-- The coordinate isomorphism of centers sends the class of `x` to the class of its image under
the ambient isomorphism. -/
@[simp]
theorem centerCoordinateIso_hom_mk (e : H ≅ K) (x : H) :
    (centerCoordinateIso e).hom.hom
        (Ideal.Quotient.mk (centerDefiningIdeal H).toIdeal x) =
      Ideal.Quotient.mkₐ k (centerDefiningIdeal K).toIdeal (e.hom.hom x) := by
  exact centerCoordinateMap_mk e x

/-- An isomorphism of affine group schemes represented by commutative Hopf algebras restricts to
an isomorphism of their center group schemes. -/
noncomputable def centerGroupSchemeIso (e : H ≅ K) :
    centerGroupScheme H ≅ centerGroupScheme K :=
  ((AlgebraicGeometry.hopfSpec (CommRingCat.of k)).mapIso (centerCoordinateIso e).op).symm

end TauCeti.CommHopfAlgCat
