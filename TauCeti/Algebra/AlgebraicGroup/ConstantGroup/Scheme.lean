/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Constant finite group schemes

For a finite group `G` and a commutative ring `R`, this file applies relative spectrum to the
Hopf algebra of functions `G → R`.  The result is the constant affine group scheme associated
to `G`.  A group homomorphism induces a morphism of these group schemes in the same direction,
contravariantly to pullback of coordinate functions.

The structural morphism of a constant finite group scheme is finite and étale.  Finiteness
comes from the finite free function algebra, while étaleness is the scheme-side form of the
finite-product étaleness proved for the coordinate ring.

This is the scheme-side representer required for the identity-component and component-group
milestone in Layer 3 of the ReductiveGroups roadmap.  Once the component coordinate morphism is
available, its relative spectrum has this object as target; identifying that morphism with the
fppf quotient remains downstream.

## Main declarations

* `TauCeti.ConstantGroup.groupScheme`: the constant affine group scheme attached to `G`.
* `TauCeti.ConstantGroup.groupSchemeMap`: the group-scheme morphism induced by a group
  homomorphism.
* `TauCeti.ConstantGroup.schemePointsMulEquiv`: the canonical comparison between algebra-valued
  coordinate points and scheme-valued points.
* `TauCeti.ConstantGroup.isFinite_groupScheme`: the structural morphism is finite.
* `TauCeti.ConstantGroup.etale_groupScheme`: the structural morphism is étale.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 2.a.
-/

public section

open CategoryTheory Opposite WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.ConstantGroup

open AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [Finite G]

/-- The constant affine group scheme attached to a finite group `G` over `R`. -/
noncomputable def groupScheme : Grp (Over (Spec (CommRingCat.of R))) :=
  (hopfSpec (CommRingCat.of R)).obj
    (op (CommHopfAlgCat.of R (coordinateRing R G)))

/-- The constant group scheme is relative spectrum applied to its coordinate Hopf algebra. -/
theorem groupScheme_def :
    groupScheme R G =
      (hopfSpec (CommRingCat.of R)).obj
        (op (CommHopfAlgCat.of R (coordinateRing R G))) := by
  rfl

/-- The scheme underlying the constant group scheme is the spectrum of its function algebra. -/
@[simp]
theorem groupScheme_X_left :
    (groupScheme R G).X.left = Spec (CommRingCat.of (coordinateRing R G)) := by
  simpa only [groupScheme] using
    hopfSpec_obj_X_left R (CommHopfAlgCat.of R (coordinateRing R G))

/-- The structural morphism of the constant group scheme is induced by the scalar inclusion into
its function algebra. -/
@[simp]
theorem groupScheme_X_hom :
    (groupScheme R G).X.hom =
      eqToHom (groupScheme_X_left R G) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (coordinateRing R G))) := by
  simpa only [groupScheme] using
    hopfSpec_obj_X_hom R (CommHopfAlgCat.of R (coordinateRing R G))

variable {G}

/-- A homomorphism of finite groups induces a morphism of their constant group schemes. -/
noncomputable def groupSchemeMap {H : Type u} [Group H] [Finite H] (f : G →* H) :
    groupScheme R G ⟶ groupScheme R H :=
  (hopfSpec (CommRingCat.of R)).map
    (CommHopfAlgCat.ofHom (coordinateBialgHom R G H f)).op

/-- The constant-group-scheme morphism is relative spectrum applied to pullback of coordinate
functions. -/
theorem groupSchemeMap_def {H : Type u} [Group H] [Finite H] (f : G →* H) :
    groupSchemeMap R f =
      eqToHom (groupScheme_def R G) ≫
        (hopfSpec (CommRingCat.of R)).map
          (CommHopfAlgCat.ofHom (coordinateBialgHom R G H f)).op ≫
        eqToHom (groupScheme_def R H).symm := by
  apply (conj_eqToHom_iff_heq _ _
    (groupScheme_def R G) (groupScheme_def R H)).2
  unfold groupSchemeMap
  rfl

/-- The underlying scheme map of `groupSchemeMap f` is spectrum applied to pullback of
coordinate functions along `f`. -/
@[simp]
theorem groupSchemeMap_hom_left {H : Type u} [Group H] [Finite H] (f : G →* H) :
    (groupSchemeMap R f).hom.hom.left =
      eqToHom (groupScheme_X_left R G) ≫
        Spec.map (CommRingCat.ofHom (coordinateMap R G H f).toRingHom) ≫
        eqToHom (groupScheme_X_left R H).symm := by
  apply (conj_eqToHom_iff_heq _ _
    (groupScheme_X_left R G) (groupScheme_X_left R H)).2
  unfold groupSchemeMap
  rw [Functor.comp_map, Functor.mapGrp_map_hom_hom]
  rw [← coordinateBialgHom_toAlgHom R G H f]
  exact heq_of_eq
    (algSpec_map_left_ofAlgHom R (coordinateBialgHom R G H f).toAlgHom)

/-- The identity group homomorphism induces the identity morphism of constant group schemes. -/
@[simp]
theorem groupSchemeMap_id :
    groupSchemeMap R (MonoidHom.id G) = 𝟙 (groupScheme R G) := by
  have hb :
      coordinateBialgHom R G G (MonoidHom.id G) =
        BialgHom.id R (coordinateRing R G) := by
    apply BialgHom.coe_toAlgHom_injective
    rw [coordinateBialgHom_toAlgHom]
    exact coordinateMap_id R G
  have h :
      CommHopfAlgCat.ofHom (coordinateBialgHom R G G (MonoidHom.id G)) =
        𝟙 (CommHopfAlgCat.of R (coordinateRing R G)) := by
    rw [hb]
    exact CommHopfAlgCat.ofHom_id
  unfold groupSchemeMap
  have hop := congrArg Quiver.Hom.op h
  simp only [op_id] at hop
  rw [hop]
  simpa only [groupScheme] using
    (hopfSpec (CommRingCat.of R)).map_id
      (op (CommHopfAlgCat.of R (coordinateRing R G)))

/-- Composition of homomorphisms is preserved by the associated constant-group-scheme maps. -/
@[simp]
theorem groupSchemeMap_comp {H K : Type u} [Group H] [Finite H] [Group K] [Finite K]
    (f : G →* H) (q : H →* K) :
    groupSchemeMap R (q.comp f) = groupSchemeMap R f ≫ groupSchemeMap R q := by
  have hb :
      coordinateBialgHom R G K (q.comp f) =
        (coordinateBialgHom R G H f).comp (coordinateBialgHom R H K q) := by
    apply BialgHom.coe_toAlgHom_injective
    rw [coordinateBialgHom_toAlgHom, BialgHom.comp_toAlgHom,
      coordinateBialgHom_toAlgHom, coordinateBialgHom_toAlgHom]
    exact coordinateMap_comp R G H K f q
  have h :
      CommHopfAlgCat.ofHom (coordinateBialgHom R G K (q.comp f)) =
        CommHopfAlgCat.ofHom (coordinateBialgHom R H K q) ≫
          CommHopfAlgCat.ofHom (coordinateBialgHom R G H f) := by
    rw [← CommHopfAlgCat.ofHom_comp]
    exact congrArg CommHopfAlgCat.ofHom hb
  have hop := congrArg Quiver.Hom.op h
  simp only [op_comp] at hop
  unfold groupSchemeMap
  rw [hop, Functor.map_comp]
  rfl

variable (G)

/-- Algebra-valued points of the coordinate Hopf algebra are canonically the scheme-valued
points of the constant group scheme. -/
noncomputable def schemePointsMulEquiv (A : Type u) [CommRing A] [Algebra R A] :
    WithConv (coordinateRing R G →ₐ[R] A) ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
        (groupScheme R G).X) :=
  CommHopfAlgCat.mapMulEquivOfPresentation
    (CommHopfAlgCat.of R (coordinateRing R G)) A (groupScheme_def R G)

/-- Under `schemePointsMulEquiv`, an algebra point is represented by its spectrum map. -/
@[simp]
theorem schemePointsMulEquiv_apply_left (A : Type u) [CommRing A] [Algebra R A]
    (p : WithConv (coordinateRing R G →ₐ[R] A)) :
    (schemePointsMulEquiv R G A p).left =
      Spec.map (CommRingCat.ofHom p.ofConv.toRingHom) ≫
        eqToHom (groupScheme_X_left R G).symm := by
  exact CommHopfAlgCat.mapMulEquivOfPresentation_apply_left
    (CommHopfAlgCat.of R (coordinateRing R G)) A (groupScheme_def R G)
      (groupScheme_X_left R G) p

/-- The scheme-valued point comparison is natural in the finite group: applying the
group-scheme map induced by `f` is precomposition by pullback of coordinate functions. -/
theorem schemePointsMulEquiv_groupSchemeMap {H : Type u} [Group H] [Finite H]
    (A : Type u) [CommRing A] [Algebra R A] (f : G →* H)
    (p : WithConv (coordinateRing R G →ₐ[R] A)) :
    schemePointsMulEquiv R G A p ≫ (groupSchemeMap R f).hom.hom =
      schemePointsMulEquiv R H A
        ((CommHopfAlgCat.mapPointsFunctor
          (CommHopfAlgCat.ofHom (coordinateBialgHom R G H f))).app
            (CommAlgCat.of R A) p) := by
  rw [groupSchemeMap_def]
  exact CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain A
    (groupScheme_def R H) (groupScheme_def R G)
    (schemePointsMulEquiv R H A) (schemePointsMulEquiv R G A)
    (schemePointsMulEquiv_apply_left R H A)
    (schemePointsMulEquiv_apply_left R G A)
    (CommHopfAlgCat.ofHom (coordinateBialgHom R G H f)) p

/-- The constant group scheme is affine. -/
instance isAffine_groupScheme : IsAffine (groupScheme R G).X.left := by
  rw [groupScheme_X_left]
  infer_instance

/-- The structural morphism of a constant finite group scheme is finite. -/
instance isFinite_groupScheme : IsFinite (groupScheme R G).X.hom := by
  rw [groupScheme_def]
  rw [← moduleFinite_iff_isFinite_hopfSpec R
    (CommHopfAlgCat.of R (coordinateRing R G))]
  infer_instance

/-- The structural morphism of a constant finite group scheme is étale. -/
instance etale_groupScheme : Etale (groupScheme R G).X.hom := by
  rw [groupScheme_X_hom]
  let _ : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap R (coordinateRing R G)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2
      (RingHom.etale_algebraMap.mpr inferInstance)
  infer_instance

end TauCeti.ConstantGroup
