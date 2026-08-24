/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.CategoryTheory.Monoidal.Normal
import Mathlib.Algebra.Category.CommAlgCat.Monoidal

/-!
# Normal Hopf ideals as categorical normal subgroups

A commutative Hopf algebra is equivalently a group object in the opposite category of
commutative algebras. Under this equivalence, a Hopf-ideal quotient `H ⟶ H/I` represents the
closed-subgroup inclusion `Spec(H/I) ⟶ Spec H`.

This file proves that normality of the Hopf ideal makes this inclusion a normal subgroup object
in Mathlib's sense. The proof uses the generalized-point criterion for categorical normality and
the existing characterization of normal Hopf ideals by normality of their subgroups of
algebra-valued points.

The result is the bridge needed to apply the internal semidirect-product construction to two
normal closed affine subgroup schemes. Its multiplication map and scheme-theoretic image are the
binary product used in the maximal-dimension construction of the unipotent radical.

## Main declarations

* `TauCeti.CommHopfAlgCat.cogrpObj`: the group object in `(CommAlgCat R)ᵒᵖ` represented by a
  commutative Hopf algebra.
* `TauCeti.CommHopfAlgCat.cogrpPointsMulEquiv`: generalized points of the represented group
  object are convolution points.
* `TauCeti.CommHopfAlgCat.quotientCogrpInclusion`: the categorical closed-subgroup inclusion
  represented by a Hopf-ideal quotient.
* `TauCeti.CommHopfAlgCat.quotientCogrpInclusion_normal`: a normal Hopf ideal represents a normal
  subgroup object.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15–17.
* J. S. Milne, *Algebraic Groups* (2017), §§6.a and 10.20.

This advances Layer 5, "The unipotent radical", of the ReductiveGroups roadmap. It connects the
coordinate normality API to the categorical semidirect-product API used to form the product of
two normal unipotent-radical candidates.
-/

public section

open CategoryTheory Opposite WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- The group object in the opposite category of commutative `R`-algebras represented by a
commutative Hopf algebra. -/
noncomputable abbrev cogrpObj (H : _root_.CommHopfAlgCat.{u} R) :
    (CommAlgCat.{u} R)ᵒᵖ :=
  ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.obj H).unop.X

/-- Generalized points of the group object represented by `H` are the convolution group of
algebra-valued points of `H`. -/
noncomputable def cogrpPointsMulEquiv (H : _root_.CommHopfAlgCat.{u} R)
    (A : CommAlgCat.{u} R) :
    (op A ⟶ cogrpObj H) ≃* HopfAlgebra.points (R := R) (H := H) A where
  toFun g := toConv g.unop.hom
  invFun p := op (CommAlgCat.ofHom p.ofConv)
  left_inv g := by
    apply Quiver.Hom.unop_inj
    exact CommAlgCat.hom_ext rfl
  right_inv p := WithConv.toConv_ofConv p
  map_mul' f g := by
    apply WithConv.ofConv_injective
    change (CartesianMonoidalCategory.lift f g ≫ μ).unop.hom =
      (toConv f.unop.hom * toConv g.unop.hom).ofConv
    apply AlgHom.ext
    intro h
    simp only [unop_comp, CommAlgCat.hom_comp, CommAlgCat.lift_unop_hom,
      AlgHom.comp_apply, AlgHom.convMul_apply]
    exact congrArg _ (Bialgebra.comulAlgHom_apply R H h)

/-- The generalized-point equivalence regards a categorical point as the convolution wrapper
of its underlying algebra morphism. -/
@[simp]
theorem cogrpPointsMulEquiv_apply (H : _root_.CommHopfAlgCat.{u} R)
    (A : CommAlgCat.{u} R) (g : op A ⟶ cogrpObj H) :
    cogrpPointsMulEquiv H A g = toConv g.unop.hom := (rfl)

/-- The categorical closed-subgroup inclusion represented contravariantly by the quotient map
`H ⟶ H/I`. -/
noncomputable def quotientCogrpInclusion (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) : cogrpObj (quotient H I) ⟶ cogrpObj H :=
  ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.map (mkQuotient H I)).unop.hom.hom

/-- The categorical quotient inclusion is the opposite of the coordinate quotient map. -/
theorem quotientCogrpInclusion_unop (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) :
    (quotientCogrpInclusion H I).unop = CommAlgCat.ofHom (mkQuotient H I).hom := (rfl)

/-- Under `cogrpPointsMulEquiv`, composition with the categorical quotient inclusion is the
usual quotient-points homomorphism. -/
@[simp]
theorem cogrpPointsMulEquiv_comp_quotientCogrpInclusion
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (A : CommAlgCat.{u} R)
    (q : op A ⟶ cogrpObj (quotient H I)) :
    cogrpPointsMulEquiv H A (q ≫ quotientCogrpInclusion H I) =
      quotientPointsHom H I A (cogrpPointsMulEquiv (quotient H I) A q) := by
  rw [cogrpPointsMulEquiv_apply, cogrpPointsMulEquiv_apply]
  apply WithConv.ofConv_injective
  change (q ≫ quotientCogrpInclusion H I).unop.hom =
    (quotientPointsHom H I A (toConv q.unop.hom)).ofConv
  rw [quotientPointsHom_apply]
  rw [unop_comp, quotientCogrpInclusion_unop]
  rfl

/-- A normal Hopf ideal represents a normal subgroup object in the opposite category of
commutative algebras. -/
theorem quotientCogrpInclusion_normal (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) :
    IsMonHom.Normal (quotientCogrpInclusion H I) := by
  let i := quotientCogrpInclusion H I
  let q : CommAlgCat.of R H ⟶ CommAlgCat.of R (quotient H I) :=
    CommAlgCat.ofHom (mkQuotient H I).hom
  let _ : Epi q := ConcreteCategory.epi_of_surjective q (by
    intro x
    obtain ⟨y, hy⟩ := mkQuotient_surjective H I x
    exact ⟨y, hy⟩)
  let _ : Mono i := ⟨fun {Z} a b hab ↦ by
    apply Quiver.Hom.unop_inj
    apply (cancel_epi q).1
    have hab' := congrArg Quiver.Hom.unop hab
    change (quotientCogrpInclusion H I).unop ≫ a.unop =
      (quotientCogrpInclusion H I).unop ≫ b.unop at hab'
    rw [quotientCogrpInclusion_unop] at hab'
    exact hab'⟩
  let _ : IsMonHom i := by
    dsimp only [i, quotientCogrpInclusion]
    infer_instance
  rw [IsMonHom.normal_iff_normal_monoidHom]
  intro A
  let hnormal := quotientPointsSubgroup_normal H I hI A.unop
  constructor
  rintro n ⟨q, rfl⟩ g
  let qPoint : HopfAlgebra.points (R := R) (H := quotient H I) A.unop :=
    toConv q.unop.hom
  let gPoint : HopfAlgebra.points (R := R) (H := H) A.unop :=
    toConv g.unop.hom
  have hq : quotientPointsHom H I A.unop qPoint ∈ quotientPointsSubgroup H I A.unop :=
    quotientPointsHom_mem_quotientPointsSubgroup H I A.unop qPoint
  have hconj := hnormal.conj_mem (quotientPointsHom H I A.unop qPoint) hq gPoint
  change _ ∈ (quotientPointsHom H I A.unop).hom.range at hconj
  obtain ⟨q', hq'⟩ := hconj
  let qCat : A ⟶ cogrpObj (quotient H I) :=
    (cogrpPointsMulEquiv (quotient H I) A.unop).symm q'
  refine ⟨qCat, ?_⟩
  apply (cogrpPointsMulEquiv H A.unop).injective
  change cogrpPointsMulEquiv H A.unop (qCat ≫ i) =
    cogrpPointsMulEquiv H A.unop (g * (q ≫ i) * g⁻¹)
  dsimp only [i]
  rw [map_mul, map_mul, map_inv,
    cogrpPointsMulEquiv_comp_quotientCogrpInclusion,
    cogrpPointsMulEquiv_comp_quotientCogrpInclusion]
  have hqCatPoint : cogrpPointsMulEquiv (quotient H I) A.unop qCat = q' := by
    dsimp only [qCat]
    exact (cogrpPointsMulEquiv (quotient H I) A.unop).apply_symm_apply q'
  have hqPoint' : cogrpPointsMulEquiv (quotient H I) A.unop q = qPoint := (rfl)
  have hgPoint : cogrpPointsMulEquiv H A.unop g = gPoint := (rfl)
  rw [hqCatPoint, hqPoint', hgPoint]
  exact hq'

end TauCeti.CommHopfAlgCat
