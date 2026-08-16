/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Kernel
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic

/-!
# The special linear group scheme

This file presents the special linear group scheme `SLₙ` as the closed subgroup scheme of
`GeneralLinear.groupScheme R n` cut out by the determinant-one condition.

## Main declarations

* `TauCeti.SpecialLinear.groupScheme`: the special linear group scheme.
* `TauCeti.SpecialLinear.groupSchemeι`: the closed immersion `SLₙ ⟶ GLₙ`.
* `TauCeti.SpecialLinear.groupSchemePointMulEquiv`: the spectrum-points equivalence for `SLₙ`.
* `TauCeti.SpecialLinear.schemePointsMulEquiv`: the group of scheme-valued points of `SLₙ` is
  `Matrix.SpecialLinearGroup (Fin n) A`.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Part I, §1.7, pp. 49–50.
-/

public section

open AlgebraicGeometry CategoryTheory MonObj WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti

namespace SpecialLinear

universe u w

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The special linear group scheme obtained by applying relative spectrum to the determinant-one
coordinate Hopf algebra, which is the kernel Hopf-ideal quotient of
`GeneralLinear.coordinateHopfAlgebra`. -/
noncomputable def groupScheme : Grp (Over (Spec (CommRingCat.of R))) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
    (Opposite.op (coordinateHopfAlgebra R n))

/-- The special linear group scheme is the relative spectrum of its determinant-one coordinate
Hopf algebra. -/
lemma groupScheme_def :
    groupScheme R n =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op (coordinateHopfAlgebra R n)) := by
  unfold groupScheme
  rfl

/-- The scheme underlying the special linear group scheme is the spectrum of its coordinate Hopf
algebra. -/
lemma groupScheme_X_left :
    (groupScheme R n).X.left = Spec (CommRingCat.of (coordinateHopfAlgebra R n)) := by
  simpa only [groupScheme] using
    hopfSpec_obj_X_left R (coordinateHopfAlgebra R n)

/-- The closed immersion of the special linear group scheme into the general linear group scheme. -/
noncomputable def groupSchemeι :
    groupScheme R n ⟶ GeneralLinear.groupScheme R n :=
  eqToHom (groupScheme_def R n) ≫
    CommHopfAlgCat.kernelSpecι (GeneralLinear.determinantCoordinateMap R n) ≫
    eqToHom (GeneralLinear.groupScheme_def R n).symm

/-- The special-linear inclusion is the generic determinant-kernel inclusion transported to the
named special-linear and general-linear presentations. -/
theorem groupSchemeι_def :
    groupSchemeι R n =
      eqToHom (groupScheme_def R n) ≫
        CommHopfAlgCat.kernelSpecι (GeneralLinear.determinantCoordinateMap R n) ≫
        eqToHom (GeneralLinear.groupScheme_def R n).symm := by
  unfold groupSchemeι
  rfl

/-- The determinant is the unit section after restricting it along the named special-linear
inclusion. -/
theorem groupSchemeι_comp_determinant :
    groupSchemeι R n ≫ eqToHom (GeneralLinear.groupScheme_def R n) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (GeneralLinear.determinantCoordinateMap R n).op =
      eqToHom (groupScheme_def R n) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (_root_.CommHopfAlgCat.ofHom
            ((Bialgebra.unitBialgHom R (coordinateHopfAlgebra R n)).comp
              (Bialgebra.counitBialgHom R
                (_root_.CommHopfAlgCat.of R
                  (MonoidAlgebra R (Multiplicative ℤ)))))).op := by
  rw [groupSchemeι_def]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [CommHopfAlgCat.kernelSpecι_comp]

/-- The special-linear group scheme is a closed subgroup scheme of the named general-linear
group scheme. -/
instance isClosedImmersion_groupSchemeι :
    AlgebraicGeometry.IsClosedImmersion (groupSchemeι R n).hom.hom.left := by
  let e1 := (eqToHom (groupScheme_def R n)).hom.hom.left
  let c := (CommHopfAlgCat.kernelSpecι (GeneralLinear.determinantCoordinateMap R n)).hom.hom.left
  let e2 := (eqToHom (GeneralLinear.groupScheme_def R n).symm).hom.hom.left
  have he1 : IsIso e1 :=
    ((Over.forget (Spec (CommRingCat.of R))).mapIso
      ((Grp.forget (Over (Spec (CommRingCat.of R)))).mapIso
        (eqToIso (groupScheme_def R n)))).isIso_hom
  have he2 : IsIso e2 :=
    ((Over.forget (Spec (CommRingCat.of R))).mapIso
      ((Grp.forget (Over (Spec (CommRingCat.of R)))).mapIso
        (eqToIso (GeneralLinear.groupScheme_def R n).symm))).isIso_hom
  have hc : AlgebraicGeometry.IsClosedImmersion c := by
    dsimp only [c]
    rw [CommHopfAlgCat.kernelSpecι_def]
    infer_instance
  have hec : AlgebraicGeometry.IsClosedImmersion (e1 ≫ c) :=
    (@MorphismProperty.cancel_left_of_respectsIso
      Scheme _ @AlgebraicGeometry.IsClosedImmersion inferInstance _ _ _ e1 c he1).2 hc
  have hece : AlgebraicGeometry.IsClosedImmersion ((e1 ≫ c) ≫ e2) :=
    (@MorphismProperty.cancel_right_of_respectsIso
      Scheme _ @AlgebraicGeometry.IsClosedImmersion inferInstance _ _ _ (e1 ≫ c) e2 he2).2 hec
  rw [groupSchemeι_def]
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left]
  exact hece

/-- The structural morphism of the special-linear group scheme is locally of finite type. -/
instance locallyOfFiniteType_groupScheme :
    AlgebraicGeometry.LocallyOfFiniteType (groupScheme R n).X.hom := by
  let H : FiniteTypeCommHopfAlgCat R :=
    ⟨GeneralLinear.coordinateHopfAlgebra R n, by
      rw [← GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj]
      exact (GeneralLinear.finiteTypeCoordinateHopfAlgebra R n).property⟩
  rw [groupScheme_def]
  exact FiniteTypeCommHopfAlgCat.locallyOfFiniteType_quotientSpec
    H (definingHopfIdeal R n)

/-! ### Scheme-valued points -/

section SchemePoints

variable {R} (A : Type u) [CommRing A] [Algebra R A]

/-- Mathlib's spectrum-points equivalence for the special-linear coordinate Hopf algebra. -/
noncomputable def groupSchemePointMulEquiv :
    WithConv (coordinateHopfAlgebra R n →ₐ[R] A) ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
        (groupScheme R n).X) :=
  CommHopfAlgCat.mapMulEquivOfPresentation
    (coordinateHopfAlgebra R n) A (groupScheme_def R n)

/-- The underlying spectrum map of the scheme point associated to a special-linear algebra
point. -/
@[simp]
lemma groupSchemePointMulEquiv_apply_left
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (groupSchemePointMulEquiv n A f).left =
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
        eqToHom (groupScheme_X_left R n).symm := by
  simpa only [groupSchemePointMulEquiv] using
    CommHopfAlgCat.mapMulEquivOfPresentation_apply_left
      (coordinateHopfAlgebra R n) A (groupScheme_def R n)
        (groupScheme_X_left R n) f

/-- The group of scheme-valued points of the special-linear group scheme is the ordinary special
linear group over the value algebra. -/
noncomputable def schemePointsMulEquiv :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R n).X) ≃* Matrix.SpecialLinearGroup (Fin n) A :=
  (groupSchemePointMulEquiv n A).symm.trans
    (pointsMulEquiv (R := R) (A := A) n)

/-- Evaluating the scheme-points equivalence on a point presented by `groupSchemePointMulEquiv`
recovers the canonical algebra point. -/
@[simp]
theorem schemePointsMulEquiv_groupSchemePointMulEquiv
    (q : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    schemePointsMulEquiv n A (groupSchemePointMulEquiv n A q) =
      pointsMulEquiv (R := R) (A := A) n q := by
  simp [schemePointsMulEquiv]

/-- The inverse scheme-points equivalence sends a determinant-one matrix to the spectrum point
induced by its canonical coordinate-algebra point. -/
@[simp]
lemma schemePointsMulEquiv_symm_apply (g : Matrix.SpecialLinearGroup (Fin n) A) :
    (schemePointsMulEquiv n A).symm g =
      groupSchemePointMulEquiv n A
        ((pointsMulEquiv (R := R) (A := A) n).symm g) := by
  rfl

/-- Evaluating the scheme-points equivalence directly on a scheme morphism. -/
theorem schemePointsMulEquiv_apply
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R n).X) :
    schemePointsMulEquiv n A p =
      pointsMulEquiv (R := R) (A := A) n
        ((groupSchemePointMulEquiv n A).symm p) := by
  unfold schemePointsMulEquiv
  rfl

private lemma groupSchemePointMulEquiv_comp_groupSchemeι
    (q : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    groupSchemePointMulEquiv n A q ≫ (groupSchemeι R n).hom.hom =
      GeneralLinear.groupSchemePointMulEquiv n A
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
          (CommAlgCat.of R A) q) := by
  rw [groupSchemeι_def, CommHopfAlgCat.kernelSpecι_def,
    CommHopfAlgCat.quotientSpecι_def]
  exact CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := R) A (GeneralLinear.groupScheme_def R n) (groupScheme_def R n)
      (GeneralLinear.groupSchemePointMulEquiv n A) (groupSchemePointMulEquiv n A)
      (GeneralLinear.groupSchemePointMulEquiv_apply_left n A)
      (groupSchemePointMulEquiv_apply_left n A) (coordinateMap R n) q

/-- Composing a special-linear scheme point with the named inclusion into the general-linear
group scheme is Mathlib's canonical inclusion `Matrix.SpecialLinearGroup.toGL`. -/
@[simp]
theorem schemePointsMulEquiv_comp_groupSchemeι
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R n).X) :
    GeneralLinear.schemePointsMulEquiv n A (p ≫ (groupSchemeι R n).hom.hom) =
      Matrix.SpecialLinearGroup.toGL (schemePointsMulEquiv n A p) := by
  obtain ⟨q, rfl⟩ := (groupSchemePointMulEquiv n A).surjective p
  rw [groupSchemePointMulEquiv_comp_groupSchemeι,
    GeneralLinear.schemePointsMulEquiv_groupSchemePointMulEquiv,
    schemePointsMulEquiv_groupSchemePointMulEquiv]
  exact pointsMulEquiv_toGL (R := R) (A := A) n q

end SchemePoints

end SpecialLinear

end TauCeti
