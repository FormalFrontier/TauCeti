/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints

/-!
# The affine fppf site and affine-group points

For a commutative ring `R`, the category `(CommAlgCat R)ᵒᵖ` is the category of affine schemes
over `Spec R`. This file equips it with the fppf topology induced by Mathlib's fppf topology on
schemes over `Spec R`. Thus a presheaf on this site has the expected variance

```text
CommAlgCat R ⥤ Type.
```

The induced affine topology is subcanonical. The proof restricts each representable presheaf on
schemes over `Spec R` along the fully faithful relative spectrum functor and identifies the result
with the corresponding affine representable presheaf.

For a commutative Hopf algebra `H`, the underlying type-valued presheaf of convolution points
`A ↦ WithConv (H →ₐ[R] A)` is then compared with the restriction of the Yoneda presheaf represented
by `Spec H`. Mathlib's multiplicative spectrum-points equivalence gives the components, while its
naturality in the value algebra gives the natural isomorphism. Consequently affine-group points
form an fppf sheaf.

This is the affine-site foundation for fppf sheafification of pointwise quotients. It does not
assert that such a quotient sheaf is representable; representability requires separate hypotheses.

## Main declarations

* `TauCeti.CommAlgCat.fppfTopology`: the fppf topology on opposite commutative `R`-algebras.
* `TauCeti.CommAlgCat.fppfTopology_subcanonical`: affine representable functors are fppf sheaves.
* `TauCeti.HopfAlgebra.pointsGroupPresheaf`: the group-valued convolution-points presheaf.
* `TauCeti.HopfAlgebra.pointsPresheaf`: its underlying type-valued presheaf.
* `TauCeti.CommHopfAlgCat.schemePointsPresheaf`: the same presheaf through relative `Spec` and
  Yoneda.
* `TauCeti.CommHopfAlgCat.pointsPresheafIsoSchemePointsPresheaf`: the natural comparison.
* `TauCeti.HopfAlgebra.pointsPresheaf_isSheaf`: affine-group points satisfy fppf descent.
* `TauCeti.HopfAlgebra.pointsFppfSheaf`: affine-group points bundled as an fppf sheaf.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 2 and 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 1 and 14.

This advances the cross-cutting sheaves-and-descent prerequisite and Layer 3, "Normality and
quotients", of the ReductiveGroups roadmap. The next step is to sheafify the existing pointwise
quotient presheaf and prove its quotient universal property in the fppf topos.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

namespace CommAlgCat

/-- The fppf topology on affine schemes over `Spec R`, expressed on the equivalent category
`(CommAlgCat R)ᵒᵖ`.

It is the topology induced along the relative spectrum functor from the fppf topology on schemes
over `Spec R`. -/
noncomputable def fppfTopology (R : Type u) [CommRing R] :
    GrothendieckTopology (CommAlgCat.{u} R)ᵒᵖ :=
  (AlgebraicGeometry.algSpec (CommRingCat.of R)).inducedTopology
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))

/-- Relative spectrum is continuous from the affine fppf site to the fppf site of schemes over
the base. -/
instance algSpec_isContinuous_fppfTopology (R : Type u) [CommRing R] :
    (AlgebraicGeometry.algSpec (CommRingCat.of R)).IsContinuous
      (fppfTopology R)
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) := by
  unfold fppfTopology
  infer_instance

/-- **The affine fppf topology is subcanonical.** Every presheaf represented by an affine scheme
over `Spec R` is an fppf sheaf. -/
noncomputable instance fppfTopology_subcanonical (R : Type u) [CommRing R] :
    (fppfTopology R).Subcanonical := by
  let K := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  let _ : K.Subcanonical := by
    dsimp only [K]
    infer_instance
  apply GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
  intro X
  let P := yoneda.obj
    ((AlgebraicGeometry.algSpec (CommRingCat.of R)).obj X)
  have hP : Presieve.IsSheaf K P :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P
  let S : Sheaf K (Type u) :=
    ⟨P, (isSheaf_iff_isSheaf_of_type K P).mpr hP⟩
  have hpull' : Presieve.IsSheaf (fppfTopology R)
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).op ⋙ P) :=
    Functor.op_comp_isSheaf_of_types
      (AlgebraicGeometry.algSpec (CommRingCat.of R)) (fppfTopology R) K S
  have hpull : Presheaf.IsSheaf (fppfTopology R)
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).op ⋙ P) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr hpull'
  let e : yoneda.obj X ≅
      (AlgebraicGeometry.algSpec (CommRingCat.of R)).op ⋙ P :=
    NatIso.ofComponents
      (fun _ =>
        (AlgebraicGeometry.algSpec.fullyFaithful
          (R := CommRingCat.of R)).homEquiv.toIso)
      (by
        intro Y Z f
        ext g
        exact (AlgebraicGeometry.algSpec (CommRingCat.of R)).map_comp f.unop g)
  exact (isSheaf_iff_isSheaf_of_type _ _).mp <|
    (Presheaf.isSheaf_of_iso_iff e).mpr hpull

end CommAlgCat

namespace HopfAlgebra

variable {R : Type u} [CommRing R]

/-- The group-valued presheaf of convolution points of a commutative Hopf algebra.

The double-opposite equivalence presents the existing covariant functor on `CommAlgCat R` as a
presheaf on the site `(CommAlgCat R)ᵒᵖ`. -/
noncomputable abbrev pointsGroupPresheaf (H : _root_.CommHopfAlgCat.{u} R) :
    ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ GrpCat.{u} :=
  (opOpEquivalence (CommAlgCat.{u} R)).functor ⋙
    pointsFunctor (R := R) (H := H)

/-- The underlying type-valued presheaf of convolution points of a commutative Hopf algebra.

This is `pointsGroupPresheaf` followed by the forgetful functor from groups to types. -/
noncomputable abbrev pointsPresheaf (H : _root_.CommHopfAlgCat.{u} R) :
    ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type u :=
  pointsGroupPresheaf H ⋙ forget GrpCat

/-- Evaluating the points presheaf at an affine `R`-scheme gives its convolution group of
algebra-valued points, with the group structure forgotten. -/
theorem pointsPresheaf_obj (H : _root_.CommHopfAlgCat.{u} R)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    (pointsPresheaf H).obj A = WithConv (H →ₐ[R] A.unop.unop) :=
  rfl

end HopfAlgebra

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- Scheme-valued affine-group points, restricted along relative `Spec` and regarded as a
type-valued presheaf on the affine fppf site. -/
noncomputable abbrev schemePointsPresheaf (H : _root_.CommHopfAlgCat.{u} R) :
    ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type u :=
  (AlgebraicGeometry.algSpec (CommRingCat.of R)).op ⋙
    yoneda.obj
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)).X

/-- The scheme-points presheaf at `A` is the set of morphisms over `Spec R` from `Spec A` to
`Spec H`. -/
theorem schemePointsPresheaf_obj (H : _root_.CommHopfAlgCat.{u} R)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ) :
    (schemePointsPresheaf H).obj A =
      ((Spec (CommRingCat.of A.unop.unop)).asOver (Spec (CommRingCat.of R)) ⟶
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)).X) :=
  rfl

/-- **Convolution points agree naturally with scheme-valued points.** This is Mathlib's
`Spec.mapMulEquiv`, assembled over all value algebras. -/
@[expose] noncomputable def pointsPresheafIsoSchemePointsPresheaf
    (H : _root_.CommHopfAlgCat.{u} R) :
    HopfAlgebra.pointsPresheaf H ≅ schemePointsPresheaf H :=
  NatIso.ofComponents
    (fun A =>
      (AlgebraicGeometry.Spec.mapMulEquiv
        (R := R) (S := H) (T := A.unop.unop)).toEquiv.toIso)
    (by
      intro A B f
      ext p
      exact mapMulEquiv_mapValue H f.unop.unop p)

/-- The comparison from convolution points to scheme-valued points is Mathlib's spectrum-points
equivalence at every value algebra. -/
theorem pointsPresheafIsoSchemePointsPresheaf_hom_app_apply
    (H : _root_.CommHopfAlgCat.{u} R)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (p : WithConv (H →ₐ[R] A.unop.unop)) :
    (pointsPresheafIsoSchemePointsPresheaf H).hom.app A p =
      AlgebraicGeometry.Spec.mapMulEquiv p :=
  rfl

/-- The inverse comparison recovers the convolution point represented by a relative spectrum
morphism. -/
theorem pointsPresheafIsoSchemePointsPresheaf_inv_app_apply
    (H : _root_.CommHopfAlgCat.{u} R)
    (A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ)
    (p : (schemePointsPresheaf H).obj A) :
    (pointsPresheafIsoSchemePointsPresheaf H).inv.app A p =
      AlgebraicGeometry.Spec.mapMulEquiv.symm p :=
  rfl

end CommHopfAlgCat

namespace HopfAlgebra

variable {R : Type u} [CommRing R]

/-- **Affine-group points form an fppf sheaf.** The type-valued convolution-points presheaf is
the restriction of the representable scheme-valued points functor along relative `Spec`. -/
theorem pointsPresheaf_isSheaf (H : _root_.CommHopfAlgCat.{u} R) :
    Presheaf.IsSheaf (CommAlgCat.fppfTopology R) (pointsPresheaf H) := by
  let K := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  let _ : K.Subcanonical := by
    dsimp only [K]
    infer_instance
  let G := (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)
  let P := yoneda.obj G.X
  have hP : Presieve.IsSheaf K P :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P
  let S : Sheaf K (Type u) :=
    ⟨P, (isSheaf_iff_isSheaf_of_type K P).mpr hP⟩
  have hscheme' : Presieve.IsSheaf (CommAlgCat.fppfTopology R)
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).op ⋙ P) :=
    Functor.op_comp_isSheaf_of_types
      (AlgebraicGeometry.algSpec (CommRingCat.of R))
      (CommAlgCat.fppfTopology R) K S
  have hscheme : Presheaf.IsSheaf (CommAlgCat.fppfTopology R)
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).op ⋙ P) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr hscheme'
  exact (Presheaf.isSheaf_of_iso_iff
    (CommHopfAlgCat.pointsPresheafIsoSchemePointsPresheaf H)).mpr hscheme

/-- **The group-valued convolution-points presheaf is an fppf sheaf.** This is the group-valued
form of `pointsPresheaf_isSheaf`; the forgetful functor from groups preserves limits and reflects
isomorphisms. -/
theorem pointsGroupPresheaf_isSheaf (H : _root_.CommHopfAlgCat.{u} R) :
    Presheaf.IsSheaf (CommAlgCat.fppfTopology R) (pointsGroupPresheaf H) := by
  exact Presheaf.isSheaf_of_isSheaf_comp
    (CommAlgCat.fppfTopology R) (pointsGroupPresheaf H) (forget GrpCat.{u})
    (pointsPresheaf_isSheaf H)

/-- The convolution-points functor, bundled as a group-valued sheaf on the affine fppf site. -/
noncomputable def pointsFppfSheaf (H : _root_.CommHopfAlgCat.{u} R) :
    Sheaf (CommAlgCat.fppfTopology R) GrpCat.{u} :=
  ⟨pointsGroupPresheaf H, pointsGroupPresheaf_isSheaf H⟩

end HopfAlgebra

end TauCeti
