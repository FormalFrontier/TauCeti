/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.Category.CommAlgCat.Fppf

/-!
# Affine-group points on the affine fppf site

For a commutative ring `R`, the category `(CommAlgCat R)ᵒᵖ` is the category of affine schemes
over `Spec R`. The imported generic affine-site module equips it with the fppf topology induced by
Mathlib's fppf topology on schemes over `Spec R`. Thus a presheaf on this site has the expected
variance

```text
CommAlgCat R ⥤ Type.
```

For a commutative Hopf algebra `H`, the imported Yoneda module registers the underlying type-valued
presheaf of convolution points `A ↦ WithConv (H →ₐ[R] A)` as representable. Its representability
and subcanonicity imply that affine-group points form an fppf sheaf.

This is the affine-site foundation for fppf sheafification of pointwise quotients. It does not
assert that such a quotient sheaf is representable; representability requires separate hypotheses.

## Main declarations

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

namespace HopfAlgebra

variable {R : Type u} [CommRing R]

/-- **Affine-group points form an fppf sheaf.** The type-valued convolution-points presheaf is
representable on the opposite site because the original covariant points functor is
corepresentable. -/
theorem pointsPresheaf_isSheaf (H : _root_.CommHopfAlgCat.{u} R) :
    Presheaf.IsSheaf (CommAlgCat.fppfTopology R) (pointsPresheaf H) := by
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr <|
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (pointsPresheaf H)

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

/-- The presheaf underlying `pointsFppfSheaf` is the convolution-points presheaf. -/
@[simp]
theorem pointsFppfSheaf_obj (H : _root_.CommHopfAlgCat.{u} R) :
    (pointsFppfSheaf H).obj = pointsGroupPresheaf H :=
  by rw [pointsFppfSheaf]

end HopfAlgebra

end TauCeti
