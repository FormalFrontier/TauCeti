/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Representable

/-!
# The component group is finite etale

Let `H` be the coordinate Hopf algebra of a finite-type affine group over an algebraically
closed field. The fppf quotient by the identity component is represented by the constant group
scheme on the finite group of connected components of `Spec H`. This group scheme is finite and
etale by the corresponding instances for constant finite group schemes.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupScheme`: the constant group scheme on the
  connected components of `Spec H`.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupFppfSheafIsoComponentGroupSchemePoints`: the
  component quotient is isomorphic to the sheafified functor of points of that scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 6.7 and 14.

This completes the algebraically closed-field case of the finite etale component-group target in
Layer 3, "Identity component `G°` and component group `π₀(G)`", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.FiniteTypeCommHopfAlgCat

open AlgebraicGeometry

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The constant group scheme on the connected components of the spectrum of a finite-type
commutative Hopf algebra over an algebraically closed field. -/
noncomputable abbrev componentGroupScheme
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Grp (Over (Spec (CommRingCat.of k))) :=
  ConstantGroup.groupScheme k (ConnectedComponents (PrimeSpectrum H))

/-- The fppf component quotient is represented by `componentGroupScheme H`: its underlying sheaf
is isomorphic to the sheafification of the scheme's Yoneda functor of points on affine schemes. -/
noncomputable def componentGroupFppfSheafIsoComponentGroupSchemePoints
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (componentGroupFppfSheaf H).X ≅
      (presheafToSheaf (CommAlgCat.fppfTopology k) (Type (u + 1))).obj
        (((AlgebraicGeometry.algSpec (CommRingCat.of k)).op ⋙
          yoneda.obj (componentGroupScheme H).X) ⋙
            CategoryTheory.uliftFunctor.{u + 1, u}) := by
  let K := CommHopfAlgCat.of k
    (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)))
  let F := presheafToSheaf (CommAlgCat.fppfTopology k) (Type (u + 1))
  let e₀ : (CommHopfAlgCat.pointsPresheafGrp K).X ≅
      HopfAlgebra.pointsPresheaf K ⋙ CategoryTheory.uliftFunctor.{u + 1, u} :=
    eqToIso (CommHopfAlgCat.pointsPresheafGrp_X_eq K) ≪≫
      eqToIso (CommHopfAlgCat.pointsGroupPresheaf_ulift_forget K)
  let e₁ : HopfAlgebra.pointsPresheaf K ⋙ CategoryTheory.uliftFunctor.{u + 1, u} ≅
      CommHopfAlgCat.schemePointsPresheaf K ⋙
        CategoryTheory.uliftFunctor.{u + 1, u} :=
    Functor.isoWhiskerRight
      (CommHopfAlgCat.pointsPresheafIsoSchemePointsPresheaf K)
      CategoryTheory.uliftFunctor.{u + 1, u}
  have hScheme : CommHopfAlgCat.schemePointsPresheaf K =
      (AlgebraicGeometry.algSpec (CommRingCat.of k)).op ⋙
        yoneda.obj (componentGroupScheme H).X := by
    dsimp only [componentGroupScheme]
    rw [ConstantGroup.groupScheme_def]
  let e₂ : CommHopfAlgCat.schemePointsPresheaf K ⋙
        CategoryTheory.uliftFunctor.{u + 1, u} ≅
      (((AlgebraicGeometry.algSpec (CommRingCat.of k)).op ⋙
        yoneda.obj (componentGroupScheme H).X) ⋙
          CategoryTheory.uliftFunctor.{u + 1, u}) :=
    Functor.isoWhiskerRight (eqToIso hScheme) CategoryTheory.uliftFunctor.{u + 1, u}
  exact (Grp.forget _).mapIso (componentGroupFppfGroupObjectIso H) ≪≫
    eqToIso (CommHopfAlgCat.pointsFppfGroupObject_X_eq K) ≪≫
      F.mapIso (e₀ ≪≫ e₁ ≪≫ e₂)

end TauCeti.FiniteTypeCommHopfAlgCat
