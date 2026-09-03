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
closed field. The existing group-object representation of the fppf quotient by the identity
component uses the constant group scheme on the finite group of connected components of `Spec H`.
Here that scheme is named and its affineness, finiteness, and etaleness are recorded explicitly.
The underlying sheaf of the quotient is also compared with the sheafification of the scheme's
Yoneda functor of points on affine schemes.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupScheme`: the constant group scheme on the
  connected components of `Spec H`.
* `TauCeti.FiniteTypeCommHopfAlgCat.isFinite_componentGroupScheme`: the component group scheme
  is finite.
* `TauCeti.FiniteTypeCommHopfAlgCat.etale_componentGroupScheme`: the component group scheme is
  etale.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupFppfSheafIsoSheafifiedSchemePoints`: the
  underlying component quotient sheaf is isomorphic to the sheafified functor of points.

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
noncomputable def componentGroupScheme
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Grp (Over (Spec (CommRingCat.of k))) :=
  ConstantGroup.groupScheme k (ConnectedComponents (PrimeSpectrum H))

/-- The component group scheme is the constant group scheme on the connected components. -/
theorem componentGroupScheme_def (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    componentGroupScheme H =
      ConstantGroup.groupScheme k (ConnectedComponents (PrimeSpectrum H)) := by
  rfl

/-- The component group scheme is affine. -/
instance isAffine_componentGroupScheme (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsAffine (componentGroupScheme H).X.left := by
  rw [componentGroupScheme_def]
  infer_instance

/-- The structural morphism of the component group scheme is finite. -/
instance isFinite_componentGroupScheme (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsFinite (componentGroupScheme H).X.hom := by
  rw [componentGroupScheme_def]
  infer_instance

/-- The structural morphism of the component group scheme is etale. -/
instance etale_componentGroupScheme (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Etale (componentGroupScheme H).X.hom := by
  rw [componentGroupScheme_def]
  infer_instance

/-- The sheafification of the universe-lifted Yoneda functor of points of the component group
scheme on the affine fppf site. -/
noncomputable def componentGroupSchemePointsFppfSheaf
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Sheaf (CommAlgCat.fppfTopology k) (Type (u + 1)) :=
  (presheafToSheaf (CommAlgCat.fppfTopology k) (Type (u + 1))).obj
    (((AlgebraicGeometry.algSpec (CommRingCat.of k)).op ⋙
      yoneda.obj (componentGroupScheme H).X) ⋙
        CategoryTheory.uliftFunctor.{u + 1, u})

/-- The underlying fppf component quotient sheaf is isomorphic to the sheafification of the
component group scheme's universe-lifted Yoneda functor of points on affine schemes. -/
noncomputable def componentGroupFppfSheafIsoSheafifiedSchemePoints
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (componentGroupFppfSheaf H).X ≅ componentGroupSchemePointsFppfSheaf H := by
  let K := CommHopfAlgCat.of k
    (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)))
  let F := presheafToSheaf (CommAlgCat.fppfTopology k) (Type (u + 1))
  have hScheme : CommHopfAlgCat.schemePointsPresheaf K =
      (AlgebraicGeometry.algSpec (CommRingCat.of k)).op ⋙
        yoneda.obj (componentGroupScheme H).X := by
    rw [componentGroupScheme_def, ConstantGroup.groupScheme_def]
  let e : CommHopfAlgCat.schemePointsPresheaf K ⋙
      CategoryTheory.uliftFunctor.{u + 1, u} ≅
        ((AlgebraicGeometry.algSpec (CommRingCat.of k)).op ⋙
          yoneda.obj (componentGroupScheme H).X) ⋙
            CategoryTheory.uliftFunctor.{u + 1, u} :=
    Functor.isoWhiskerRight (eqToIso hScheme) CategoryTheory.uliftFunctor.{u + 1, u}
  exact componentGroupFppfSheafIso H ≪≫
    CommHopfAlgCat.pointsFppfGroupObjectXIsoSchemePointsFppfSheaf K ≪≫
      F.mapIso e

end TauCeti.FiniteTypeCommHopfAlgCat
