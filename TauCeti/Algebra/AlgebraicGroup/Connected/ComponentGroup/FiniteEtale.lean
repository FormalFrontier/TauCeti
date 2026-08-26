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
scheme on the finite group of connected components of `Spec H`. This file names that canonical
representing group scheme and records that its structural morphism is finite and etale.

No smoothness hypothesis on `H` is needed over an algebraically closed field. The representer is
constant, and constant finite group schemes are finite etale over any commutative base ring. The
existing isomorphism `componentGroupFppfGroupObjectIso` identifies its fppf points with the
component quotient, compatibly with the quotient projection.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupScheme`: the canonical group scheme
  representing the component quotient.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupRepresentation`: the representation
  isomorphism from the fppf component quotient to the named coordinate model.
* `TauCeti.FiniteTypeCommHopfAlgCat.isFinite_componentGroupScheme`: its structural morphism is
  finite.
* `TauCeti.FiniteTypeCommHopfAlgCat.etale_componentGroupScheme`: its structural morphism is
  etale.

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

/-- The coordinate Hopf algebra of the component group of a finite-type affine group over an
algebraically closed field.

It is the function Hopf algebra on the finite group of connected components of the prime
spectrum. -/
noncomputable def componentGroupCoordinateHopfAlgebra
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) : CommHopfAlgCat.{u} k :=
  CommHopfAlgCat.of k
    (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)))

/-- The component-group coordinate Hopf algebra is the function Hopf algebra on the connected
components. -/
theorem componentGroupCoordinateHopfAlgebra_def
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    componentGroupCoordinateHopfAlgebra H =
      CommHopfAlgCat.of k
        (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) := by
  rfl

/-- The finite constant group scheme representing the component quotient of a finite-type
affine group over an algebraically closed field. -/
noncomputable def componentGroupScheme
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Grp (Over (Spec (CommRingCat.of k))) :=
  ConstantGroup.groupScheme k (ConnectedComponents (PrimeSpectrum H))

/-- The component group scheme is relative spectrum applied to its coordinate Hopf algebra. -/
theorem componentGroupScheme_def (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    componentGroupScheme H =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).obj
        (op (componentGroupCoordinateHopfAlgebra H)) := by
  simpa only [componentGroupScheme, componentGroupCoordinateHopfAlgebra] using
    ConstantGroup.groupScheme_def k (ConnectedComponents (PrimeSpectrum H))

/-- The scheme underlying the component group is the spectrum of the function algebra on the
connected components. -/
@[simp]
theorem componentGroupScheme_X_left (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (componentGroupScheme H).X.left =
      Spec (CommRingCat.of
        (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)))) := by
  exact ConstantGroup.groupScheme_X_left k (ConnectedComponents (PrimeSpectrum H))

/-- The structural morphism of the component group is induced by the scalar inclusion into its
function algebra. -/
@[simp]
theorem componentGroupScheme_X_hom (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (componentGroupScheme H).X.hom =
      eqToHom (componentGroupScheme_X_left H) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k
            (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))))) := by
  exact ConstantGroup.groupScheme_X_hom k (ConnectedComponents (PrimeSpectrum H))

/-- The fppf component quotient is represented by the group scheme with the named component-group
coordinate Hopf algebra. -/
noncomputable def componentGroupRepresentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    componentGroupFppfSheaf H ≅
      CommHopfAlgCat.pointsFppfGroupObject (componentGroupCoordinateHopfAlgebra H) :=
  componentGroupFppfGroupObjectIso H ≪≫
    eqToIso (congrArg CommHopfAlgCat.pointsFppfGroupObject
      (componentGroupCoordinateHopfAlgebra_def H).symm)

/-- Under the named representation, the component quotient projection is the sheafified
component-coordinate morphism, followed only by the equality identifying the named coordinate
algebra. -/
theorem componentGroupFppfProjection_comp_componentGroupRepresentation_hom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    componentGroupFppfProjection H ≫ (componentGroupRepresentation H).hom =
      componentCoordinateFppfGroupObjectHom H ≫
        eqToHom (congrArg CommHopfAlgCat.pointsFppfGroupObject
          (componentGroupCoordinateHopfAlgebra_def H).symm) := by
  rw [componentGroupRepresentation, Iso.trans_hom, ← Category.assoc,
    componentGroupFppfProjection_comp_componentGroupFppfGroupObjectIso_hom]
  rfl

/-- The component group scheme is affine. -/
instance isAffine_componentGroupScheme (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsAffine (componentGroupScheme H).X.left := by
  unfold componentGroupScheme
  infer_instance

/-- The structural morphism of the component group scheme is finite. -/
instance isFinite_componentGroupScheme (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsFinite (componentGroupScheme H).X.hom := by
  unfold componentGroupScheme
  infer_instance

/-- The structural morphism of the component group scheme is etale. -/
instance etale_componentGroupScheme (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Etale (componentGroupScheme H).X.hom := by
  unfold componentGroupScheme
  infer_instance

end TauCeti.FiniteTypeCommHopfAlgCat
