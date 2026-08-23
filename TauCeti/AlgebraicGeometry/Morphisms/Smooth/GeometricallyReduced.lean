/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Smooth morphisms are geometrically reduced

A smooth morphism of schemes has geometrically reduced fibres. After base change to a field,
smoothness is preserved, and an affine cover of the source has smooth coordinate algebras over
the ring of global functions of the target. That ring is isomorphic to the field, so the
coordinate algebras are reduced by `TauCeti.isReduced_of_smooth_of_field`.

The main result is the instance `AlgebraicGeometry.Smooth.geometricallyReduced`. It supplies the
geometric-reducedness half of the Jacobian challenge's standing-hypotheses deduction that a
smooth, geometrically connected curve is geometrically integral. The remaining irreducibility
half uses that the local rings of a smooth scheme over a field are regular domains.

No formalization is vendored. The commutative-algebra input is
`TauCeti.isReduced_of_smooth_of_field`; the passage from affine opens to the whole scheme uses
Mathlib's `AlgebraicGeometry.IsReduced.of_openCover`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

private theorem isReduced_of_smooth_toSpec_field (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f] : IsReduced X := by
  let hred : ∀ i, IsReduced (X.affineCover.X i) := fun i ↦ by
    let _ := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
    have hf : ((X.affineCover.f i ≫ f).appTop).hom.Smooth :=
      HasRingHomProperty.appTop @Smooth _
        (HasRingHomProperty.comp_of_isOpenImmersion @Smooth (X.affineCover.f i) f inferInstance)
    let _ : Algebra Γ(Spec (.of K), ⊤) Γ(X.affineCover.X i, ⊤) :=
      ((X.affineCover.f i ≫ f).appTop).hom.toAlgebra
    let _ : Algebra.Smooth Γ(Spec (.of K), ⊤) Γ(X.affineCover.X i, ⊤) := hf.toAlgebra
    let _ : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
      isReduced_of_smooth_of_field Γ(Spec (.of K), ⊤) Γ(X.affineCover.X i, ⊤)
    exact isReduced_of_isAffine_isReduced (X.affineCover.X i)
  exact @IsReduced.of_openCover X X.affineCover hred

/-- Every smooth morphism of schemes is geometrically reduced. -/
instance (priority := low) Smooth.geometricallyReduced {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] : GeometricallyReduced f := by
  constructor
  intro K _ y Z fst snd h
  let _ : Smooth snd := MorphismProperty.of_isPullback h inferInstance
  exact isReduced_of_smooth_toSpec_field K snd

end AlgebraicGeometry

end TauCeti
