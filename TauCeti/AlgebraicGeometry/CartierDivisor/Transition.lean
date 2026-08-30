/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.LocalEquations

/-!
# Transition units for Cartier divisors

Local equations for a Cartier divisor differ by regular units on overlaps.  This file packages
that unit and exposes the restriction compatibility needed to glue the local copies of the
structure sheaf:

* `CartierDivisor.transitionUnit` chooses the unique unit between two local equations;
* `regularUnitRestrict` identifies the underlying structure-sheaf restriction map;
* `transitionUnit_spec` exposes the defining equation for the chosen unit.

This prepares the exact descent datum used in the Cartier-divisor-to-line-bundle construction in
Layer A of `TauCetiRoadmap/JacobianChallenge/README.md`; no smoothness or Noetherian hypothesis
is needed for this part.  The construction follows Hartshorne, *Algebraic Geometry*, II.6, and
the Stacks Project, *Divisors*, Tag 02AR.  It reuses the local equation and uniqueness theorem from
`TauCeti.AlgebraicGeometry.CartierDivisor.LocalEquations`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X]

namespace CartierDivisor

/-- Restriction of a regular unit, expressed using the underlying structure sheaf. -/
def regularUnitRestrict {U V : X.Opens} (e : U ≤ V)
    (r : Additive (((X.presheaf.obj (op V)) : Type u)ˣ)) :
    Additive (((X.presheaf.obj (op U)) : Type u)ˣ) :=
  Additive.ofMul
    (Units.map (X.presheaf.map (homOfLE e).op).hom.toMonoidHom (Additive.toMul r))

@[simp]
lemma toRationalUnitSheaf_regularUnitRestrict {U V : X.Opens} (e : U ≤ V)
    (r : Additive (((X.presheaf.obj (op V)) : Type u)ˣ)) :
    ((toRationalUnitSheaf X).hom.app (op U)).hom
        (regularUnitRestrict (X := X) e r) =
      ((toRationalUnitSheaf X).hom.app (op V)).hom r |_ₗ U ⟪e⟫ := by
  -- Unfold the additive-units presheaf map so that naturality applies directly.
  change ((toRationalUnitSheaf X).hom.app (op U)).hom
      ((regularUnitSheaf X).presheaf.map (homOfLE e).op r) = _
  exact TopCat.Presheaf.map_restrict (toRationalUnitSheaf X).hom e r

/-- The regular unit relating two chosen local equations of a Cartier divisor. -/
noncomputable def transitionUnit (D : CartierDivisor X) {U V : X.Opens}
    (f : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (g : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ))
    (hf : ((toCartierDivisorSheaf X).hom.app (op U)).hom f = D |_ U)
    (hg : ((toCartierDivisorSheaf X).hom.app (op V)).hom g = D |_ V) :
    Additive (((X.presheaf.obj (op (U ⊓ V))) : Type u)ˣ) :=
  (existsUnique_transitionUnit X D f g hf hg).choose

/-- The defining equation for `transitionUnit`. -/
@[simp]
lemma transitionUnit_spec (D : CartierDivisor X) {U V : X.Opens}
    (f : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (g : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ))
    (hf : ((toCartierDivisorSheaf X).hom.app (op U)).hom f = D |_ U)
    (hg : ((toCartierDivisorSheaf X).hom.app (op V)).hom g = D |_ V) :
    ((toRationalUnitSheaf X).hom.app (op (U ⊓ V))).hom
        (transitionUnit D f g hf hg) = f |_ (U ⊓ V) - g |_ (U ⊓ V) :=
  (existsUnique_transitionUnit X D f g hf hg).choose_spec.1

/-- The transition unit is uniquely determined by its defining equation. -/
lemma transitionUnit_eq_of_spec (D : CartierDivisor X) {U V : X.Opens}
    (f : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (g : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ))
    (hf : ((toCartierDivisorSheaf X).hom.app (op U)).hom f = D |_ U)
    (hg : ((toCartierDivisorSheaf X).hom.app (op V)).hom g = D |_ V)
    {r : Additive (((X.presheaf.obj (op (U ⊓ V))) : Type u)ˣ)}
    (hr : ((toRationalUnitSheaf X).hom.app (op (U ⊓ V))).hom r =
      f |_ (U ⊓ V) - g |_ (U ⊓ V)) :
    r = transitionUnit D f g hf hg :=
  (existsUnique_transitionUnit X D f g hf hg).choose_spec.2 r hr

end CartierDivisor

end Scheme

end

end AlgebraicGeometry

end TauCeti
