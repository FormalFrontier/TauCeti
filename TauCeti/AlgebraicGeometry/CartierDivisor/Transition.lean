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
