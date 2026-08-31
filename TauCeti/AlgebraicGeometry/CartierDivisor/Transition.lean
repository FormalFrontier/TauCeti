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

/-- The defining equation for `transitionUnit` remains valid after restriction to a refinement.
-/
@[simp]
lemma transitionUnit_restrict_spec (D : CartierDivisor X) {U V W : X.Opens}
    (f : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (g : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ))
    (hf : ((toCartierDivisorSheaf X).hom.app (op U)).hom f = D |_ U)
    (hg : ((toCartierDivisorSheaf X).hom.app (op V)).hom g = D |_ V)
    (hW : W ≤ U ⊓ V) :
    ((toRationalUnitSheaf X).hom.app (op W)).hom
        (TopCat.Presheaf.restrictOpen (F := (regularUnitSheaf X).presheaf)
          (transitionUnit D f g hf hg) W hW) = f |_ W - g |_ W := by
  calc
    _ = (((toRationalUnitSheaf X).hom.app (op (U ⊓ V))).hom
        (transitionUnit D f g hf hg)) |_ W :=
      TopCat.Presheaf.map_restrict (toRationalUnitSheaf X).hom hW _
    _ = (f |_ (U ⊓ V) - g |_ (U ⊓ V)) |_ W := by rw [transitionUnit_spec]
    _ = f |_ W - g |_ W := by
      have hfres := TopCat.Presheaf.restrict_restrict
        (F := (rationalUnitSheaf X).presheaf) hW inf_le_left f
      have hgres := TopCat.Presheaf.restrict_restrict
        (F := (rationalUnitSheaf X).presheaf) hW inf_le_right g
      simpa only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_sub] using
        congrArg₂ (· - ·) hfres hgres

/-- A local equation has trivial transition unit with itself. -/
@[simp]
lemma transitionUnit_self (D : CartierDivisor X) {U : X.Opens}
    (f : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (hf : ((toCartierDivisorSheaf X).hom.app (op U)).hom f = D |_ U) :
    transitionUnit D f f hf hf = 0 := by
  symm
  apply transitionUnit_eq_of_spec D f f hf hf
  rw [sub_self]
  exact AddMonoidHom.map_zero ((toRationalUnitSheaf X).hom.app (op (U ⊓ U))).hom

/-- Reversing two local equations inverts their transition unit on every common refinement. -/
lemma transitionUnit_symm_restrict (D : CartierDivisor X) {U V W : X.Opens}
    (f : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (g : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ))
    (hf : ((toCartierDivisorSheaf X).hom.app (op U)).hom f = D |_ U)
    (hg : ((toCartierDivisorSheaf X).hom.app (op V)).hom g = D |_ V)
    (hW : W ≤ U ⊓ V) :
    TopCat.Presheaf.restrictOpen (F := (regularUnitSheaf X).presheaf)
        (transitionUnit D g f hg hf) W (by simpa [inf_comm] using hW) =
      -(TopCat.Presheaf.restrictOpen (F := (regularUnitSheaf X).presheaf)
        (transitionUnit D f g hf hg) W hW) := by
  have hW' : W ≤ V ⊓ U := by simpa [inf_comm] using hW
  apply toRationalUnitSheaf_app_injective X W
  rw [transitionUnit_restrict_spec D g f hg hf hW']
  rw [map_neg, transitionUnit_restrict_spec D f g hf hg hW]
  simp

/-- Transition units satisfy the cocycle identity on every triple overlap. -/
lemma transitionUnit_cocycle (D : CartierDivisor X) {U V W T : X.Opens}
    (f : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (g : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ))
    (h : Additive (((rationalFunctionsRing X).presheaf.obj (op W))ˣ))
    (hf : ((toCartierDivisorSheaf X).hom.app (op U)).hom f = D |_ U)
    (hg : ((toCartierDivisorSheaf X).hom.app (op V)).hom g = D |_ V)
    (hh : ((toCartierDivisorSheaf X).hom.app (op W)).hom h = D |_ W)
    (hT : T ≤ U ⊓ V ⊓ W) :
    TopCat.Presheaf.restrictOpen (F := (regularUnitSheaf X).presheaf)
        (transitionUnit D f h hf hh) T (by
          exact le_inf
            (le_trans (le_trans hT inf_le_left) inf_le_left)
            (le_trans hT inf_le_right)) =
      TopCat.Presheaf.restrictOpen (F := (regularUnitSheaf X).presheaf)
        (transitionUnit D f g hf hg) T (le_trans hT inf_le_left) +
        TopCat.Presheaf.restrictOpen (F := (regularUnitSheaf X).presheaf)
          (transitionUnit D g h hg hh) T (by
            exact le_inf
              (le_trans (le_trans hT inf_le_left) inf_le_right)
              (le_trans hT inf_le_right)) := by
  have hT_uh : T ≤ U ⊓ W := by
    exact le_inf
      (le_trans (le_trans hT inf_le_left) inf_le_left)
      (le_trans hT inf_le_right)
  have hT_uv : T ≤ U ⊓ V := le_trans hT (inf_le_left)
  have hT_vw : T ≤ V ⊓ W := by
    exact le_inf
      (le_trans (le_trans hT inf_le_left) inf_le_right)
      (le_trans hT inf_le_right)
  apply toRationalUnitSheaf_app_injective X T
  rw [transitionUnit_restrict_spec D f h hf hh hT_uh]
  rw [map_add, transitionUnit_restrict_spec D f g hf hg hT_uv,
    transitionUnit_restrict_spec D g h hg hh hT_vw]
  abel

end CartierDivisor

end Scheme

end

end AlgebraicGeometry

end TauCeti
