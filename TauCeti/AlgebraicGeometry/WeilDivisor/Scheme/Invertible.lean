/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Regular
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# The sheaf of a principal Weil divisor is a line bundle

Let `X` be a Noetherian integral scheme of dimension at most one whose codimension-one local
rings are discrete valuation rings. This file identifies the sheaf `𝒪_X(0)` of the zero divisor
with the structure sheaf and deduces that `𝒪_X(D)` is an invertible sheaf whenever `D` is the
divisor of a nonzero rational function.

## Main declarations

* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.mem_sections_zero_iff`: the sections of `𝒪_X(0)`
  over an open subset are exactly the regular functions there;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.unitIsoSheafZero`: the induced isomorphism
  `𝒪_X ≅ 𝒪_X(0)`;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.sheafPrincipalDivisorIsoUnit`: the trivialization
  `𝒪_X(div g) ≅ 𝒪_X` of the sheaf of a principal divisor;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.isInvertible_sheaf_principalDivisor`: the sheaf of
  a principal divisor is an invertible sheaf on `X`.

Together with the already available fact that linearly equivalent divisors have isomorphic
sheaves, this is the statement that the map `D ↦ 𝒪_X(D)` sends the trivial divisor class to the
trivial line bundle. It advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors
on a curve: Weil divisors `⊕_x ℤ` and Cartier divisors; the dictionaries `Cartier ≃ line bundles`
and (smooth curve) `Weil ≃ Cartier`; principal divisors; `Cl(X) ≅ Pic X`". Invertibility of
`𝒪_X(D)` for a merely locally principal `D` needs the same argument carried out over the members
of a trivializing cover, and is left to subsequent work.

The identification `𝒪_X(0) = 𝒪_X` follows Hartshorne, *Algebraic Geometry*, Proposition II.6.11.
No formalization is vendored. The construction reuses the submodule-of-a-sheaf API and the
multiplication isomorphisms of `TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Sheaf.lean`, and
Mathlib's fully faithful forgetful functor from `𝒪_X`-modules to presheaves of abelian groups.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

noncomputable section

/-- **The sections of `𝒪_X(0)` are the regular functions.** On a scheme of dimension at most one,
a rational function with no poles on `U` is regular on `U`, so the sections of the sheaf of the
zero divisor over `U` are exactly the images of the sections of `𝒪_X`. -/
theorem mem_sections_zero_iff (hX : ∀ y : X, coheight y ≤ 1) {U : X.Opens}
    (s : Γ(Scheme.rationalFunctions X, U)) :
    s ∈ sections (0 : SchemeWeilDivisor X) U ↔
      ∃ a : Γ(X, U), Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) U a = s := by
  rcases isEmpty_or_nonempty U with hU | hU
  · have hbot : U = ⊥ := by
      ext x
      simpa using fun hx ↦ hU.elim ⟨x, hx⟩
    have := Scheme.subsingleton_rationalFunctions U hbot
    exact ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩,
      fun _ ↦ by rw [sections_eq_top_of_eq_bot _ hbot]; trivial⟩
  constructor
  · intro hs
    have hord : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
        0 ≤ X.ord (Scheme.rationalFunctionsEquiv U s) y := by
      rcases mem_sections_iff.mp hs with h0 | h
      · intro y _
        rw [h0]
        simp
      · exact fun y hy ↦ by simpa using h y hy
    obtain ⟨a, ha⟩ :=
      Scheme.exists_germToFunctionField_eq_of_ord_nonneg (fun y _ ↦ hX y) hord
    refine ⟨a, (Scheme.rationalFunctionsEquiv U).injective ?_⟩
    rw [Scheme.rationalFunctionsEquiv_toRationalFunctions_app, ha]
  · rintro ⟨a, rfl⟩
    exact toRationalFunctions_app_mem_sections WeilDivisor.isEffective_zero U a

/-- **The sheaf of the zero divisor is the structure sheaf.** The canonical factorization of
`𝒪_X ⟶ 𝒦_X` through `𝒪_X(0)` is an isomorphism: it is injective because `𝒪_X ⟶ 𝒦_X` is, and
surjective because a rational function without poles is regular. -/
theorem isIso_unitToSheaf_zero (hX : ∀ y : X, coheight y ≤ 1) :
    IsIso (unitToSheaf (D := (0 : SchemeWeilDivisor X)) WeilDivisor.isEffective_zero) := by
  have key : ∀ (U : X.Opens) (a : Γ(SheafOfModules.unit X.ringCatSheaf, U)),
      Scheme.Modules.Hom.app (sheafι (0 : SchemeWeilDivisor X)) U
          (Scheme.Modules.Hom.app
            (unitToSheaf (D := (0 : SchemeWeilDivisor X)) WeilDivisor.isEffective_zero) U a) =
        Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) U a := by
    intro U a
    exact congrArg (fun φ ↦ Scheme.Modules.Hom.app φ U a)
      (unitToSheaf_ι (D := (0 : SchemeWeilDivisor X)) WeilDivisor.isEffective_zero)
  have h : ∀ U : X.Opens, IsIso (Scheme.Modules.Hom.app
      (unitToSheaf (D := (0 : SchemeWeilDivisor X)) WeilDivisor.isEffective_zero) U) := by
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro a b hab
      refine Scheme.toRationalFunctions_app_injective U ?_
      rw [← key U a, ← key U b, hab]
    · intro t
      obtain ⟨a, ha⟩ :=
        (mem_sections_zero_iff hX _).mp (sheafι_app_mem (0 : SchemeWeilDivisor X) U t)
      exact ⟨a, sheafι_app_injective (0 : SchemeWeilDivisor X) U (by rw [key U a, ha])⟩
  exact Scheme.Modules.Hom.isIso_iff_isIso_app.mpr h

/-- The isomorphism `𝒪_X ≅ 𝒪_X(0)` given by `SchemeWeilDivisor.isIso_unitToSheaf_zero`. -/
def unitIsoSheafZero (hX : ∀ y : X, coheight y ≤ 1) :
    @Iso X.Modules _ (SheafOfModules.unit X.ringCatSheaf) (sheaf (0 : SchemeWeilDivisor X)) :=
  @asIso _ _ _ _ (unitToSheaf (D := (0 : SchemeWeilDivisor X)) WeilDivisor.isEffective_zero)
    (isIso_unitToSheaf_zero hX)

/-- The forward map of `SchemeWeilDivisor.unitIsoSheafZero` is the canonical factorization of
`𝒪_X ⟶ 𝒦_X` through `𝒪_X(0)`. -/
@[simp]
lemma unitIsoSheafZero_hom (hX : ∀ y : X, coheight y ≤ 1) :
    (unitIsoSheafZero hX).hom =
      unitToSheaf (D := (0 : SchemeWeilDivisor X)) WeilDivisor.isEffective_zero :=
  (rfl)

/-- **The sheaf of a principal divisor is trivial.** Multiplication by `g` identifies
`𝒪_X(div g)` with `𝒪_X(0)`, which is the structure sheaf. -/
def sheafPrincipalDivisorIsoUnit (hX : ∀ y : X, coheight y ≤ 1)
    (g : Additive X.functionFieldˣ) :
    sheaf ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  sheafMulIso g _ ≪≫ eqToIso (congrArg sheaf (sub_self _)) ≪≫ (unitIsoSheafZero hX).symm

/-- The sheaf of the zero divisor is an invertible sheaf. -/
theorem isInvertible_sheaf_zero (hX : ∀ y : X, coheight y ≤ 1) :
    SheafOfModules.isInvertible X (sheaf (0 : SchemeWeilDivisor X)) :=
  TauCeti.SheafOfModules.IsInvertible.of_iso
    (M := SheafOfModules.unit X.ringCatSheaf) (N := sheaf (0 : SchemeWeilDivisor X))
    (unitIsoSheafZero hX)

/-- **The sheaf of a principal Weil divisor is a line bundle.** This is the case of the
divisor-to-line-bundle dictionary in which the divisor is globally the divisor of a rational
function; it sends the trivial divisor class to the trivial line bundle. -/
theorem isInvertible_sheaf_principalDivisor (hX : ∀ y : X, coheight y ≤ 1)
    (g : Additive X.functionFieldˣ) :
    SheafOfModules.isInvertible X
      (sheaf ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g)) :=
  TauCeti.SheafOfModules.IsInvertible.of_iso
    (M := SheafOfModules.unit X.ringCatSheaf)
    (N := sheaf ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g))
    (sheafPrincipalDivisorIsoUnit hX g).symm

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
