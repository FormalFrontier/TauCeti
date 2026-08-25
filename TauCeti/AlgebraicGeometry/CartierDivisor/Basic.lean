/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import TauCeti.CategoryTheory.Sites.Units
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Cartier divisors on an integral scheme

Let `X` be an integral scheme and let `𝒦_X` be its sheaf of rational functions. The Cartier
divisor sheaf is the quotient

`𝒦_X^× / 𝒪_X^×`,

and a Cartier divisor is a global section of this quotient sheaf. The quotient is a sheaf
quotient, not the pointwise quotient of groups of sections: its sections are represented locally
by nonzero rational functions, with two representatives identified when their ratio is a regular
unit.

## Main declarations

* `Scheme.regularUnitSheaf` and `Scheme.rationalUnitSheaf` are the sheaves of units of `𝒪_X` and
  `𝒦_X`, written additively;
* `Scheme.toRationalUnitSheaf` is the inclusion `𝒪_X^× ⟶ 𝒦_X^×`;
* `Scheme.cartierDivisorSheaf` is its cokernel in sheaves of abelian groups;
* `Scheme.CartierDivisor` is the additive group of global sections of that cokernel;
* `Scheme.principalCartierDivisor` sends a nonzero rational function to its principal Cartier
  divisor.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Cartier divisors; the
dictionaries `Cartier ≃ line bundles` and (smooth curve) `Weil ≃ Cartier`". The rational-function
sheaf was constructed in `TauCeti/AlgebraicGeometry/Modules/RationalFunctions.lean`; the next step
is to construct `𝒪_X(D)` from a Cartier divisor and prove the Cartier--line-bundle dictionary.

The definition follows the Stacks Project, *Divisors* (Tag 02AR). No formalization is vendored.
The sheaf quotient is Mathlib's categorical cokernel in the abelian category of sheaves of
abelian groups.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The sheaf `𝒪_X^×` of regular units, regarded as a sheaf of additive commutative groups. -/
noncomputable abbrev regularUnitSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).obj X.sheaf

/-- The sheaf `𝒦_X^×` of nonzero rational functions, regarded as a sheaf of additive
commutative groups. -/
noncomputable abbrev rationalUnitSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).obj
    (rationalFunctionsRing X)

/-- The inclusion `𝒪_X^× ⟶ 𝒦_X^×` of regular units into nonzero rational functions. -/
def toRationalUnitSheaf : regularUnitSheaf X ⟶ rationalUnitSheaf X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).map
    (toRationalFunctionsRing X)

/-- The Cartier-divisor sheaf `𝒦_X^× / 𝒪_X^×`. This is the cokernel in the category of sheaves
of abelian groups, and hence is the sheafification of the pointwise quotient presheaf.

Use Mathlib's generic `cokernel.desc`, `cokernel.π_desc`, and cancellation through
`cokernel.π` for its universal property. -/
def cartierDivisorSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  cokernel (toRationalUnitSheaf X)

/-- The quotient projection `𝒦_X^× ⟶ 𝒦_X^× / 𝒪_X^×`. -/
def toCartierDivisorSheaf : rationalUnitSheaf X ⟶ cartierDivisorSheaf X :=
  cokernel.π (toRationalUnitSheaf X)

/-- The quotient projection to the Cartier-divisor sheaf is an epimorphism. -/
instance : Epi (toCartierDivisorSheaf X) := by
  dsimp only [toCartierDivisorSheaf]
  exact Cofork.IsColimit.epi (colimit.isColimit _)

/-- A regular unit has zero class in the Cartier-divisor sheaf. -/
@[reassoc (attr := simp)]
lemma toRationalUnitSheaf_comp_toCartierDivisorSheaf :
    toRationalUnitSheaf X ≫ toCartierDivisorSheaf X = 0 :=
  cokernel.condition (toRationalUnitSheaf X)

/-- The group of Cartier divisors on `X`, defined as the global sections of
`𝒦_X^× / 𝒪_X^×`. -/
abbrev CartierDivisor : Type u :=
  ((cartierDivisorSheaf X).obj.obj (op (⊤ : X.Opens)) : Type u)

/-- The map on global sections induced by the quotient projection from `𝒦_X^×` to the
Cartier-divisor sheaf. Its source is the group of units of `Γ(X, 𝒦_X)`, written additively. -/
def toCartierDivisor :
    Additive (((rationalFunctionsRing X).presheaf.obj (op (⊤ : X.Opens)))ˣ) →+
      CartierDivisor X :=
  ((toCartierDivisorSheaf X).hom.app (op (⊤ : X.Opens))).hom

/-- A global regular unit maps to zero under the quotient map to Cartier divisors. -/
@[simp]
lemma toRationalUnitSheaf_app_comp_toCartierDivisor :
    (toCartierDivisor X).comp
        ((toRationalUnitSheaf X).hom.app (op (⊤ : X.Opens))).hom = 0 := by
  have h :
      (toRationalUnitSheaf X).hom ≫ (toCartierDivisorSheaf X).hom = 0 :=
    congrArg (fun f => f.hom) (toRationalUnitSheaf_comp_toCartierDivisorSheaf X)
  have h :
      (toRationalUnitSheaf X).hom.app (op (⊤ : X.Opens)) ≫
          (toCartierDivisorSheaf X).hom.app (op (⊤ : X.Opens)) = 0 :=
    congrArg (fun f => f.app (op (⊤ : X.Opens))) h
  have h := congrArg (fun f => f.hom) h
  exact h

local instance : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice (inferInstanceAs (Nonempty X)), by simp⟩⟩

/-- On the whole space, the units of the rational-function sheaf are the units of the function
field. -/
def rationalUnitSectionsEquiv :
    Additive (((rationalFunctionsRing X).presheaf.obj (op (⊤ : X.Opens)))ˣ) ≃+
      Additive X.functionFieldˣ := by
  exact (Units.mapEquiv (rationalFunctionsRingEquiv (⊤ : X.Opens)).toMulEquiv).toAdditive

/-- The global rational-unit equivalence applies the rational-functions equivalence to a
unit. -/
@[simp]
lemma rationalUnitSectionsEquiv_apply
    (f : ((rationalFunctionsRing X).presheaf.obj (op (⊤ : X.Opens)))ˣ) :
    rationalUnitSectionsEquiv X (Additive.ofMul f) =
      Additive.ofMul (Units.map
        (rationalFunctionsRingEquiv (⊤ : X.Opens)).toMonoidHom f) := by
  rfl

/-- The homomorphism from global regular units to units of the function field induced by the
germ map. -/
noncomputable def regularUnitToFunctionField :
    ((X.presheaf.obj (op (⊤ : X.Opens))) : Type u)ˣ →* X.functionFieldˣ := by
  exact Units.map (X.germToFunctionField (⊤ : X.Opens)).hom.toMonoidHom

/-- The map on regular units applies the germ map to the underlying section. -/
@[simp]
lemma regularUnitToFunctionField_apply
    (f : ((X.presheaf.obj (op (⊤ : X.Opens))) : Type u)ˣ) :
    regularUnitToFunctionField X f =
      Units.map (X.germToFunctionField (⊤ : X.Opens)).hom.toMonoidHom f := by
  rfl

/-- The equivalence from global rational units to function-field units carries the image of a
global regular unit to the unit induced by its germ in the function field. -/
lemma rationalUnitSectionsEquiv_toRationalUnitSheaf_app
    (f : ((X.presheaf.obj (op (⊤ : X.Opens))) : Type u)ˣ) :
    rationalUnitSectionsEquiv X
        (((toRationalUnitSheaf X).hom.app (op (⊤ : X.Opens))).hom (Additive.ofMul f)) =
      Additive.ofMul (regularUnitToFunctionField X f) := by
  have hunit :
      ((toRationalUnitSheaf X).hom.app (op (⊤ : X.Opens))).hom (Additive.ofMul f) =
        Additive.ofMul (Units.map
          ((toRationalFunctionsRing X).hom.app
            (op (⊤ : X.Opens))).hom.toMonoidHom f) :=
    CategoryTheory.Sheaf.additiveUnitsFunctor_map_app_apply
      (Opens.grothendieckTopology X) (toRationalFunctionsRing X)
        (op (⊤ : X.Opens)) (Additive.ofMul f)
  rw [hunit, rationalUnitSectionsEquiv_apply, regularUnitToFunctionField_apply]
  apply congrArg Additive.ofMul
  apply Units.ext
  simp only [Units.coe_map]
  -- The units API exposes underlying values, while the rational-functions comparison
  -- theorems use the definitionally equal module-sheaf section type.
  change rationalFunctionsRingEquiv (⊤ : X.Opens)
      ((toRationalFunctionsRing X).hom.app (op (⊤ : X.Opens)) (f : Γ(X, ⊤))) =
    X.germToFunctionField (⊤ : X.Opens) f
  rw [← toRationalFunctionsRing_app, ← rationalFunctionsEquiv_apply,
    rationalFunctionsEquiv_toRationalFunctions_app]

/-- A nonzero rational function determines its principal Cartier divisor. The multiplicative
group of the function field is written additively in the domain. -/
def principalCartierDivisorAddHom : Additive X.functionFieldˣ →+ CartierDivisor X :=
  (toCartierDivisor X).comp (rationalUnitSectionsEquiv X).symm.toAddMonoidHom

/-- The principal Cartier divisor of a nonzero rational function. -/
def principalCartierDivisor (f : X.functionFieldˣ) : CartierDivisor X :=
  principalCartierDivisorAddHom X (Additive.ofMul f)

/-- The principal Cartier divisor of one is zero. -/
@[simp]
lemma principalCartierDivisor_one : principalCartierDivisor X 1 = 0 :=
  map_zero (principalCartierDivisorAddHom X)

/-- The principal Cartier divisor of a product is the sum of the principal Cartier divisors. -/
@[simp]
lemma principalCartierDivisor_mul (f g : X.functionFieldˣ) :
    principalCartierDivisor X (f * g) =
      principalCartierDivisor X f + principalCartierDivisor X g :=
  map_add (principalCartierDivisorAddHom X) (Additive.ofMul f) (Additive.ofMul g)

/-- The principal Cartier divisor of an inverse is the negation of the principal Cartier
divisor. -/
@[simp]
lemma principalCartierDivisor_inv (f : X.functionFieldˣ) :
    principalCartierDivisor X f⁻¹ = -principalCartierDivisor X f :=
  map_neg (principalCartierDivisorAddHom X) (Additive.ofMul f)

/-- A global regular unit has zero principal Cartier divisor. -/
@[simp]
lemma principalCartierDivisor_regularUnitToFunctionField
    (f : ((X.presheaf.obj (op (⊤ : X.Opens))) : Type u)ˣ) :
    principalCartierDivisor X
      (Units.map (X.germToFunctionField (⊤ : X.Opens)).hom f) = 0 := by
  refine (congrArg (principalCartierDivisor X)
    (regularUnitToFunctionField_apply X f).symm).trans ?_
  have hsymm :
      (rationalUnitSectionsEquiv X).symm
          (Additive.ofMul (regularUnitToFunctionField X f)) =
        ((toRationalUnitSheaf X).hom.app
          (op (⊤ : X.Opens))).hom (Additive.ofMul f) := by
    apply (rationalUnitSectionsEquiv X).injective
    rw [AddEquiv.apply_symm_apply]
    exact (rationalUnitSectionsEquiv_toRationalUnitSheaf_app X f).symm
  calc
    principalCartierDivisor X (regularUnitToFunctionField X f) =
        (toCartierDivisor X) ((rationalUnitSectionsEquiv X).symm
          (Additive.ofMul (regularUnitToFunctionField X f))) := rfl
    _ = (toCartierDivisor X)
        (((toRationalUnitSheaf X).hom.app
          (op (⊤ : X.Opens))).hom (Additive.ofMul f)) := congrArg _ hsymm
    _ = 0 := by
      have hzero := DFunLike.congr_fun
        (toRationalUnitSheaf_app_comp_toCartierDivisor X) (Additive.ofMul f)
      -- Evaluating the categorical composite gives the definitionally equal composite of
      -- the underlying additive homomorphisms.
      change (toCartierDivisor X)
        (((toRationalUnitSheaf X).hom.app
          (op (⊤ : X.Opens))).hom (Additive.ofMul f)) = 0 at hzero
      exact hzero

end Scheme

end

end AlgebraicGeometry

end TauCeti
