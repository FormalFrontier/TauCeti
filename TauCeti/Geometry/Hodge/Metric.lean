/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import TauCeti.Geometry.Hodge.HodgeForm

/-!
# The Hodge metric of a polarized Hodge structure

The positive-definite Hermitian Hodge form associated to a polarization defines a complex inner
product. This file packages that form as `InnerProductSpace.Core` data. It does not install a global
instance, since different choices of polarization on the same Hodge structure can give different
inner products.

The construction and sign convention follow Voisin, *Hodge Theory and Complex Algebraic Geometry I*,
§7.1.2, and Peters--Steenbrink, *Mixed Hodge Structures*, §2.

## Main declarations

* `TauCeti.Hodge.Polarization.hodgeInnerProductCore`: the Hodge form packaged as an
  `InnerProductSpace.Core`.

This is the positive Hermitian metric targeted in Layer L1 of
`TauCetiRoadmap/HodgeStructures/README.md`.
-/

public section

namespace TauCeti.Hodge.Polarization

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ}
variable {hs : HodgeStructure hℂ n}

/-- The Hodge form, packaged as the core of a complex inner-product-space structure. This is data,
not a global instance, so choosing a polarization does not create competing typeclass instances. -/
@[implicit_reducible]
noncomputable def hodgeInnerProductCore (P : Polarization hℂ hs) :
    InnerProductSpace.Core ℂ Vℂ where
  inner := fun x y ↦ P.hodgeForm x y
  conj_inner_symm x y := P.isSymm_hodgeForm.eq y x
  re_inner_nonneg x := (Complex.nonneg_iff.mp (P.hodgeForm_self_nonneg x)).1
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := P.hodgeForm_self_eq_zero_iff.mp hx

/-- The inner product in `hodgeInnerProductCore` is the Hodge form. -/
@[simp]
theorem hodgeInnerProductCore_inner (P : Polarization hℂ hs) (x y : Vℂ) :
    @inner ℂ Vℂ P.hodgeInnerProductCore.toInner x y = P.hodgeForm x y :=
  (rfl)

end TauCeti.Hodge.Polarization
