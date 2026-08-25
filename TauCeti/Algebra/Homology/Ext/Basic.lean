/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Transport and exactness lemmas for `Ext` groups

This file collects general `Ext` API that Mathlib does not state in this form:

* the transport of `Extⁿ(X, Y)` along isomorphisms `X ≅ X'` and `Y ≅ Y'`, additively as
  `TauCeti.extAddEquivOfIso` and `R`-linearly as `TauCeti.extLinearEquivOfIso`;
* the vanishing of `Extⁿ(X, Y)` when either of the two objects is a zero object;
* Mathlib's long exact `Ext` sequences of a short exact sequence `S`, repackaged as
  `Function.Exact` statements about the composition maps: `TauCeti.exact_postcomp` and
  `TauCeti.exact_precomp` for `CategoryTheory.Abelian.Ext.postcomp` and
  `CategoryTheory.Abelian.Ext.precomp`, and `TauCeti.exact_postcompOfLinear` and
  `TauCeti.exact_precompOfLinear` for their `R`-linear forms.

The exactness statements are `CategoryTheory.Abelian.Ext.covariant_sequence_exact₂` and
`CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂` with the vanishing of the composite
supplied, which is what makes them usable with the `Function.Exact` API.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 2.4--2.7, for `Ext` and its long
  exact sequences.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-! ### Transport along isomorphisms -/

variable {X X' Y Y' : C}

/-- Isomorphisms `e : X ≅ X'` and `f : Y ≅ Y'` induce an isomorphism
`Extⁿ(X, Y) ≃ Extⁿ(X', Y')`, by composing with `e.inv` on the left and with `f.hom` on the right.
This is the action of an isomorphism through `CategoryTheory.Abelian.extFunctor`, spelled out so
that `TauCeti.extLinearEquivOfIso` can refine it to an `R`-linear equivalence. -/
noncomputable def extAddEquivOfIso (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) :
    Ext.{w} X Y n ≃+ Ext.{w} X' Y' n where
  toFun x := (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n)
  invFun y := (Ext.mk₀ e.hom).comp (y.comp (Ext.mk₀ f.inv) (add_zero n)) (zero_add n)
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp

/-- `TauCeti.extAddEquivOfIso` composes with `e.inv` and `f.hom`. -/
@[simp]
theorem extAddEquivOfIso_apply (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) (x : Ext.{w} X Y n) :
    extAddEquivOfIso e f n x =
      (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n) :=
  (rfl)

/-- The `R`-linear refinement of `TauCeti.extAddEquivOfIso`: in an `R`-linear abelian category,
isomorphisms `X ≅ X'` and `Y ≅ Y'` identify `Extⁿ(X, Y)` and `Extⁿ(X', Y')` as `R`-modules. -/
noncomputable def extLinearEquivOfIso (R : Type t) [CommRing R] [Linear R C] (e : X ≅ X')
    (f : Y ≅ Y') (n : ℕ) : Ext.{w} X Y n ≃ₗ[R] Ext.{w} X' Y' n where
  __ := extAddEquivOfIso e f n
  map_smul' r x := by simp [extAddEquivOfIso_apply]

/-- `TauCeti.extLinearEquivOfIso` composes with `e.inv` and `f.hom`. -/
@[simp]
theorem extLinearEquivOfIso_apply (R : Type t) [CommRing R] [Linear R C] (e : X ≅ X')
    (f : Y ≅ Y') (n : ℕ) (x : Ext.{w} X Y n) :
    extLinearEquivOfIso R e f n x =
      (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n) :=
  (rfl)

/-! ### Vanishing against a zero object -/

/-- There is no `Ext` out of a zero object, in any degree. -/
theorem subsingleton_ext_of_isZero_left (hX : IsZero X) (Y : C) (n : ℕ) :
    Subsingleton (Ext.{w} X Y n) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  rw [← Ext.mk₀_id_comp x, hX.eq_of_src (𝟙 X) 0, Ext.mk₀_zero, Ext.zero_comp]

/-- There is no `Ext` into a zero object, in any degree. -/
theorem subsingleton_ext_of_isZero_right (X : C) (hY : IsZero Y) (n : ℕ) :
    Subsingleton (Ext.{w} X Y n) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  rw [← Ext.comp_mk₀_id x, hY.eq_of_src (𝟙 Y) 0, Ext.mk₀_zero, Ext.comp_zero]

/-! ### The long exact sequences as `Function.Exact` statements -/

variable {S : ShortComplex C}

/-- Exactness of `Extⁿ(X, S.X₁) → Extⁿ(X, S.X₂) → Extⁿ(X, S.X₃)` at the middle term, for a short
exact sequence `S`. This is `CategoryTheory.Abelian.Ext.covariant_sequence_exact₂` packaged as a
`Function.Exact` statement about the postcomposition maps. -/
theorem exact_postcomp (hS : S.ShortExact) (X : C) (n : ℕ) :
    Function.Exact (Ext.postcomp (Ext.mk₀ S.f) X (add_zero n))
      (Ext.postcomp (Ext.mk₀ S.g) X (add_zero n)) := fun x₂ ↦
  ⟨fun hx ↦ Ext.covariant_sequence_exact₂ X hS x₂ hx, by
    rintro ⟨x₁, rfl⟩
    simp [S.zero]⟩

/-- Exactness of `Extⁿ(S.X₃, Y) → Extⁿ(S.X₂, Y) → Extⁿ(S.X₁, Y)` at the middle term, for a short
exact sequence `S`. This is `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂` packaged as
a `Function.Exact` statement about the precomposition maps. -/
theorem exact_precomp (hS : S.ShortExact) (Y : C) (n : ℕ) :
    Function.Exact (Ext.precomp (Ext.mk₀ S.g) Y (zero_add n))
      (Ext.precomp (Ext.mk₀ S.f) Y (zero_add n)) := fun x₂ ↦
  ⟨fun hx ↦ Ext.contravariant_sequence_exact₂ hS Y x₂ hx, by
    rintro ⟨x₃, rfl⟩
    simp [S.zero]⟩

/-- The linear postcomposition map has `CategoryTheory.Abelian.Ext.postcomp` as its underlying
function. -/
@[simp]
theorem coe_postcompOfLinear (R : Type t) [CommRing R] [Linear R C] {Y Z : C} {n a b : ℕ}
    (beta : Ext.{w} Y Z n) (X : C) (h : a + n = b) :
    ⇑(Ext.postcompOfLinear beta R X h) = Ext.postcomp beta X h :=
  rfl

/-- The linear precomposition map has `CategoryTheory.Abelian.Ext.precomp` as its underlying
function. -/
@[simp]
theorem coe_precompOfLinear (R : Type t) [CommRing R] [Linear R C] {X Y : C} {n a b : ℕ}
    (alpha : Ext.{w} X Y n) (Z : C) (h : n + a = b) :
    ⇑(Ext.precompOfLinear alpha R Z h) = Ext.precomp alpha Z h :=
  rfl

/-- The `R`-linear form of `TauCeti.exact_postcomp`. -/
theorem exact_postcompOfLinear (R : Type t) [CommRing R] [Linear R C] (hS : S.ShortExact) (X : C)
    (n : ℕ) :
    Function.Exact (Ext.postcompOfLinear (Ext.mk₀ S.f) R X (add_zero n))
      (Ext.postcompOfLinear (Ext.mk₀ S.g) R X (add_zero n)) := by
  simp only [coe_postcompOfLinear]
  exact exact_postcomp hS X n

/-- The `R`-linear form of `TauCeti.exact_precomp`. -/
theorem exact_precompOfLinear (R : Type t) [CommRing R] [Linear R C] (hS : S.ShortExact) (Y : C)
    (n : ℕ) :
    Function.Exact (Ext.precompOfLinear (Ext.mk₀ S.g) R Y (zero_add n))
      (Ext.precompOfLinear (Ext.mk₀ S.f) R Y (zero_add n)) := by
  simp only [coe_precompOfLinear]
  exact exact_precomp hS Y n

end TauCeti
