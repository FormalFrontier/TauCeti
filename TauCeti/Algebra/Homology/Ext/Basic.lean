/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Transport and exactness lemmas for `Ext` groups

This file collects general `Ext` API that Mathlib does not state in this form:

* the transport of `Extⁿ(X, Y)` along isomorphisms `X ≅ X'` and `Y ≅ Y'`, additively as
  `TauCeti.extAddEquivOfIso` and `R`-linearly as `TauCeti.extLinearEquivOfIso`;
* the vanishing of `Extⁿ(X, Y)` when either of the two objects is a zero object;
* short exact cokernel sequences, the cokernel sequence of the chosen embedding into an injective
  object, and a dimension-shift criterion for vanishing of the next `Ext` group;
* Mathlib's long exact `Ext` sequences of a short exact sequence `S`, repackaged as
  `Function.Exact` statements about the composition maps: `TauCeti.exact_postcomp` and
  `TauCeti.exact_precomp` for `CategoryTheory.Abelian.Ext.postcomp` and
  `CategoryTheory.Abelian.Ext.precomp`, and `TauCeti.exact_postcompOfLinear` and
  `TauCeti.exact_precompOfLinear` for their `R`-linear forms; `TauCeti.exact_precomp₃` and
  `TauCeti.exact_precompOfLinear₃` are the same repackaging one step further along the
  contravariant sequence, where the incoming map is precomposition with the extension class.

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

/-! ### Dimension shifting along an injective embedding -/

section DimensionShift

/-- The first map in the cokernel sequence of a monomorphism is a monomorphism. -/
instance mono_cokernelSequence_f {X Y : C} (f : X ⟶ Y) [Mono f] :
    Mono (ShortComplex.cokernelSequence f).f :=
  (inferInstance : Mono f)

/-- The middle object in a cokernel sequence is injective when the target of its first map is. -/
instance injective_cokernelSequence_X₂ {X Y : C} (f : X ⟶ Y) [Injective Y] :
    Injective (ShortComplex.cokernelSequence f).X₂ :=
  (inferInstance : Injective Y)

omit [HasExt C] in
/-- The cokernel sequence of a monomorphism is short exact. -/
lemma cokernelSequence_shortExact {X Y : C} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.cokernelSequence f).ShortExact :=
  { exact := ShortComplex.cokernelSequence_exact _ }

/-- A dimension-shift criterion along a short exact sequence with injective middle term: if
composition with its extension class vanishes, then the next `Ext` group is subsingleton. -/
lemma subsingleton_ext_succ_of_comp_extClass_eq_zero {S : ShortComplex C}
    (hS : S.ShortExact) [Injective S.X₂] (X : C) (n : ℕ)
    (hzero : ∀ x₃ : Ext X S.X₃ n, x₃.comp hS.extClass rfl = 0) :
    Subsingleton (Ext X S.X₁ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ X hS y
    (Ext.eq_zero_of_injective _) rfl
  exact hzero x₃

variable [EnoughInjectives C]

/-- The cokernel sequence of the chosen embedding of an object into an injective object. -/
noncomputable abbrev injectiveCokernelSequence (Y : C) : ShortComplex C :=
  ShortComplex.cokernelSequence (Injective.ι Y)

omit [HasExt C] in
/-- The cokernel sequence of the chosen embedding into an injective object is short exact. -/
lemma injectiveCokernelSequence_shortExact (Y : C) :
    (injectiveCokernelSequence Y).ShortExact :=
  cokernelSequence_shortExact _

/-- The dimension-shift criterion specialised to the chosen embedding into an injective object. -/
lemma subsingleton_ext_succ_of_injectiveCokernelSequence (X Y : C) (n : ℕ)
    (hzero : ∀ x₃ : Ext X (injectiveCokernelSequence Y).X₃ n,
      x₃.comp (injectiveCokernelSequence_shortExact Y).extClass rfl = 0) :
    Subsingleton (Ext X Y (n + 1)) :=
  subsingleton_ext_succ_of_comp_extClass_eq_zero
    (injectiveCokernelSequence_shortExact Y) X n hzero

end DimensionShift

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

/-- Exactness of `Extⁿ⁰(S.X₁, Y) → Extⁿ¹(S.X₃, Y) → Extⁿ¹(S.X₂, Y)` at the middle term, for a
short exact sequence `S` and `n₁ = 1 + n₀`. The first map is precomposition with the extension
class of `S`. This is `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃'` with its
`AddCommGrpCat` wrapper removed. -/
theorem exact_precomp₃ (hS : S.ShortExact) (Y : C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    Function.Exact (Ext.precomp hS.extClass Y h)
      (Ext.precomp (Ext.mk₀ S.g) Y (zero_add n₁)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.contravariant_sequence_exact₃' hS Y n₀ n₁ h)

/-- The `R`-linear form of `TauCeti.exact_precomp₃`. -/
theorem exact_precompOfLinear₃ (R : Type t) [CommRing R] [Linear R C] (hS : S.ShortExact) (Y : C)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    Function.Exact (Ext.precompOfLinear hS.extClass R Y h)
      (Ext.precompOfLinear (Ext.mk₀ S.g) R Y (zero_add n₁)) := by
  simp only [coe_precompOfLinear]
  exact exact_precomp₃ hS Y n₀ n₁ h

end TauCeti
