/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The long exact cohomology sequence of a short exact sequence of abelian sheaves

Mathlib defines the cohomology `CategoryTheory.Sheaf.H F n` of an abelian sheaf `F` on a site
`(C, J)` as the `Ext`-group in degree `n` from the constant sheaf `ℤ` to `F`. A short exact
sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of abelian sheaves therefore has a long exact cohomology
sequence

`⋯ ⟶ Hⁿ⁰(F₁) ⟶ Hⁿ⁰(F₂) ⟶ Hⁿ⁰(F₃) ⟶ Hⁿ¹(F₁) ⟶ Hⁿ¹(F₂) ⟶ Hⁿ¹(F₃) ⟶ ⋯`

whose connecting map is composition with the extension class of the sequence. This file records
it, in the form in which it is used: a connecting homomorphism together with the exactness of
each of the three consecutive pairs.

## Main declarations

* `TauCeti.CategoryTheory.Sheaf.H.δ`, the connecting map `Hⁿ⁰(F₃) →+ Hⁿ¹(F₁)`;
* `TauCeti.CategoryTheory.Sheaf.H.exact_map_map`, `H.exact_map_δ` and `H.exact_δ_map`, the
  exactness of the sequence at `Hⁿ(F₂)`, at `Hⁿ⁰(F₃)` and at `Hⁿ¹(F₁)`;
* `TauCeti.CategoryTheory.Sheaf.H.map_injective`, the injectivity of `H⁰(F₁) →+ H⁰(F₂)`, which
  is where the sequence starts;
* `TauCeti.CategoryTheory.Sheaf.H.map_g_surjective`, `H.subsingleton_X₂`, `H.subsingleton_X₃`
  and `H.subsingleton_X₁`, the vanishing consequences that the sequence is normally used for;
* `TauCeti.CategoryTheory.Sheaf.H.δ_naturality`, the naturality of the connecting map in the
  short exact sequence, which is what makes the sequence one of modules over a ring acting on
  all three terms rather than merely one of abelian groups.

The six-term form of the sequence as a `ComposableArrows` is already available: it is Mathlib's
`CategoryTheory.Abelian.Ext.covariantSequence` for the constant sheaf `ℤ`, whose arrows are
definitionally the maps used here.

Sheaf cohomology on the small Zariski site of a scheme is the cohomology of a sheaf of modules,
so this is Layer B infrastructure for `TauCetiRoadmap/JacobianChallenge/README.md`; see
`TauCeti/AlgebraicGeometry/Cohomology/LongExactSequence.lean`. No formalization is vendored: the
underlying long exact sequence is Mathlib's `CategoryTheory.Abelian.Ext.covariant_sequence_exact₁'`,
`covariant_sequence_exact₂'` and `covariant_sequence_exact₃'`, and the naturality of the
extension class is Mathlib's `CategoryTheory.ShortComplex.ShortExact.extClass_naturality`.
-/

public section

open CategoryTheory Limits Abelian

universe w v u

namespace TauCeti

namespace CategoryTheory

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

/-- The constant sheaf `ℤ`, the object the cohomology of the site is corepresented by. -/
private noncomputable abbrev constZ : Sheaf J AddCommGrpCat.{v} :=
  (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))

namespace H

/-- The connecting map `Hⁿ⁰(F₃) →+ Hⁿ¹(F₁)` of the long exact cohomology sequence of a short
exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of abelian sheaves: composition with the extension class
of the sequence. -/
noncomputable def δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    _root_.CategoryTheory.Sheaf.H S.X₃ n₀ →+ _root_.CategoryTheory.Sheaf.H S.X₁ n₁ :=
  hS.extClass.postcomp _ h

include hS

/-- The long exact cohomology sequence is exact at `Hⁿ(F₂)`. -/
theorem exact_map_map (n : ℕ) :
    Function.Exact (_root_.CategoryTheory.Sheaf.H.map S.f n)
      (_root_.CategoryTheory.Sheaf.H.map S.g n) := by
  have := Ext.covariant_sequence_exact₂' (constZ (J := J)) hS n
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

/-- The long exact cohomology sequence is exact at `Hⁿ⁰(F₃)`. -/
theorem exact_map_δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (_root_.CategoryTheory.Sheaf.H.map S.g n₀) (δ hS n₀ n₁ h) := by
  have := Ext.covariant_sequence_exact₃' (constZ (J := J)) hS n₀ n₁ h
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

/-- The long exact cohomology sequence is exact at `Hⁿ¹(F₁)`. -/
theorem exact_δ_map (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (δ hS n₀ n₁ h) (_root_.CategoryTheory.Sheaf.H.map S.f n₁) := by
  have := Ext.covariant_sequence_exact₁' (constZ (J := J)) hS n₀ n₁ h
  rwa [ShortComplex.ab_exact_iff_function_exact] at this

omit hS in
/-- A monomorphism of abelian sheaves is injective on cohomology in degree zero. -/
theorem map_injective {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) [Mono f] :
    Function.Injective (_root_.CategoryTheory.Sheaf.H.map f 0) := by
  intro x y hxy
  apply (Ext.addEquiv₀ (C := Sheaf J AddCommGrpCat.{v})).injective
  rw [← cancel_mono f, ← _root_.CategoryTheory.Sheaf.H.addEquiv₀_map,
    ← _root_.CategoryTheory.Sheaf.H.addEquiv₀_map, hxy]

/-- If `Hⁿ¹(F₁)` vanishes, then `Hⁿ⁰(F₂) →+ Hⁿ⁰(F₃)` is surjective. -/
theorem map_g_surjective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₁ : Subsingleton (_root_.CategoryTheory.Sheaf.H S.X₁ n₁)) :
    Function.Surjective (_root_.CategoryTheory.Sheaf.H.map S.g n₀) := fun x ↦
  (exact_map_δ hS n₀ n₁ h x).1 (Subsingleton.elim _ _)

/-- If `Hⁿ(F₁)` and `Hⁿ(F₃)` vanish, then so does `Hⁿ(F₂)`. -/
theorem subsingleton_X₂ (n : ℕ) (h₁ : Subsingleton (_root_.CategoryTheory.Sheaf.H S.X₁ n))
    (h₃ : Subsingleton (_root_.CategoryTheory.Sheaf.H S.X₃ n)) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H S.X₂ n) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x₁, hx₁⟩ := (exact_map_map hS n x).1 (Subsingleton.elim _ _)
  obtain ⟨y₁, hy₁⟩ := (exact_map_map hS n y).1 (Subsingleton.elim _ _)
  rw [← hx₁, ← hy₁, Subsingleton.elim x₁ y₁]

/-- If `Hⁿ⁰(F₂)` and `Hⁿ¹(F₁)` vanish, then so does `Hⁿ⁰(F₃)`. -/
theorem subsingleton_X₃ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (_root_.CategoryTheory.Sheaf.H S.X₂ n₀))
    (h₁ : Subsingleton (_root_.CategoryTheory.Sheaf.H S.X₁ n₁)) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H S.X₃ n₀) :=
  (map_g_surjective hS n₀ n₁ h h₁).subsingleton

/-- If `Hⁿ⁰(F₃)` and `Hⁿ¹(F₂)` vanish, then so does `Hⁿ¹(F₁)`. -/
theorem subsingleton_X₁ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₃ : Subsingleton (_root_.CategoryTheory.Sheaf.H S.X₃ n₀))
    (h₂ : Subsingleton (_root_.CategoryTheory.Sheaf.H S.X₂ n₁)) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H S.X₁ n₁) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x₃, hx₃⟩ := (exact_δ_map hS n₀ n₁ h x).1 (Subsingleton.elim _ _)
  obtain ⟨y₃, hy₃⟩ := (exact_δ_map hS n₀ n₁ h y).1 (Subsingleton.elim _ _)
  rw [← hx₃, ← hy₃, Subsingleton.elim x₃ y₃]

omit hS in
/-- The connecting map is postcomposition with the extension class of the short exact
sequence. -/
private lemma δ_apply {T : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hT : T.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : _root_.CategoryTheory.Sheaf.H T.X₃ n₀) :
    δ hT n₀ n₁ h x = x.comp hT.extClass h :=
  (rfl)

omit hS in
/-- The connecting map of the long exact cohomology sequence is natural in the short exact
sequence: a morphism `φ : T₁ ⟶ T₂` of short exact sequences of abelian sheaves makes the square
formed by the two connecting maps and the maps induced by `φ.τ₃` and `φ.τ₁` commute. -/
theorem δ_naturality {T₁ T₂ : ShortComplex (Sheaf J AddCommGrpCat.{v})}
    (h₁ : T₁.ShortExact) (h₂ : T₂.ShortExact) (φ : T₁ ⟶ T₂)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : _root_.CategoryTheory.Sheaf.H T₁.X₃ n₀) :
    _root_.CategoryTheory.Sheaf.H.map φ.τ₁ n₁ (δ h₁ n₀ n₁ h x) =
      δ h₂ n₀ n₁ h (_root_.CategoryTheory.Sheaf.H.map φ.τ₃ n₀ x) := by
  rw [_root_.CategoryTheory.Sheaf.H.map_apply, _root_.CategoryTheory.Sheaf.H.map_apply,
    δ_apply, δ_apply, Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero,
    ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ]

end H

end Sheaf

end CategoryTheory

end TauCeti
