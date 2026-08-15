/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.CategoryTheory.Exact.ExactStructure
public import TauCeti.CategoryTheory.Exact.KernelCokernelPair
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.Monomorphisms

/-!
# The canonical exact structure on an abelian category

Every abelian category `C` carries a canonical Quillen exact structure
`ExactStructure.abelian C` whose conflations are the short exact short complexes
`S : X ⟶ Y ⟶ Z` (in the sense of `CategoryTheory.ShortComplex.ShortExact`).

In this exact structure:
* Conflations are short exact short complexes:
  `(ExactStructure.abelian C).Conflation S ↔ S.ShortExact`.
* Inflations are monomorphisms: `(ExactStructure.abelian C).IsInflation i ↔ Mono i`.
* Deflations are epimorphisms: `(ExactStructure.abelian C).IsDeflation p ↔ Epi p`.

The Quillen axioms E0/E0op, E1/E1op, and E2/E2op translate directly to standard properties
of abelian categories:
* E0/E0op: identity morphisms are monomorphisms and epimorphisms.
* E1/E1op: composites of monomorphisms (epimorphisms) are monomorphisms (epimorphisms).
* E2/E2op: pushouts of monomorphisms (pullbacks of epimorphisms) exist and are
  monomorphisms (epimorphisms), as in `Mathlib.CategoryTheory.Abelian.Monomorphisms`.

## Main definitions

* `TauCeti.ConflationClass.abelian`: the isomorphism-closed class of short exact short
  complexes in an abelian category `C`.
* `TauCeti.ExactStructure.abelian`: the canonical Quillen exact structure on `C`.

## Main results

* `TauCeti.ExactStructure.abelian_conflation`: conflations are short exact complexes.
* `TauCeti.ExactStructure.abelian_conflation_iff_isKernelCokernelPair`: conflations are
  exactly kernel–cokernel pairs.
* `TauCeti.ExactStructure.abelian_isInflation_iff`: inflations are monomorphisms.
* `TauCeti.ExactStructure.abelian_isDeflation_iff`: deflations are epimorphisms.
* `TauCeti.ExactStructure.abelian_inflations_eq`: inflations equal `monomorphisms C`.
* `TauCeti.ExactStructure.abelian_deflations_eq`: deflations equal `epimorphisms C`.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>. Section 13.2 details the canonical exact structure.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Section 6.1.2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive ZeroObject

universe v u

section Abelian

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The conflation class of short exact sequences in an abelian category `C`. -/
def ConflationClass.abelian : ConflationClass C where
  Conflation S := S.ShortExact
  isKernelCokernelPair _ hS := IsKernelCokernelPair.of_shortExact hS
  isClosedUnderIsomorphisms := ⟨fun e h => ShortComplex.shortExact_of_iso e h⟩

namespace ConflationClass

variable {C}

@[simp]
theorem abelian_conflation (S : ShortComplex C) :
    (ConflationClass.abelian C).Conflation S ↔ S.ShortExact :=
  Iff.rfl

/-- In an abelian category, every monomorphism `i : X ⟶ Y` is an inflation of the canonical
conflation class, witnessed by `X ⟶ Y ⟶ cokernel i`. -/
theorem isInflation_abelian_of_mono {X Y : C} (i : X ⟶ Y) [Mono i] :
    (ConflationClass.abelian C).IsInflation i := by
  refine (ConflationClass.isInflation_iff (ConflationClass.abelian C) i).mpr
    ⟨cokernel i, cokernel.π i, cokernel.condition i, ?_⟩
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance

/-- In an abelian category, every epimorphism `p : Y ⟶ Z` is a deflation of the canonical
conflation class, witnessed by `kernel p ⟶ Y ⟶ Z`. -/
theorem isDeflation_abelian_of_epi {Y Z : C} (p : Y ⟶ Z) [Epi p] :
    (ConflationClass.abelian C).IsDeflation p := by
  refine (ConflationClass.isDeflation_iff (ConflationClass.abelian C) p).mpr
    ⟨kernel p, kernel.ι p, kernel.condition p, ?_⟩
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance

/-- A morphism in an abelian category is an inflation of the canonical conflation class if
and only if it is a monomorphism. -/
@[simp]
theorem isInflation_abelian_iff {X Y : C} (i : X ⟶ Y) :
    (ConflationClass.abelian C).IsInflation i ↔ Mono i := by
  constructor
  · intro hi
    obtain ⟨Z, p, zero, hS⟩ :=
      (ConflationClass.isInflation_iff (ConflationClass.abelian C) i).mp hi
    exact hS.mono_f
  · intro _
    exact isInflation_abelian_of_mono i

/-- A morphism in an abelian category is a deflation of the canonical conflation class if
and only if it is an epimorphism. -/
@[simp]
theorem isDeflation_abelian_iff {Y Z : C} (p : Y ⟶ Z) :
    (ConflationClass.abelian C).IsDeflation p ↔ Epi p := by
  constructor
  · intro hp
    obtain ⟨X, i, zero, hS⟩ :=
      (ConflationClass.isDeflation_iff (ConflationClass.abelian C) p).mp hp
    exact hS.epi_g
  · intro _
    exact isDeflation_abelian_of_epi p

/-- The inflations of the canonical conflation class are precisely the monomorphisms. -/
theorem inflations_abelian_eq :
    (ConflationClass.abelian C).inflations = MorphismProperty.monomorphisms C := by
  ext X Y f
  exact isInflation_abelian_iff f

/-- The deflations of the canonical conflation class are precisely the epimorphisms. -/
theorem deflations_abelian_eq :
    (ConflationClass.abelian C).deflations = MorphismProperty.epimorphisms C := by
  ext X Y f
  exact isDeflation_abelian_iff f

end ConflationClass

/-- The canonical exact structure on an abelian category `C`, whose conflations are the
short exact short complexes. -/
noncomputable def ExactStructure.abelian : ExactStructure C where
  toConflationClass := ConflationClass.abelian C
  isInflation_id X := ConflationClass.isInflation_abelian_of_mono (𝟙 X)
  isDeflation_id X := ConflationClass.isDeflation_abelian_of_epi (𝟙 X)
  isInflation_comp i j hi hj := by
    rw [ConflationClass.isInflation_abelian_iff] at hi hj ⊢
    infer_instance
  isDeflation_comp p q hp hq := by
    rw [ConflationClass.isDeflation_abelian_iff] at hp hq ⊢
    infer_instance
  hasPushouts_inflations := by
    infer_instance
  isStableUnderCobaseChange_inflations := {
    of_isPushout := fun sq hf => by
      have hmono : (MorphismProperty.monomorphisms C) _ :=
        (ConflationClass.isInflation_abelian_iff _).mp hf
      have hinst : (MorphismProperty.monomorphisms C).IsStableUnderCobaseChange :=
        inferInstance
      have hk : (MorphismProperty.monomorphisms C) _ :=
        hinst.of_isPushout sq hmono
      exact (ConflationClass.isInflation_abelian_iff _).mpr hk
  }
  hasPullbacks_deflations := by
    infer_instance
  isStableUnderBaseChange_deflations := {
    of_isPullback := fun sq hg => by
      have hepi : (MorphismProperty.epimorphisms C) _ :=
        (ConflationClass.isDeflation_abelian_iff _).mp hg
      have hinst : (MorphismProperty.epimorphisms C).IsStableUnderBaseChange :=
        inferInstance
      have hh : (MorphismProperty.epimorphisms C) _ :=
        hinst.of_isPullback sq hepi
      exact (ConflationClass.isDeflation_abelian_iff _).mpr hh
  }

namespace ExactStructure

variable {C}

/-- The conflations of the canonical exact structure on an abelian category are the
short exact short complexes. -/
@[simp]
theorem abelian_conflation (S : ShortComplex C) :
    (ExactStructure.abelian C).Conflation S ↔ S.ShortExact :=
  Iff.rfl

/-- In an abelian category, conflations of the canonical exact structure are precisely the
kernel–cokernel pairs. -/
theorem abelian_conflation_iff_isKernelCokernelPair (S : ShortComplex C) :
    (ExactStructure.abelian C).Conflation S ↔ IsKernelCokernelPair S :=
  (isKernelCokernelPair_iff_shortExact S).symm

/-- A morphism in an abelian category is an inflation of the canonical exact structure if and
only if it is a monomorphism. -/
@[simp]
theorem abelian_isInflation_iff {X Y : C} (i : X ⟶ Y) :
    (ExactStructure.abelian C).IsInflation i ↔ Mono i :=
  ConflationClass.isInflation_abelian_iff i

/-- A morphism in an abelian category is a deflation of the canonical exact structure if and
only if it is an epimorphism. -/
@[simp]
theorem abelian_isDeflation_iff {Y Z : C} (p : Y ⟶ Z) :
    (ExactStructure.abelian C).IsDeflation p ↔ Epi p :=
  ConflationClass.isDeflation_abelian_iff p

/-- The inflations of the canonical exact structure are precisely the monomorphisms. -/
theorem abelian_inflations_eq :
    (ExactStructure.abelian C).inflations = MorphismProperty.monomorphisms C :=
  ConflationClass.inflations_abelian_eq

/-- The deflations of the canonical exact structure are precisely the epimorphisms. -/
theorem abelian_deflations_eq :
    (ExactStructure.abelian C).deflations = MorphismProperty.epimorphisms C :=
  ConflationClass.deflations_abelian_eq

/-- In an abelian category, every monomorphism `i : X ⟶ Y` yields a canonical conflation
`X ⟶ Y ⟶ cokernel i`. -/
theorem abelian_conflation_of_mono {X Y : C} (i : X ⟶ Y) [Mono i] :
    (ExactStructure.abelian C).Conflation
      (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)) :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance

/-- In an abelian category, every epimorphism `p : Y ⟶ Z` yields a canonical conflation
`kernel p ⟶ Y ⟶ Z`. -/
theorem abelian_conflation_of_epi {Y Z : C} (p : Y ⟶ Z) [Epi p] :
    (ExactStructure.abelian C).Conflation
      (ShortComplex.mk (kernel.ι p) p (kernel.condition p)) :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance

/-- A short complex whose first morphism is an isomorphism and whose third object is zero is a
conflation in the canonical exact structure. -/
theorem abelian_conflation_of_isIso_f_of_isZero (S : ShortComplex C) [IsIso S.f]
    (h₃ : IsZero S.X₃) : (ExactStructure.abelian C).Conflation S :=
  (isKernelCokernelPair_iff_shortExact S).mp (IsKernelCokernelPair.of_isIso_f_of_isZero S h₃)

/-- A short complex whose second morphism is an isomorphism and whose first object is zero is a
conflation in the canonical exact structure. -/
theorem abelian_conflation_of_isIso_g_of_isZero (S : ShortComplex C) [IsIso S.g]
    (h₁ : IsZero S.X₁) : (ExactStructure.abelian C).Conflation S :=
  (isKernelCokernelPair_iff_shortExact S).mp (IsKernelCokernelPair.of_isIso_g_of_isZero S h₁)

/-- `0 ⟶ X ⟶ X` is a conflation in the canonical exact structure. -/
theorem abelian_conflation_zero_left (X : C) :
    (ExactStructure.abelian C).Conflation
      (ShortComplex.mk (0 : (0 : C) ⟶ X) (𝟙 X) (zero_comp)) :=
  abelian_conflation_of_isIso_g_of_isZero _ (isZero_zero C)

/-- `X ⟶ X ⟶ 0` is a conflation in the canonical exact structure. -/
theorem abelian_conflation_zero_right (X : C) :
    (ExactStructure.abelian C).Conflation
      (ShortComplex.mk (𝟙 X) (0 : X ⟶ (0 : C)) (comp_zero)) :=
  abelian_conflation_of_isIso_f_of_isZero _ (isZero_zero C)

/-- A split short complex in an abelian category is a conflation of the canonical
exact structure. -/
theorem abelian_conflation_of_splitting (S : ShortComplex C) (s : S.Splitting) :
    (ExactStructure.abelian C).Conflation S :=
  s.shortExact

/-- The canonical biproduct short complex `X ⟶ X ⊞ Y ⟶ Y` is a conflation in the
canonical exact structure. -/
theorem abelian_conflation_biprod_exact (X Y : C) :
    (ExactStructure.abelian C).Conflation
      (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) (biprod.snd : X ⊞ Y ⟶ Y) (biprod.inl_snd)) :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact

/-- A binary direct sum of conflations in an abelian category is a conflation. -/
theorem abelian_conflation_biprod (S₁ S₂ : ShortComplex C)
    (h₁ : (ExactStructure.abelian C).Conflation S₁)
    (h₂ : (ExactStructure.abelian C).Conflation S₂) :
    (ExactStructure.abelian C).Conflation
      (ShortComplex.mk (biprod.map S₁.f S₂.f) (biprod.map S₁.g S₂.g)
        (by ext <;> simp [reassoc_of% S₁.zero, reassoc_of% S₂.zero])) := by
  rw [abelian_conflation_iff_isKernelCokernelPair] at h₁ h₂ ⊢
  exact h₁.biprod h₂

/-- Duality for canonical conflations: a short complex in `Cᵒᵖ` is a conflation if and only if
its un-opposite is a conflation in `C`. -/
theorem abelian_conflation_op_iff (S : ShortComplex C) :
    (ExactStructure.abelian Cᵒᵖ).Conflation S.op ↔ (ExactStructure.abelian C).Conflation S :=
  (ShortComplex.shortExact_iff_op S).symm

/-- Duality for canonical conflations: a short complex in `C` is a conflation if and only if
its opposite is a conflation in `Cᵒᵖ`. -/
theorem abelian_conflation_unop_iff (S : ShortComplex Cᵒᵖ) :
    (ExactStructure.abelian C).Conflation S.unop ↔ (ExactStructure.abelian Cᵒᵖ).Conflation S :=
  (ShortComplex.shortExact_iff_unop S).symm

/-- In an abelian category, the cobase change of an inflation is an inflation. -/
theorem abelian_isInflation_pushout_inr {X Y X' : C} (i : X ⟶ Y) (f : X ⟶ X')
    (hi : (ExactStructure.abelian C).IsInflation i) :
    (ExactStructure.abelian C).IsInflation (pushout.inr i f) := by
  rw [abelian_isInflation_iff] at hi ⊢
  infer_instance

/-- In an abelian category, the base change of a deflation is a deflation. -/
theorem abelian_isDeflation_pullback_fst {Y Z Y' : C} (p : Y ⟶ Z) (f : Y' ⟶ Z)
    (hp : (ExactStructure.abelian C).IsDeflation p) :
    (ExactStructure.abelian C).IsDeflation (pullback.fst f p) := by
  rw [abelian_isDeflation_iff] at hp ⊢
  infer_instance

end ExactStructure

end Abelian

end TauCeti
