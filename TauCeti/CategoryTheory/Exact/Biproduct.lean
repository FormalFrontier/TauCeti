/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Exact.ExactStructure

/-!
# Binary biproducts of conflations

Distinguished conflations in an exact category are closed under binary direct sums.  The proof
uses only Quillen's axioms.  First, E2 shows that adjoining an identity summand to an inflation
again gives an inflation: the relevant square is a biproduct pushout.  E1 then gives the direct
sum of two inflations by factoring it as

```text
X₁ ⊞ X₂  --(i₁ ⊞ 1)-->  Y₁ ⊞ X₂  --(1 ⊞ i₂)-->  Y₁ ⊞ Y₂.
```

The dual argument applies to deflations.  Finally, the direct sum of the two underlying
kernel--cokernel pairs identifies the cokernel supplied by E1 with the componentwise direct sum,
so the componentwise short complex itself is a conflation.

## Main declarations

* `TauCeti.shortComplexBiprod`: the componentwise binary direct sum of two short complexes.
* `TauCeti.ExactStructure.isInflation_biprod`: binary direct sums preserve inflations.
* `TauCeti.ExactStructure.isDeflation_biprod`: binary direct sums preserve deflations.
* `TauCeti.ExactStructure.conflation_biprod`: binary direct sums preserve conflations.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), Proposition 2.9.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace ExactStructure

variable [HasZeroObject C] [HasBinaryBiproducts C]

/-- Adjoining an identity map as the second summand preserves inflations.  This is E2 applied to
the biproduct pushout square. -/
theorem isInflation_biprod_id (E : ExactStructure C) {X Y : C} {i : X ⟶ Y}
    (hi : E.IsInflation i) (Z : C) :
    E.IsInflation (Limits.biprod.map i (𝟙 Z)) := by
  have sq : IsPushout (Limits.biprod.inl : X ⟶ X ⊞ Z) i
      (Limits.biprod.map i (𝟙 Z)) (Limits.biprod.inl : Y ⟶ Y ⊞ Z) :=
    isPushout_biprod_inl_map i Z
  exact E.isStableUnderCobaseChange_inflations.of_isPushout sq hi

/-- Adjoining an identity map as the first summand preserves inflations. -/
theorem isInflation_id_biprod (E : ExactStructure C) {X Y : C} {i : X ⟶ Y}
    (hi : E.IsInflation i) (Z : C) :
    E.IsInflation (Limits.biprod.map (𝟙 Z) i) := by
  rw [← Limits.biprod.braiding_map_braiding i (𝟙 Z)]
  -- `rw` cannot key through the `IsInflation` abbrev, so expose the morphism property.
  change E.inflations _
  rw [E.inflations.cancel_left_of_respectsIso, E.inflations.cancel_right_of_respectsIso]
  exact E.isInflation_biprod_id hi Z

/-- A binary direct sum of inflations is an inflation. -/
theorem isInflation_biprod (E : ExactStructure C)
    {X₁ Y₁ X₂ Y₂ : C} {i₁ : X₁ ⟶ Y₁} {i₂ : X₂ ⟶ Y₂}
    (hi₁ : E.IsInflation i₁) (hi₂ : E.IsInflation i₂) :
    E.IsInflation (Limits.biprod.map i₁ i₂) := by
  have h₁ : E.IsInflation (Limits.biprod.map i₁ (𝟙 X₂)) :=
    E.isInflation_biprod_id hi₁ X₂
  have h₂ : E.IsInflation (Limits.biprod.map (𝟙 Y₁) i₂) :=
    E.isInflation_id_biprod hi₂ Y₁
  rw [show Limits.biprod.map i₁ i₂ =
    Limits.biprod.map i₁ (𝟙 X₂) ≫ Limits.biprod.map (𝟙 Y₁) i₂ by ext <;> simp]
  exact E.isInflation_comp _ _ h₁ h₂

/-- Adjoining an identity map as the second summand preserves deflations.  This is E2op applied
to the biproduct pullback square. -/
theorem isDeflation_biprod_id (E : ExactStructure C) {Y Z : C} {p : Y ⟶ Z}
    (hp : E.IsDeflation p) (W : C) :
    E.IsDeflation (Limits.biprod.map p (𝟙 W)) := by
  have sq : IsPullback (Limits.biprod.fst : Y ⊞ W ⟶ Y)
      (Limits.biprod.map p (𝟙 W)) p (Limits.biprod.fst : Z ⊞ W ⟶ Z) :=
    isPullback_biprod_map_fst p W
  exact E.isStableUnderBaseChange_deflations.of_isPullback sq hp

/-- Adjoining an identity map as the first summand preserves deflations. -/
theorem isDeflation_id_biprod (E : ExactStructure C) {Y Z : C} {p : Y ⟶ Z}
    (hp : E.IsDeflation p) (W : C) :
    E.IsDeflation (Limits.biprod.map (𝟙 W) p) := by
  rw [← Limits.biprod.braiding_map_braiding p (𝟙 W)]
  -- `rw` cannot key through the `IsDeflation` abbrev, so expose the morphism property.
  change E.deflations _
  rw [E.deflations.cancel_left_of_respectsIso, E.deflations.cancel_right_of_respectsIso]
  exact E.isDeflation_biprod_id hp W

/-- A binary direct sum of deflations is a deflation. -/
theorem isDeflation_biprod (E : ExactStructure C)
    {Y₁ Z₁ Y₂ Z₂ : C} {p₁ : Y₁ ⟶ Z₁} {p₂ : Y₂ ⟶ Z₂}
    (hp₁ : E.IsDeflation p₁) (hp₂ : E.IsDeflation p₂) :
    E.IsDeflation (Limits.biprod.map p₁ p₂) := by
  have h₁ : E.IsDeflation (Limits.biprod.map p₁ (𝟙 Y₂)) :=
    E.isDeflation_biprod_id hp₁ Y₂
  have h₂ : E.IsDeflation (Limits.biprod.map (𝟙 Z₁) p₂) :=
    E.isDeflation_id_biprod hp₂ Z₁
  rw [show Limits.biprod.map p₁ p₂ =
    Limits.biprod.map p₁ (𝟙 Y₂) ≫ Limits.biprod.map (𝟙 Z₁) p₂ by ext <;> simp]
  exact E.isDeflation_comp _ _ h₁ h₂

/-- A binary direct sum of conflations is a conflation. -/
theorem conflation_biprod (E : ExactStructure C) {S₁ S₂ : ShortComplex C}
    (hS₁ : E.Conflation S₁) (hS₂ : E.Conflation S₂) :
    E.Conflation (shortComplexBiprod S₁ S₂) :=
  E.conflation_of_isKernelCokernelPair
    ((E.isKernelCokernelPair S₁ hS₁).biprod (E.isKernelCokernelPair S₂ hS₂))
    (E.isInflation_biprod (E.isInflation_f hS₁) (E.isInflation_f hS₂))

end ExactStructure

end TauCeti
