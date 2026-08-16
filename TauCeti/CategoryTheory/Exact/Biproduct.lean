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

* `TauCeti.ShortComplex.biprod`: the componentwise binary direct sum of two short complexes.
* `TauCeti.ExactStructure.IsInflation.biprod`: binary direct sums preserve inflations.
* `TauCeti.ExactStructure.IsDeflation.biprod`: binary direct sums preserve deflations.
* `TauCeti.ExactStructure.conflation_biprod`: binary direct sums preserve conflations.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), Proposition 2.9.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace ShortComplex

/-- The componentwise binary direct sum of two short complexes. -/
noncomputable def biprod (S₁ S₂ : CategoryTheory.ShortComplex C)
    [HasBinaryBiproduct S₁.X₁ S₂.X₁] [HasBinaryBiproduct S₁.X₂ S₂.X₂]
    [HasBinaryBiproduct S₁.X₃ S₂.X₃] : CategoryTheory.ShortComplex C :=
  CategoryTheory.ShortComplex.mk (Limits.biprod.map S₁.f S₂.f)
    (Limits.biprod.map S₁.g S₂.g)
    (by ext <;> simp [reassoc_of% S₁.zero, reassoc_of% S₂.zero])

end ShortComplex

namespace ExactStructure

variable [HasZeroObject C] [HasBinaryBiproducts C] (E : ExactStructure C)

namespace IsInflation

/-- Adjoining an identity map as the second summand preserves inflations.  This is E2 applied to
the biproduct pushout square. -/
theorem biprod_id {X Y : C} {i : X ⟶ Y} (hi : E.IsInflation i) (Z : C) :
    E.IsInflation (Limits.biprod.map i (𝟙 Z)) := by
  have sq : IsPushout (Limits.biprod.inl : X ⟶ X ⊞ Z) i
      (Limits.biprod.map i (𝟙 Z)) (Limits.biprod.inl : Y ⟶ Y ⊞ Z) :=
    (IsPushout.of_coprod_inl_with_id i Z).of_iso
      (Iso.refl X) (Limits.biprod.isoCoprod X Z).symm
      (Iso.refl Y) (Limits.biprod.isoCoprod Y Z).symm
      (by simp [Limits.coprod.inl_desc]) (by simp) (by ext <;> simp)
      (by simp [Limits.coprod.inl_desc])
  exact E.isStableUnderCobaseChange_inflations.of_isPushout sq hi

/-- Adjoining an identity map as the first summand preserves inflations. -/
theorem id_biprod {X Y : C} {i : X ⟶ Y} (hi : E.IsInflation i) (Z : C) :
    E.IsInflation (Limits.biprod.map (𝟙 Z) i) := by
  rw [← Limits.biprod.braiding_map_braiding i (𝟙 Z)]
  -- Expose the morphism property so its generic isomorphism-cancellation API applies.
  change E.inflations
    ((Limits.biprod.braiding Z X).hom ≫ Limits.biprod.map i (𝟙 Z) ≫
      (Limits.biprod.braiding Y Z).hom)
  rw [E.inflations.cancel_left_of_respectsIso, E.inflations.cancel_right_of_respectsIso]
  exact biprod_id (E := E) hi Z

/-- A binary direct sum of inflations is an inflation. -/
theorem biprod {X₁ Y₁ X₂ Y₂ : C} {i₁ : X₁ ⟶ Y₁} {i₂ : X₂ ⟶ Y₂}
    (hi₁ : E.IsInflation i₁) (hi₂ : E.IsInflation i₂) :
    E.IsInflation (Limits.biprod.map i₁ i₂) := by
  have h₁ : E.IsInflation (Limits.biprod.map i₁ (𝟙 X₂)) :=
    biprod_id (E := E) hi₁ X₂
  have h₂ : E.IsInflation (Limits.biprod.map (𝟙 Y₁) i₂) :=
    id_biprod (E := E) hi₂ Y₁
  rw [show Limits.biprod.map i₁ i₂ =
    Limits.biprod.map i₁ (𝟙 X₂) ≫ Limits.biprod.map (𝟙 Y₁) i₂ by ext <;> simp]
  exact E.isInflation_comp _ _ h₁ h₂

end IsInflation

namespace IsDeflation

/-- Adjoining an identity map as the second summand preserves deflations.  This is E2op applied
to the biproduct pullback square. -/
theorem biprod_id {Y Z : C} {p : Y ⟶ Z} (hp : E.IsDeflation p) (W : C) :
    E.IsDeflation (Limits.biprod.map p (𝟙 W)) := by
  have sq : IsPullback (Limits.biprod.fst : Y ⊞ W ⟶ Y)
      (Limits.biprod.map p (𝟙 W)) p (Limits.biprod.fst : Z ⊞ W ⟶ Z) :=
    (IsPullback.of_prod_fst_with_id p W).of_iso
      (Limits.biprod.isoProd Y W).symm (Iso.refl Y)
      (Limits.biprod.isoProd Z W).symm (Iso.refl Z)
      (by simp) (by ext <;> simp) (by simp) (by simp)
  exact E.isStableUnderBaseChange_deflations.of_isPullback sq hp

/-- Adjoining an identity map as the first summand preserves deflations. -/
theorem id_biprod {Y Z : C} {p : Y ⟶ Z} (hp : E.IsDeflation p) (W : C) :
    E.IsDeflation (Limits.biprod.map (𝟙 W) p) := by
  rw [← Limits.biprod.braiding_map_braiding p (𝟙 W)]
  -- Expose the morphism property so its generic isomorphism-cancellation API applies.
  change E.deflations
    ((Limits.biprod.braiding W Y).hom ≫ Limits.biprod.map p (𝟙 W) ≫
      (Limits.biprod.braiding Z W).hom)
  rw [E.deflations.cancel_left_of_respectsIso, E.deflations.cancel_right_of_respectsIso]
  exact biprod_id (E := E) hp W

/-- A binary direct sum of deflations is a deflation. -/
theorem biprod {Y₁ Z₁ Y₂ Z₂ : C} {p₁ : Y₁ ⟶ Z₁} {p₂ : Y₂ ⟶ Z₂}
    (hp₁ : E.IsDeflation p₁) (hp₂ : E.IsDeflation p₂) :
    E.IsDeflation (Limits.biprod.map p₁ p₂) := by
  have h₁ : E.IsDeflation (Limits.biprod.map p₁ (𝟙 Y₂)) :=
    biprod_id (E := E) hp₁ Y₂
  have h₂ : E.IsDeflation (Limits.biprod.map (𝟙 Z₁) p₂) :=
    id_biprod (E := E) hp₂ Z₁
  rw [show Limits.biprod.map p₁ p₂ =
    Limits.biprod.map p₁ (𝟙 Y₂) ≫ Limits.biprod.map (𝟙 Z₁) p₂ by ext <;> simp]
  exact E.isDeflation_comp _ _ h₁ h₂

end IsDeflation

/-- A binary direct sum of conflations is a conflation. -/
theorem conflation_biprod {S₁ S₂ : ShortComplex C} (hS₁ : E.Conflation S₁)
    (hS₂ : E.Conflation S₂) : E.Conflation (TauCeti.ShortComplex.biprod S₁ S₂) := by
  rw [TauCeti.ShortComplex.biprod]
  let S : ShortComplex C :=
    ShortComplex.mk (Limits.biprod.map S₁.f S₂.f) (Limits.biprod.map S₁.g S₂.g)
      (by ext <;> simp [reassoc_of% S₁.zero, reassoc_of% S₂.zero])
  suffices hS : E.Conflation S by simpa [S] using hS
  have hi : E.IsInflation S.f :=
    IsInflation.biprod (E := E) (E.isInflation_f hS₁) (E.isInflation_f hS₂)
  obtain ⟨Z, q, hq, hT⟩ := (ConflationClass.isInflation_iff E.toConflationClass _).mp hi
  let T := ShortComplex.mk S.f q hq
  have hT' : E.Conflation T := by simpa [T] using hT
  have hpairT : IsKernelCokernelPair T := E.isKernelCokernelPair T hT'
  have hpair : IsKernelCokernelPair S :=
    IsKernelCokernelPair.biprod (E.isKernelCokernelPair S₁ hS₁)
      (E.isKernelCokernelPair S₂ hS₂)
  let e : Z ≅ S.X₃ :=
    IsColimit.coconePointUniqueUpToIso hpairT.gIsCokernel hpair.gIsCokernel
  have he : q ≫ e.hom = S.g :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hpairT.gIsCokernel hpair.gIsCokernel
      WalkingParallelPair.one
  exact E.conflation_of_iso (S := T) (T := S)
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
      (by simp [T]) (by simpa [T] using he.symm)) hT'

end ExactStructure

end TauCeti
