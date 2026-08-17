/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.Split
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Functors between exact categories

An additive functor between categories with chosen exact structures is *conflation-exact* when it
maps every distinguished kernel--cokernel pair to a distinguished kernel--cokernel pair. The name
distinguishes this relative notion from Mathlib's `CategoryTheory.exactFunctor`, which means
preservation of finite limits and finite colimits.

This file develops the functorial interface needed by exact Grothendieck groups. Conflation-exact
functors preserve inflations and deflations, compose, and are invariant under natural isomorphism.
Every additive functor is conflation-exact for the split exact structures. For the canonical exact
structures on abelian categories, conflation-exactness is equivalent to Mathlib's finite-limit and
finite-colimit exactness.

## Main definitions and results

* `TauCeti.ExactStructure.IsConflationExact`: an additive functor preserves the distinguished
  conflations.
* `TauCeti.ExactStructure.IsConflationExact.map_isInflation` and
  `TauCeti.ExactStructure.IsConflationExact.map_isDeflation`: the induced preservation results for
  admissible morphisms.
* `TauCeti.ExactStructure.IsConflationExact.id`, `.comp`, and `.of_iso`: identity, composition,
  and natural-isomorphism invariance.
* `TauCeti.ExactStructure.ReflectsConflations`: a functor detects the distinguished
  conflations, with the corresponding composition and natural-isomorphism API.
* `TauCeti.ExactStructure.isConflationExact_split`: every additive functor preserves split
  conflations.
* `TauCeti.ExactStructure.isConflationExact_abelian_iff`: for canonical abelian exact structures,
  conflation-exactness agrees with Mathlib's exact-functor predicate.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Section 5.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 7.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace ExactStructure

variable {C : Type u₁} {D : Type u₂} {K : Type u₃}
variable [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
variable [Category.{v₃} K] [Preadditive K] [HasZeroObject K] [HasBinaryBiproducts K]

/-- An additive functor is **conflation-exact** when it maps every conflation of the source exact
structure to a conflation of the target exact structure.

This is exactness relative to two chosen Quillen exact structures. It is deliberately distinct
from `CategoryTheory.exactFunctor`, the property of preserving finite limits and finite colimits. -/
structure IsConflationExact (E : ExactStructure C) (E' : ExactStructure D) (F : C ⥤ D)
    [F.Additive] : Prop where
  /-- The image under `F` of a distinguished conflation is distinguished. -/
  map_conflation : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F)

namespace IsConflationExact

variable {E : ExactStructure C} {E' : ExactStructure D} {E'' : ExactStructure K}
variable {F G : C ⥤ D} {H : D ⥤ K}

/-- A conflation-exact functor sends a conflation to a kernel--cokernel pair. -/
theorem map_isKernelCokernelPair [F.Additive] (hF : E.IsConflationExact E' F)
    {S : ShortComplex C} (hS : E.Conflation S) : IsKernelCokernelPair (S.map F) :=
  E'.isKernelCokernelPair _ (hF.map_conflation hS)

/-- A conflation-exact functor preserves inflations. -/
theorem map_isInflation [F.Additive] (hF : E.IsConflationExact E' F) {X Y : C}
    {i : X ⟶ Y} (hi : E.IsInflation i) : E'.IsInflation (F.map i) := by
  obtain ⟨Z, p, zero, hS⟩ := (ConflationClass.isInflation_iff E.toConflationClass i).mp hi
  exact (ConflationClass.isInflation_iff E'.toConflationClass (F.map i)).mpr
    ⟨F.obj Z, F.map p, by rw [← F.map_comp, zero, F.map_zero], hF.map_conflation hS⟩

/-- A conflation-exact functor preserves deflations. -/
theorem map_isDeflation [F.Additive] (hF : E.IsConflationExact E' F) {Y Z : C}
    {p : Y ⟶ Z} (hp : E.IsDeflation p) : E'.IsDeflation (F.map p) := by
  obtain ⟨X, i, zero, hS⟩ := (ConflationClass.isDeflation_iff E.toConflationClass p).mp hp
  exact (ConflationClass.isDeflation_iff E'.toConflationClass (F.map p)).mpr
    ⟨F.obj X, F.map i, by rw [← F.map_comp, zero, F.map_zero], hF.map_conflation hS⟩

/-- The identity functor is conflation-exact. -/
protected theorem id : E.IsConflationExact E (𝟭 C) where
  map_conflation hS := by simpa using hS

/-- A composite of conflation-exact functors is conflation-exact. -/
protected theorem comp [F.Additive] [H.Additive] (hF : E.IsConflationExact E' F)
    (hH : E'.IsConflationExact E'' H) : E.IsConflationExact E'' (F ⋙ H) where
  map_conflation {S} hS := by
    simpa only [ShortComplex.map_comp] using hH.map_conflation (hF.map_conflation hS)

/-- Conflation-exactness is preserved by replacing a functor with a naturally isomorphic additive
functor. -/
theorem of_iso [F.Additive] [G.Additive] (hF : E.IsConflationExact E' F) (e : F ≅ G) :
    E.IsConflationExact E' G where
  map_conflation {S} hS :=
    E'.conflation_of_iso (S.mapNatIso e) (hF.map_conflation hS)

/-- Naturally isomorphic additive functors are conflation-exact together. -/
theorem iff_of_iso [F.Additive] [G.Additive] (e : F ≅ G) :
    E.IsConflationExact E' F ↔ E.IsConflationExact E' G :=
  ⟨fun hF ↦ hF.of_iso e, fun hG ↦ hG.of_iso e.symm⟩

end IsConflationExact

/-- An additive functor **reflects conflations** when a short complex is a source conflation
whenever its image is a target conflation. Together with `IsConflationExact`, this says that the
chosen exact structures agree along the functor. -/
structure ReflectsConflations (E : ExactStructure C) (E' : ExactStructure D) (F : C ⥤ D)
    [F.Additive] : Prop where
  /-- A short complex whose image is a conflation was already a conflation. -/
  reflects_conflation : ∀ {S : ShortComplex C}, E'.Conflation (S.map F) → E.Conflation S

namespace ReflectsConflations

variable {E : ExactStructure C} {E' : ExactStructure D} {E'' : ExactStructure K}
variable {F G : C ⥤ D} {H : D ⥤ K}

/-- The identity functor reflects conflations. -/
protected theorem id : E.ReflectsConflations E (𝟭 C) where
  reflects_conflation hS := by simpa using hS

/-- A composite of functors which reflect conflations reflects conflations. -/
protected theorem comp [F.Additive] [H.Additive] (hF : E.ReflectsConflations E' F)
    (hH : E'.ReflectsConflations E'' H) : E.ReflectsConflations E'' (F ⋙ H) where
  reflects_conflation {S} hS := by
    apply hF.reflects_conflation
    apply hH.reflects_conflation
    simpa only [ShortComplex.map_comp] using hS

/-- Reflection of conflations is preserved by replacing a functor with a naturally isomorphic
additive functor. -/
theorem of_iso [F.Additive] [G.Additive] (hF : E.ReflectsConflations E' F) (e : F ≅ G) :
    E.ReflectsConflations E' G where
  reflects_conflation {S} hS := by
    apply hF.reflects_conflation
    exact E'.conflation_of_iso (S.mapNatIso e).symm hS

/-- Naturally isomorphic additive functors reflect conflations together. -/
theorem iff_of_iso [F.Additive] [G.Additive] (e : F ≅ G) :
    E.ReflectsConflations E' F ↔ E.ReflectsConflations E' G :=
  ⟨fun hF ↦ hF.of_iso e, fun hG ↦ hG.of_iso e.symm⟩

end ReflectsConflations

/-- If a functor both preserves and reflects conflations, a short complex is distinguished exactly
when its image is distinguished. -/
theorem conflation_map_iff {E : ExactStructure C} {E' : ExactStructure D} {F : C ⥤ D}
    [F.Additive] (hF : E.IsConflationExact E' F)
    (hF' : E.ReflectsConflations E' F) (S : ShortComplex C) :
    E'.Conflation (S.map F) ↔ E.Conflation S :=
  ⟨hF'.reflects_conflation, hF.map_conflation⟩

/-- Every additive functor preserves split conflations. -/
theorem isConflationExact_split (F : C ⥤ D) [F.Additive] :
    (split C).IsConflationExact (split D) F where
  map_conflation {S} hS := by
    obtain ⟨s⟩ := (split_conflation S).mp hS
    exact (split_conflation (S.map F)).mpr ⟨s.map F⟩

section Abelian

variable {A : Type u₁} {B : Type u₂}
variable [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]

/-- For the canonical exact structures on abelian categories, conflation-exactness is precisely
Mathlib's exactness condition: preservation of finite limits and finite colimits. -/
theorem isConflationExact_abelian_iff (F : A ⥤ B) [F.Additive] :
    (abelian A).IsConflationExact (abelian B) F ↔
      PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  constructor
  · intro hF
    apply ((CategoryTheory.Functor.exact_tfae F).out 1 4).mp
    intro S hS
    exact (abelian_conflation (S.map F)).mp
      (hF.map_conflation ((abelian_conflation S).mpr hS))
  · intro hF
    have hmap := ((CategoryTheory.Functor.exact_tfae F).out 1 4).mpr hF
    exact ⟨fun {S} hS ↦ (abelian_conflation (S.map F)).mpr
      (hmap S ((abelian_conflation S).mp hS))⟩

/-- An additive functor which is exact in Mathlib's finite-limit and finite-colimit sense is
conflation-exact for the canonical exact structures. -/
theorem isConflationExact_abelian (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (abelian A).IsConflationExact (abelian B) F :=
  (isConflationExact_abelian_iff F).mpr ⟨inferInstance, inferInstance⟩

/-- A faithful additive functor between abelian categories reflects conflations of the canonical
exact structures. No exactness assumption is needed for this direction. -/
theorem reflectsConflations_abelian_of_faithful (F : A ⥤ B) [F.Additive] [F.Faithful] :
    (abelian A).ReflectsConflations (abelian B) F where
  reflects_conflation {S} hS := by
    apply (abelian_conflation S).mpr
    exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful F
      ((abelian_conflation (S.map F)).mp hS)

end Abelian

end ExactStructure

end TauCeti
