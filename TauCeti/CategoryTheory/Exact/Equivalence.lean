/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Exact.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square

/-!
# Transporting exact structures along equivalences

An additive equivalence transports a Quillen exact structure to its target. A short complex in
the target is distinguished precisely when its image under the inverse equivalence is
distinguished. This file verifies all six exact-category axioms for that transported class and
shows that both functors of the equivalence preserve and reflect conflations.

## Main definitions and results

* `TauCeti.ExactStructure.transportConflationClass`: the transported conflation class.
* `TauCeti.ExactStructure.transport`: the exact structure transported along an additive
  equivalence.
* `TauCeti.ExactStructure.transport_conflation_iff`: the defining characterization of its
  conflations.
* `TauCeti.ExactStructure.isConflationExact_functor_transport` and
  `TauCeti.ExactStructure.reflectsConflations_functor_transport`: the forward equivalence
  preserves and reflects conflations.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Section 5.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace ExactStructure

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]

/-- The conflation class transported along an additive equivalence. A target short complex is
distinguished when applying the inverse equivalence produces a source conflation. -/
noncomputable def transportConflationClass (E : ExactStructure C) (e : C ≌ D)
    [e.functor.Additive] : ConflationClass D where
  Conflation S := E.Conflation (S.map e.inverse)
  isKernelCokernelPair S hS := by
    have hpair := (E.isKernelCokernelPair (S.map e.inverse) hS).map e.functor
    exact hpair.of_iso (by
      simpa only [ShortComplex.map_comp, ShortComplex.map_id] using
        (S.mapNatIso e.counitIso))
  isClosedUnderIsomorphisms :=
    { of_iso := fun i hS ↦ E.conflation_of_iso (e.inverse.mapShortComplex.mapIso i) hS }

omit [HasZeroObject D] [HasBinaryBiproducts D] in
/-- A morphism is an inflation in the transported conflation class exactly when its image under
the inverse equivalence is an inflation. -/
theorem transportConflationClass_inflations (E : ExactStructure C) (e : C ≌ D)
    [e.functor.Additive] :
    (transportConflationClass E e).inflations = E.inflations.inverseImage e.inverse := by
  ext X Y i
  constructor
  · intro hi
    obtain ⟨Z, p, zero, hS⟩ :=
      (ConflationClass.isInflation_iff (transportConflationClass E e) i).mp hi
    change E.IsInflation (e.inverse.map i)
    exact (ConflationClass.isInflation_iff E.toConflationClass _).mpr
      ⟨e.inverse.obj Z, e.inverse.map p, by
        rw [← e.inverse.map_comp, zero, e.inverse.map_zero], hS⟩
  · intro hi
    change E.IsInflation (e.inverse.map i) at hi
    obtain ⟨Z, p, zero, hS⟩ :=
      (ConflationClass.isInflation_iff E.toConflationClass _).mp hi
    let S := ShortComplex.mk (e.inverse.map i) p zero
    have hmap : (transportConflationClass E e).IsInflation
        (e.functor.map (e.inverse.map i)) := by
      have hmapS : (transportConflationClass E e).Conflation (S.map e.functor) :=
        E.conflation_of_iso (by
          simpa only [ShortComplex.map_comp, ShortComplex.map_id] using
            (S.mapNatIso e.unitIso)) hS
      exact ConflationClass.isInflation_f (transportConflationClass E e) hmapS
    exact ((transportConflationClass E e).inflations.arrow_mk_iso_iff
      (((Functor.mapArrowFunctor D D).mapIso e.counitIso).app (Arrow.mk i))).mp hmap

omit [HasZeroObject D] [HasBinaryBiproducts D] in
/-- A morphism is a deflation in the transported conflation class exactly when its image under
the inverse equivalence is a deflation. -/
theorem transportConflationClass_deflations (E : ExactStructure C) (e : C ≌ D)
    [e.functor.Additive] :
    (transportConflationClass E e).deflations = E.deflations.inverseImage e.inverse := by
  ext Y Z p
  constructor
  · intro hp
    obtain ⟨X, i, zero, hS⟩ :=
      (ConflationClass.isDeflation_iff (transportConflationClass E e) p).mp hp
    change E.IsDeflation (e.inverse.map p)
    exact (ConflationClass.isDeflation_iff E.toConflationClass _).mpr
      ⟨e.inverse.obj X, e.inverse.map i, by
        rw [← e.inverse.map_comp, zero, e.inverse.map_zero], hS⟩
  · intro hp
    change E.IsDeflation (e.inverse.map p) at hp
    obtain ⟨X, i, zero, hS⟩ :=
      (ConflationClass.isDeflation_iff E.toConflationClass _).mp hp
    let S := ShortComplex.mk i (e.inverse.map p) zero
    have hmap : (transportConflationClass E e).IsDeflation
        (e.functor.map (e.inverse.map p)) := by
      have hmapS : (transportConflationClass E e).Conflation (S.map e.functor) :=
        E.conflation_of_iso (by
          simpa only [ShortComplex.map_comp, ShortComplex.map_id] using
            (S.mapNatIso e.unitIso)) hS
      exact ConflationClass.isDeflation_g (transportConflationClass E e) hmapS
    exact ((transportConflationClass E e).deflations.arrow_mk_iso_iff
      (((Functor.mapArrowFunctor D D).mapIso e.counitIso).app (Arrow.mk p))).mp hmap

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem hasPushout_of_equivalence (e : C ≌ D) {X Y S : D}
    (f : S ⟶ X) (g : S ⟶ Y) [hpo : HasPushout (e.inverse.map f) (e.inverse.map g)] :
    HasPushout f g := by
  have h := (IsPushout.of_hasPushout (e.inverse.map f) (e.inverse.map g)).map e.functor
  let inl' := e.counitIso.inv.app X ≫ e.functor.map
    (pushout.inl (e.inverse.map f) (e.inverse.map g))
  let inr' := e.counitIso.inv.app Y ≫ e.functor.map
    (pushout.inr (e.inverse.map f) (e.inverse.map g))
  have h' : IsPushout f g inl' inr' := h.of_iso
    (e.counitIso.app S) (e.counitIso.app X) (e.counitIso.app Y) (Iso.refl _)
    (by simp) (by simp) (by simp [inl']) (by simp [inr'])
  exact h'.hasPushout

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem inverseImageHasPushouts (P : MorphismProperty C) [P.HasPushouts]
    (e : C ≌ D) : (P.inverseImage e.inverse).HasPushouts := by
  constructor
  intro X Y S f g hf
  exact hasPushout_of_equivalence e f g
    (hpo := MorphismProperty.HasPushouts.hasPushout (e.inverse.map g) hf)

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem inverseImageIsStableUnderCobaseChange (P : MorphismProperty C)
    [P.IsStableUnderCobaseChange] (e : C ≌ D) :
    (P.inverseImage e.inverse).IsStableUnderCobaseChange := by
  constructor
  intro A A' B B' f g f' g' sq hf
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout (P := P)
    (sq.map e.inverse) hf

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem hasPullback_of_equivalence (e : C ≌ D) {X Y S : D}
    (f : X ⟶ S) (g : Y ⟶ S) [hpb : HasPullback (e.inverse.map f) (e.inverse.map g)] :
    HasPullback f g := by
  have h := (IsPullback.of_hasPullback (e.inverse.map f) (e.inverse.map g)).map e.functor
  let fst' := e.functor.map (pullback.fst (e.inverse.map f) (e.inverse.map g)) ≫
    e.counitIso.hom.app X
  let snd' := e.functor.map (pullback.snd (e.inverse.map f) (e.inverse.map g)) ≫
    e.counitIso.hom.app Y
  have h' : IsPullback fst' snd' f g := h.of_iso
    (Iso.refl _) (e.counitIso.app X) (e.counitIso.app Y) (e.counitIso.app S)
    (by simp [fst']) (by simp [snd']) (by simp) (by simp)
  exact h'.hasPullback

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem inverseImageHasPullbacks (P : MorphismProperty C) [P.HasPullbacks]
    (e : C ≌ D) : (P.inverseImage e.inverse).HasPullbacks := by
  constructor
  intro X Y S f g hf
  exact hasPullback_of_equivalence e f g
    (hpb := MorphismProperty.HasPullbacks.hasPullback (e.inverse.map g) hf)

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem inverseImageIsStableUnderBaseChange (P : MorphismProperty C)
    [P.IsStableUnderBaseChange] (e : C ≌ D) :
    (P.inverseImage e.inverse).IsStableUnderBaseChange := by
  constructor
  intro X Y Y' S f g f' g' sq hf
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P)
    (sq.map e.inverse) hf

/-- Transport an exact structure along an additive equivalence. The distinguished short
complexes in the target are those whose images under the inverse equivalence are distinguished
in the source. -/
noncomputable def transport (E : ExactStructure C) (e : C ≌ D) [e.functor.Additive] :
    ExactStructure D where
  toConflationClass := transportConflationClass E e
  isInflation_id X := by
    change (transportConflationClass E e).inflations (𝟙 X)
    rw [transportConflationClass_inflations]
    change E.IsInflation (e.inverse.map (𝟙 X))
    simpa using E.isInflation_id (e.inverse.obj X)
  isDeflation_id X := by
    change (transportConflationClass E e).deflations (𝟙 X)
    rw [transportConflationClass_deflations]
    change E.IsDeflation (e.inverse.map (𝟙 X))
    simpa using E.isDeflation_id (e.inverse.obj X)
  isInflation_comp i j hi hj := by
    change (transportConflationClass E e).inflations i at hi
    change (transportConflationClass E e).inflations j at hj
    change (transportConflationClass E e).inflations (i ≫ j)
    rw [transportConflationClass_inflations] at hi hj ⊢
    change E.IsInflation (e.inverse.map i) at hi
    change E.IsInflation (e.inverse.map j) at hj
    change E.IsInflation (e.inverse.map (i ≫ j))
    simpa only [e.inverse.map_comp] using E.isInflation_comp _ _ hi hj
  isDeflation_comp p q hp hq := by
    change (transportConflationClass E e).deflations p at hp
    change (transportConflationClass E e).deflations q at hq
    change (transportConflationClass E e).deflations (p ≫ q)
    rw [transportConflationClass_deflations] at hp hq ⊢
    change E.IsDeflation (e.inverse.map p) at hp
    change E.IsDeflation (e.inverse.map q) at hq
    change E.IsDeflation (e.inverse.map (p ≫ q))
    simpa only [e.inverse.map_comp] using E.isDeflation_comp _ _ hp hq
  hasPushouts_inflations := by
    rw [transportConflationClass_inflations]
    exact inverseImageHasPushouts E.inflations e
  isStableUnderCobaseChange_inflations := by
    rw [transportConflationClass_inflations]
    exact inverseImageIsStableUnderCobaseChange E.inflations e
  hasPullbacks_deflations := by
    rw [transportConflationClass_deflations]
    exact inverseImageHasPullbacks E.deflations e
  isStableUnderBaseChange_deflations := by
    rw [transportConflationClass_deflations]
    exact inverseImageIsStableUnderBaseChange E.deflations e

/-- A short complex is a conflation in the transported exact structure exactly when its image
under the inverse equivalence is a conflation in the source. -/
@[simp]
theorem transport_conflation_iff (E : ExactStructure C) (e : C ≌ D)
    [e.functor.Additive] (S : ShortComplex D) :
    (transport E e).Conflation S ↔ E.Conflation (S.map e.inverse) :=
  Iff.rfl

/-- The forward functor of an additive equivalence is conflation-exact from an exact structure
to its transport. -/
theorem isConflationExact_functor_transport (E : ExactStructure C) (e : C ≌ D)
    [e.functor.Additive] : E.IsConflationExact (transport E e) e.functor where
  map_conflation {S} hS := by
    rw [transport_conflation_iff]
    exact E.conflation_of_iso (by
      simpa only [ShortComplex.map_comp, ShortComplex.map_id] using
        (S.mapNatIso e.unitIso)) hS

/-- The forward functor of an additive equivalence reflects the conflations of a transported
exact structure. -/
theorem reflectsConflations_functor_transport (E : ExactStructure C) (e : C ≌ D)
    [e.functor.Additive] : E.ReflectsConflations (transport E e) e.functor where
  reflects_conflation {S} hS := by
    rw [transport_conflation_iff] at hS
    exact E.conflation_of_iso (by
      simpa only [ShortComplex.map_comp, ShortComplex.map_id] using
        (S.mapNatIso e.unitIso).symm) hS

/-- The inverse functor of an additive equivalence is conflation-exact from the transported
exact structure back to the source. -/
theorem isConflationExact_inverse_transport (E : ExactStructure C) (e : C ≌ D)
    [e.functor.Additive] : (transport E e).IsConflationExact E e.inverse where
  map_conflation {S} hS := (transport_conflation_iff E e S).mp hS

/-- The inverse functor of an additive equivalence reflects source conflations back to the
transported exact structure. -/
theorem reflectsConflations_inverse_transport (E : ExactStructure C) (e : C ≌ D)
    [e.functor.Additive] : (transport E e).ReflectsConflations E e.inverse where
  reflects_conflation {S} hS := (transport_conflation_iff E e S).mpr hS

/-- Transporting an exact structure along an equivalence and then along its inverse recovers the
original exact structure. -/
@[simp]
theorem transport_symm (E : ExactStructure C) (e : C ≌ D) [e.functor.Additive] :
    @transport D C _ _ _ _ _ _ _ _ (transport E e) e.symm
      (inferInstanceAs e.inverse.Additive) = E := by
  apply ExactStructure.ext
  intro S
  rw [transport_conflation_iff, transport_conflation_iff]
  have i : S ≅ (S.map e.symm.inverse).map e.inverse := by
    change S ≅ (S.map e.functor).map e.inverse
    simpa only [ShortComplex.map_comp, ShortComplex.map_id] using
      (S.mapNatIso e.unitIso)
  exact (E.conflation_iff_of_iso i).symm

end ExactStructure

end TauCeti
