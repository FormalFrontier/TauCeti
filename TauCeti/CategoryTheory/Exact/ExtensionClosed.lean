/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.BaseChange
public import TauCeti.CategoryTheory.Exact.Functor
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# The exact structure induced on an extension-closed full subcategory

Let `E` be a Quillen exact structure on an additive category `C` and let `P : ObjectProperty C`
be closed under extensions: whenever `X ⟶ Y ⟶ Z` is an `E`-conflation with `P X` and `P Z`,
also `P Y`. If moreover `P` holds for a zero object and is closed under binary products — the
explicit form of "the full subcategory is additive" — then `P.FullSubcategory` carries an exact
structure whose conflations are the conflations of `E` all of whose terms lie in `P`, and the
inclusion functor both preserves and reflects conflations.

This is the third of the three fundamental constructions of exact structures, after the split
structure on an additive category and the canonical structure on an abelian category. It is what
lets a subcategory such as the finitely generated projective modules, or the modules admitting a
finite projective resolution, be treated as an exact category in its own right.

## Main definitions

* `TauCeti.ExactStructure.IsExtensionClosed`: closure of an object property under extensions in
  a given exact structure.
* `TauCeti.ExactStructure.fullSubcategory`: the induced exact structure.

## Main results

* `TauCeti.ExactStructure.IsExtensionClosed.prop_biprod`: extension closure implies closure under
  binary biproducts, so additivity of the subcategory only has to be assumed for the zero object.
* `TauCeti.ExactStructure.isExtensionClosed_split_iff` and
  `TauCeti.ExactStructure.isExtensionClosed_abelian_iff`: for the split exact structure extension
  closure is closure under binary biproducts, and for the canonical exact structure of an abelian
  category it agrees with Mathlib's
  `CategoryTheory.ObjectProperty.IsClosedUnderExtensions`.
* `TauCeti.ExactStructure.isConflationExact_ι` and
  `TauCeti.ExactStructure.reflectsConflations_ι`: the inclusion of the subcategory is
  conflation-exact and reflects conflations.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>. Lemma 10.20 is the statement proved here; the proof of E1
  uses the Noether conflation of `TauCeti/CategoryTheory/Exact/BaseChange.lean`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable [HasZeroObject C] [HasBinaryBiproducts C]

/-- A full subcategory of an additive category closed under binary products has binary
biproducts: in a preadditive category binary products already are biproducts. -/
instance (P : ObjectProperty C) [P.IsClosedUnderBinaryProducts] :
    HasBinaryBiproducts P.FullSubcategory :=
  HasBinaryBiproducts.of_hasBinaryProducts

namespace ExactStructure

/-- An object property is **extension closed** for an exact structure `E` when the middle term of
every `E`-conflation whose outer terms satisfy the property satisfies the property.

For the canonical exact structure of an abelian category this is Mathlib's
`CategoryTheory.ObjectProperty.IsClosedUnderExtensions`; see
`TauCeti.ExactStructure.isExtensionClosed_abelian_iff`. -/
structure IsExtensionClosed (E : ExactStructure C) (P : ObjectProperty C) : Prop where
  /-- The middle term of a conflation with outer terms in `P` lies in `P`. -/
  prop_X₂ {S : ShortComplex C} (hS : E.Conflation S) (h₁ : P S.X₁) (h₃ : P S.X₃) : P S.X₂

namespace IsExtensionClosed

variable {E : ExactStructure C} {P : ObjectProperty C}

/-- An extension-closed property is closed under binary biproducts, because the biproduct short
complex is a conflation of every exact structure. -/
theorem prop_biprod (hP : E.IsExtensionClosed P) {X Y : C} (hX : P X) (hY : P Y) : P (X ⊞ Y) :=
  hP.prop_X₂ (E.conflation_biprodShortComplex X Y) hX hY

/-- A replete extension-closed property is closed under binary products. Together with
`CategoryTheory.ObjectProperty.ContainsZero` this is exactly the additivity of the full
subcategory, so no separate closure hypothesis on biproducts is needed. -/
theorem isClosedUnderBinaryProducts (hP : E.IsExtensionClosed P) [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderBinaryProducts := by
  refine IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  refine P.prop_of_iso ?_ (hP.prop_biprod (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))
  exact (biprod.isoProd _ _).trans (HasLimit.isoOfNatIso (diagramIsoPair F)).symm

end IsExtensionClosed

/-- For the split exact structure, extension closure is exactly closure under binary biproducts.
This is the hypothesis under which a subcategory such as the finitely generated projective
modules inherits the split structure. -/
theorem isExtensionClosed_split_iff (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    (ExactStructure.split C).IsExtensionClosed P ↔ ∀ X Y : C, P X → P Y → P (X ⊞ Y) := by
  refine ⟨fun hP X Y hX hY => hP.prop_biprod hX hY, fun h => ⟨fun {S} hS h₁ h₃ => ?_⟩⟩
  obtain ⟨s⟩ := (ExactStructure.split_conflation S).mp hS
  exact P.prop_of_iso s.isoBinaryBiproduct.symm (h _ _ h₁ h₃)

/-- For the canonical exact structure of an abelian category, extension closure agrees with
Mathlib's `CategoryTheory.ObjectProperty.IsClosedUnderExtensions`. -/
theorem isExtensionClosed_abelian_iff {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) :
    (ExactStructure.abelian A).IsExtensionClosed P ↔ P.IsClosedUnderExtensions := by
  constructor
  · exact fun hP => ⟨fun hS h₁ h₃ => hP.prop_X₂ ((abelian_conflation _).mpr hS) h₁ h₃⟩
  · exact fun _ => ⟨fun hS h₁ h₃ =>
      P.prop_X₂_of_shortExact ((abelian_conflation _).mp hS) h₁ h₃⟩

section FullSubcategory

variable (E : ExactStructure C) (P : ObjectProperty C)

/-- The conflations induced on a full subcategory: the short complexes of the subcategory whose
image in the ambient category is a conflation. -/
private def conflationClassFullSubcategory : ConflationClass P.FullSubcategory where
  Conflation S := E.Conflation (S.map P.ι)
  isKernelCokernelPair _ hS := (E.isKernelCokernelPair _ hS).of_map P.ι
  isClosedUnderIsomorphisms :=
    ⟨fun e hS => E.conflation_of_iso (P.ι.mapShortComplex.mapIso e) hS⟩

variable {E P}

@[simp]
private theorem conflationClassFullSubcategory_conflation (S : ShortComplex P.FullSubcategory) :
    (E.conflationClassFullSubcategory P).Conflation S ↔ E.Conflation (S.map P.ι) :=
  Iff.rfl

/-- A short complex of the subcategory admitting a splitting is a conflation of the induced
class, because a splitting is carried to a splitting by the additive inclusion functor. -/
private theorem conflation_fullSubcategory_of_splitting {S : ShortComplex P.FullSubcategory}
    (s : S.Splitting) : (E.conflationClassFullSubcategory P).Conflation S :=
  E.conflation_of_splitting (s.map P.ι)

section ZeroObject

variable [P.ContainsZero]

/-- E0 for the induced class: identity morphisms are inflations. -/
private theorem isInflation_id_fullSubcategory (X : P.FullSubcategory) :
    (E.conflationClassFullSubcategory P).IsInflation (𝟙 X) :=
  (ConflationClass.isInflation_iff _ _).mpr ⟨0, 0, by simp,
    conflation_fullSubcategory_of_splitting
      (ShortComplex.Splitting.ofIsIsoOfIsZero (S := ShortComplex.mk (𝟙 X) (0 : X ⟶ 0) (by simp))
        inferInstance (isZero_zero _))⟩

/-- E0op for the induced class: identity morphisms are deflations. -/
private theorem isDeflation_id_fullSubcategory (X : P.FullSubcategory) :
    (E.conflationClassFullSubcategory P).IsDeflation (𝟙 X) :=
  (ConflationClass.isDeflation_iff _ _).mpr ⟨0, 0, by simp,
    conflation_fullSubcategory_of_splitting
      (ShortComplex.Splitting.ofIsZeroOfIsIso
        (S := ShortComplex.mk (0 : (0 : P.FullSubcategory) ⟶ X) (𝟙 X) (by simp))
        (isZero_zero _) inferInstance)⟩

end ZeroObject

/-- E1 for the induced class: a composite of inflations is an inflation. This is where extension
closure is needed — the cokernel of the composite is an extension of the two cokernels, by the
Noether conflation `TauCeti.ExactStructure.exists_conflation_comp`. -/
private theorem isInflation_comp_fullSubcategory (hP : E.IsExtensionClosed P)
    {X Y W : P.FullSubcategory} (i : X ⟶ Y) (j : Y ⟶ W)
    (hi : (E.conflationClassFullSubcategory P).IsInflation i)
    (hj : (E.conflationClassFullSubcategory P).IsInflation j) :
    (E.conflationClassFullSubcategory P).IsInflation (i ≫ j) := by
  obtain ⟨Z, p, hip, hS₁⟩ := (ConflationClass.isInflation_iff _ _).mp hi
  obtain ⟨V, v, hjv, hS₂⟩ := (ConflationClass.isInflation_iff _ _).mp hj
  obtain ⟨Q, c, α, β, hc, hβ, hQ₁, hQ₂, -, -⟩ := E.exists_conflation_comp hS₁ hS₂
  refine (ConflationClass.isInflation_iff _ _).mpr
    ⟨⟨Q, hP.prop_X₂ hQ₂ Z.property V.property⟩, ObjectProperty.homMk c, ?_, hQ₁⟩
  apply ObjectProperty.hom_ext
  simpa using hc

/-- E1op for the induced class: a composite of deflations is a deflation. -/
private theorem isDeflation_comp_fullSubcategory (hP : E.IsExtensionClosed P)
    {W Y Z : P.FullSubcategory} (q : W ⟶ Y) (p : Y ⟶ Z)
    (hq : (E.conflationClassFullSubcategory P).IsDeflation q)
    (hp : (E.conflationClassFullSubcategory P).IsDeflation p) :
    (E.conflationClassFullSubcategory P).IsDeflation (q ≫ p) := by
  obtain ⟨V, v, hvq, hS₂⟩ := (ConflationClass.isDeflation_iff _ _).mp hq
  obtain ⟨X, i, hip, hS₁⟩ := (ConflationClass.isDeflation_iff _ _).mp hp
  obtain ⟨Q, c, α, β, hc, hβ, hQ₁, hQ₂, -, -⟩ := E.exists_conflation_comp' hS₁ hS₂
  refine (ConflationClass.isDeflation_iff _ _).mpr
    ⟨⟨Q, hP.prop_X₂ hQ₂ V.property X.property⟩, ObjectProperty.homMk c, ?_, hQ₁⟩
  apply ObjectProperty.hom_ext
  simpa using hc

/-- E2 for the induced class: a pushout of an inflation along an arbitrary morphism exists inside
the subcategory, and the cobase-changed morphism is again an inflation.

The pushout is computed in the ambient category; extension closure is what places it back in the
subcategory, since by `TauCeti.ExactStructure.conflation_cobaseChange` it is an extension of the
cokernel of the inflation by the target of the arbitrary morphism. -/
private theorem exists_isPushout_fullSubcategory (hP : E.IsExtensionClosed P)
    {X Y T : P.FullSubcategory}
    {i : X ⟶ Y} (hi : (E.conflationClassFullSubcategory P).IsInflation i) (f : X ⟶ T) :
    ∃ (Q : P.FullSubcategory) (v : Y ⟶ Q) (w : T ⟶ Q),
      IsPushout i f v w ∧ (E.conflationClassFullSubcategory P).IsInflation w := by
  obtain ⟨Z, p, hip, hS⟩ := (ConflationClass.isInflation_iff _ _).mp hi
  have hS' : E.Conflation ((ShortComplex.mk i p hip).map P.ι) := hS
  have : HasPushout (P.ι.map i) (P.ι.map f) :=
    E.hasPushouts_inflations.hasPushout (P.ι.map f) (E.isInflation_f hS')
  have sqC : IsPushout (P.ι.map i) (P.ι.map f) (pushout.inl (P.ι.map i) (P.ι.map f))
      (pushout.inr (P.ι.map i) (P.ι.map f)) := IsPushout.of_hasPushout _ _
  have hconf := E.conflation_cobaseChange hS' sqC
  rw [cobaseChange_def ((ShortComplex.mk i p hip).map P.ι) sqC] at hconf
  refine ⟨⟨_, hP.prop_X₂ hconf T.property Z.property⟩,
    ObjectProperty.homMk (pushout.inl _ _), ObjectProperty.homMk (pushout.inr _ _),
    IsPushout.of_map_of_faithful P.ι sqC, (ConflationClass.isInflation_iff _ _).mpr
      ⟨Z, ObjectProperty.homMk (cobaseChangeπ ((ShortComplex.mk i p hip).map P.ι) sqC),
        ?_, hconf⟩⟩
  exact ObjectProperty.hom_ext _ (inr_cobaseChangeπ ((ShortComplex.mk i p hip).map P.ι) sqC)

/-- E2op for the induced class: a pullback of a deflation along an arbitrary morphism exists
inside the subcategory, and the base-changed morphism is again a deflation. -/
private theorem exists_isPullback_fullSubcategory (hP : E.IsExtensionClosed P)
    {Y Z T : P.FullSubcategory}
    {p : Y ⟶ Z} (hp : (E.conflationClassFullSubcategory P).IsDeflation p) (f : T ⟶ Z) :
    ∃ (Q : P.FullSubcategory) (v : Q ⟶ Y) (w : Q ⟶ T),
      IsPullback v w p f ∧ (E.conflationClassFullSubcategory P).IsDeflation w := by
  obtain ⟨X, i, hip, hS⟩ := (ConflationClass.isDeflation_iff _ _).mp hp
  have hS' : E.Conflation ((ShortComplex.mk i p hip).map P.ι) := hS
  have : HasPullback (P.ι.map p) (P.ι.map f) :=
    E.hasPullbacks_deflations.hasPullback (P.ι.map f) (E.isDeflation_g hS')
  have sqC : IsPullback (pullback.fst (P.ι.map p) (P.ι.map f))
      (pullback.snd (P.ι.map p) (P.ι.map f)) (P.ι.map p) (P.ι.map f) :=
    IsPullback.of_hasPullback _ _
  have hconf := E.conflation_baseChange hS' sqC
  rw [baseChange_def ((ShortComplex.mk i p hip).map P.ι) sqC] at hconf
  refine ⟨⟨_, hP.prop_X₂ hconf X.property T.property⟩,
    ObjectProperty.homMk (pullback.fst _ _), ObjectProperty.homMk (pullback.snd _ _),
    IsPullback.of_map_of_faithful P.ι sqC, (ConflationClass.isDeflation_iff _ _).mpr
      ⟨X, ObjectProperty.homMk (baseChangeι ((ShortComplex.mk i p hip).map P.ι) sqC),
        ?_, hconf⟩⟩
  exact ObjectProperty.hom_ext _ (baseChangeι_snd ((ShortComplex.mk i p hip).map P.ι) sqC)

variable (P) in
/-- **The exact structure induced on an extension-closed full subcategory.** Its conflations are
the conflations of `E` all of whose terms lie in `P`.

The subcategory is required to be additive in the explicit form of containing a zero object and
being closed under binary products; by
`TauCeti.ExactStructure.IsExtensionClosed.isClosedUnderBinaryProducts` the second condition is
automatic for a replete extension-closed `P`. -/
noncomputable def fullSubcategory [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
    (hP : E.IsExtensionClosed P) : ExactStructure P.FullSubcategory where
  toConflationClass := E.conflationClassFullSubcategory P
  isInflation_id := isInflation_id_fullSubcategory
  isDeflation_id := isDeflation_id_fullSubcategory
  isInflation_comp := isInflation_comp_fullSubcategory hP
  isDeflation_comp := isDeflation_comp_fullSubcategory hP
  hasPushouts_inflations := by
    refine ⟨fun {_ _ _ _} g hf => ?_⟩
    obtain ⟨_, _, _, sq, -⟩ := exists_isPushout_fullSubcategory hP hf g
    exact sq.hasPushout
  isStableUnderCobaseChange_inflations := by
    refine ⟨fun {_ _ _ _ _ g _ _} sq hf => ?_⟩
    obtain ⟨_, _, w, sq₀, hw⟩ := exists_isPushout_fullSubcategory hP hf g
    rw [← sq₀.inr_isoIsPushout_hom _ _ sq.flip]
    exact ((E.conflationClassFullSubcategory P).inflations.cancel_right_of_respectsIso w
      (sq₀.isoIsPushout _ _ sq.flip).hom).mpr hw
  hasPullbacks_deflations := by
    refine ⟨fun {_ _ _ _} g hf => ?_⟩
    obtain ⟨_, _, _, sq, -⟩ := exists_isPullback_fullSubcategory hP hf g
    exact sq.hasPullback
  isStableUnderBaseChange_deflations := by
    refine ⟨fun {_ _ _ _ f _ _ _} sq hg => ?_⟩
    obtain ⟨_, _, w, sq₀, hw⟩ := exists_isPullback_fullSubcategory hP hg f
    rw [← sq₀.isoIsPullback_inv_snd _ _ sq]
    exact ((E.conflationClassFullSubcategory P).deflations.cancel_left_of_respectsIso
      (sq₀.isoIsPullback _ _ sq).inv w).mpr hw

variable [P.ContainsZero] [P.IsClosedUnderBinaryProducts] (hP : E.IsExtensionClosed P)

/-- A short complex of the subcategory is a conflation of the induced exact structure exactly
when its image in the ambient category is a conflation. -/
@[simp]
theorem fullSubcategory_conflation_iff (S : ShortComplex P.FullSubcategory) :
    (E.fullSubcategory P hP).Conflation S ↔ E.Conflation (S.map P.ι) :=
  Iff.rfl

/-- The inclusion of an extension-closed full subcategory is conflation-exact. -/
theorem isConflationExact_ι : (E.fullSubcategory P hP).IsConflationExact E P.ι where
  map_conflation hS := hS

/-- The inclusion of an extension-closed full subcategory reflects conflations: a short complex
of the subcategory whose image is a conflation of `E` is a conflation of the induced structure. -/
theorem reflectsConflations_ι : (E.fullSubcategory P hP).ReflectsConflations E P.ι where
  reflects_conflation hS := hS

end FullSubcategory

end ExactStructure

end TauCeti
