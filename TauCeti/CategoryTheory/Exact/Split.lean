/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExactStructure
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The split exact structure on an additive category

Every additive category `C` carries a Quillen exact structure `ExactStructure.split C` whose
conflations are the short complexes admitting a splitting, that is, the short complexes
isomorphic to `X ⟶ X ⊞ Z ⟶ Z`.

In this exact structure a morphism `i : X ⟶ Y` is an inflation exactly when it is the inclusion
of a biproduct summand: there are an object `Z` and an isomorphism `e : Y ≅ X ⊞ Z` with
`i ≫ e.hom = biprod.inl`. Being a split monomorphism is *not* enough, because the complementary
summand need not exist; the two notions agree as soon as the relevant idempotent splits.

The split structure is the smallest exact structure on `C`: the last section proves that a short
complex with a splitting is a conflation for *every* exact structure `E` on `C`. This is Bühler's
Lemma 2.7, and it is what makes the comparison out of split `K₀` available for an arbitrary exact
structure.

## Main definitions

* `TauCeti.biprodShortComplex X Z`: the short complex `X ⟶ X ⊞ Z ⟶ Z`.
* `TauCeti.ConflationClass.split`: the class of short complexes admitting a splitting.
* `TauCeti.ExactStructure.split`: the split exact structure on an additive category.

## Main results

* `TauCeti.ConflationClass.split_isInflation_iff` and
  `TauCeti.ConflationClass.split_isDeflation_iff`: the split inflations are the biproduct
  inclusions and the split deflations are the biproduct projections.
* `TauCeti.ConflationClass.exists_isPushout_of_split_isInflation` and
  `TauCeti.ConflationClass.exists_isPullback_of_split_isDeflation`: the E2/E2op squares, computed
  explicitly in the biproduct decomposition.
* `TauCeti.ExactStructure.conflation_of_splitting`: a split short complex is a conflation of
  every exact structure, so `ExactStructure.split C` is the smallest one.
* `TauCeti.ExactStructure.conflation_zero_id`: the trivial conflation `0 ↪ X ↠ X`, split by the
  identity, is a conflation of every exact structure.
* `TauCeti.ExactStructure.split_isInflation_iff` and
  `TauCeti.ExactStructure.split_isDeflation_iff`: the characteristic API of
  `TauCeti.ExactStructure.split`.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>. Section 13.1 constructs the split exact structure, and
  Lemma 2.7 shows that split short complexes are conflations of any exact structure.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Section 5, where split `K₀` is presented through the split exact structure.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

section BiprodShortComplex

variable (X Z : C) [HasBinaryBiproduct X Z]

/-- The biproduct short complex `X ⟶ X ⊞ Z ⟶ Z`. Up to isomorphism these are exactly the
conflations of the split exact structure. -/
noncomputable abbrev biprodShortComplex : ShortComplex C :=
  ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Z) biprod.snd (by simp)

variable {X Z}

/-- A splitting of `S` identifies `S` with the biproduct short complex on its outer terms. -/
noncomputable def isoBiprodShortComplex {S : ShortComplex C} (s : S.Splitting)
    [HasBinaryBiproduct S.X₁ S.X₃] : S ≅ biprodShortComplex S.X₁ S.X₃ :=
  ShortComplex.isoMk (Iso.refl _) s.isoBinaryBiproduct (Iso.refl _)
    (by apply biprod.hom_ext <;> simp) (by simp)

end BiprodShortComplex

namespace ConflationClass

variable (C) in
/-- The class of short complexes admitting a splitting. These are the conflations of the split
exact structure. -/
def split : ConflationClass C where
  Conflation S := Nonempty S.Splitting
  isKernelCokernelPair _ hS := .of_splitting hS.some
  isClosedUnderIsomorphisms := ⟨fun e hS => ⟨hS.some.ofIso e⟩⟩

/-- The split conflations are exactly the short complexes admitting a splitting. -/
@[simp]
theorem split_conflation_iff (S : ShortComplex C) :
    (split C).Conflation S ↔ Nonempty S.Splitting :=
  Iff.rfl

/-- The biproduct short complex `X ⟶ X ⊞ Z ⟶ Z` is a split conflation. -/
theorem split_conflation_biprodShortComplex (X Z : C) [HasBinaryBiproduct X Z] :
    (split C).Conflation (biprodShortComplex X Z) :=
  ⟨ShortComplex.Splitting.ofHasBinaryBiproduct X Z⟩

/-- The short complex `Z ⟶ X ⊞ Z ⟶ X` on the other biproduct summand is a split conflation. -/
theorem split_conflation_biprod_inr_fst (X Z : C) [HasBinaryBiproduct X Z] :
    (split C).Conflation
      (ShortComplex.mk (biprod.inr : Z ⟶ X ⊞ Z) (biprod.fst : X ⊞ Z ⟶ X) (by simp)) :=
  ⟨{ r := biprod.snd
     s := biprod.inl
     id := by rw [add_comm]; exact biprod.total }⟩

/-- A biproduct inclusion is a split inflation. -/
@[simp]
theorem split_isInflation_biprod_inl (X Z : C) [HasBinaryBiproduct X Z] :
    (split C).IsInflation (biprod.inl : X ⟶ X ⊞ Z) :=
  (split C).isInflation_f (split_conflation_biprodShortComplex X Z)

/-- The other biproduct inclusion is a split inflation as well. -/
@[simp]
theorem split_isInflation_biprod_inr (X Z : C) [HasBinaryBiproduct X Z] :
    (split C).IsInflation (biprod.inr : Z ⟶ X ⊞ Z) :=
  (split C).isInflation_f (split_conflation_biprod_inr_fst X Z)

/-- A biproduct projection is a split deflation. -/
@[simp]
theorem split_isDeflation_biprod_snd (X Z : C) [HasBinaryBiproduct X Z] :
    (split C).IsDeflation (biprod.snd : X ⊞ Z ⟶ Z) :=
  (split C).isDeflation_g (split_conflation_biprodShortComplex X Z)

/-- The other biproduct projection is a split deflation as well. -/
@[simp]
theorem split_isDeflation_biprod_fst (X Z : C) [HasBinaryBiproduct X Z] :
    (split C).IsDeflation (biprod.fst : X ⊞ Z ⟶ X) :=
  (split C).isDeflation_g (split_conflation_biprod_inr_fst X Z)

/-- Every split inflation is a split monomorphism. The converse fails in general: a split
monomorphism is an inflation only once its complementary idempotent splits. -/
theorem isSplitMono_of_split_isInflation {X Y : C} {i : X ⟶ Y}
    (hi : (split C).IsInflation i) : IsSplitMono i := by
  obtain ⟨Z, p, zero, hS⟩ := (isInflation_iff (split C) i).mp hi
  obtain ⟨s⟩ := (split_conflation_iff _).mp hS
  exact ⟨⟨s.r, s.f_r⟩⟩

/-- Every split deflation is a split epimorphism. -/
theorem isSplitEpi_of_split_isDeflation {Y Z : C} {p : Y ⟶ Z}
    (hp : (split C).IsDeflation p) : IsSplitEpi p := by
  obtain ⟨X, i, zero, hS⟩ := (isDeflation_iff (split C) p).mp hp
  obtain ⟨s⟩ := (split_conflation_iff _).mp hS
  exact ⟨⟨s.s, s.s_g⟩⟩

variable [HasBinaryBiproducts C]

/-- **The split inflations are the biproduct inclusions.** A split monomorphism whose
complementary idempotent does not split is *not* an inflation of the split exact structure. -/
theorem split_isInflation_iff {X Y : C} (i : X ⟶ Y) :
    (split C).IsInflation i ↔ ∃ (Z : C) (e : Y ≅ X ⊞ Z), i ≫ e.hom = biprod.inl := by
  rw [isInflation_iff]
  constructor
  · rintro ⟨Z, p, zero, hS⟩
    obtain ⟨s⟩ := (split_conflation_iff _).mp hS
    have hr : i ≫ s.r = 𝟙 X := s.f_r
    refine ⟨Z, s.isoBinaryBiproduct, ?_⟩
    apply biprod.hom_ext <;> simp [hr, zero]
  · rintro ⟨Z, e, he⟩
    have hi : biprod.inl ≫ e.inv = i := by
      rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
    refine ⟨Z, e.hom ≫ biprod.snd, by rw [← Category.assoc, he]; simp,
      (split_conflation_iff _).mpr ⟨?_⟩⟩
    exact (ShortComplex.Splitting.ofHasBinaryBiproduct X Z).ofIso
      (ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) (by simpa using hi.symm) (by simp))

/-- **The split deflations are the biproduct projections.** -/
theorem split_isDeflation_iff {Y Z : C} (p : Y ⟶ Z) :
    (split C).IsDeflation p ↔ ∃ (X : C) (e : Y ≅ X ⊞ Z), e.inv ≫ p = biprod.snd := by
  rw [isDeflation_iff]
  constructor
  · rintro ⟨X, i, zero, hS⟩
    obtain ⟨s⟩ := (split_conflation_iff _).mp hS
    have hs : s.s ≫ p = 𝟙 Z := s.s_g
    refine ⟨X, s.isoBinaryBiproduct, ?_⟩
    apply biprod.hom_ext' <;> simp [hs, zero]
  · rintro ⟨X, e, he⟩
    refine ⟨X, biprod.inl ≫ e.inv, by rw [Category.assoc, he]; simp,
      (split_conflation_iff _).mpr ⟨?_⟩⟩
    exact (ShortComplex.Splitting.ofHasBinaryBiproduct X Z).ofIso
      (ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simpa using he))

/-- **E1 for the split exact structure**: a composite of split inflations is a split inflation.
The cokernel of `i ≫ j` is the biproduct of the two cokernels. -/
theorem split_isInflation_comp {X Y W : C} {i : X ⟶ Y} {j : Y ⟶ W}
    (hi : (split C).IsInflation i) (hj : (split C).IsInflation j) :
    (split C).IsInflation (i ≫ j) := by
  obtain ⟨Z₁, p, hip, hS₁⟩ := (isInflation_iff (split C) i).mp hi
  obtain ⟨Z₂, q, hjq, hS₂⟩ := (isInflation_iff (split C) j).mp hj
  obtain ⟨s₁⟩ := (split_conflation_iff _).mp hS₁
  obtain ⟨s₂⟩ := (split_conflation_iff _).mp hS₂
  have hir : i ≫ s₁.r = 𝟙 X := s₁.f_r
  have hsp : s₁.s ≫ p = 𝟙 Z₁ := s₁.s_g
  have hid₁ : s₁.r ≫ i + p ≫ s₁.s = 𝟙 Y := s₁.id
  have hjr : j ≫ s₂.r = 𝟙 Y := s₂.f_r
  have hsq : s₂.s ≫ q = 𝟙 Z₂ := s₂.s_g
  have hsr : s₂.s ≫ s₂.r = 0 := s₂.s_r
  have hid₂ : s₂.r ≫ j + q ≫ s₂.s = 𝟙 W := s₂.id
  have key : s₁.r ≫ i ≫ j + p ≫ s₁.s ≫ j = j := by
    rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, hid₁, Category.id_comp]
  refine (isInflation_iff (split C) _).mpr ⟨Z₁ ⊞ Z₂, biprod.lift (s₂.r ≫ p) q, by
    apply biprod.hom_ext <;> simp [reassoc_of% hjr, hip, hjq],
    (split_conflation_iff _).mpr ⟨?_⟩⟩
  exact
    { r := s₂.r ≫ s₁.r
      s := biprod.desc (s₁.s ≫ j) s₂.s
      f_r := by simp [reassoc_of% hjr, hir]
      s_g := by ext <;> simp [reassoc_of% hjr, hsp, hjq, reassoc_of% hsr, hsq]
      id := by
        simp only [biprod.lift_desc, Category.assoc]
        rw [← add_assoc, ← Preadditive.comp_add, key]
        exact hid₂ }

/-- **E1op for the split exact structure**: a composite of split deflations is a split
deflation. The kernel of `p ≫ q` is the biproduct of the two kernels. -/
theorem split_isDeflation_comp {X Y Z : C} {p : X ⟶ Y} {q : Y ⟶ Z}
    (hp : (split C).IsDeflation p) (hq : (split C).IsDeflation q) :
    (split C).IsDeflation (p ≫ q) := by
  obtain ⟨K₁, i₁, hi₁p, hS₁⟩ := (isDeflation_iff (split C) p).mp hp
  obtain ⟨K₂, i₂, hi₂q, hS₂⟩ := (isDeflation_iff (split C) q).mp hq
  obtain ⟨t₁⟩ := (split_conflation_iff _).mp hS₁
  obtain ⟨t₂⟩ := (split_conflation_iff _).mp hS₂
  have hi₁r : i₁ ≫ t₁.r = 𝟙 K₁ := t₁.f_r
  have hsp : t₁.s ≫ p = 𝟙 Y := t₁.s_g
  have hsr : t₁.s ≫ t₁.r = 0 := t₁.s_r
  have hid₁ : t₁.r ≫ i₁ + p ≫ t₁.s = 𝟙 X := t₁.id
  have hi₂r : i₂ ≫ t₂.r = 𝟙 K₂ := t₂.f_r
  have hsq : t₂.s ≫ q = 𝟙 Z := t₂.s_g
  have hid₂ : t₂.r ≫ i₂ + q ≫ t₂.s = 𝟙 Y := t₂.id
  have key : t₂.r ≫ i₂ ≫ t₁.s + q ≫ t₂.s ≫ t₁.s = t₁.s := by
    rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, hid₂, Category.id_comp]
  refine (isDeflation_iff (split C) _).mpr ⟨K₁ ⊞ K₂, biprod.desc i₁ (i₂ ≫ t₁.s), by
    apply biprod.hom_ext' <;> simp [reassoc_of% hi₁p, reassoc_of% hsp, hi₂q],
    (split_conflation_iff _).mpr ⟨?_⟩⟩
  exact
    { r := biprod.lift t₁.r (p ≫ t₂.r)
      s := t₂.s ≫ t₁.s
      f_r := by ext <;> simp [hi₁r, reassoc_of% hi₁p, reassoc_of% hsp, hi₂r]
      s_g := by simp [reassoc_of% hsp, hsq]
      id := by
        simp only [biprod.lift_desc, Category.assoc]
        rw [add_assoc, ← Preadditive.comp_add, key]
        exact hid₁ }

/-- **E2 for the split exact structure**: the pushout of a split inflation `i : A ⟶ B` along an
arbitrary `g : A ⟶ A'` exists and its cobase change is again a split inflation. Concretely, if
`B ≅ A ⊞ Z` identifies `i` with `biprod.inl`, then the pushout is `A' ⊞ Z`. -/
theorem exists_isPushout_of_split_isInflation {A B A' : C} {i : A ⟶ B}
    (hi : (split C).IsInflation i) (g : A ⟶ A') :
    ∃ (T : C) (inl : B ⟶ T) (inr : A' ⟶ T),
      IsPushout i g inl inr ∧ (split C).IsInflation inr := by
  obtain ⟨Z, e, he⟩ := (split_isInflation_iff i).mp hi
  have hi' : biprod.inl ≫ e.inv = i := by
    rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hbase : IsPushout (biprod.inl : A ⟶ A ⊞ Z) g (biprod.map g (𝟙 Z))
      (biprod.inl : A' ⟶ A' ⊞ Z) := isPushout_biprod_inl_map g Z
  refine ⟨A' ⊞ Z, e.hom ≫ biprod.map g (𝟙 Z), biprod.inl, ?_, split_isInflation_biprod_inl A' Z⟩
  exact hbase.of_iso (Iso.refl A) e.symm (Iso.refl A') (Iso.refl _) (by simpa using hi')
    (by simp) (by simp) (by simp)

/-- **E2op for the split exact structure**: the pullback of a split deflation `p : Y ⟶ Z` along
an arbitrary `f : A ⟶ Z` exists and its base change is again a split deflation. Concretely, if
`Y ≅ X ⊞ Z` identifies `p` with `biprod.snd`, then the pullback is `X ⊞ A`. -/
theorem exists_isPullback_of_split_isDeflation {Y Z A : C} {p : Y ⟶ Z}
    (hp : (split C).IsDeflation p) (f : A ⟶ Z) :
    ∃ (T : C) (fst : T ⟶ A) (snd : T ⟶ Y),
      IsPullback fst snd f p ∧ (split C).IsDeflation fst := by
  obtain ⟨X, e, he⟩ := (split_isDeflation_iff p).mp hp
  have hbase : IsPullback (biprod.snd : X ⊞ A ⟶ A) (biprod.map (𝟙 X) f) f
      (biprod.snd : X ⊞ Z ⟶ Z) :=
    (isPullback_biprod_map_fst f X).of_iso
      (biprod.braiding A X) (Iso.refl A) (biprod.braiding Z X) (Iso.refl Z)
      (by simp) (by ext <;> simp) (by simp) (by simp)
  refine ⟨X ⊞ A, biprod.snd, biprod.map (𝟙 X) f ≫ e.inv, ?_, split_isDeflation_biprod_snd X A⟩
  exact hbase.of_iso (Iso.refl _) (Iso.refl A) e.symm (Iso.refl Z) (by simp) (by simp) (by simp)
    (by simpa using he.symm)

end ConflationClass

variable (C) in
/-- The **split exact structure** on an additive category: its conflations are the short
complexes admitting a splitting.

Its conflations are only the split short complexes, whereas those of the canonical exact
structure of an abelian category are all the short exact ones; see
`TauCeti.ExactStructure.conflation_of_splitting` for the general comparison. -/
noncomputable def ExactStructure.split [HasZeroObject C] [HasBinaryBiproducts C] :
    ExactStructure C where
  toConflationClass := ConflationClass.split C
  isInflation_id X := by
    refine (ConflationClass.isInflation_iff _ _).mpr
      ⟨0, 0, by simp, (ConflationClass.split_conflation_iff _).mpr ⟨?_⟩⟩
    exact ShortComplex.Splitting.ofIsIsoOfIsZero _ (inferInstanceAs (IsIso (𝟙 X)))
      (isZero_zero C)
  isDeflation_id X := by
    refine (ConflationClass.isDeflation_iff _ _).mpr
      ⟨0, 0, by simp, (ConflationClass.split_conflation_iff _).mpr ⟨?_⟩⟩
    exact ShortComplex.Splitting.ofIsZeroOfIsIso _ (isZero_zero C)
      (inferInstanceAs (IsIso (𝟙 X)))
  isInflation_comp _ _ hi hj := ConflationClass.split_isInflation_comp hi hj
  isDeflation_comp _ _ hp hq := ConflationClass.split_isDeflation_comp hp hq
  hasPushouts_inflations := ⟨fun g hf => by
    obtain ⟨_, _, _, sq, -⟩ := ConflationClass.exists_isPushout_of_split_isInflation hf g
    exact sq.hasPushout⟩
  isStableUnderCobaseChange_inflations :=
    .of_forall_exists_isPullback fun _ g _ hf =>
      ConflationClass.exists_isPushout_of_split_isInflation hf g
  hasPullbacks_deflations := ⟨fun g hf => by
    obtain ⟨_, _, _, sq, -⟩ := ConflationClass.exists_isPullback_of_split_isDeflation hf g
    exact sq.flip.hasPullback⟩
  isStableUnderBaseChange_deflations :=
    .of_forall_exists_isPullback fun f _ _ hg =>
      ConflationClass.exists_isPullback_of_split_isDeflation hg f

namespace ExactStructure

variable [HasZeroObject C] [HasBinaryBiproducts C]

/-- The conflations of the split exact structure are exactly the short complexes admitting a
splitting. -/
@[simp]
theorem split_conflation (S : ShortComplex C) :
    (ExactStructure.split C).Conflation S ↔ Nonempty S.Splitting :=
  ConflationClass.split_conflation_iff S

/-- **The inflations of the split exact structure are the biproduct inclusions.** -/
@[simp]
theorem split_isInflation_iff {X Y : C} (i : X ⟶ Y) :
    (ExactStructure.split C).IsInflation i ↔ ∃ (Z : C) (e : Y ≅ X ⊞ Z), i ≫ e.hom = biprod.inl :=
  ConflationClass.split_isInflation_iff i

/-- **The deflations of the split exact structure are the biproduct projections.** -/
@[simp]
theorem split_isDeflation_iff {Y Z : C} (p : Y ⟶ Z) :
    (ExactStructure.split C).IsDeflation p ↔ ∃ (X : C) (e : Y ≅ X ⊞ Z), e.inv ≫ p = biprod.snd :=
  ConflationClass.split_isDeflation_iff p

/-- In every exact structure the biproduct short complex `X ⟶ X ⊞ Z ⟶ Z` is a conflation.

No exact structure can therefore omit a biproduct decomposition. This is the key step of
Bühler's Lemma 2.7, from which `TauCeti.ExactStructure.conflation_of_splitting` — the
minimality of the split exact structure — follows by closure under isomorphisms. -/
@[simp]
theorem conflation_biprodShortComplex (E : ExactStructure C) (X Z : C) :
    E.Conflation (biprodShortComplex X Z) := by
  obtain ⟨K, i, hi, hK⟩ :=
    (ConflationClass.isDeflation_iff E.toConflationClass _).mp (E.isDeflation_id Z)
  have hi0 : i = 0 := by simpa using hi
  -- `X ⊞ Z` is the pushout of the zero span `X ⟵ K ⟶ Z`.
  have hcomm : (0 : K ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Z) = i ≫ biprod.inr := by
    rw [hi0]; simp
  have sq : IsPushout (0 : K ⟶ X) i (biprod.inl : X ⟶ X ⊞ Z) (biprod.inr : Z ⟶ X ⊞ Z) :=
    IsPushout.of_isColimit' ⟨hcomm⟩ (PushoutCocone.IsColimit.mk hcomm
      (fun s => biprod.desc s.inl s.inr) (fun _ => by simp) (fun _ => by simp)
      (fun _ m h₁ h₂ => by apply biprod.hom_ext' <;> simp [h₁, h₂]))
  have hinl : E.IsInflation (biprod.inl : X ⟶ X ⊞ Z) :=
    E.isStableUnderCobaseChange_inflations.of_isPushout sq
      (E.toConflationClass.isInflation_f hK)
  have hzero : (biprod.inl : X ⟶ X ⊞ Z) ≫ (biprod.snd : X ⊞ Z ⟶ Z) = 0 := by simp
  have hpair' : IsKernelCokernelPair
      (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Z) biprod.snd hzero) :=
    IsKernelCokernelPair.of_hasBinaryBiproduct X Z
  exact E.conflation_of_isKernelCokernelPair_of_isInflation hpair' hinl

/-- **A short complex with a splitting is a conflation of every exact structure.**
Equivalently, the split exact structure is the smallest exact structure on `C`. -/
theorem conflation_of_splitting (E : ExactStructure C) {S : ShortComplex C} (s : S.Splitting) :
    E.Conflation S :=
  E.toConflationClass.conflation_of_iso (isoBiprodShortComplex s).symm
    (E.conflation_biprodShortComplex S.X₁ S.X₃)

/-- The trivial conflation `0 ↪ X ↠ X`, split by the identity. -/
theorem conflation_zero_id (E : ExactStructure C) (X : C) :
    E.Conflation (ShortComplex.mk (0 : (0 : C) ⟶ X) (𝟙 X) (by simp)) :=
  E.conflation_of_splitting { r := 0, s := 𝟙 X, f_r := (isZero_zero C).eq_of_src _ _ }

/-- A conflation of the split exact structure is a conflation of every exact structure. -/
theorem conflation_of_split_conflation (E : ExactStructure C) {S : ShortComplex C}
    (hS : (ExactStructure.split C).Conflation S) : E.Conflation S :=
  E.conflation_of_splitting ((split_conflation S).mp hS).some

/-- Every split inflation is an inflation of any exact structure. -/
theorem isInflation_of_split_isInflation (E : ExactStructure C) {X Y : C} {i : X ⟶ Y}
    (hi : (ExactStructure.split C).IsInflation i) : E.IsInflation i := by
  obtain ⟨Z, p, zero, hS⟩ :=
    (ConflationClass.isInflation_iff (ExactStructure.split C).toConflationClass i).mp hi
  exact (ConflationClass.isInflation_iff E.toConflationClass i).mpr
    ⟨Z, p, zero, E.conflation_of_split_conflation hS⟩

/-- Every split deflation is a deflation of any exact structure. -/
theorem isDeflation_of_split_isDeflation (E : ExactStructure C) {Y Z : C} {p : Y ⟶ Z}
    (hp : (ExactStructure.split C).IsDeflation p) : E.IsDeflation p := by
  obtain ⟨X, i, zero, hS⟩ :=
    (ConflationClass.isDeflation_iff (ExactStructure.split C).toConflationClass p).mp hp
  exact (ConflationClass.isDeflation_iff E.toConflationClass p).mpr
    ⟨X, i, zero, E.conflation_of_split_conflation hS⟩

end ExactStructure

end TauCeti
