/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Functor
public import TauCeti.CategoryTheory.Exact.Opposite
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# The category of conflations

For a fixed conflation class `E`, a conflation is not merely a proposition about a short complex:
conflations and commutative diagrams between them form a category. This file realizes that
category as the full subcategory of `ShortComplex C` on the distinguished kernel--cokernel pairs.
Consequently, a morphism of conflations is exactly a ladder of two commuting squares with three
vertical maps, and an isomorphism of conflations is exactly such a ladder whose vertical maps are
isomorphisms.

The construction deliberately reuses Mathlib's category of short complexes. In particular,
composition, identities, the preadditive structure, component functors, and the componentwise
criterion for isomorphisms are inherited rather than duplicated.

Conflation-exact functors induce functors between conflation categories. Naturally isomorphic
conflation-exact functors induce naturally isomorphic functors, and passage to the opposite
conflation class gives the expected equivalence on conflations.

## Main definitions and results

* `TauCeti.ConflationClass.ConflationCategory`: the full subcategory of distinguished short
  complexes.
* `TauCeti.ConflationClass.ConflationCategory.homMk` and `.isoMk`: constructors for maps and
  isomorphisms of conflations from their three components.
* `TauCeti.ConflationClass.ConflationCategory.isIso_iff`: a map of conflations is an isomorphism
  exactly when all three components are isomorphisms.
* `TauCeti.ConflationClass.ConflationCategory.map`: the functor induced by a functor preserving
  conflations, with `TauCeti.ExactStructure.ConflationCategory.map` as its exact-structure
  specialization.
* `TauCeti.ConflationClass.ConflationCategory.mapIdIso` and `.mapCompIso`: identity and composition
  coherence for the induced functor.
* `TauCeti.ConflationClass.ConflationCategory.mapNatIso`: natural-isomorphism invariance of the
  induced functor.
* `TauCeti.ConflationClass.ConflationCategory.opEquivalence`: the equivalence
  `E.ConflationCategoryᵒᵖ ≃ E.op.ConflationCategory`.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Sections 2 and 5.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace ConflationClass

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

/-- The category of conflations of a conflation class `E`. Its objects are distinguished short
complexes, and its morphisms are arbitrary morphisms of the underlying short complexes. -/
abbrev ConflationCategory (E : ConflationClass C) :=
  ObjectProperty.FullSubcategory (fun S : ShortComplex C ↦ E.Conflation S)

namespace ConflationCategory

variable {E : ConflationClass C}

/-- The fully faithful inclusion of the category of conflations into the category of short
complexes. -/
abbrev ι (E : ConflationClass C) : E.ConflationCategory ⥤ ShortComplex C :=
  ObjectProperty.ι (fun S : ShortComplex C ↦ E.Conflation S)

/-- The left-object functor on the category of conflations. -/
abbrev π₁ (E : ConflationClass C) : E.ConflationCategory ⥤ C :=
  ι E ⋙ ShortComplex.π₁

/-- The middle-object functor on the category of conflations. -/
abbrev π₂ (E : ConflationClass C) : E.ConflationCategory ⥤ C :=
  ι E ⋙ ShortComplex.π₂

/-- The right-object functor on the category of conflations. -/
abbrev π₃ (E : ConflationClass C) : E.ConflationCategory ⥤ C :=
  ι E ⋙ ShortComplex.π₃

/-- The first arrow of every conflation, as a natural transformation. -/
abbrev π₁Toπ₂ (E : ConflationClass C) : π₁ E ⟶ π₂ E :=
  Functor.whiskerLeft (ι E) ShortComplex.π₁Toπ₂

/-- The second arrow of every conflation, as a natural transformation. -/
abbrev π₂Toπ₃ (E : ConflationClass C) : π₂ E ⟶ π₃ E :=
  Functor.whiskerLeft (ι E) ShortComplex.π₂Toπ₃

/-- The composite of the natural transformations `π₁Toπ₂ E` and `π₂Toπ₃ E` between the
component functors is zero. -/
@[reassoc (attr := simp)]
theorem π₁Toπ₂_comp_π₂Toπ₃ (E : ConflationClass C) : π₁Toπ₂ E ≫ π₂Toπ₃ E = 0 := by
  rw [← Functor.whiskerLeft_comp, ShortComplex.π₁Toπ₂_comp_π₂Toπ₃]
  ext S
  simp

/-- The first arrow of a conflation is a monomorphism. -/
instance mono_f (S : E.ConflationCategory) : Mono S.obj.f :=
  (E.isKernelCokernelPair S.obj S.property).mono_f

/-- The second arrow of a conflation is an epimorphism. -/
instance epi_g (S : E.ConflationCategory) : Epi S.obj.g :=
  (E.isKernelCokernelPair S.obj S.property).epi_g

/-- Construct a morphism of conflations from three maps making the two squares commute. -/
def homMk {S T : E.ConflationCategory} (τ₁ : S.obj.X₁ ⟶ T.obj.X₁)
    (τ₂ : S.obj.X₂ ⟶ T.obj.X₂) (τ₃ : S.obj.X₃ ⟶ T.obj.X₃)
    (comm₁₂ : τ₁ ≫ T.obj.f = S.obj.f ≫ τ₂ := by cat_disch)
    (comm₂₃ : τ₂ ≫ T.obj.g = S.obj.g ≫ τ₃ := by cat_disch) : S ⟶ T :=
  ObjectProperty.homMk (ShortComplex.homMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃)

@[simp]
theorem homMk_hom_τ₁ {S T : E.ConflationCategory} (τ₁ : S.obj.X₁ ⟶ T.obj.X₁)
    (τ₂ : S.obj.X₂ ⟶ T.obj.X₂) (τ₃ : S.obj.X₃ ⟶ T.obj.X₃)
    (comm₁₂ : τ₁ ≫ T.obj.f = S.obj.f ≫ τ₂ := by cat_disch)
    (comm₂₃ : τ₂ ≫ T.obj.g = S.obj.g ≫ τ₃ := by cat_disch) :
    (homMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃).hom.τ₁ = τ₁ := (rfl)

@[simp]
theorem homMk_hom_τ₂ {S T : E.ConflationCategory} (τ₁ : S.obj.X₁ ⟶ T.obj.X₁)
    (τ₂ : S.obj.X₂ ⟶ T.obj.X₂) (τ₃ : S.obj.X₃ ⟶ T.obj.X₃)
    (comm₁₂ : τ₁ ≫ T.obj.f = S.obj.f ≫ τ₂ := by cat_disch)
    (comm₂₃ : τ₂ ≫ T.obj.g = S.obj.g ≫ τ₃ := by cat_disch) :
    (homMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃).hom.τ₂ = τ₂ := (rfl)

@[simp]
theorem homMk_hom_τ₃ {S T : E.ConflationCategory} (τ₁ : S.obj.X₁ ⟶ T.obj.X₁)
    (τ₂ : S.obj.X₂ ⟶ T.obj.X₂) (τ₃ : S.obj.X₃ ⟶ T.obj.X₃)
    (comm₁₂ : τ₁ ≫ T.obj.f = S.obj.f ≫ τ₂ := by cat_disch)
    (comm₂₃ : τ₂ ≫ T.obj.g = S.obj.g ≫ τ₃ := by cat_disch) :
    (homMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃).hom.τ₃ = τ₃ := (rfl)

/-- Construct an isomorphism of conflations from compatible isomorphisms of the three terms. -/
def isoMk {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃)
    (comm₁₂ : e₁.hom ≫ T.obj.f = S.obj.f ≫ e₂.hom := by cat_disch)
    (comm₂₃ : e₂.hom ≫ T.obj.g = S.obj.g ≫ e₃.hom := by cat_disch) : S ≅ T :=
  ObjectProperty.isoMk (fun S : ShortComplex C ↦ E.Conflation S)
    (ShortComplex.isoMk e₁ e₂ e₃ comm₁₂ comm₂₃)

@[simp]
theorem isoMk_hom_hom_τ₁ {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃)
    (comm₁₂ : e₁.hom ≫ T.obj.f = S.obj.f ≫ e₂.hom := by cat_disch)
    (comm₂₃ : e₂.hom ≫ T.obj.g = S.obj.g ≫ e₃.hom := by cat_disch) :
    (isoMk e₁ e₂ e₃ comm₁₂ comm₂₃).hom.hom.τ₁ = e₁.hom := (rfl)

@[simp]
theorem isoMk_hom_hom_τ₂ {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃)
    (comm₁₂ : e₁.hom ≫ T.obj.f = S.obj.f ≫ e₂.hom := by cat_disch)
    (comm₂₃ : e₂.hom ≫ T.obj.g = S.obj.g ≫ e₃.hom := by cat_disch) :
    (isoMk e₁ e₂ e₃ comm₁₂ comm₂₃).hom.hom.τ₂ = e₂.hom := (rfl)

@[simp]
theorem isoMk_hom_hom_τ₃ {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃)
    (comm₁₂ : e₁.hom ≫ T.obj.f = S.obj.f ≫ e₂.hom := by cat_disch)
    (comm₂₃ : e₂.hom ≫ T.obj.g = S.obj.g ≫ e₃.hom := by cat_disch) :
    (isoMk e₁ e₂ e₃ comm₁₂ comm₂₃).hom.hom.τ₃ = e₃.hom := (rfl)

@[simp]
theorem isoMk_inv_hom_τ₁ {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃)
    (comm₁₂ : e₁.hom ≫ T.obj.f = S.obj.f ≫ e₂.hom := by cat_disch)
    (comm₂₃ : e₂.hom ≫ T.obj.g = S.obj.g ≫ e₃.hom := by cat_disch) :
    (isoMk e₁ e₂ e₃ comm₁₂ comm₂₃).inv.hom.τ₁ = e₁.inv := (rfl)

@[simp]
theorem isoMk_inv_hom_τ₂ {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃)
    (comm₁₂ : e₁.hom ≫ T.obj.f = S.obj.f ≫ e₂.hom := by cat_disch)
    (comm₂₃ : e₂.hom ≫ T.obj.g = S.obj.g ≫ e₃.hom := by cat_disch) :
    (isoMk e₁ e₂ e₃ comm₁₂ comm₂₃).inv.hom.τ₂ = e₂.inv := (rfl)

@[simp]
theorem isoMk_inv_hom_τ₃ {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃)
    (comm₁₂ : e₁.hom ≫ T.obj.f = S.obj.f ≫ e₂.hom := by cat_disch)
    (comm₂₃ : e₂.hom ≫ T.obj.g = S.obj.g ≫ e₃.hom := by cat_disch) :
    (isoMk e₁ e₂ e₃ comm₁₂ comm₂₃).inv.hom.τ₃ = e₃.inv := (rfl)

/-- A morphism of conflations is an isomorphism exactly when its three components are
isomorphisms. -/
theorem isIso_iff {S T : E.ConflationCategory} (a : S ⟶ T) :
    IsIso a ↔ IsIso a.hom.τ₁ ∧ IsIso a.hom.τ₂ ∧ IsIso a.hom.τ₃ := by
  rw [← ObjectProperty.isIso_hom_iff]
  exact ShortComplex.isIso_iff a.hom

section Opposite

/-- Taking opposites gives an equivalence from the opposite of the category of conflations to the
category of conflations of the opposite conflation class. -/
noncomputable def opEquivalence (E : ConflationClass C) :
    E.ConflationCategoryᵒᵖ ≌ E.op.ConflationCategory :=
  (ObjectProperty.opEquivalence E.Conflation).symm.trans
    ((ShortComplex.opEquiv C).congrFullSubcategory E.op_conflation_inverseImage)

/-- The underlying short complex of the opposite of a conflation is `S.unop.obj.op`: its arrows
are `S.unop.obj.g.op` and `S.unop.obj.f.op`, so its outer terms are exchanged. -/
@[simp]
theorem opEquivalence_functor_obj_obj (E : ConflationClass C)
    (S : E.ConflationCategoryᵒᵖ) :
    ((opEquivalence E).functor.obj S).obj = S.unop.obj.op := (rfl)

/-- The underlying short complex obtained by unopposing a conflation reverses the opposite short
complex again, exchanging its outer terms. -/
@[simp]
theorem opEquivalence_inverse_obj_unop_obj (E : ConflationClass C)
    (S : E.op.ConflationCategory) :
    ((opEquivalence E).inverse.obj S).unop.obj = S.obj.unop := (rfl)

/-- On morphisms, taking opposites applies `ShortComplex.opMap`, which reverses direction and sends
`τ₁` to `τ₃.op`. -/
theorem opEquivalence_functor_map_hom_heq (E : ConflationClass C)
    {S T : E.ConflationCategoryᵒᵖ} (a : S ⟶ T) :
    HEq ((opEquivalence E).functor.map a).hom (ShortComplex.opMap a.unop.hom) := HEq.rfl

/-- On the first component, taking opposites reverses direction and sends `τ₁` to `τ₃.op`. -/
@[simp]
theorem opEquivalence_functor_map_hom_τ₁ (E : ConflationClass C)
    {S T : E.ConflationCategoryᵒᵖ} (a : S ⟶ T) :
    ((opEquivalence E).functor.map a).hom.τ₁ =
      eqToHom (congrArg (fun X : ShortComplex Cᵒᵖ ↦ X.X₁) (opEquivalence_functor_obj_obj E S)) ≫
        a.unop.hom.τ₃.op ≫ eqToHom (congrArg (fun X : ShortComplex Cᵒᵖ ↦ X.X₁)
          (opEquivalence_functor_obj_obj E T)).symm :=
  (conj_eqToHom_iff_heq _ _
    (congrArg (fun X : ShortComplex Cᵒᵖ ↦ X.X₁) (opEquivalence_functor_obj_obj E S))
    (congrArg (fun X : ShortComplex Cᵒᵖ ↦ X.X₁) (opEquivalence_functor_obj_obj E T))).2 HEq.rfl

/-- On the middle component, taking opposites sends `τ₂` to `τ₂.op`. -/
@[simp]
theorem opEquivalence_functor_map_hom_τ₂ (E : ConflationClass C)
    {S T : E.ConflationCategoryᵒᵖ} (a : S ⟶ T) :
    ((opEquivalence E).functor.map a).hom.τ₂ =
      eqToHom (congrArg (fun X : ShortComplex Cᵒᵖ ↦ X.X₂) (opEquivalence_functor_obj_obj E S)) ≫
        a.unop.hom.τ₂.op ≫ eqToHom (congrArg (fun X : ShortComplex Cᵒᵖ ↦ X.X₂)
          (opEquivalence_functor_obj_obj E T)).symm :=
  (conj_eqToHom_iff_heq _ _
    (congrArg (fun X : ShortComplex Cᵒᵖ ↦ X.X₂) (opEquivalence_functor_obj_obj E S))
    (congrArg (fun X : ShortComplex Cᵒᵖ ↦ X.X₂) (opEquivalence_functor_obj_obj E T))).2 HEq.rfl

/-- On the third component, taking opposites reverses direction and sends `τ₃` to `τ₁.op`. -/
@[simp]
theorem opEquivalence_functor_map_hom_τ₃ (E : ConflationClass C)
    {S T : E.ConflationCategoryᵒᵖ} (a : S ⟶ T) :
    ((opEquivalence E).functor.map a).hom.τ₃ =
      eqToHom (congrArg (fun X : ShortComplex Cᵒᵖ ↦ X.X₃) (opEquivalence_functor_obj_obj E S)) ≫
        a.unop.hom.τ₁.op ≫ eqToHom (congrArg (fun X : ShortComplex Cᵒᵖ ↦ X.X₃)
          (opEquivalence_functor_obj_obj E T)).symm :=
  (conj_eqToHom_iff_heq _ _
    (congrArg (fun X : ShortComplex Cᵒᵖ ↦ X.X₃) (opEquivalence_functor_obj_obj E S))
    (congrArg (fun X : ShortComplex Cᵒᵖ ↦ X.X₃) (opEquivalence_functor_obj_obj E T))).2 HEq.rfl

/-- On morphisms, unopposing applies `ShortComplex.unopMap`, which reverses direction and sends
`τ₁` to `τ₃.unop`. -/
theorem opEquivalence_inverse_map_unop_hom_heq (E : ConflationClass C)
    {S T : E.op.ConflationCategory} (a : S ⟶ T) :
    HEq ((opEquivalence E).inverse.map a).unop.hom (ShortComplex.unopMap a.hom) := HEq.rfl

/-- On the first component, unopposing reverses direction and sends `τ₁` to `τ₃.unop`. -/
@[simp]
theorem opEquivalence_inverse_map_unop_hom_τ₁ (E : ConflationClass C)
    {S T : E.op.ConflationCategory} (a : S ⟶ T) :
    ((opEquivalence E).inverse.map a).unop.hom.τ₁ =
      eqToHom (congrArg (fun X : ShortComplex C ↦ X.X₁) (opEquivalence_inverse_obj_unop_obj E T)) ≫
        a.hom.τ₃.unop ≫ eqToHom (congrArg (fun X : ShortComplex C ↦ X.X₁)
          (opEquivalence_inverse_obj_unop_obj E S)).symm :=
  (conj_eqToHom_iff_heq _ _
    (congrArg (fun X : ShortComplex C ↦ X.X₁) (opEquivalence_inverse_obj_unop_obj E T))
    (congrArg (fun X : ShortComplex C ↦ X.X₁) (opEquivalence_inverse_obj_unop_obj E S))).2 HEq.rfl

/-- On the middle component, unopposing sends `τ₂` to `τ₂.unop`. -/
@[simp]
theorem opEquivalence_inverse_map_unop_hom_τ₂ (E : ConflationClass C)
    {S T : E.op.ConflationCategory} (a : S ⟶ T) :
    ((opEquivalence E).inverse.map a).unop.hom.τ₂ =
      eqToHom (congrArg (fun X : ShortComplex C ↦ X.X₂) (opEquivalence_inverse_obj_unop_obj E T)) ≫
        a.hom.τ₂.unop ≫ eqToHom (congrArg (fun X : ShortComplex C ↦ X.X₂)
          (opEquivalence_inverse_obj_unop_obj E S)).symm :=
  (conj_eqToHom_iff_heq _ _
    (congrArg (fun X : ShortComplex C ↦ X.X₂) (opEquivalence_inverse_obj_unop_obj E T))
    (congrArg (fun X : ShortComplex C ↦ X.X₂) (opEquivalence_inverse_obj_unop_obj E S))).2 HEq.rfl

/-- On the third component, unopposing reverses direction and sends `τ₃` to `τ₁.unop`. -/
@[simp]
theorem opEquivalence_inverse_map_unop_hom_τ₃ (E : ConflationClass C)
    {S T : E.op.ConflationCategory} (a : S ⟶ T) :
    ((opEquivalence E).inverse.map a).unop.hom.τ₃ =
      eqToHom (congrArg (fun X : ShortComplex C ↦ X.X₃) (opEquivalence_inverse_obj_unop_obj E T)) ≫
        a.hom.τ₁.unop ≫ eqToHom (congrArg (fun X : ShortComplex C ↦ X.X₃)
          (opEquivalence_inverse_obj_unop_obj E S)).symm :=
  (conj_eqToHom_iff_heq _ _
    (congrArg (fun X : ShortComplex C ↦ X.X₃) (opEquivalence_inverse_obj_unop_obj E T))
    (congrArg (fun X : ShortComplex C ↦ X.X₃) (opEquivalence_inverse_obj_unop_obj E S))).2 HEq.rfl

end Opposite

section Functor

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable {E' : ConflationClass D} {F G : Functor C D}

/-- A functor preserving zero morphisms and conflations induces a functor between the corresponding
categories of conflations. -/
def map (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F)) :
    Functor E.ConflationCategory E'.ConflationCategory :=
  ObjectProperty.lift _ (ConflationCategory.ι E ⋙ F.mapShortComplex) fun S ↦ hF S.property

/-- The underlying short complex of a mapped conflation is its componentwise image. -/
@[simp]
theorem map_obj_obj (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (S : E.ConflationCategory) : ((map F hF).obj S).obj = F.mapShortComplex.obj S.obj := by
  rfl

theorem map_obj_obj_X₁ (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (S : E.ConflationCategory) : ((map F hF).obj S).obj.X₁ = F.obj S.obj.X₁ := by
  rfl

theorem map_obj_obj_X₂ (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (S : E.ConflationCategory) : ((map F hF).obj S).obj.X₂ = F.obj S.obj.X₂ := by
  rfl

theorem map_obj_obj_X₃ (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (S : E.ConflationCategory) : ((map F hF).obj S).obj.X₃ = F.obj S.obj.X₃ := by
  rfl

@[simp]
theorem map_obj_obj_f (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (S : E.ConflationCategory) : ((map F hF).obj S).obj.f =
      eqToHom (map_obj_obj_X₁ F hF S) ≫ F.map S.obj.f ≫
        eqToHom (map_obj_obj_X₂ F hF S).symm :=
  (conj_eqToHom_iff_heq _ _ (map_obj_obj_X₁ F hF S) (map_obj_obj_X₂ F hF S)).2 HEq.rfl

@[simp]
theorem map_obj_obj_g (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (S : E.ConflationCategory) : ((map F hF).obj S).obj.g =
      eqToHom (map_obj_obj_X₂ F hF S) ≫ F.map S.obj.g ≫
        eqToHom (map_obj_obj_X₃ F hF S).symm :=
  (conj_eqToHom_iff_heq _ _ (map_obj_obj_X₂ F hF S) (map_obj_obj_X₃ F hF S)).2 HEq.rfl

@[simp]
theorem map_map_hom_τ₁ (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    {S T : E.ConflationCategory} (a : S ⟶ T) :
    ((map F hF).map a).hom.τ₁ = eqToHom (map_obj_obj_X₁ F hF S) ≫
      F.map a.hom.τ₁ ≫ eqToHom (map_obj_obj_X₁ F hF T).symm :=
  (conj_eqToHom_iff_heq _ _ (map_obj_obj_X₁ F hF S) (map_obj_obj_X₁ F hF T)).2 HEq.rfl

@[simp]
theorem map_map_hom_τ₂ (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    {S T : E.ConflationCategory} (a : S ⟶ T) :
    ((map F hF).map a).hom.τ₂ = eqToHom (map_obj_obj_X₂ F hF S) ≫
      F.map a.hom.τ₂ ≫ eqToHom (map_obj_obj_X₂ F hF T).symm :=
  (conj_eqToHom_iff_heq _ _ (map_obj_obj_X₂ F hF S) (map_obj_obj_X₂ F hF T)).2 HEq.rfl

@[simp]
theorem map_map_hom_τ₃ (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    {S T : E.ConflationCategory} (a : S ⟶ T) :
    ((map F hF).map a).hom.τ₃ = eqToHom (map_obj_obj_X₃ F hF S) ≫
      F.map a.hom.τ₃ ≫ eqToHom (map_obj_obj_X₃ F hF T).symm :=
  (conj_eqToHom_iff_heq _ _ (map_obj_obj_X₃ F hF S) (map_obj_obj_X₃ F hF T)).2 HEq.rfl

/-- After forgetting that its objects are conflations, the induced functor is the ordinary
componentwise map on short complexes. -/
def mapCompιIso (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F)) :
    map F hF ⋙ ι E' ≅ ι E ⋙ F.mapShortComplex :=
  ObjectProperty.liftCompιIso _ _ _

/-- The forward component of `mapCompιIso` is the equality transport from the lifted object to
its componentwise image. -/
@[simp]
theorem mapCompιIso_hom_app (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (S : E.ConflationCategory) : (mapCompιIso F hF).hom.app S =
      eqToHom (map_obj_obj F hF S) := by
  rfl

/-- The inverse component of `mapCompιIso` is the reverse equality transport. -/
@[simp]
theorem mapCompιIso_inv_app (F : Functor C D) [F.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (S : E.ConflationCategory) : (mapCompιIso F hF).inv.app S =
      eqToHom (map_obj_obj F hF S).symm := by
  rfl

/-- The functor on conflations induced by the identity functor is naturally isomorphic to the
identity functor. The two functors are definitionally equal. -/
def mapIdIso : map (E := E) (E' := E) (Functor.id C) (fun hS ↦ hS) ≅
    Functor.id E.ConflationCategory := Iso.refl _

/-- The mapped underlying short complex for the identity functor is the original short complex. -/
theorem mapId_obj_obj (S : E.ConflationCategory) :
    ((map (E := E) (E' := E) (Functor.id C) (fun hS ↦ hS)).obj S).obj = S.obj := by
  rfl

/-- The forward component of `mapIdIso` is the equality transport to the original short complex. -/
@[simp]
theorem mapIdIso_hom_app_hom (S : E.ConflationCategory) :
    ((mapIdIso (E := E)).hom.app S).hom =
      eqToHom (mapId_obj_obj S) := by
  rfl

/-- The inverse component of `mapIdIso` is the reverse equality transport. -/
@[simp]
theorem mapIdIso_inv_app_hom (S : E.ConflationCategory) :
    ((mapIdIso (E := E)).inv.app S).hom =
      eqToHom (mapId_obj_obj S).symm := by
  rfl

/-- Mapping conflations by a composite is naturally isomorphic to mapping successively.
The two functors are definitionally equal. -/
def mapCompIso {K : Type*} [Category* K] [Preadditive K]
    {E'' : ConflationClass K} (F : Functor C D) (H : Functor D K)
    [F.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (hH : ∀ {S : ShortComplex D}, E'.Conflation S → E''.Conflation (S.map H)) :
    map (F ⋙ H) (fun hS ↦ hH (hF hS)) ≅ map F hF ⋙ map H hH := Iso.refl _

/-- Mapping an underlying short complex by a composite is definitionally the same as mapping it
successively. -/
theorem mapComp_obj_obj {K : Type*} [Category* K] [Preadditive K]
    {E'' : ConflationClass K} (F : Functor C D) (H : Functor D K)
    [F.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (hH : ∀ {S : ShortComplex D}, E'.Conflation S → E''.Conflation (S.map H))
    (S : E.ConflationCategory) :
    ((map (F ⋙ H) (fun hS ↦ hH (hF hS))).obj S).obj =
      ((map F hF ⋙ map H hH).obj S).obj := by
  rfl

/-- The forward component of `mapCompIso` is the equality transport between the two mapped
short complexes. -/
@[simp]
theorem mapCompIso_hom_app_hom {K : Type*} [Category* K] [Preadditive K]
    {E'' : ConflationClass K} (F : Functor C D) (H : Functor D K)
    [F.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (hH : ∀ {S : ShortComplex D}, E'.Conflation S → E''.Conflation (S.map H))
    (S : E.ConflationCategory) : ((mapCompIso F H hF hH).hom.app S).hom =
      eqToHom (mapComp_obj_obj F H hF hH S) := by
  rfl

/-- The inverse component of `mapCompIso` is the reverse equality transport. -/
@[simp]
theorem mapCompIso_inv_app_hom {K : Type*} [Category* K] [Preadditive K]
    {E'' : ConflationClass K} (F : Functor C D) (H : Functor D K)
    [F.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (hH : ∀ {S : ShortComplex D}, E'.Conflation S → E''.Conflation (S.map H))
    (S : E.ConflationCategory) : ((mapCompIso F H hF hH).inv.app S).hom =
      eqToHom (mapComp_obj_obj F H hF hH S).symm := by
  rfl

/-- A natural isomorphism between functors preserving conflations induces a natural isomorphism
between their functors on conflations. -/
def mapNatIso (F G : Functor C D) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (hG : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map G))
    (e : F ≅ G) : map F hF ≅ map G hG :=
  NatIso.ofComponents (fun S ↦ ObjectProperty.isoMk _ (S.obj.mapNatIso e)) (by
    intro S T a
    apply ObjectProperty.hom_ext
    apply ShortComplex.hom_ext
    all_goals exact e.hom.naturality _)

@[simp]
theorem mapNatIso_hom_app_hom_τ₁ (F G : Functor C D)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (hG : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map G))
    (e : F ≅ G) (S : E.ConflationCategory) :
    ((mapNatIso F G hF hG e).hom.app S).hom.τ₁ =
      eqToHom (map_obj_obj_X₁ F hF S) ≫ e.hom.app S.obj.X₁ ≫
        eqToHom (map_obj_obj_X₁ G hG S).symm :=
  (conj_eqToHom_iff_heq _ _ (map_obj_obj_X₁ F hF S) (map_obj_obj_X₁ G hG S)).2 HEq.rfl

@[simp]
theorem mapNatIso_hom_app_hom_τ₂ (F G : Functor C D)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (hG : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map G))
    (e : F ≅ G) (S : E.ConflationCategory) :
    ((mapNatIso F G hF hG e).hom.app S).hom.τ₂ =
      eqToHom (map_obj_obj_X₂ F hF S) ≫ e.hom.app S.obj.X₂ ≫
        eqToHom (map_obj_obj_X₂ G hG S).symm :=
  (conj_eqToHom_iff_heq _ _ (map_obj_obj_X₂ F hF S) (map_obj_obj_X₂ G hG S)).2 HEq.rfl

@[simp]
theorem mapNatIso_hom_app_hom_τ₃ (F G : Functor C D)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (hG : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map G))
    (e : F ≅ G) (S : E.ConflationCategory) :
    ((mapNatIso F G hF hG e).hom.app S).hom.τ₃ =
      eqToHom (map_obj_obj_X₃ F hF S) ≫ e.hom.app S.obj.X₃ ≫
        eqToHom (map_obj_obj_X₃ G hG S).symm :=
  (conj_eqToHom_iff_heq _ _ (map_obj_obj_X₃ F hF S) (map_obj_obj_X₃ G hG S)).2 HEq.rfl

@[simp]
theorem mapNatIso_inv_app_hom_τ₁ (F G : Functor C D)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (hG : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map G))
    (e : F ≅ G) (S : E.ConflationCategory) :
    ((mapNatIso F G hF hG e).inv.app S).hom.τ₁ =
      eqToHom (map_obj_obj_X₁ G hG S) ≫ e.inv.app S.obj.X₁ ≫
        eqToHom (map_obj_obj_X₁ F hF S).symm :=
  (conj_eqToHom_iff_heq _ _ (map_obj_obj_X₁ G hG S) (map_obj_obj_X₁ F hF S)).2 HEq.rfl

@[simp]
theorem mapNatIso_inv_app_hom_τ₂ (F G : Functor C D)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (hG : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map G))
    (e : F ≅ G) (S : E.ConflationCategory) :
    ((mapNatIso F G hF hG e).inv.app S).hom.τ₂ =
      eqToHom (map_obj_obj_X₂ G hG S) ≫ e.inv.app S.obj.X₂ ≫
        eqToHom (map_obj_obj_X₂ F hF S).symm :=
  (conj_eqToHom_iff_heq _ _ (map_obj_obj_X₂ G hG S) (map_obj_obj_X₂ F hF S)).2 HEq.rfl

@[simp]
theorem mapNatIso_inv_app_hom_τ₃ (F G : Functor C D)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (hF : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map F))
    (hG : ∀ {S : ShortComplex C}, E.Conflation S → E'.Conflation (S.map G))
    (e : F ≅ G) (S : E.ConflationCategory) :
    ((mapNatIso F G hF hG e).inv.app S).hom.τ₃ =
      eqToHom (map_obj_obj_X₃ G hG S) ≫ e.inv.app S.obj.X₃ ≫
        eqToHom (map_obj_obj_X₃ F hF S).symm :=
  (conj_eqToHom_iff_heq _ _ (map_obj_obj_X₃ G hG S) (map_obj_obj_X₃ F hF S)).2 HEq.rfl

end Functor

end ConflationCategory

end ConflationClass

namespace ExactStructure

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

/-- The category of conflations of an exact structure. -/
abbrev ConflationCategory (E : ExactStructure C) :=
  E.toConflationClass.ConflationCategory

namespace ConflationCategory

variable {E : ExactStructure C}

section Functor

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]
variable {E' : ExactStructure D} {F G : Functor C D}

/-- A conflation-exact functor induces a functor between the corresponding categories of
conflations. -/
abbrev map [F.Additive] (hF : E.IsConflationExact E' F) :
    Functor E.ConflationCategory E'.ConflationCategory :=
  ConflationClass.ConflationCategory.map F hF.map_conflation

/-- After forgetting that its objects are conflations, the induced functor is the ordinary
componentwise map on short complexes. -/
abbrev mapCompιIso [F.Additive] (hF : E.IsConflationExact E' F) :
    map hF ⋙ ConflationClass.ConflationCategory.ι E'.toConflationClass ≅
      ConflationClass.ConflationCategory.ι E.toConflationClass ⋙ F.mapShortComplex :=
  ConflationClass.ConflationCategory.mapCompιIso F hF.map_conflation

/-- The functor on conflations induced by the identity functor is naturally isomorphic to the
identity functor. The two functors are definitionally equal. -/
abbrev mapIdIso : map (ExactStructure.IsConflationExact.id (E := E)) ≅
    Functor.id E.ConflationCategory :=
  ConflationClass.ConflationCategory.mapIdIso

/-- Mapping conflations by a composite is naturally isomorphic to mapping successively.
The two functors are definitionally equal. -/
abbrev mapCompIso {K : Type*} [Category* K] [Preadditive K] [HasZeroObject K]
    [HasBinaryBiproducts K] {E'' : ExactStructure K} {H : D ⥤ K} [F.Additive] [H.Additive]
    (hF : E.IsConflationExact E' F) (hH : E'.IsConflationExact E'' H)
    : map (hF.comp hH) ≅ map hF ⋙ map hH :=
  ConflationClass.ConflationCategory.mapCompIso F H hF.map_conflation hH.map_conflation

/-- A natural isomorphism between conflation-exact functors induces a natural isomorphism between
their functors on conflations. -/
abbrev mapNatIso [F.Additive] [G.Additive] (hF : E.IsConflationExact E' F)
    (hG : E.IsConflationExact E' G) (e : F ≅ G) : map hF ≅ map hG :=
  ConflationClass.ConflationCategory.mapNatIso F G hF.map_conflation hG.map_conflation e

end Functor

end ConflationCategory

end ExactStructure

end TauCeti
