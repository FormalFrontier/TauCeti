/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Functor
public import TauCeti.CategoryTheory.Exact.Opposite
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.Opposite

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
* `TauCeti.ExactStructure.ConflationCategory.map`: the functor induced by a conflation-exact
  functor.
* `TauCeti.ExactStructure.ConflationCategory.mapNatIso`: natural-isomorphism invariance of the
  induced functor.
* `TauCeti.ConflationClass.ConflationCategory.opEquivalence`: the equivalence supplied by the
  opposite conflation class.

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

/-- The inverse image of opposite conflations under the short-complex opposite equivalence is
the opposite of the original conflation property. -/
theorem op_conflation_inverseImage (E : ConflationClass C) :
    E.op.Conflation.inverseImage (ShortComplex.opEquiv C).functor = E.Conflation.op :=
  by
    ext S
    rw [ObjectProperty.prop_inverseImage_iff, ObjectProperty.op_iff]
    dsimp only [ShortComplex.opEquiv, ShortComplex.opFunctor]
    exact E.op_conflation_op_iff S.unop

/-- Taking opposites gives an equivalence from the opposite of the category of conflations to the
category of conflations of the opposite conflation class. -/
noncomputable def opEquivalence (E : ConflationClass C) :
    E.ConflationCategoryᵒᵖ ≌ E.op.ConflationCategory :=
  (ObjectProperty.opEquivalence E.Conflation).symm.trans
    ((ShortComplex.opEquiv C).congrFullSubcategory (op_conflation_inverseImage E))

/-- The underlying short complex of the opposite of a conflation is its termwise opposite. -/
@[simp]
theorem opEquivalence_functor_obj_obj (E : ConflationClass C)
    (S : E.ConflationCategoryᵒᵖ) :
    ((opEquivalence E).functor.obj S).obj = S.unop.obj.op := (rfl)

/-- The underlying short complex obtained by unopposing a conflation is its termwise unopposite. -/
@[simp]
theorem opEquivalence_inverse_obj_unop_obj (E : ConflationClass C)
    (S : E.op.ConflationCategory) :
    ((opEquivalence E).inverse.obj S).unop.obj = S.obj.unop := (rfl)

/-- `opEquivalence` is the canonical composite of the opposite-property equivalence and the
short-complex opposite equivalence restricted to conflations. -/
theorem opEquivalence_eq (E : ConflationClass C) : opEquivalence E =
    (ObjectProperty.opEquivalence E.Conflation).symm.trans
      ((ShortComplex.opEquiv C).congrFullSubcategory (op_conflation_inverseImage E)) := (rfl)

end Opposite

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
variable {E' : ExactStructure D} {F G : C ⥤ D}

/-- A conflation-exact functor induces a functor between the corresponding categories of
conflations. -/
def map [F.Additive] (hF : E.IsConflationExact E' F) :
    E.ConflationCategory ⥤ E'.ConflationCategory :=
  ObjectProperty.lift _ (ConflationClass.ConflationCategory.ι E.toConflationClass ⋙
    F.mapShortComplex) fun S ↦ hF.map_conflation S.property

@[simp]
theorem map_obj_obj_X₁ [F.Additive] (hF : E.IsConflationExact E' F)
    (S : E.ConflationCategory) : ((map hF).obj S).obj.X₁ = F.obj S.obj.X₁ := (rfl)

@[simp]
theorem map_obj_obj_X₂ [F.Additive] (hF : E.IsConflationExact E' F)
    (S : E.ConflationCategory) : ((map hF).obj S).obj.X₂ = F.obj S.obj.X₂ := (rfl)

@[simp]
theorem map_obj_obj_X₃ [F.Additive] (hF : E.IsConflationExact E' F)
    (S : E.ConflationCategory) : ((map hF).obj S).obj.X₃ = F.obj S.obj.X₃ := (rfl)

@[simp]
theorem map_obj_obj_f [F.Additive] (hF : E.IsConflationExact E' F)
    (S : E.ConflationCategory) : HEq ((map hF).obj S).obj.f (F.map S.obj.f) := by
  exact heq_of_eq rfl

@[simp]
theorem map_obj_obj_g [F.Additive] (hF : E.IsConflationExact E' F)
    (S : E.ConflationCategory) : HEq ((map hF).obj S).obj.g (F.map S.obj.g) := by
  exact heq_of_eq rfl

@[simp]
theorem map_map_hom_τ₁ [F.Additive] (hF : E.IsConflationExact E' F)
    {S T : E.ConflationCategory} (a : S ⟶ T) :
    HEq ((map hF).map a).hom.τ₁ (F.map a.hom.τ₁) := by
  exact heq_of_eq rfl

@[simp]
theorem map_map_hom_τ₂ [F.Additive] (hF : E.IsConflationExact E' F)
    {S T : E.ConflationCategory} (a : S ⟶ T) :
    HEq ((map hF).map a).hom.τ₂ (F.map a.hom.τ₂) := by
  exact heq_of_eq rfl

@[simp]
theorem map_map_hom_τ₃ [F.Additive] (hF : E.IsConflationExact E' F)
    {S T : E.ConflationCategory} (a : S ⟶ T) :
    HEq ((map hF).map a).hom.τ₃ (F.map a.hom.τ₃) := by
  exact heq_of_eq rfl

/-- After forgetting that its objects are conflations, the induced functor is the ordinary
componentwise map on short complexes. -/
def mapCompιIso [F.Additive] (hF : E.IsConflationExact E' F) :
    map hF ⋙ ConflationClass.ConflationCategory.ι E'.toConflationClass ≅
      ConflationClass.ConflationCategory.ι E.toConflationClass ⋙ F.mapShortComplex :=
  ObjectProperty.liftCompιIso _ _ _

/-- The forward component of `mapCompιIso` is heterogeneously equal to the identity of the
ordinary componentwise image. -/
@[simp]
theorem mapCompιIso_hom_app [F.Additive] (hF : E.IsConflationExact E' F)
    (S : E.ConflationCategory) : HEq ((mapCompιIso hF).hom.app S)
      (𝟙 ((ConflationClass.ConflationCategory.ι E.toConflationClass ⋙
        F.mapShortComplex).obj S)) := by
  exact heq_of_eq rfl

/-- The inverse component of `mapCompιIso` is heterogeneously equal to the identity of the
ordinary componentwise image. -/
@[simp]
theorem mapCompιIso_inv_app [F.Additive] (hF : E.IsConflationExact E' F)
    (S : E.ConflationCategory) : HEq ((mapCompιIso hF).inv.app S)
      (𝟙 ((ConflationClass.ConflationCategory.ι E.toConflationClass ⋙
        F.mapShortComplex).obj S)) := by
  exact heq_of_eq rfl

/-- Mapping conflations by the identity functor gives the identity functor. -/
theorem map_id : map (ExactStructure.IsConflationExact.id (E := E)) =
    Functor.id E.ConflationCategory := (rfl)

/-- The functor on conflations induced by the identity functor is naturally isomorphic to the
identity functor. -/
def mapIdIso : map (ExactStructure.IsConflationExact.id (E := E)) ≅
    Functor.id E.ConflationCategory :=
  eqToIso map_id

/-- `mapIdIso` is the canonical isomorphism associated to `map_id`. -/
@[simp]
theorem mapIdIso_eq_eqToIso : mapIdIso (E := E) = eqToIso map_id := (rfl)

/-- Mapping conflations by a composite is the same functor as mapping successively. -/
theorem map_comp {K : Type*} [Category* K] [Preadditive K] [HasZeroObject K]
    [HasBinaryBiproducts K] {E'' : ExactStructure K} {H : D ⥤ K} [F.Additive] [H.Additive]
    (hF : E.IsConflationExact E' F) (hH : E'.IsConflationExact E'' H) :
    map (hF.comp hH) = map hF ⋙ map hH := (rfl)

/-- Mapping conflations by a composite is naturally isomorphic to mapping successively. -/
def mapCompIso {K : Type*} [Category* K] [Preadditive K] [HasZeroObject K]
    [HasBinaryBiproducts K] {E'' : ExactStructure K} {H : D ⥤ K} [F.Additive] [H.Additive]
    (hF : E.IsConflationExact E' F) (hH : E'.IsConflationExact E'' H)
    : map (hF.comp hH) ≅ map hF ⋙ map hH :=
  eqToIso (map_comp hF hH)

/-- `mapCompIso` is the canonical isomorphism associated to `map_comp`. -/
@[simp]
theorem mapCompIso_eq_eqToIso {K : Type*} [Category* K] [Preadditive K] [HasZeroObject K]
    [HasBinaryBiproducts K] {E'' : ExactStructure K} {H : D ⥤ K} [F.Additive] [H.Additive]
    (hF : E.IsConflationExact E' F) (hH : E'.IsConflationExact E'' H) :
    mapCompIso hF hH = eqToIso (map_comp hF hH) := (rfl)

/-- A natural isomorphism between conflation-exact functors induces a natural isomorphism between
their functors on conflations. -/
def mapNatIso [F.Additive] [G.Additive] (hF : E.IsConflationExact E' F)
    (hG : E.IsConflationExact E' G) (e : F ≅ G) : map hF ≅ map hG :=
  NatIso.ofComponents (fun S ↦
    ObjectProperty.isoMk (fun T : ShortComplex D ↦ E'.Conflation T) (S.obj.mapNatIso e))
    (by
      intro S T a
      apply ObjectProperty.hom_ext
      apply ShortComplex.hom_ext
      all_goals exact e.hom.naturality _)

@[simp]
theorem mapNatIso_hom_app_hom_τ₁ [F.Additive] [G.Additive]
    (hF : E.IsConflationExact E' F) (hG : E.IsConflationExact E' G) (e : F ≅ G)
    (S : E.ConflationCategory) : HEq ((mapNatIso hF hG e).hom.app S).hom.τ₁
      (e.hom.app S.obj.X₁) := by
  exact heq_of_eq rfl

@[simp]
theorem mapNatIso_hom_app_hom_τ₂ [F.Additive] [G.Additive]
    (hF : E.IsConflationExact E' F) (hG : E.IsConflationExact E' G) (e : F ≅ G)
    (S : E.ConflationCategory) : HEq ((mapNatIso hF hG e).hom.app S).hom.τ₂
      (e.hom.app S.obj.X₂) := by
  exact heq_of_eq rfl

@[simp]
theorem mapNatIso_hom_app_hom_τ₃ [F.Additive] [G.Additive]
    (hF : E.IsConflationExact E' F) (hG : E.IsConflationExact E' G) (e : F ≅ G)
    (S : E.ConflationCategory) : HEq ((mapNatIso hF hG e).hom.app S).hom.τ₃
      (e.hom.app S.obj.X₃) := by
  exact heq_of_eq rfl

@[simp]
theorem mapNatIso_inv_app_hom_τ₁ [F.Additive] [G.Additive]
    (hF : E.IsConflationExact E' F) (hG : E.IsConflationExact E' G) (e : F ≅ G)
    (S : E.ConflationCategory) : HEq ((mapNatIso hF hG e).inv.app S).hom.τ₁
      (e.inv.app S.obj.X₁) := by
  exact heq_of_eq rfl

@[simp]
theorem mapNatIso_inv_app_hom_τ₂ [F.Additive] [G.Additive]
    (hF : E.IsConflationExact E' F) (hG : E.IsConflationExact E' G) (e : F ≅ G)
    (S : E.ConflationCategory) : HEq ((mapNatIso hF hG e).inv.app S).hom.τ₂
      (e.inv.app S.obj.X₂) := by
  exact heq_of_eq rfl

@[simp]
theorem mapNatIso_inv_app_hom_τ₃ [F.Additive] [G.Additive]
    (hF : E.IsConflationExact E' F) (hG : E.IsConflationExact E' G) (e : F ≅ G)
    (S : E.ConflationCategory) : HEq ((mapNatIso hF hG e).inv.app S).hom.τ₃
      (e.inv.app S.obj.X₃) := by
  exact heq_of_eq rfl

end Functor

end ConflationCategory

end ExactStructure

end TauCeti
