/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Functor
public import TauCeti.CategoryTheory.Exact.Opposite

/-!
# The category of conflations

For a fixed exact structure `E`, a conflation is not merely a proposition about a short complex:
conflations and commutative diagrams between them form a category. This file realizes that
category as the full subcategory of `ShortComplex C` on the distinguished kernel--cokernel pairs.
Consequently, a morphism of conflations is exactly a three-by-three commutative diagram, and an
isomorphism of conflations is exactly such a diagram whose three vertical maps are isomorphisms.

The construction deliberately reuses Mathlib's category of short complexes. In particular,
composition, identities, the preadditive structure, component functors, and the componentwise
criterion for isomorphisms are inherited rather than duplicated.

Conflation-exact functors induce functors between conflation categories. Naturally isomorphic
conflation-exact functors induce naturally isomorphic functors, and passage to the opposite exact
structure gives the expected contravariant functors on conflations.

## Main definitions and results

* `TauCeti.ExactStructure.ConflationCategory`: the full subcategory of distinguished short
  complexes.
* `TauCeti.ExactStructure.ConflationCategory.homMk` and `.isoMk`: constructors for maps and
  isomorphisms of conflations from their three components.
* `TauCeti.ExactStructure.ConflationCategory.isIso_iff`: a map of conflations is an isomorphism
  exactly when all three components are isomorphisms.
* `TauCeti.ExactStructure.ConflationCategory.map`: the functor induced by a conflation-exact
  functor.
* `TauCeti.ExactStructure.ConflationCategory.mapIso`: natural-isomorphism invariance of the
  induced functor.
* `TauCeti.ExactStructure.ConflationCategory.opFunctor` and `.unopFunctor`: the contravariant
  functors supplied by the opposite exact structure.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Sections 2 and 5.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace ExactStructure

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

/-- The category of conflations of an exact structure `E`. Its objects are distinguished short
complexes, and its morphisms are arbitrary morphisms of the underlying short complexes. -/
abbrev ConflationCategory (E : ExactStructure C) :=
  ObjectProperty.FullSubcategory (fun S : ShortComplex C ↦ E.Conflation S)

namespace ConflationCategory

variable {E : ExactStructure C}

/-- Construct an object of the conflation category from a distinguished short complex. -/
def mk (S : ShortComplex C) (hS : E.Conflation S) : E.ConflationCategory := ⟨S, hS⟩

@[simp]
theorem mk_obj (S : ShortComplex C) (hS : E.Conflation S) : (mk S hS).obj = S := (rfl)

/-- The fully faithful inclusion of the category of conflations into the category of short
complexes. -/
abbrev ι (E : ExactStructure C) : E.ConflationCategory ⥤ ShortComplex C :=
  ObjectProperty.ι (fun S : ShortComplex C ↦ E.Conflation S)

/-- The left-object functor on the category of conflations. -/
abbrev π₁ (E : ExactStructure C) : E.ConflationCategory ⥤ C :=
  ι E ⋙ ShortComplex.π₁

/-- The middle-object functor on the category of conflations. -/
abbrev π₂ (E : ExactStructure C) : E.ConflationCategory ⥤ C :=
  ι E ⋙ ShortComplex.π₂

/-- The right-object functor on the category of conflations. -/
abbrev π₃ (E : ExactStructure C) : E.ConflationCategory ⥤ C :=
  ι E ⋙ ShortComplex.π₃

/-- The first arrow of every conflation, as a natural transformation. -/
def f (E : ExactStructure C) : π₁ E ⟶ π₂ E where
  app S := S.obj.f
  naturality := fun {S T} φ ↦ by
    -- Unwrap the induced-category morphism to use the first square of the short-complex map.
    change φ.hom.τ₁ ≫ T.obj.f = S.obj.f ≫ φ.hom.τ₂
    exact φ.hom.comm₁₂

@[simp]
theorem f_app (E : ExactStructure C) (S : E.ConflationCategory) : (f E).app S = S.obj.f :=
  (rfl)

/-- The second arrow of every conflation, as a natural transformation. -/
def g (E : ExactStructure C) : π₂ E ⟶ π₃ E where
  app S := S.obj.g
  naturality := fun {S T} φ ↦ by
    -- Unwrap the induced-category morphism to use the second square of the short-complex map.
    change φ.hom.τ₂ ≫ T.obj.g = S.obj.g ≫ φ.hom.τ₃
    exact φ.hom.comm₂₃

@[simp]
theorem g_app (E : ExactStructure C) (S : E.ConflationCategory) : (g E).app S = S.obj.g :=
  (rfl)

/-- The two natural transformations carried by the universal conflation compose to zero. -/
@[reassoc (attr := simp)]
theorem f_comp_g (E : ExactStructure C) : f E ≫ g E = 0 := by
  ext S
  -- Evaluation of the natural transformations leaves the underlying short-complex equation.
  change S.obj.f ≫ S.obj.g = 0
  exact S.obj.zero

/-- A conflation is, in particular, a kernel--cokernel pair. -/
theorem isKernelCokernelPair (S : E.ConflationCategory) : IsKernelCokernelPair S.obj :=
  E.isKernelCokernelPair S.obj S.property

/-- The first arrow of a conflation is an inflation. -/
theorem isInflation_f (S : E.ConflationCategory) : E.IsInflation S.obj.f :=
  E.isInflation_f S.property

/-- The second arrow of a conflation is a deflation. -/
theorem isDeflation_g (S : E.ConflationCategory) : E.IsDeflation S.obj.g :=
  E.isDeflation_g S.property

/-- The first arrow of a conflation is a monomorphism. -/
instance mono_f (S : E.ConflationCategory) : Mono S.obj.f :=
  S.isKernelCokernelPair.mono_f

/-- The second arrow of a conflation is an epimorphism. -/
instance epi_g (S : E.ConflationCategory) : Epi S.obj.g :=
  S.isKernelCokernelPair.epi_g

/-- Construct a morphism of conflations from three maps making the two squares commute. -/
def homMk {S T : E.ConflationCategory} (τ₁ : S.obj.X₁ ⟶ T.obj.X₁)
    (τ₂ : S.obj.X₂ ⟶ T.obj.X₂) (τ₃ : S.obj.X₃ ⟶ T.obj.X₃)
    (comm₁₂ : τ₁ ≫ T.obj.f = S.obj.f ≫ τ₂ := by cat_disch)
    (comm₂₃ : τ₂ ≫ T.obj.g = S.obj.g ≫ τ₃ := by cat_disch) : S ⟶ T :=
  ObjectProperty.homMk (ShortComplex.homMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃)

@[simp]
theorem homMk_hom_τ₁ {S T : E.ConflationCategory} (τ₁ : S.obj.X₁ ⟶ T.obj.X₁)
    (τ₂ : S.obj.X₂ ⟶ T.obj.X₂) (τ₃ : S.obj.X₃ ⟶ T.obj.X₃) (comm₁₂) (comm₂₃) :
    (homMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃).hom.τ₁ = τ₁ := (rfl)

@[simp]
theorem homMk_hom_τ₂ {S T : E.ConflationCategory} (τ₁ : S.obj.X₁ ⟶ T.obj.X₁)
    (τ₂ : S.obj.X₂ ⟶ T.obj.X₂) (τ₃ : S.obj.X₃ ⟶ T.obj.X₃) (comm₁₂) (comm₂₃) :
    (homMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃).hom.τ₂ = τ₂ := (rfl)

@[simp]
theorem homMk_hom_τ₃ {S T : E.ConflationCategory} (τ₁ : S.obj.X₁ ⟶ T.obj.X₁)
    (τ₂ : S.obj.X₂ ⟶ T.obj.X₂) (τ₃ : S.obj.X₃ ⟶ T.obj.X₃) (comm₁₂) (comm₂₃) :
    (homMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃).hom.τ₃ = τ₃ := (rfl)

/-- Two morphisms of conflations are equal when their three components are equal. -/
@[ext]
theorem hom_ext {S T : E.ConflationCategory} (a b : S ⟶ T)
    (h₁ : a.hom.τ₁ = b.hom.τ₁) (h₂ : a.hom.τ₂ = b.hom.τ₂)
    (h₃ : a.hom.τ₃ = b.hom.τ₃) : a = b := by
  apply ObjectProperty.hom_ext
  exact ShortComplex.hom_ext _ _ h₁ h₂ h₃

/-- Construct an isomorphism of conflations from compatible isomorphisms of the three terms. -/
def isoMk {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃)
    (comm₁₂ : e₁.hom ≫ T.obj.f = S.obj.f ≫ e₂.hom := by cat_disch)
    (comm₂₃ : e₂.hom ≫ T.obj.g = S.obj.g ≫ e₃.hom := by cat_disch) : S ≅ T :=
  ObjectProperty.isoMk (fun S : ShortComplex C ↦ E.Conflation S)
    (ShortComplex.isoMk e₁ e₂ e₃ comm₁₂ comm₂₃)

@[simp]
theorem isoMk_hom_hom_τ₁ {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃) (comm₁₂) (comm₂₃) :
    (isoMk e₁ e₂ e₃ comm₁₂ comm₂₃).hom.hom.τ₁ = e₁.hom := (rfl)

@[simp]
theorem isoMk_hom_hom_τ₂ {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃) (comm₁₂) (comm₂₃) :
    (isoMk e₁ e₂ e₃ comm₁₂ comm₂₃).hom.hom.τ₂ = e₂.hom := (rfl)

@[simp]
theorem isoMk_hom_hom_τ₃ {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃) (comm₁₂) (comm₂₃) :
    (isoMk e₁ e₂ e₃ comm₁₂ comm₂₃).hom.hom.τ₃ = e₃.hom := (rfl)

@[simp]
theorem isoMk_inv_hom_τ₁ {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃) (comm₁₂) (comm₂₃) :
    (isoMk e₁ e₂ e₃ comm₁₂ comm₂₃).inv.hom.τ₁ = e₁.inv := (rfl)

@[simp]
theorem isoMk_inv_hom_τ₂ {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃) (comm₁₂) (comm₂₃) :
    (isoMk e₁ e₂ e₃ comm₁₂ comm₂₃).inv.hom.τ₂ = e₂.inv := (rfl)

@[simp]
theorem isoMk_inv_hom_τ₃ {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃) (comm₁₂) (comm₂₃) :
    (isoMk e₁ e₂ e₃ comm₁₂ comm₂₃).inv.hom.τ₃ = e₃.inv := (rfl)

/-- A morphism of conflations is an isomorphism exactly when its three components are
isomorphisms. -/
theorem isIso_iff {S T : E.ConflationCategory} (a : S ⟶ T) :
    IsIso a ↔ IsIso a.hom.τ₁ ∧ IsIso a.hom.τ₂ ∧ IsIso a.hom.τ₃ := by
  rw [← ObjectProperty.isIso_hom_iff]
  exact ShortComplex.isIso_iff a.hom

section Functor

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]
variable {E' : ExactStructure D} {F G : C ⥤ D}

/-- A conflation-exact functor induces a functor between the corresponding categories of
conflations. -/
def map [F.Additive] (hF : E.IsConflationExact E' F) :
    E.ConflationCategory ⥤ E'.ConflationCategory where
  obj S := mk (S.obj.map F) (hF.map_conflation S.property)
  map a := ObjectProperty.homMk (F.mapShortComplex.map a.hom)

@[simp]
theorem map_obj_obj [F.Additive] (hF : E.IsConflationExact E' F)
    (S : E.ConflationCategory) : ((map hF).obj S).obj = S.obj.map F := (rfl)

/-- After forgetting that its objects are conflations, the induced functor is the ordinary
componentwise map on short complexes. -/
def mapCompιIso [F.Additive] (hF : E.IsConflationExact E' F) :
    map hF ⋙ ι E' ≅ ι E ⋙ F.mapShortComplex :=
  Iso.refl _

/-- The functor on conflations induced by the identity functor is naturally isomorphic to the
identity. -/
def mapIdIso : map (ExactStructure.IsConflationExact.id (E := E)) ≅
    Functor.id E.ConflationCategory :=
  NatIso.ofComponents (fun S ↦
    ObjectProperty.isoMk (fun T : ShortComplex C ↦ E.Conflation T) (Iso.refl S.obj))
    (by
      intro S T a
      apply ObjectProperty.hom_ext
      apply ShortComplex.hom_ext
      -- The two functors agree componentwise after forgetting the conflation proofs.
      · change (Functor.id C).map a.hom.τ₁ ≫ 𝟙 _ = 𝟙 _ ≫ a.hom.τ₁
        simp
      · change (Functor.id C).map a.hom.τ₂ ≫ 𝟙 _ = 𝟙 _ ≫ a.hom.τ₂
        simp
      · change (Functor.id C).map a.hom.τ₃ ≫ 𝟙 _ = 𝟙 _ ≫ a.hom.τ₃
        simp)

/-- Mapping conflations by a composite is naturally isomorphic to mapping successively. -/
def mapCompIso {K : Type*} [Category* K] [Preadditive K] [HasZeroObject K]
    [HasBinaryBiproducts K] {E'' : ExactStructure K} {H : D ⥤ K} [F.Additive] [H.Additive]
    (hF : E.IsConflationExact E' F) (hH : E'.IsConflationExact E'' H) :
    map (hF.comp hH) ≅ map hF ⋙ map hH :=
  NatIso.ofComponents (fun S ↦
    ObjectProperty.isoMk (fun T : ShortComplex K ↦ E''.Conflation T)
      (Iso.refl ((S.obj.map F).map H)))
    (by
      intro S T a
      apply ObjectProperty.hom_ext
      apply ShortComplex.hom_ext
      -- The two functors agree componentwise after forgetting the conflation proofs.
      · change (F ⋙ H).map a.hom.τ₁ ≫ 𝟙 _ = 𝟙 _ ≫ H.map (F.map a.hom.τ₁)
        simp
      · change (F ⋙ H).map a.hom.τ₂ ≫ 𝟙 _ = 𝟙 _ ≫ H.map (F.map a.hom.τ₂)
        simp
      · change (F ⋙ H).map a.hom.τ₃ ≫ 𝟙 _ = 𝟙 _ ≫ H.map (F.map a.hom.τ₃)
        simp)

/-- A natural isomorphism between conflation-exact functors induces a natural isomorphism between
their functors on conflations. -/
def mapIso [F.Additive] [G.Additive] (hF : E.IsConflationExact E' F)
    (hG : E.IsConflationExact E' G) (e : F ≅ G) : map hF ≅ map hG :=
  NatIso.ofComponents (fun S ↦
    ObjectProperty.isoMk (fun T : ShortComplex D ↦ E'.Conflation T) (S.obj.mapNatIso e))
    (by
      intro S T a
      apply ObjectProperty.hom_ext
      apply ShortComplex.hom_ext
      -- Naturality in each term is exactly naturality of the original functor isomorphism.
      · change F.map a.hom.τ₁ ≫ e.hom.app T.obj.X₁ =
          e.hom.app S.obj.X₁ ≫ G.map a.hom.τ₁
        exact e.hom.naturality a.hom.τ₁
      · change F.map a.hom.τ₂ ≫ e.hom.app T.obj.X₂ =
          e.hom.app S.obj.X₂ ≫ G.map a.hom.τ₂
        exact e.hom.naturality a.hom.τ₂
      · change F.map a.hom.τ₃ ≫ e.hom.app T.obj.X₃ =
          e.hom.app S.obj.X₃ ≫ G.map a.hom.τ₃
        exact e.hom.naturality a.hom.τ₃)

end Functor

section Opposite

/-- Taking opposites sends a conflation contravariantly to a conflation in the opposite exact
structure. -/
noncomputable def opFunctor (E : ExactStructure C) :
    E.ConflationCategoryᵒᵖ ⥤ E.op.ConflationCategory where
  obj S := mk S.unop.obj.op ((E.op_conflation_op_iff S.unop.obj).mpr S.unop.property)
  map a := ObjectProperty.homMk (ShortComplex.opMap a.unop.hom)

@[simp]
theorem opFunctor_obj_obj (E : ExactStructure C) (S : E.ConflationCategoryᵒᵖ) :
    ((opFunctor E).obj S).obj = S.unop.obj.op := (rfl)

/-- Forgetting the conflation proof after taking opposites recovers Mathlib's opposite functor on
short complexes. -/
noncomputable def opFunctorCompιIso (E : ExactStructure C) :
    opFunctor E ⋙ ι E.op ≅ (ι E).op ⋙ ShortComplex.opFunctor C :=
  Iso.refl _

/-- Un-oppositing sends a conflation in the opposite exact structure contravariantly back to the
original conflation category. -/
noncomputable def unopFunctor (E : ExactStructure C) :
    E.op.ConflationCategory ⥤ E.ConflationCategoryᵒᵖ where
  obj S := Opposite.op (mk S.obj.unop ((E.op_conflation S.obj).mp S.property))
  map a := (ObjectProperty.homMk (ShortComplex.unopMap a.hom)).op

@[simp]
theorem unopFunctor_obj_unop_obj (E : ExactStructure C) (S : E.op.ConflationCategory) :
    ((unopFunctor E).obj S).unop.obj = S.obj.unop := (rfl)

/-- Forgetting the conflation proof after un-oppositing recovers Mathlib's un-opposite functor on
short complexes. -/
noncomputable def unopFunctorCompιOpIso (E : ExactStructure C) :
    unopFunctor E ⋙ (ι E).op ≅ ι E.op ⋙ ShortComplex.unopFunctor C :=
  Iso.refl _

end Opposite

end ConflationCategory

end ExactStructure

end TauCeti
