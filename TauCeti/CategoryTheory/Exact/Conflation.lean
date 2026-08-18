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
abbrev f (E : ExactStructure C) : π₁ E ⟶ π₂ E :=
  Functor.whiskerLeft (ι E) ShortComplex.π₁Toπ₂

/-- The second arrow of every conflation, as a natural transformation. -/
abbrev g (E : ExactStructure C) : π₂ E ⟶ π₃ E :=
  Functor.whiskerLeft (ι E) ShortComplex.π₂Toπ₃

/-- The two natural transformations carried by the universal conflation compose to zero. -/
@[reassoc (attr := simp)]
theorem f_comp_g (E : ExactStructure C) : f E ≫ g E = 0 := by
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
@[expose, simps!]
def homMk {S T : E.ConflationCategory} (τ₁ : S.obj.X₁ ⟶ T.obj.X₁)
    (τ₂ : S.obj.X₂ ⟶ T.obj.X₂) (τ₃ : S.obj.X₃ ⟶ T.obj.X₃)
    (comm₁₂ : τ₁ ≫ T.obj.f = S.obj.f ≫ τ₂ := by cat_disch)
    (comm₂₃ : τ₂ ≫ T.obj.g = S.obj.g ≫ τ₃ := by cat_disch) : S ⟶ T :=
  ObjectProperty.homMk (ShortComplex.homMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃)

/-- Construct an isomorphism of conflations from compatible isomorphisms of the three terms. -/
@[expose, simps!]
def isoMk {S T : E.ConflationCategory} (e₁ : S.obj.X₁ ≅ T.obj.X₁)
    (e₂ : S.obj.X₂ ≅ T.obj.X₂) (e₃ : S.obj.X₃ ≅ T.obj.X₃)
    (comm₁₂ : e₁.hom ≫ T.obj.f = S.obj.f ≫ e₂.hom := by cat_disch)
    (comm₂₃ : e₂.hom ≫ T.obj.g = S.obj.g ≫ e₃.hom := by cat_disch) : S ≅ T :=
  ObjectProperty.isoMk (fun S : ShortComplex C ↦ E.Conflation S)
    (ShortComplex.isoMk e₁ e₂ e₃ comm₁₂ comm₂₃)

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
    E.ConflationCategory ⥤ E'.ConflationCategory :=
  ObjectProperty.lift _ (ι E ⋙ F.mapShortComplex) fun S ↦ hF.map_conflation S.property

/-- After forgetting that its objects are conflations, the induced functor is the ordinary
componentwise map on short complexes. -/
def mapCompιIso [F.Additive] (hF : E.IsConflationExact E' F) :
    map hF ⋙ ι E' ≅ ι E ⋙ F.mapShortComplex :=
  ObjectProperty.liftCompιIso _ _ _

/-- The functor on conflations induced by the identity functor is naturally isomorphic to the
identity. -/
def mapIdIso : map (ExactStructure.IsConflationExact.id (E := E)) ≅
    Functor.id E.ConflationCategory :=
  Iso.refl _

/-- Mapping conflations by a composite is naturally isomorphic to mapping successively. -/
def mapCompIso {K : Type*} [Category* K] [Preadditive K] [HasZeroObject K]
    [HasBinaryBiproducts K] {E'' : ExactStructure K} {H : D ⥤ K} [F.Additive] [H.Additive]
    (hF : E.IsConflationExact E' F) (hH : E'.IsConflationExact E'' H) :
    map (hF.comp hH) ≅ map hF ⋙ map hH :=
  Iso.refl _

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
    E.ConflationCategoryᵒᵖ ⥤ E.op.ConflationCategory :=
  ObjectProperty.lift _ ((ι E).op ⋙ ShortComplex.opFunctor C)
    fun S ↦ (E.op_conflation_op_iff S.unop.obj).mpr S.unop.property

/-- Forgetting the conflation proof after taking opposites recovers Mathlib's opposite functor on
short complexes. -/
noncomputable def opFunctorCompιIso (E : ExactStructure C) :
    opFunctor E ⋙ ι E.op ≅ (ι E).op ⋙ ShortComplex.opFunctor C :=
  ObjectProperty.liftCompιIso _ _ _

/-- Un-oppositing sends a conflation in the opposite exact structure contravariantly back to the
original conflation category. -/
noncomputable def unopFunctor (E : ExactStructure C) :
    E.op.ConflationCategory ⥤ E.ConflationCategoryᵒᵖ :=
  (ObjectProperty.lift _ (ι E.op ⋙ ShortComplex.unopFunctor C).leftOp
    fun S ↦ (E.op_conflation S.unop.obj).mp S.unop.property).rightOp

/-- Forgetting the conflation proof after un-oppositing recovers Mathlib's un-opposite functor on
short complexes. -/
noncomputable def unopFunctorCompιOpIso (E : ExactStructure C) :
    unopFunctor E ⋙ (ι E).op ≅ ι E.op ⋙ ShortComplex.unopFunctor C :=
  Iso.refl _

end Opposite

end ConflationCategory

end ExactStructure

end TauCeti
