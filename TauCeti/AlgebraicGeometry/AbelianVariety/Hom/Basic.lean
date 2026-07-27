/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Basic

/-!
# Homomorphisms of abelian varieties

This file supplies the morphism part of the basic abelian-variety API. A homomorphism of abelian
varieties over `K` is a morphism over `Spec K` preserving the unit and multiplication of the
underlying group schemes. Such morphisms form the category `AbelianVariety K`, inherited from
Mathlib's category of commutative group objects.

The category morphism type `A ⟶ B` is the type required by the Jacobian's universal property: the
factorization from the Jacobian to another abelian variety must preserve the group law, rather than
being only a morphism of the underlying schemes. The characteristic lemmas expose preservation of
the unit, multiplication, and inverse, as well as the underlying morphism of schemes.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API", and prepares Layer F's unique
"homomorphism of abelian varieties". No external mathematics is vendored; the implementation
reuses Mathlib's `CommGrp` category and its `IsMonHom` API for group objects in a cartesian
monoidal category.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

noncomputable section

/-- Abelian varieties over a fixed field form a category with group-scheme homomorphisms. -/
noncomputable instance : Category (AbelianVariety K) :=
  inferInstanceAs (Category (InducedCategory _ (fun A ↦ CommGrp.mk A.toOver)))

/-- Construct a homomorphism of abelian varieties from a morphism over `Spec K` and proofs that it
preserves the unit and multiplication. -/
def Hom.mk' {A B : AbelianVariety K} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) : A ⟶ B :=
  InducedCategory.homMk (InducedCategory.homMk (Grp.homMk'' f one_f mul_f))

/-- The forgetful functor from abelian varieties to schemes over `Spec K`. -/
@[expose] noncomputable def Hom.toOverFunctor :
    AbelianVariety K ⥤ Over (Spec (.of K)) :=
  inducedFunctor (fun A : AbelianVariety K ↦ CommGrp.mk A.toOver) ⋙
    CommGrp.forget (Over (Spec (.of K)))

/-- The underlying morphism of group schemes over `Spec K`. -/
abbrev Hom.toOverHom {A B : AbelianVariety K} (f : A ⟶ B) : A.toOver ⟶ B.toOver :=
  (Hom.toOverFunctor).map f

/-- `toOverHom` sends the identity homomorphism to the identity over `Spec K`. -/
lemma Hom.toOverHom_id (A : AbelianVariety K) : Hom.toOverHom (𝟙 A) = 𝟙 A.toOver :=
  (Hom.toOverFunctor).map_id A

/-- `toOverHom` sends composition to composition over `Spec K`. -/
@[reassoc]
lemma Hom.toOverHom_comp {A B C : AbelianVariety K} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.toOverHom (f ≫ g) = Hom.toOverHom f ≫ Hom.toOverHom g :=
  (Hom.toOverFunctor).map_comp f g

/-- `toOverHom` is definitionally the iterated underlying-morphism projection through the two
induced categories, `CommGrp`, and `Grp`. -/
private lemma Hom.toOverHom_def {A B : AbelianVariety K} (f : A ⟶ B) :
    Hom.toOverHom f = f.hom.hom.hom.hom :=
  rfl

/-- The underlying morphism of an abelian-variety homomorphism preserves the group-object
structure. -/
instance {A B : AbelianVariety K} (f : A ⟶ B) : IsMonHom (Hom.toOverHom f) :=
  Hom.toOverHom_def f ▸ inferInstance

/-- The underlying morphism over `Spec K` of a homomorphism built by `Hom.mk'` is the supplied
morphism. -/
@[simp]
lemma Hom.toOverHom_mk' {A B : AbelianVariety K} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) :
    Hom.toOverHom (Hom.mk' f one_f mul_f) = f :=
  by
    rw [Hom.toOverHom_def]
    exact Grp.homMk''_hom_hom (A := Grp.mk A.toOver) (B := Grp.mk B.toOver) f one_f mul_f

/-- A homomorphism of abelian varieties preserves the unit section. -/
@[reassoc]
lemma Hom.one_hom {A B : AbelianVariety K} (f : A ⟶ B) :
    η[A.toOver] ≫ Hom.toOverHom f = η[B.toOver] := by
  rw [Hom.toOverHom_def]
  exact IsMonHom.one_hom _

/-- A homomorphism of abelian varieties preserves multiplication. -/
@[reassoc]
lemma Hom.mul_hom {A B : AbelianVariety K} (f : A ⟶ B) :
    μ[A.toOver] ≫ Hom.toOverHom f =
      (Hom.toOverHom f ⊗ₘ Hom.toOverHom f) ≫ μ[B.toOver] := by
  rw [Hom.toOverHom_def]
  exact IsMonHom.mul_hom _

/-- A homomorphism of abelian varieties preserves inverses. -/
@[reassoc]
lemma Hom.inv_hom {A B : AbelianVariety K} (f : A ⟶ B) :
    ι[A.toOver] ≫ Hom.toOverHom f = Hom.toOverHom f ≫ ι[B.toOver] := by
  rw [Hom.toOverHom_def]
  exact GrpObj.inv_hom _

/-- The underlying morphism between the schemes of two abelian varieties. -/
abbrev Hom.toSchemeHom {A B : AbelianVariety K} (f : A ⟶ B) : A.toScheme ⟶ B.toScheme :=
  (Hom.toOverHom f).left

/-- The underlying scheme morphism of a homomorphism built by `Hom.mk'` is the supplied morphism's
left component. -/
@[simp]
lemma Hom.toSchemeHom_mk' {A B : AbelianVariety K} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) :
    Hom.toSchemeHom (Hom.mk' f one_f mul_f) = f.left := by
  exact congrArg Over.Hom.left (Hom.toOverHom_mk' f one_f mul_f)

/-- `toSchemeHom` sends the identity homomorphism to the identity scheme morphism. -/
@[simp]
lemma Hom.toSchemeHom_id (A : AbelianVariety K) :
    Hom.toSchemeHom (𝟙 A) = 𝟙 A.toScheme :=
  congrArg Over.Hom.left (Hom.toOverHom_id A)

/-- `toSchemeHom` sends composition to composition of scheme morphisms. -/
@[simp, reassoc]
lemma Hom.toSchemeHom_comp {A B C : AbelianVariety K} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.toSchemeHom (f ≫ g) = Hom.toSchemeHom f ≫ Hom.toSchemeHom g :=
  congrArg Over.Hom.left (Hom.toOverHom_comp f g)

/-- The underlying scheme morphism of an abelian-variety homomorphism commutes with the structure
morphisms to `Spec K`. -/
-- Not `@[simp]`: `CategoryTheory.Over.w` is already a simp lemma and discharges this goal.
@[reassoc]
lemma Hom.toSchemeHom_comp_hom {A B : AbelianVariety K} (f : A ⟶ B) :
    Hom.toSchemeHom f ≫ B.toOver.hom = A.toOver.hom :=
  (Hom.toOverHom f).w

/-- Two homomorphisms of abelian varieties are equal when their underlying scheme morphisms are
equal. -/
@[ext]
lemma Hom.ext {A B : AbelianVariety K} {f g : A ⟶ B}
    (h : Hom.toSchemeHom f = Hom.toSchemeHom g) : f = g := by
  simp only [Hom.toSchemeHom, Hom.toOverHom_def] at h
  apply InducedCategory.hom_ext
  apply CommGrp.hom_ext
  exact Over.OverMorphism.ext h

/-- Forgetting an abelian-variety homomorphism to its underlying morphism over `Spec K` is
faithful. -/
instance : (Hom.toOverFunctor (K := K)).Faithful where
  map_injective h := Hom.ext (congrArg Over.Hom.left h)

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
