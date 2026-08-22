/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# The `R`-linear Hom complex of two cochain complexes

Let `C` be an `R`-linear preadditive category and let `F` and `G` be cochain complexes in `C`.
Mathlib's `CochainComplex.HomComplex.Cochain F G n` is the `R`-module of degree-`n` cochains from
`F` to `G`, and `CochainComplex.HomComplex.δ` is the signed differential
`δ z = d_G ∘ z + (-1)^{n+1} z ∘ d_F`, already known to be `R`-linear and square-zero.  Mathlib
assembles this data into `CochainComplex.HomComplex F G`, a cochain complex of *abelian groups*,
which forgets the `R`-module structure.  This file assembles the same data into a cochain complex
of `R`-modules.

That complex is the object a differential graded category is enriched in: a DG category over `R`
is a category enriched in `CochainComplex (ModuleCat R) ℤ`, and `CochainComplex C ℤ` is the
motivating example.  The `AddCommGrpCat`-valued complex retains only the underlying
`ℤ`-linearity, whereas a DG category over `R` requires the `R`-module structure on its Hom
complexes.

## Main definitions

* `TauCeti.linearHomComplex R F G`: the `R`-linear Hom complex, a cochain complex of `R`-modules
  whose degree-`n` term is `Cochain F G n` and whose differential is `δ`.
* `TauCeti.linearHomComplexPrecomp` and `TauCeti.linearHomComplexPostcomp`: precomposition and
  postcomposition by a morphism of cochain complexes, as morphisms of `R`-linear Hom complexes.
* `TauCeti.linearHomComplexFunctor`: the two variances bundled into a bifunctor, contravariant in
  the source and covariant in the target.

## Main results

* `TauCeti.forget₂LinearHomComplexIso`: forgetting the `R`-module structure degreewise recovers
  Mathlib's `CochainComplex.HomComplex`.

This advances `TauCetiRoadmap/DGAInfinity/README.md`, Layer 0, item "signed graded multilinear and
tensor-coalgebra infrastructure", specifically its request to "construct the `k`-linear Hom
complex, its signed differential `d(f) = d_Y f - (-1)^{|f|} f d_X`, closed composition map, and
the enrichment, and compare its underlying additive-group complex with Mathlib's
`CochainComplex.HomComplex`".  No formalization is vendored: the cochain modules, the differential
`δ`, its `R`-linearity and the Leibniz rule for composition are all Mathlib's.

## Implementation notes

`linearHomComplex` and `linearHomComplexFunctor` carry `@[expose]`, while every operation built
from them is sealed and used only through its characteristic lemmas.  The two exposures are
forced by the statements of the API, not by its proofs: `(linearHomComplex R F G).X n` is the
type at which every application lemma below is stated, and
`((linearHomComplexFunctor R).obj F).obj G` is the pair of types between which the object and
map equations of the bifunctor are stated.  Sealing either makes those statements ill-typed
(`Type mismatch ... not unfolded because their definition is not exposed`), so no proof syntax
recovers them.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* Joël Riou's Mathlib construction `CochainComplex.HomComplex` and its cochain/`δ` API in
  `Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean`.  The construction here adapts it
  by retaining `ModuleCat R` in place of `AddCommGrpCat`, with the same sign convention.
-/

public section

open CategoryTheory Limits CochainComplex.HomComplex

namespace TauCeti

universe v u w

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The `R`-linear Hom complex of two cochain complexes: in degree `n` it is the `R`-module
`CochainComplex.HomComplex.Cochain F G n` of degree-`n` cochains, and its differential is the
signed differential `δ`. -/
@[expose, simps! X]
def linearHomComplex (F G : CochainComplex C ℤ) : CochainComplex (ModuleCat.{v} R) ℤ where
  X n := ModuleCat.of R (Cochain F G n)
  d n m := ModuleCat.ofHom (δ_hom R F G n m)
  shape n m hnm := ModuleCat.hom_ext (LinearMap.ext fun z => δ_shape n m hnm z)
  d_comp_d' n m p _ _ := ModuleCat.hom_ext (LinearMap.ext fun z => δ_δ n m p z)

@[simp]
lemma linearHomComplex_d_apply (F G : CochainComplex C ℤ) (n m : ℤ)
    (z : (linearHomComplex R F G).X n) :
    (linearHomComplex R F G).d n m z =
      (δ n m (z : Cochain F G n) : (linearHomComplex R F G).X m) :=
  rfl

/-- Forgetting the `R`-module structure of the `R`-linear Hom complex recovers Mathlib's
`CochainComplex.HomComplex`. -/
def forget₂LinearHomComplexIso (F G : CochainComplex C ℤ) :
    ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex _).obj
        (linearHomComplex R F G) ≅ CochainComplex.HomComplex F G :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => rfl)

/-- The forward component of the comparison isomorphism is the identity. -/
@[simp]
lemma forget₂LinearHomComplexIso_hom_f (F G : CochainComplex C ℤ) (n : ℤ) :
    (forget₂LinearHomComplexIso R F G).hom.f n = 𝟙 _ := by
  ext z
  rfl

/-- The inverse component of the comparison isomorphism is the identity. -/
@[simp]
lemma forget₂LinearHomComplexIso_inv_f (F G : CochainComplex C ℤ) (n : ℤ) :
    (forget₂LinearHomComplexIso R F G).inv.f n = 𝟙 _ := by
  ext z
  rfl

section Functoriality

variable {F₁ F₂ F₃ G₁ G₂ G₃ : CochainComplex C ℤ}

private def cochainPrecomp (φ : F₁ ⟶ F₂) (G : CochainComplex C ℤ) (n : ℤ) :
    Cochain F₂ G n →ₗ[R] Cochain F₁ G n where
  toFun z := (Cochain.ofHom φ).comp z (zero_add n)
  map_add' z z' := Cochain.comp_add _ z z' (zero_add n)
  map_smul' r z := Cochain.comp_smul _ r z (zero_add n)

private def cochainPostcomp (F : CochainComplex C ℤ) (ψ : G₁ ⟶ G₂) (n : ℤ) :
    Cochain F G₁ n →ₗ[R] Cochain F G₂ n where
  toFun z := z.comp (Cochain.ofHom ψ) (add_zero n)
  map_add' z z' := Cochain.add_comp z z' _ (add_zero n)
  map_smul' r z := Cochain.smul_comp r z _ (add_zero n)

/-- Precomposition by a morphism `φ : F₁ ⟶ F₂` of cochain complexes, as a morphism of `R`-linear
Hom complexes.  It commutes with the differentials because `φ` is a cocycle, so that the second
term of the Leibniz rule for `δ` vanishes. -/
def linearHomComplexPrecomp (φ : F₁ ⟶ F₂) (G : CochainComplex C ℤ) :
    linearHomComplex R F₂ G ⟶ linearHomComplex R F₁ G where
  f n := ModuleCat.ofHom (cochainPrecomp R φ G n)
  comm' _ m _ := ModuleCat.hom_ext (LinearMap.ext fun z => δ_ofHom_comp φ z m)

/-- Postcomposition by a morphism `ψ : G₁ ⟶ G₂` of cochain complexes, as a morphism of `R`-linear
Hom complexes. -/
def linearHomComplexPostcomp (F : CochainComplex C ℤ) (ψ : G₁ ⟶ G₂) :
    linearHomComplex R F G₁ ⟶ linearHomComplex R F G₂ where
  f n := ModuleCat.ofHom (cochainPostcomp R F ψ n)
  comm' _ m _ := ModuleCat.hom_ext (LinearMap.ext fun z => δ_comp_ofHom z ψ m)

variable {R}

@[simp]
lemma linearHomComplexPrecomp_f_apply (φ : F₁ ⟶ F₂) (G : CochainComplex C ℤ) (n : ℤ)
    (z : (linearHomComplex R F₂ G).X n) :
    (linearHomComplexPrecomp R φ G).f n z =
      ((Cochain.ofHom φ).comp (z : Cochain F₂ G n) (zero_add n) :
        (linearHomComplex R F₁ G).X n) :=
  (rfl)

@[simp]
lemma linearHomComplexPostcomp_f_apply (F : CochainComplex C ℤ) (ψ : G₁ ⟶ G₂) (n : ℤ)
    (z : (linearHomComplex R F G₁).X n) :
    (linearHomComplexPostcomp R F ψ).f n z =
      ((z : Cochain F G₁ n).comp (Cochain.ofHom ψ) (add_zero n) :
        (linearHomComplex R F G₂).X n) :=
  (rfl)

variable (R)

@[simp]
lemma linearHomComplexPrecomp_id (F G : CochainComplex C ℤ) :
    linearHomComplexPrecomp R (𝟙 F) G = 𝟙 _ := by
  ext n (z : (linearHomComplex R F G).X n)
  exact Cochain.id_comp z

@[simp]
lemma linearHomComplexPrecomp_comp (φ : F₁ ⟶ F₂) (φ' : F₂ ⟶ F₃) (G : CochainComplex C ℤ) :
    linearHomComplexPrecomp R (φ ≫ φ') G =
      linearHomComplexPrecomp R φ' G ≫ linearHomComplexPrecomp R φ G := by
  ext n (z : (linearHomComplex R F₃ G).X n)
  simp only [linearHomComplexPrecomp_f_apply, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.coe_comp]
  rw [Cochain.ofHom_comp]
  exact Cochain.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega)

@[simp]
lemma linearHomComplexPostcomp_id (F G : CochainComplex C ℤ) :
    linearHomComplexPostcomp R F (𝟙 G) = 𝟙 _ := by
  ext n (z : (linearHomComplex R F G).X n)
  exact Cochain.comp_id z

@[simp]
lemma linearHomComplexPostcomp_comp (F : CochainComplex C ℤ) (ψ : G₁ ⟶ G₂) (ψ' : G₂ ⟶ G₃) :
    linearHomComplexPostcomp R F (ψ ≫ ψ') =
      linearHomComplexPostcomp R F ψ ≫ linearHomComplexPostcomp R F ψ' := by
  ext n (z : (linearHomComplex R F G₁).X n)
  simp only [linearHomComplexPostcomp_f_apply, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.coe_comp]
  rw [Cochain.ofHom_comp]
  exact (Cochain.comp_assoc _ _ _ (add_zero n) (zero_add 0) (by omega)).symm

/-- Precomposition and postcomposition commute. -/
lemma linearHomComplexPrecomp_postcomp_comm (φ : F₁ ⟶ F₂) (ψ : G₁ ⟶ G₂) :
    linearHomComplexPrecomp R φ G₁ ≫ linearHomComplexPostcomp R F₁ ψ =
      linearHomComplexPostcomp R F₂ ψ ≫ linearHomComplexPrecomp R φ G₂ := by
  ext n (z : (linearHomComplex R F₂ G₁).X n)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact Cochain.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)

/-- The `R`-linear Hom complex as a bifunctor: contravariant in the source cochain complex and
covariant in the target one. -/
@[expose, simps]
def linearHomComplexFunctor :
    (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ where
  obj F :=
    { obj G := linearHomComplex R F.unop G
      map ψ := linearHomComplexPostcomp R F.unop ψ
      map_id G := linearHomComplexPostcomp_id R F.unop G
      map_comp ψ ψ' := linearHomComplexPostcomp_comp R F.unop ψ ψ' }
  map φ :=
    { app G := linearHomComplexPrecomp R φ.unop G
      naturality _ _ ψ := (linearHomComplexPrecomp_postcomp_comm R φ.unop ψ).symm }
  map_id F := by ext G : 2; exact linearHomComplexPrecomp_id R F.unop G
  map_comp φ φ' := by ext G : 2; exact linearHomComplexPrecomp_comp R φ'.unop φ.unop G

end Functoriality

end TauCeti
