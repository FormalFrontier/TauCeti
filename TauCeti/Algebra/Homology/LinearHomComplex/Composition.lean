/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.Monoidal
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.CategoryTheory.Monoidal.Closed.Colimits

/-!
# Composition of cochains as a morphism of `R`-linear Hom complexes

Composition of cochains is `R`-bilinear and satisfies the Leibniz rule

`δ (z₁.comp z₂) = z₁.comp (δ z₂) + (-1)^{|z₂|} • (δ z₁).comp z₂`

(Mathlib's `CochainComplex.HomComplex.δ_comp`; `Cochain.comp` is written in diagrammatic order, so
`z₁ : Cochain F G n₁` comes first and `z₂ : Cochain G K n₂` second).  Together these say exactly
that composition is a *closed degree-zero* map of `R`-linear Hom complexes, that is, a morphism

`linearHomComplex R G K ⊗ linearHomComplex R F G ⟶ linearHomComplex R F K`

in `CochainComplex (ModuleCat R) ℤ`.  The order of the two tensor factors is forced by the Koszul
sign rule: a morphism `φ` out of a tensor product of complexes is a chain map exactly when
`d (φ (x ⊗ y)) = φ (d x ⊗ y) + (-1)^{|x|} φ (x ⊗ d y)`, so the sign is carried by the term whose
differential hits the *second* factor.  In `δ_comp` the sign is carried by `(δ z₁).comp z₂`, the
term differentiating `z₁`; hence `z₁` must be the second tensor factor and `z₂` the first.  This
is Keller's `m₂ (g, f) = g ∘ f` convention.

Mathlib's `CategoryTheory.EnrichedCategory` instead asks for
`Hom(X, Y) ⊗ Hom(Y, Z) ⟶ Hom(X, Z)`; converting between the two orders is exactly the braiding of
`CochainComplex (ModuleCat R) ℤ`, which carries the Koszul sign `x ⊗ y ↦ (-1)^{|x||y|} y ⊗ x` and
is not yet available, so the enrichment itself is left to a later file.

The monoidal structure used here is Mathlib's `HomologicalComplex.monoidalCategory` at
`ComplexShape.up ℤ`; nothing is re-totalized.  Its hypotheses are discharged by the
colimit-preservation instances of `TauCeti/CategoryTheory/Monoidal/Closed/Colimits.lean`.  Note
that `ModuleCat.{v} R` is monoidal only for `R : Type v`, so this file, unlike
`TauCeti/Algebra/Homology/LinearHomComplex/Basic.lean`, ties the ring to the morphism universe
of `C`.

## Main definitions

* `TauCeti.linearHomComplexComp`: composition, as a morphism of `R`-linear Hom complexes out of
  the tensor product.
* `TauCeti.linearHomComplexUnit`: the identity cochain, as a morphism from the tensor unit.

## Main results

* `TauCeti.ι_linearHomComplexComp`: composition sends the pure tensor `z₂ ⊗ₜ z₁` in bidegree
  `(p, q)` to `z₁.comp z₂`.
* `TauCeti.whiskerLeft_linearHomComplexComp` and `TauCeti.whiskerRight_linearHomComplexComp`:
  composition is natural in the source and in the target cochain complex.
* `TauCeti.linearHomComplexUnit_f_zero`: the unit is the identity cochain in degree zero.

This advances `TauCetiRoadmap/DGAInfinity/README.md`, Layer 0, item "signed graded multilinear and
tensor-coalgebra infrastructure", specifically "construct the `k`-linear Hom complex, its signed
differential ..., closed composition map, and the enrichment".  No formalization is vendored: the
Leibniz rule `δ_comp` and the totalized monoidal structure are Mathlib's.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory Limits MonoidalCategory CochainComplex.HomComplex

namespace TauCeti

universe v u

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  (F G K : CochainComplex C ℤ)

/-- Composition of a degree-`p` cochain from `G` to `K` with a degree-`q` cochain from `F` to `G`,
as a map out of the tensor product of the two cochain modules.  This is the bidegree-`(p, q)`
component of `TauCeti.linearHomComplexComp`. -/
@[expose]
noncomputable def cochainCompTensor (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    (linearHomComplex R G K).X p ⊗ (linearHomComplex R F G).X q ⟶
      (linearHomComplex R F K).X j :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun (z₂ : Cochain G K p) (z₁ : Cochain F G q) => z₁.comp z₂ (by dsimp at h; omega))
    (fun _ _ _ => Cochain.comp_add _ _ _ _)
    (fun _ _ _ => Cochain.comp_smul _ _ _ _)
    (fun _ _ _ => Cochain.add_comp _ _ _ _)
    (fun _ _ _ => Cochain.smul_comp _ _ _ _)

@[simp]
lemma cochainCompTensor_tmul (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j)
    (z₂ : Cochain G K p) (z₁ : Cochain F G q) :
    ModuleCat.Hom.hom (cochainCompTensor R F G K p q j h) (z₂ ⊗ₜ z₁) =
      z₁.comp z₂ (by dsimp at h; omega) :=
  rfl

/-- **Composition of cochains is a closed degree-zero map.**  It assembles into a morphism of
cochain complexes of `R`-modules out of the tensor product; the differential of a composite is
computed by the Leibniz rule, which is precisely the condition for this to be a chain map. -/
@[expose]
noncomputable def linearHomComplexComp :
    linearHomComplex R G K ⊗ linearHomComplex R F G ⟶ linearHomComplex R F K where
  f j := HomologicalComplex.mapBifunctorDesc (cochainCompTensor R F G K · · j ·)
  comm' j j' hjj' := by
    replace hjj' : j + 1 = j' := hjj'
    subst hjj'
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    replace h : p + q = j := h
    have hd : (linearHomComplex R G K ⊗ linearHomComplex R F G).d j (j + 1) =
        HomologicalComplex.mapBifunctor.D₁ (linearHomComplex R G K) (linearHomComplex R F G)
            (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) j (j + 1) +
          HomologicalComplex.mapBifunctor.D₂ (linearHomComplex R G K) (linearHomComplex R F G)
            (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) j (j + 1) := rfl
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc, hd,
      Preadditive.add_comp, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q (j + 1) (by dsimp; omega),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
        (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) (j + 1) (by dsimp; omega),
      Linear.units_smul_comp, Linear.units_smul_comp, Category.assoc, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc]
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro z₂ z₁
    simp only [curriedTensor_obj_obj, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ComplexShape.ε₁_def, curriedTensor_map_app, one_smul, ComplexShape.ε₂_def,
      ComplexShape.ε_up_ℤ, curriedTensor_obj_map, ModuleCat.hom_add, ModuleCat.hom_smul,
      LinearMap.add_apply, ModuleCat.MonoidalCategory.whiskerRight_apply, LinearMap.smul_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply]
    exact δ_comp z₁ z₂ (by omega) (q + 1) (p + 1) (j + 1) rfl rfl rfl

lemma linearHomComplexComp_f (j : ℤ) :
    (linearHomComplexComp R F G K).f j =
      HomologicalComplex.mapBifunctorDesc (cochainCompTensor R F G K · · j ·) :=
  rfl

@[reassoc (attr := simp)]
lemma ι_linearHomComplexComp (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    HomologicalComplex.ιMapBifunctor (linearHomComplex R G K) (linearHomComplex R F G)
        (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) p q j h ≫
      (linearHomComplexComp R F G K).f j = cochainCompTensor R F G K p q j h := by
  rw [linearHomComplexComp_f]
  apply HomologicalComplex.ι_mapBifunctorDesc

/-- The identity cochain of `F`, as a morphism from the tensor unit to the `R`-linear Hom complex
of `F` with itself.  It is a chain map because `Cochain.ofHom (𝟙 F)` is a cocycle. -/
@[expose]
noncomputable def linearHomComplexUnit :
    𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ linearHomComplex R F F :=
  HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R (Cochain F F 0) (Cochain.ofHom (𝟙 F))))
    (fun i _ => ModuleCat.hom_ext (LinearMap.ext fun r => by
      have h : δ 0 i (r • Cochain.ofHom (𝟙 F)) = 0 := by rw [δ_smul, δ_ofHom, smul_zero]
      exact h))

lemma linearHomComplexUnit_f_zero :
    (linearHomComplexUnit R F).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R (Cochain F F 0) (Cochain.ofHom (𝟙 F))) :=
  HomologicalComplex.mkHomFromSingle_f _ _


section Naturality

variable {F G K}
variable {F₁ F₂ K₁ K₂ : CochainComplex C ℤ}

/-- Composition is natural in the source: composing after precomposition by `φ` is the same as
precomposing the composite by `φ`.  This is associativity of `Cochain.comp` with a degree-zero
cochain in the outermost slot. -/
lemma whiskerLeft_linearHomComplexComp (φ : F₁ ⟶ F₂) (G K : CochainComplex C ℤ) :
    linearHomComplex R G K ◁ linearHomComplexPrecomp R φ G ≫ linearHomComplexComp R F₁ G K =
      linearHomComplexComp R F₂ G K ≫ linearHomComplexPrecomp R φ K := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hw : (linearHomComplex R G K ◁ linearHomComplexPrecomp R φ G).f j =
      (HomologicalComplex.mapBifunctorMap (𝟙 (linearHomComplex R G K))
        (linearHomComplexPrecomp R φ G) (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℤ)).f j := rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc, hw,
    HomologicalComplex.ι_mapBifunctorMap, Category.assoc, Category.assoc,
    ι_linearHomComplexComp, ι_linearHomComplexComp_assoc]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z₂ z₁
  simp only [curriedTensor_obj_obj, HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    NatTrans.id_app, curriedTensor_obj_map, Category.id_comp, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply]
  have h' : p + q = j := h
  have hassoc : ((Cochain.ofHom φ).comp z₁ (zero_add q)).comp z₂ (by omega) =
      (Cochain.ofHom φ).comp (z₁.comp z₂ (by omega)) (zero_add j) :=
    Cochain.comp_assoc _ _ _ (zero_add q) (by omega) (by omega)
  exact hassoc

/-- Composition is natural in the target: composing after postcomposition by `ψ` is the same as
postcomposing the composite by `ψ`.  This is associativity of `Cochain.comp` with a degree-zero
cochain in the innermost slot. -/
lemma whiskerRight_linearHomComplexComp (ψ : K₁ ⟶ K₂) (F G : CochainComplex C ℤ) :
    linearHomComplexPostcomp R G ψ ▷ linearHomComplex R F G ≫ linearHomComplexComp R F G K₂ =
      linearHomComplexComp R F G K₁ ≫ linearHomComplexPostcomp R F ψ := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hw : (linearHomComplexPostcomp R G ψ ▷ linearHomComplex R F G).f j =
      (HomologicalComplex.mapBifunctorMap (linearHomComplexPostcomp R G ψ)
        (𝟙 (linearHomComplex R F G)) (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℤ)).f j := rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc, hw,
    HomologicalComplex.ι_mapBifunctorMap, Category.assoc, Category.assoc,
    ι_linearHomComplexComp, ι_linearHomComplexComp_assoc]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z₂ z₁
  simp only [curriedTensor_obj_obj, HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    curriedTensor_map_app, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  have h' : p + q = j := h
  have hassoc : (z₁.comp z₂ (by omega)).comp (Cochain.ofHom ψ) (add_zero j) =
      z₁.comp (z₂.comp (Cochain.ofHom ψ) (add_zero p)) (by omega) :=
    Cochain.comp_assoc _ _ _ (by omega) (add_zero p) (by omega)
  exact hassoc.symm

end Naturality

end TauCeti
