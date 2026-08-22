/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic

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
`ComplexShape.up ℤ`; nothing is re-totalized.  Its colimit-preservation hypotheses are discharged
by Mathlib's instances for a braided monoidal closed category, so
`Mathlib.CategoryTheory.Monoidal.Closed.Braided` has to be imported for the tensor product of
cochain complexes to exist at all.  Note that `ModuleCat.{v} R` is monoidal only for
`R : Type v`, so this file, unlike
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
* `TauCeti.linearHomComplexComp_naturality_middle`: composition is natural in the middle
  cochain complex.
* `TauCeti.linearHomComplexComp_assoc`, `TauCeti.linearHomComplexUnit_comp`, and
  `TauCeti.linearHomComplexComp_unit`: composition is associative and unital.
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
  by
    unfold cochainCompTensor
    exact ModuleCat.MonoidalCategory.tensorLift_tmul _ _ _ _ _ _ _

/- The expansion through `D₁` and `D₂` below is the unavoidable alignment between Mathlib's
totalized tensor differential and its bidegree inclusions.  Keeping it in this summand formula
isolates those implementation details from the chain-map construction. -/
private lemma cochainCompTensor_d (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = j) :
    HomologicalComplex.ιMapBifunctor (linearHomComplex R G K) (linearHomComplex R F G)
          (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) p q j h ≫
        (linearHomComplex R G K ⊗ linearHomComplex R F G).d j (j + 1) ≫
        HomologicalComplex.mapBifunctorDesc (cochainCompTensor R F G K · · (j + 1) ·) =
      cochainCompTensor R F G K p q j h ≫ (linearHomComplex R F K).d j (j + 1) := by
  replace h : p + q = j := h
  -- The differential of a totalized tensor product is the sum `D₁ + D₂` of its two half
  -- differentials by definition of `HomologicalComplex.tensorObj`.
  have hd : (linearHomComplex R G K ⊗ linearHomComplex R F G).d j (j + 1) =
      HomologicalComplex.mapBifunctor.D₁ (linearHomComplex R G K) (linearHomComplex R F G)
          (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) j (j + 1) +
        HomologicalComplex.mapBifunctor.D₂ (linearHomComplex R G K) (linearHomComplex R F G)
          (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) j (j + 1) := rfl
  rw [hd, Preadditive.add_comp, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (ComplexShape.up_mk p (p + 1) rfl) q (j + 1) (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
      (ComplexShape.up_mk q (q + 1) rfl) (j + 1) (by dsimp; omega),
    Linear.units_smul_comp, Linear.units_smul_comp, Category.assoc, Category.assoc,
    HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z₂ z₁
  simp only [curriedTensor_obj_obj, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ComplexShape.ε₁_def, curriedTensor_map_app, one_smul, ComplexShape.ε₂_def,
    ComplexShape.ε_up_ℤ, curriedTensor_obj_map, ModuleCat.hom_add, ModuleCat.hom_smul,
    LinearMap.add_apply, ModuleCat.MonoidalCategory.whiskerRight_apply, LinearMap.smul_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]
  erw [cochainCompTensor_tmul, cochainCompTensor_tmul, cochainCompTensor_tmul,
    linearHomComplex_d_apply, linearHomComplex_d_apply, linearHomComplex_d_apply]
  exact (δ_comp z₁ z₂ (by omega) (q + 1) (p + 1) (j + 1) rfl rfl rfl).symm

/-- **Composition of cochains is a closed degree-zero map.**  It assembles into a morphism of
cochain complexes of `R`-modules out of the tensor product; the differential of a composite is
computed by the Leibniz rule, which is precisely the condition for this to be a chain map. -/
noncomputable def linearHomComplexComp :
    linearHomComplex R G K ⊗ linearHomComplex R F G ⟶ linearHomComplex R F K where
  f j := HomologicalComplex.mapBifunctorDesc (cochainCompTensor R F G K · · j ·)
  comm' j j' hjj' := by
    replace hjj' : j + 1 = j' := hjj'
    subst hjj'
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    exact (cochainCompTensor_d R F G K p q j h).symm

/-- The degree-`j` component of cochain composition is induced by its maps on the bidegree
summands of the totalized tensor product. -/
lemma linearHomComplexComp_f (j : ℤ) :
    (linearHomComplexComp R F G K).f j =
      HomologicalComplex.mapBifunctorDesc (cochainCompTensor R F G K · · j ·) :=
  by simp [linearHomComplexComp]

/-- On the bidegree-`(p, q)` summand, composition sends a pure tensor `z₂ ⊗ₜ z₁` to the
cochain composite `z₁.comp z₂`. -/
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
noncomputable def linearHomComplexUnit :
    𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ linearHomComplex R F F :=
  HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R (Cochain F F 0) (Cochain.ofHom (𝟙 F))))
    (fun i _ => ModuleCat.hom_ext (LinearMap.ext fun r => by
      have h : δ 0 i (r • Cochain.ofHom (𝟙 F)) = 0 := by rw [δ_smul, δ_ofHom, smul_zero]
      exact h))

/-- The degree-zero component of the unit map is the linear map sending a scalar to that scalar
multiple of the identity cochain. -/
lemma linearHomComplexUnit_f_zero :
    (linearHomComplexUnit R F).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R (Cochain F F 0) (Cochain.ofHom (𝟙 F))) :=
  HomologicalComplex.mkHomFromSingle_f _ _

@[simp]
lemma linearHomComplexUnit_f_zero_apply (r : R) :
    ModuleCat.Hom.hom ((linearHomComplexUnit R F).f 0) r =
      r • Cochain.ofHom (𝟙 F) := by
  rw [linearHomComplexUnit_f_zero]
  rfl


section Naturality

variable {F G K}
variable {F₁ F₂ G₁ G₂ K₁ K₂ : CochainComplex C ℤ}

/-- Composition is natural in the source: composing after precomposition by `φ` is the same as
precomposing the composite by `φ`.  This is associativity of `Cochain.comp` with a degree-zero
cochain in the outermost slot. -/
lemma whiskerLeft_linearHomComplexComp (φ : F₁ ⟶ F₂) (G K : CochainComplex C ℤ) :
    linearHomComplex R G K ◁ linearHomComplexPrecomp R φ G ≫ linearHomComplexComp R F₁ G K =
      linearHomComplexComp R F₂ G K ≫ linearHomComplexPrecomp R φ K := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  -- Whiskering is `mapBifunctorMap` by definition of the monoidal structure on
  -- `HomologicalComplex`, for which Mathlib provides no component lemma; this bridge lets the
  -- inclusion formula `ι_mapBifunctorMap` be used below.
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
  erw [linearHomComplexPrecomp_f_apply, cochainCompTensor_tmul,
    cochainCompTensor_tmul, linearHomComplexPrecomp_f_apply]
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
  -- Whiskering as `mapBifunctorMap`, as in `whiskerLeft_linearHomComplexComp` above.
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
    ModuleCat.MonoidalCategory.whiskerRight_apply, ConcreteCategory.id_apply]
  erw [linearHomComplexPostcomp_f_apply, cochainCompTensor_tmul,
    cochainCompTensor_tmul, linearHomComplexPostcomp_f_apply]
  have h' : p + q = j := h
  have hassoc : (z₁.comp z₂ (by omega)).comp (Cochain.ofHom ψ) (add_zero j) =
      z₁.comp (z₂.comp (Cochain.ofHom ψ) (add_zero p)) (by omega) :=
    Cochain.comp_assoc _ _ _ (by omega) (add_zero p) (by omega)
  exact hassoc.symm

/-- Composition is natural in the middle object: precomposition in the first Hom complex agrees
with postcomposition in the second Hom complex. -/
lemma linearHomComplexComp_naturality_middle (ψ : G₁ ⟶ G₂) (F K : CochainComplex C ℤ) :
    linearHomComplexPrecomp R ψ K ▷ linearHomComplex R F G₁ ≫
        linearHomComplexComp R F G₁ K =
      linearHomComplex R G₂ K ◁ linearHomComplexPostcomp R F ψ ≫
        linearHomComplexComp R F G₂ K := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  -- Whiskering as `mapBifunctorMap`, as in `whiskerLeft_linearHomComplexComp` above.
  have hw₁ : (linearHomComplexPrecomp R ψ K ▷ linearHomComplex R F G₁).f j =
      (HomologicalComplex.mapBifunctorMap (linearHomComplexPrecomp R ψ K)
        (𝟙 (linearHomComplex R F G₁)) (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℤ)).f j := rfl
  have hw₂ : (linearHomComplex R G₂ K ◁ linearHomComplexPostcomp R F ψ).f j =
      (HomologicalComplex.mapBifunctorMap (𝟙 (linearHomComplex R G₂ K))
        (linearHomComplexPostcomp R F ψ) (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℤ)).f j := rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc, hw₁,
    HomologicalComplex.ι_mapBifunctorMap, Category.assoc, hw₂,
    HomologicalComplex.ι_mapBifunctorMap_assoc,
    ι_linearHomComplexComp, Category.assoc, ι_linearHomComplexComp]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z₂ z₁
  simp only [curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]
  erw [linearHomComplexPrecomp_f_apply, cochainCompTensor_tmul,
    linearHomComplexPostcomp_f_apply, cochainCompTensor_tmul]
  have h' : p + q = j := h
  exact (Cochain.comp_assoc z₁ (Cochain.ofHom ψ) z₂ (add_zero q) (zero_add p) (by omega)).symm

end Naturality

section CategoryLaws

variable {F G K}
variable (L : CochainComplex C ℤ)

/-- Composition of cochains is associative, with the tensor products identified by the monoidal
associator. -/
lemma linearHomComplexComp_assoc :
    (linearHomComplexComp R G K L ▷ linearHomComplex R F G) ≫
        linearHomComplexComp R F G L =
      (α_ (linearHomComplex R K L) (linearHomComplex R G K)
        (linearHomComplex R F G)).hom ≫
        (linearHomComplex R K L ◁ linearHomComplexComp R F G K) ≫
          linearHomComplexComp R F K L := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  have h' : p + q + r = j := h
  -- Whiskering as `mapBifunctorMap`, as in `whiskerLeft_linearHomComplexComp` above.
  have hw₁ : (linearHomComplexComp R G K L ▷ linearHomComplex R F G).f j =
      (HomologicalComplex.mapBifunctorMap (linearHomComplexComp R G K L)
        (𝟙 (linearHomComplex R F G)) (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℤ)).f j := rfl
  have hw₂ : (linearHomComplex R K L ◁ linearHomComplexComp R F G K).f j =
      (HomologicalComplex.mapBifunctorMap (𝟙 (linearHomComplex R K L))
        (linearHomComplexComp R F G K) (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℤ)).f j := rfl
  -- Likewise the associator's degree-`j` component is `mapBifunctorAssociatorX` by definition.
  have ha : (α_ (linearHomComplex R K L) (linearHomComplex R G K)
      (linearHomComplex R F G)).hom.f j =
      (HomologicalComplex.mapBifunctorAssociatorX
        (curriedAssociatorNatIso (ModuleCat.{v} R)) (linearHomComplex R K L)
        (linearHomComplex R G K) (linearHomComplex R F G) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) j).hom := rfl
  have hLHS :
      HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R))
          (curriedTensor (ModuleCat.{v} R)) (linearHomComplex R K L)
          (linearHomComplex R G K) (linearHomComplex R F G) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) p q r j h ≫
        ((linearHomComplexComp R G K L ▷ linearHomComplex R F G) ≫
          linearHomComplexComp R F G L).f j =
      (cochainCompTensor R G K L p q (p + q) rfl ▷ (linearHomComplex R F G).X r) ≫
        cochainCompTensor R F G L (p + q) r j (by omega) := by
    rw [HomologicalComplex.comp_f, ← Category.assoc, hw₁,
      HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor (ModuleCat.{v} R))
        (curriedTensor (ModuleCat.{v} R)) (linearHomComplex R K L)
        (linearHomComplex R G K) (linearHomComplex R F G) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) p q r (p + q) j rfl (by omega),
      Category.assoc, Category.assoc,
      HomologicalComplex.ι_mapBifunctorMap_assoc,
      ι_linearHomComplexComp]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
      curriedTensor_map_app, Category.id_comp]
    rw [← MonoidalCategory.comp_whiskerRight_assoc, ι_linearHomComplexComp]
  have hRHS :
      HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R))
          (curriedTensor (ModuleCat.{v} R)) (linearHomComplex R K L)
          (linearHomComplex R G K) (linearHomComplex R F G) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) p q r j h ≫
        ((α_ (linearHomComplex R K L) (linearHomComplex R G K)
          (linearHomComplex R F G)).hom ≫
          (linearHomComplex R K L ◁ linearHomComplexComp R F G K) ≫
          linearHomComplexComp R F K L).f j =
      (α_ ((linearHomComplex R K L).X p) ((linearHomComplex R G K).X q)
        ((linearHomComplex R F G).X r)).hom ≫
        ((linearHomComplex R K L).X p ◁ cochainCompTensor R F G K q r (q + r) rfl) ≫
          cochainCompTensor R F K L p (q + r) j (by dsimp; omega) := by
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    rw [ha, HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc]
    dsimp only [bifunctorComp₁₂, bifunctorComp₂₃, bifunctorComp₁₂Obj, bifunctorComp₂₃Obj]
    rw [MonoidalCategory.curriedAssociatorNatIso_hom_app_app_app, hw₂,
      HomologicalComplex.mapBifunctor₂₃.ι_eq (curriedTensor (ModuleCat.{v} R))
        (curriedTensor (ModuleCat.{v} R)) (linearHomComplex R K L)
        (linearHomComplex R G K) (linearHomComplex R F G) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r (q + r) j rfl (by dsimp; omega)]
    apply (cancel_epi (α_ ((linearHomComplex R K L).X p) ((linearHomComplex R G K).X q)
      ((linearHomComplex R F G).X r)).inv).1
    rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
    rw [Category.assoc, HomologicalComplex.ι_mapBifunctorMap_assoc, ι_linearHomComplexComp]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      curriedTensor_obj_map, Category.id_comp]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, ι_linearHomComplexComp]
  rw [hLHS, hRHS]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z₃₂ z₁
  induction z₃₂ using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
  | tmul z₃ z₂ =>
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply]
    erw [cochainCompTensor_tmul, cochainCompTensor_tmul]
    erw [ModuleCat.MonoidalCategory.associator_hom_apply z₃ z₂ z₁]
    erw [ModuleCat.MonoidalCategory.whiskerLeft_apply
        ((linearHomComplex R K L).X p) (cochainCompTensor R F G K q r (q + r) rfl)
        z₃ (z₂ ⊗ₜ z₁),
      cochainCompTensor_tmul R F G K q r (q + r) rfl z₂ z₁,
      cochainCompTensor_tmul R F K L p (q + r) j (by dsimp; omega)
        z₃ (z₁.comp z₂ (by omega))]
    -- The preceding application lemmas leave only the proof arguments certifying the degree
    -- equalities; this alignment states the resulting cochain equation without wrapper casts.
    change z₁.comp (z₂.comp z₃ (by omega)) (by omega) =
      (z₁.comp z₂ (by omega)).comp z₃ (by omega)
    exact (Cochain.comp_assoc (n₁₂ := q + r) (n₂₃ := p + q) (n₁₂₃ := j)
      z₁ z₂ z₃ (by omega) (by omega) (by omega)).symm

/- Mathlib builds the unitors of `HomologicalComplex` from the auxiliary graded-object
isomorphisms `leftUnitor'` and `rightUnitor'`, and states its component formulas
(`leftUnitor'_inv`, `rightUnitor'_inv`) for those; there is no lemma for the components of `λ_`
and `ρ_` themselves.  The two lemmas below bridge that gap once, by unfolding the monoidal
structure of `HomologicalComplex` down to `Hom.isoOfComponents`, so that the unit laws proved
afterwards never mention it.  The final step is the definition of `GradedObject.eval`, whose
action on morphisms is evaluation at a degree. -/
private lemma leftUnitor_inv_f (X : CochainComplex (ModuleCat.{v} R) ℤ) (j : ℤ) :
    (λ_ X).inv.f j = (HomologicalComplex.leftUnitor' X).inv j := by
  dsimp only [MonoidalCategoryStruct.leftUnitor, HomologicalComplex.monoidalCategoryStruct,
    HomologicalComplex.monoidalCategory, HomologicalComplex.leftUnitor, Iso.symm_inv]
  simp only [HomologicalComplex.Hom.isoOfComponents_hom_f, Functor.mapIso_hom, Iso.symm_hom]
  rfl

private lemma rightUnitor_inv_f (X : CochainComplex (ModuleCat.{v} R) ℤ) (j : ℤ) :
    (ρ_ X).inv.f j = (HomologicalComplex.rightUnitor' X).inv j := by
  dsimp only [MonoidalCategoryStruct.rightUnitor, HomologicalComplex.monoidalCategoryStruct,
    HomologicalComplex.monoidalCategory, HomologicalComplex.rightUnitor, Iso.symm_inv]
  simp only [HomologicalComplex.Hom.isoOfComponents_hom_f, Functor.mapIso_hom, Iso.symm_hom]
  rfl

/-- The identity cochain is a left unit for composition. -/
lemma linearHomComplexUnit_comp :
    linearHomComplexUnit R G ▷ linearHomComplex R F G ≫
        linearHomComplexComp R F G G =
      (λ_ (linearHomComplex R F G)).hom := by
  apply (cancel_epi (λ_ (linearHomComplex R F G)).inv).1
  rw [Iso.inv_hom_id]
  ext j z
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, ConcreteCategory.id_apply]
  rw [leftUnitor_inv_f, HomologicalComplex.leftUnitor'_inv]
  -- Whiskering as `mapBifunctorMap`, as in `whiskerLeft_linearHomComplexComp` above.
  have hw : (linearHomComplexUnit R G ▷ linearHomComplex R F G).f j =
      (HomologicalComplex.mapBifunctorMap (linearHomComplexUnit R G)
        (𝟙 (linearHomComplex R F G)) (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℤ)).f j := rfl
  have hι :
      HomologicalComplex.ιMapBifunctor (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))
          (linearHomComplex R F G) (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) 0 j j (zero_add j) ≫
        (linearHomComplexUnit R G ▷ linearHomComplex R F G).f j ≫
          (linearHomComplexComp R F G G).f j =
        (linearHomComplexUnit R G).f 0 ▷ (linearHomComplex R F G).X j ≫
          cochainCompTensor R F G G 0 j j (zero_add j) := by
    rw [hw, HomologicalComplex.ι_mapBifunctorMap_assoc, ι_linearHomComplexComp]
    simp only [HomologicalComplex.id_f, curriedTensor_obj_obj, curriedTensor_map_app,
      curriedTensor_obj_map, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  -- After `leftUnitor'_inv` the goal is an element of the totalized tensor product presented as
  -- a composite of three maps applied to `1`; `hι` below is stated about that composite, so the
  -- goal is restated with the composition made explicit.  Mathlib's `ιTensorObj` and
  -- `ιMapBifunctor` are the same inclusion, which is why no rewrite is available here.
  change ModuleCat.Hom.hom
    (HomologicalComplex.ιMapBifunctor (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))
        (linearHomComplex R F G) (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℤ) 0 j j (zero_add j) ≫
      (linearHomComplexUnit R G ▷ linearHomComplex R F G).f j ≫
        (linearHomComplexComp R F G G).f j)
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{v} R))).inv : _) 1 ⊗ₜ z) = z
  rw [hι]
  have hunit : ((linearHomComplexUnit R G).f 0)
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{v} R))).inv : _) 1) = Cochain.ofHom (𝟙 G) :=
    one_smul R (Cochain.ofHom (𝟙 G))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  erw [ModuleCat.MonoidalCategory.whiskerRight_apply ((linearHomComplexUnit R G).f 0)
    ((linearHomComplex R F G).X j)
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat.{v} R))).inv 1) z]
  rw [hunit]
  erw [cochainCompTensor_tmul]
  exact Cochain.comp_id z

/-- The identity cochain is a right unit for composition. -/
lemma linearHomComplexComp_unit :
    linearHomComplex R F G ◁ linearHomComplexUnit R F ≫
        linearHomComplexComp R F F G =
      (ρ_ (linearHomComplex R F G)).hom := by
  apply (cancel_epi (ρ_ (linearHomComplex R F G)).inv).1
  rw [Iso.inv_hom_id]
  ext j z
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, ConcreteCategory.id_apply]
  rw [rightUnitor_inv_f, HomologicalComplex.rightUnitor'_inv]
  -- Whiskering as `mapBifunctorMap`, as in `whiskerLeft_linearHomComplexComp` above.
  have hw : (linearHomComplex R F G ◁ linearHomComplexUnit R F).f j =
      (HomologicalComplex.mapBifunctorMap (𝟙 (linearHomComplex R F G))
        (linearHomComplexUnit R F) (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℤ)).f j := rfl
  have hι :
      HomologicalComplex.ιMapBifunctor (linearHomComplex R F G)
          (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) j 0 j (add_zero j) ≫
        (linearHomComplex R F G ◁ linearHomComplexUnit R F).f j ≫
          (linearHomComplexComp R F F G).f j =
        (linearHomComplex R F G).X j ◁ (linearHomComplexUnit R F).f 0 ≫
          cochainCompTensor R F F G j 0 j (add_zero j) := by
    rw [hw, HomologicalComplex.ι_mapBifunctorMap_assoc, ι_linearHomComplexComp]
    simp only [HomologicalComplex.id_f, curriedTensor_obj_obj, curriedTensor_map_app,
      curriedTensor_obj_map, MonoidalCategory.id_whiskerRight, Category.id_comp]
  -- As in the left unit law: the goal is restated with the composition made explicit so that
  -- `hι` applies, `ιTensorObj` and `ιMapBifunctor` being the same inclusion.
  change ModuleCat.Hom.hom
    (HomologicalComplex.ιMapBifunctor (linearHomComplex R F G)
        (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℤ) j 0 j (add_zero j) ≫
      (linearHomComplex R F G ◁ linearHomComplexUnit R F).f j ≫
        (linearHomComplexComp R F F G).f j)
      (z ⊗ₜ ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{v} R))).inv : _) 1) = z
  rw [hι]
  have hunit : ((linearHomComplexUnit R F).f 0)
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{v} R))).inv : _) 1) = Cochain.ofHom (𝟙 F) :=
    one_smul R (Cochain.ofHom (𝟙 F))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  erw [ModuleCat.MonoidalCategory.whiskerLeft_apply ((linearHomComplex R F G).X j)
    ((linearHomComplexUnit R F).f 0) z
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat.{v} R))).inv 1)]
  rw [hunit]
  erw [cochainCompTensor_tmul]
  exact Cochain.id_comp z

end CategoryLaws

end TauCeti
