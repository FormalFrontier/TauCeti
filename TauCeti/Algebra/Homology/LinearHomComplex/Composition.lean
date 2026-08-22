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
a commutative `R : Type v`, so this file, unlike
`TauCeti/Algebra/Homology/LinearHomComplex/Basic.lean`, requires `CommRing R` and ties the ring to
the morphism universe of `C`.

## Main definitions

* `TauCeti.linearHomComplexComp`: composition, as a morphism of `R`-linear Hom complexes out of
  the tensor product.
* `TauCeti.linearHomComplexOfHom`: a morphism of cochain complexes, as a degree-zero cocycle in
  the corresponding `R`-linear Hom complex.
* `TauCeti.linearHomComplexUnit`: the identity cochain, as a morphism from the tensor unit.

## Main results

* `TauCeti.ι_linearHomComplexComp`: the degree-`j` component restricted to a bidegree summand is
  `TauCeti.cochainCompTensor`; `TauCeti.cochainCompTensor_tmul` gives its pure-tensor formula.
* `TauCeti.linearHomComplexComp_naturality_source` and
  `TauCeti.linearHomComplexComp_naturality_target`: composition is natural in the source and in
  the target cochain complex.
* `TauCeti.linearHomComplexComp_dinaturality_middle`: composition is dinatural in the middle
  cochain complex.
* `TauCeti.linearHomComplexComp_assoc`, `TauCeti.linearHomComplexUnit_comp`, and
  `TauCeti.linearHomComplexComp_unit`: composition is associative and unital.
* `TauCeti.linearHomComplexOfHom_f_zero`: a morphism of complexes gives its associated cochain in
  degree zero.

This advances `TauCetiRoadmap/DGAInfinity/README.md`, Layer 0, item "signed graded multilinear and
tensor-coalgebra infrastructure", specifically "construct the `k`-linear Hom complex, its signed
differential ..., closed composition map, and the enrichment".  No formalization is vendored: the
Leibniz rule `δ_comp` and the totalized monoidal structure are Mathlib's.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
* B. Keller, *Deriving DG categories*, Section 1.
* Joël Riou's Mathlib cochain/`δ` and totalization API, together with the totalized
  `HomologicalComplex.monoidalCategory` of Joël Riou and Kim Morrison in
  `Mathlib/Algebra/Homology/Monoidal.lean`.  This file assembles Riou's `δ_comp` and the
  totalization API into the `ModuleCat R`-valued composition map, inheriting their sign convention.
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

/-- On a pure tensor, `cochainCompTensor` sends `z₂ ⊗ₜ z₁` to the composite `z₁.comp z₂`. -/
@[simp]
lemma cochainCompTensor_tmul (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j)
    (z₂ : (linearHomComplex R G K).X p) (z₁ : (linearHomComplex R F G).X q) :
    cochainCompTensor R F G K p q j h (z₂ ⊗ₜ z₁) =
      ((z₁ : Cochain F G q).comp (z₂ : Cochain G K p) (by dsimp at h; omega) :
        (linearHomComplex R F K).X j) :=
  (rfl)

/- Mathlib's element-level lemmas use the concrete-category coercion, whereas simplification of
composites in `ModuleCat` leaves the equivalent `ModuleCat.Hom.hom` projection.  Normalize that
projection once so the public application lemmas rewrite with ordinary `rw`. -/
private lemma moduleCat_hom_eq_concrete {X Y : ModuleCat.{v} R} (f : X ⟶ Y) :
    ModuleCat.Hom.hom f = ConcreteCategory.hom f :=
  rfl

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
  have hd : (linearHomComplex R G K ⊗ linearHomComplex R F G).d j (j + 1) =
      HomologicalComplex.mapBifunctor.D₁ (linearHomComplex R G K) (linearHomComplex R F G)
          (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) j (j + 1) +
        HomologicalComplex.mapBifunctor.D₂ (linearHomComplex R G K) (linearHomComplex R F G)
          (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) j (j + 1) :=
    HomologicalComplex.mapBifunctor.d_eq _ _ _ _ j (j + 1)
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
  simp only [moduleCat_hom_eq_concrete]
  rw [cochainCompTensor_tmul, cochainCompTensor_tmul, cochainCompTensor_tmul,
    linearHomComplex_d_apply, linearHomComplex_d_apply]
  -- The composite is now a `Cochain`-typed output, while the public differential lemma uses the
  -- projected `.X` type; `erw` performs this final definitional alignment at the use site.
  erw [linearHomComplex_d_apply]
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
private lemma linearHomComplexComp_f (j : ℤ) :
    (linearHomComplexComp R F G K).f j =
      HomologicalComplex.mapBifunctorDesc (cochainCompTensor R F G K · · j ·) :=
  rfl

/-- The degree-`j` component of composition restricted to the bidegree-`(p, q)` summand is
`cochainCompTensor`; see `cochainCompTensor_tmul` for its value on pure tensors. -/
@[reassoc (attr := simp)]
lemma ι_linearHomComplexComp (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    HomologicalComplex.ιMapBifunctor (linearHomComplex R G K) (linearHomComplex R F G)
        (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) p q j h ≫
      (linearHomComplexComp R F G K).f j = cochainCompTensor R F G K p q j h := by
  rw [linearHomComplexComp_f]
  apply HomologicalComplex.ι_mapBifunctorDesc

/-- A morphism of cochain complexes, regarded as a degree-zero cocycle in the corresponding
`R`-linear Hom complex. -/
noncomputable def linearHomComplexOfHom {F G : CochainComplex C ℤ} (φ : F ⟶ G) :
    𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ linearHomComplex R F G :=
  HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R (Cochain F G 0) (Cochain.ofHom φ)))
    (fun i _ => ModuleCat.hom_ext (LinearMap.ext fun r => by
      -- Evaluate the `ModuleCat` composite supplied by `mkHomFromSingle`; from here the
      -- characteristic `δ` lemmas apply directly.
      change δ 0 i (r • Cochain.ofHom φ) = 0
      rw [δ_smul, δ_ofHom, smul_zero]))

/-- The degree-zero component of `linearHomComplexOfHom` sends a scalar to that scalar multiple
of the associated cochain. -/
@[simp]
lemma linearHomComplexOfHom_f_zero {F G : CochainComplex C ℤ} (φ : F ⟶ G) :
    (linearHomComplexOfHom R φ).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R (Cochain F G 0) (Cochain.ofHom φ)) :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The identity cochain of `F`, as a morphism from the tensor unit to the `R`-linear Hom complex
of `F` with itself. -/
noncomputable def linearHomComplexUnit :
    𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ linearHomComplex R F F :=
  linearHomComplexOfHom R (𝟙 F)

/-- The unit is the degree-zero cocycle associated to the identity morphism. -/
lemma linearHomComplexUnit_eq :
    linearHomComplexUnit R F = linearHomComplexOfHom R (𝟙 F) :=
  (rfl)

/-- The degree-zero component of the unit sends a scalar to the corresponding scalar multiple of
the identity cochain. -/
@[simp]
lemma linearHomComplexUnit_f_zero_apply (r : R) :
    (linearHomComplexUnit R F).f 0
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat.{v} R))).inv r) =
      (r • Cochain.ofHom (𝟙 F) : (linearHomComplex R F F).X 0) := by
  rw [linearHomComplexUnit_eq]
  rw [linearHomComplexOfHom_f_zero]
  rfl

private lemma whiskerLeft_eq (X : CochainComplex (ModuleCat.{v} R) ℤ)
    {Y Z : CochainComplex (ModuleCat.{v} R) ℤ} (g : Y ⟶ Z) :
    X ◁ g = HomologicalComplex.mapBifunctorMap (𝟙 X) g
      (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) :=
  rfl

private lemma whiskerRight_eq {X Y : CochainComplex (ModuleCat.{v} R) ℤ} (f : X ⟶ Y)
    (Z : CochainComplex (ModuleCat.{v} R) ℤ) :
    f ▷ Z = HomologicalComplex.mapBifunctorMap f (𝟙 Z)
      (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) :=
  rfl

section Naturality

variable {F G K}
variable {F₁ F₂ G₁ G₂ K₁ K₂ : CochainComplex C ℤ}

/-- Composition is natural in the source: composing after precomposition by `φ` is the same as
precomposing the composite by `φ`.  This is associativity of `Cochain.comp` with the degree-zero
cochain `Cochain.ofHom φ` in the first (diagrammatic) argument. -/
@[reassoc]
lemma linearHomComplexComp_naturality_source (φ : F₁ ⟶ F₂) (G K : CochainComplex C ℤ) :
    linearHomComplex R G K ◁ linearHomComplexPrecomp R φ G ≫ linearHomComplexComp R F₁ G K =
      linearHomComplexComp R F₂ G K ≫ linearHomComplexPrecomp R φ K := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have h' : p + q = j := h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
    whiskerLeft_eq,
    HomologicalComplex.ι_mapBifunctorMap, Category.assoc, Category.assoc,
    ι_linearHomComplexComp, ι_linearHomComplexComp_assoc]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z₂ z₁
  simp only [curriedTensor_obj_obj, HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    NatTrans.id_app, curriedTensor_obj_map, Category.id_comp, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply]
  simp only [moduleCat_hom_eq_concrete]
  erw [linearHomComplexPrecomp_f_apply, cochainCompTensor_tmul,
    cochainCompTensor_tmul, linearHomComplexPrecomp_f_apply]
  have hassoc : ((Cochain.ofHom φ).comp z₁ (zero_add q)).comp z₂ (by omega) =
      (Cochain.ofHom φ).comp (z₁.comp z₂ (by omega)) (zero_add j) :=
    Cochain.comp_assoc _ _ _ (zero_add q) (by omega) (by omega)
  exact hassoc

/-- Composition is natural in the target: composing after postcomposition by `ψ` is the same as
postcomposing the composite by `ψ`.  This is associativity of `Cochain.comp` with the degree-zero
cochain `Cochain.ofHom ψ` in the last (diagrammatic) argument. -/
@[reassoc]
lemma linearHomComplexComp_naturality_target (ψ : K₁ ⟶ K₂) (F G : CochainComplex C ℤ) :
    linearHomComplexPostcomp R G ψ ▷ linearHomComplex R F G ≫ linearHomComplexComp R F G K₂ =
      linearHomComplexComp R F G K₁ ≫ linearHomComplexPostcomp R F ψ := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have h' : p + q = j := h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
    whiskerRight_eq,
    HomologicalComplex.ι_mapBifunctorMap, Category.assoc, Category.assoc,
    ι_linearHomComplexComp, ι_linearHomComplexComp_assoc]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z₂ z₁
  simp only [curriedTensor_obj_obj, HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    curriedTensor_map_app, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ConcreteCategory.id_apply]
  simp only [moduleCat_hom_eq_concrete]
  erw [linearHomComplexPostcomp_f_apply, cochainCompTensor_tmul,
    cochainCompTensor_tmul, linearHomComplexPostcomp_f_apply]
  have hassoc : (z₁.comp z₂ (by omega)).comp (Cochain.ofHom ψ) (add_zero j) =
      z₁.comp (z₂.comp (Cochain.ofHom ψ) (add_zero p)) (by omega) :=
    Cochain.comp_assoc _ _ _ (by omega) (add_zero p) (by omega)
  exact hassoc.symm

/-- Composition is dinatural in the middle object: precomposition in the first Hom complex agrees
with postcomposition in the second Hom complex. -/
@[reassoc]
lemma linearHomComplexComp_dinaturality_middle (ψ : G₁ ⟶ G₂) (F K : CochainComplex C ℤ) :
    linearHomComplexPrecomp R ψ K ▷ linearHomComplex R F G₁ ≫
        linearHomComplexComp R F G₁ K =
      linearHomComplex R G₂ K ◁ linearHomComplexPostcomp R F ψ ≫
        linearHomComplexComp R F G₂ K := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have h' : p + q = j := h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
    whiskerRight_eq,
    HomologicalComplex.ι_mapBifunctorMap, Category.assoc, whiskerLeft_eq,
    HomologicalComplex.ι_mapBifunctorMap_assoc,
    ι_linearHomComplexComp, Category.assoc, ι_linearHomComplexComp]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z₂ z₁
  simp only [curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]
  simp only [moduleCat_hom_eq_concrete]
  erw [linearHomComplexPrecomp_f_apply, cochainCompTensor_tmul,
    linearHomComplexPostcomp_f_apply, cochainCompTensor_tmul]
  exact (Cochain.comp_assoc z₁ (Cochain.ofHom ψ) z₂ (add_zero q) (zero_add p) (by omega)).symm

end Naturality

section CategoryLaws

variable {F G K}
variable (L : CochainComplex C ℤ)

/- Restrict the left-associated composite to a tridegree summand.  Factoring this calculation out
keeps the associativity proof focused on the resulting cochain equation. -/
private lemma ι₁₂_whiskerRight_comp (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j)
    (h' : p + q + r = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R))
        (curriedTensor (ModuleCat.{v} R)) (linearHomComplex R K L)
        (linearHomComplex R G K) (linearHomComplex R F G) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) p q r j h ≫
      ((linearHomComplexComp R G K L ▷ linearHomComplex R F G) ≫
        linearHomComplexComp R F G L).f j =
    (cochainCompTensor R G K L p q (p + q) rfl ▷ (linearHomComplex R F G).X r) ≫
      cochainCompTensor R F G L (p + q) r j (by omega) := by
  rw [HomologicalComplex.comp_f, ← Category.assoc, whiskerRight_eq,
    HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor (ModuleCat.{v} R))
      (curriedTensor (ModuleCat.{v} R)) (linearHomComplex R K L)
      (linearHomComplex R G K) (linearHomComplex R F G) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) p q r (p + q) j rfl (by omega),
    Category.assoc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap_assoc,
    ι_linearHomComplexComp]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    curriedTensor_map_app, Category.id_comp]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, ι_linearHomComplexComp]

/- Restrict the associator and right-associated composite to a tridegree summand. -/
private lemma ι₁₂_associator_whiskerLeft_comp (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j)
    (h' : p + q + r = j) :
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
  have ha : (α_ (linearHomComplex R K L) (linearHomComplex R G K)
      (linearHomComplex R F G)).hom.f j =
      (HomologicalComplex.mapBifunctorAssociatorX
        (curriedAssociatorNatIso (ModuleCat.{v} R)) (linearHomComplex R K L)
        (linearHomComplex R G K) (linearHomComplex R F G) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) j).hom := rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  rw [ha, HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc]
  dsimp only [bifunctorComp₁₂, bifunctorComp₂₃, bifunctorComp₁₂Obj, bifunctorComp₂₃Obj]
  rw [MonoidalCategory.curriedAssociatorNatIso_hom_app_app_app, whiskerLeft_eq,
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

/-- Composition of cochains is associative, with the tensor products identified by the monoidal
associator. -/
@[reassoc]
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
  rw [ι₁₂_whiskerRight_comp (R := R) (F := F) (G := G) (K := K) (L := L)
      (p := p) (q := q) (r := r) (j := j) (h := h) (h' := h'),
    ι₁₂_associator_whiskerLeft_comp (R := R) (F := F) (G := G) (K := K) (L := L)
      (p := p) (q := q) (r := r) (j := j) (h := h) (h' := h')]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z₃₂ z₁
  induction z₃₂ using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
  | tmul z₃ z₂ =>
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply]
    simp only [moduleCat_hom_eq_concrete]
    erw [cochainCompTensor_tmul R G K L p q (p + q) rfl z₃ z₂,
      cochainCompTensor_tmul]
    rw [ModuleCat.MonoidalCategory.associator_hom_apply z₃ z₂ z₁]
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
@[reassoc]
lemma linearHomComplexUnit_comp :
    linearHomComplexUnit R G ▷ linearHomComplex R F G ≫
        linearHomComplexComp R F G G =
      (λ_ (linearHomComplex R F G)).hom := by
  apply (cancel_epi (λ_ (linearHomComplex R F G)).inv).1
  rw [Iso.inv_hom_id]
  ext j : 1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  rw [leftUnitor_inv_f, HomologicalComplex.leftUnitor'_inv]
  have hι :
      HomologicalComplex.ιTensorObj
          (HomologicalComplex.tensorUnit (ModuleCat.{v} R) (ComplexShape.up ℤ))
          (linearHomComplex R F G) 0 j j (zero_add j) ≫
        (linearHomComplexUnit R G ▷ linearHomComplex R F G).f j ≫
          (linearHomComplexComp R F G G).f j =
        (linearHomComplexUnit R G).f 0 ▷ (linearHomComplex R F G).X j ≫
          cochainCompTensor R F G G 0 j j (zero_add j) := by
    rw [whiskerRight_eq, HomologicalComplex.ι_mapBifunctorMap_assoc,
      ι_linearHomComplexComp]
    simp only [HomologicalComplex.id_f, curriedTensor_obj_obj, curriedTensor_map_app,
      curriedTensor_obj_map, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [Category.assoc, Category.assoc, hι]
  ext z
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    moduleCat_hom_eq_concrete, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ConcreteCategory.id_apply]
  erw [linearHomComplexUnit_f_zero_apply, one_smul, cochainCompTensor_tmul]
  exact Cochain.comp_id z

/-- The identity cochain is a right unit for composition. -/
@[reassoc]
lemma linearHomComplexComp_unit :
    linearHomComplex R F G ◁ linearHomComplexUnit R F ≫
        linearHomComplexComp R F F G =
      (ρ_ (linearHomComplex R F G)).hom := by
  apply (cancel_epi (ρ_ (linearHomComplex R F G)).inv).1
  rw [Iso.inv_hom_id]
  ext j : 1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  rw [rightUnitor_inv_f, HomologicalComplex.rightUnitor'_inv]
  have hι :
      HomologicalComplex.ιTensorObj (linearHomComplex R F G)
          (HomologicalComplex.tensorUnit (ModuleCat.{v} R) (ComplexShape.up ℤ))
          j 0 j (add_zero j) ≫
        (linearHomComplex R F G ◁ linearHomComplexUnit R F).f j ≫
          (linearHomComplexComp R F F G).f j =
        (linearHomComplex R F G).X j ◁ (linearHomComplexUnit R F).f 0 ≫
          cochainCompTensor R F F G j 0 j (add_zero j) := by
    rw [whiskerLeft_eq, HomologicalComplex.ι_mapBifunctorMap_assoc,
      ι_linearHomComplexComp]
    simp only [HomologicalComplex.id_f, curriedTensor_obj_obj, curriedTensor_map_app,
      curriedTensor_obj_map, MonoidalCategory.id_whiskerRight, Category.id_comp]
  rw [Category.assoc, Category.assoc, hι]
  ext z
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    moduleCat_hom_eq_concrete, ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ConcreteCategory.id_apply]
  erw [linearHomComplexUnit_f_zero_apply, one_smul, cochainCompTensor_tmul]
  exact Cochain.id_comp z

end CategoryLaws

end TauCeti
