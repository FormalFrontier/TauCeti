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

/-!
# The Koszul braiding on cochain complexes of modules

Mathlib's `HomologicalComplex.monoidalCategory`, instantiated at `ComplexShape.up ℤ` and its
`ComplexShape.TensorSigns`, makes `CochainComplex (ModuleCat R) ℤ` monoidal by totalizing the
degreewise tensor product.  It does not make it braided: Mathlib's `GradedObject.braidedCategory`
uses the braiding of the base category on each summand with no sign, and that map does not commute
with the totalized differential.

This file supplies the missing sign.  On the bidegree-`(p, q)` summand of `X ⊗ Y` the braiding is
`(-1)^{p * q}` times the braiding of `ModuleCat R`, that is, `x ⊗ y ↦ (-1)^{|x| * |y|} y ⊗ x` on
homogeneous elements.  The sign is forced: the totalized differential carries `ComplexShape.up ℤ`'s
tensor signs `ε₁ = 1` and `ε₂ (p, q) = (-1)^p`, and the two Leibniz terms match after transposing
exactly when the summand map is scaled by `(-1)^{p * q}`.

## Main definitions

* `TauCeti.koszulBraidingSummand`: the bidegree component of the braiding.
* `TauCeti.koszulBraidingHom`, `TauCeti.koszulBraiding`: the braiding `X ⊗ Y ⟶ Y ⊗ X` of cochain
  complexes and the isomorphism it underlies.
* `TauCeti.koszulBraidedCategory` and `TauCeti.koszulSymmetricCategory`: the `BraidedCategory`
  and `SymmetricCategory` instances on `CochainComplex (ModuleCat R) ℤ`.

## Main results

* `TauCeti.koszulBraidingHom_naturality_left` and `TauCeti.koszulBraidingHom_naturality_right`:
  the braiding is natural in each factor.
* `TauCeti.koszulBraidingHom_hexagon_forward` and `TauCeti.koszulBraidingHom_hexagon_reverse`: the
  two hexagon identities.
* `TauCeti.koszulBraidingHom_comp`: the braiding is symmetric.

Two auxiliary equations, `TauCeti.whiskerLeft_eq_mapBifunctorMap` and
`TauCeti.whiskerRight_eq_mapBifunctorMap`, record that the whiskerings of
`CochainComplex (ModuleCat R) ℤ` are `HomologicalComplex.mapBifunctorMap`; Mathlib builds the
monoidal structure from that totalization but states no component lemma for `◁` and `▷`.

This advances `TauCetiRoadmap/DGAInfinity/README.md`, Layer 0, item "signed graded multilinear and
tensor-coalgebra infrastructure", specifically "Complete the symmetric monoidal structure on
unbounded `CochainComplex (ModuleCat k) ℤ` ... What has to be added is the braiding: transport
`GradedObject.braidedCategory` through the totalization, supply the Koszul sign
`x ⊗ y ↦ (-1)^{|x||y|}  y ⊗ x` on the degreewise summands, and prove the hexagon and symmetry
axioms at complex level."  It is the prerequisite, in the roadmap's own order, of the `R`-linear
Hom complex and its composition map built in `TauCeti/Algebra/Homology/LinearHomComplex/`.

## Implementation notes

`Mathlib.CategoryTheory.Monoidal.Closed.Braided` is imported for the colimit-preservation
instances that make the tensor product of cochain complexes exist at all, exactly as in
`TauCeti/Algebra/Homology/LinearHomComplex/Composition.lean`.

The hexagon proofs restrict both sides to a tridegree summand with
`HomologicalComplex.mapBifunctor₁₂.hom_ext` and then reduce to the corresponding hexagon of
`ModuleCat R`; the second hexagon is deduced from the first by inverting every isomorphism
involved, which is legitimate because the braiding is symmetric.

## References

* The totalized monoidal structure `HomologicalComplex.monoidalCategory` in
  `Mathlib/Algebra/Homology/Monoidal.lean`, by Joël Riou and Kim Morrison, and the unsigned
  `GradedObject.Monoidal.braiding` of `Mathlib/CategoryTheory/GradedObject/Braiding.lean`, by
  Joël Riou.  This file adds the Koszul sign and the complex-level axioms; nothing is vendored.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  convention.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe v

variable (R : Type v) [CommRing R]

/-- Left whiskering in `CochainComplex (ModuleCat R) ℤ` is the totalization of the identity and
the given morphism.  Mathlib defines the monoidal structure on homological complexes through
`HomologicalComplex.mapBifunctorMap`, but states no component lemma for `◁`. -/
lemma whiskerLeft_eq_mapBifunctorMap (X : CochainComplex (ModuleCat.{v} R) ℤ)
    {Y Z : CochainComplex (ModuleCat.{v} R) ℤ} (g : Y ⟶ Z) :
    X ◁ g = HomologicalComplex.mapBifunctorMap (𝟙 X) g
      (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) :=
  rfl

/-- Right whiskering in `CochainComplex (ModuleCat R) ℤ` is the totalization of the given
morphism and the identity; the counterpart of `TauCeti.whiskerLeft_eq_mapBifunctorMap`. -/
lemma whiskerRight_eq_mapBifunctorMap {X Y : CochainComplex (ModuleCat.{v} R) ℤ} (f : X ⟶ Y)
    (Z : CochainComplex (ModuleCat.{v} R) ℤ) :
    f ▷ Z = HomologicalComplex.mapBifunctorMap f (𝟙 Z)
      (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) :=
  rfl

/-- The bidegree-`(p, q)` component of the Koszul braiding `X ⊗ Y ⟶ Y ⊗ X`: the braiding of
`ModuleCat R` on the summand `X.X p ⊗ Y.X q`, carrying the Koszul sign `(-1)^{p * q}`. -/
noncomputable def koszulBraidingSummand (X Y : CochainComplex (ModuleCat.{v} R) ℤ) (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    X.X p ⊗ Y.X q ⟶ (Y ⊗ X).X j :=
  (p * q).negOnePow • ((β_ (X.X p) (Y.X q)).hom ≫
    HomologicalComplex.ιMapBifunctor Y X (curriedTensor (ModuleCat.{v} R))
      (ComplexShape.up ℤ) q p j (by dsimp at h ⊢; omega))

/-- The bidegree component of the Koszul braiding is the ordinary module braiding, followed by
the inclusion of the swapped summand, and scaled by `(-1)^(p*q)`. -/
lemma koszulBraidingSummand_def (X Y : CochainComplex (ModuleCat.{v} R) ℤ) (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    koszulBraidingSummand R X Y p q j h =
      (p * q).negOnePow • ((β_ (X.X p) (Y.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor Y X (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) q p j (by dsimp at h ⊢; omega)) :=
  (rfl)

private lemma koszulBraidingSummand_comm (X Y : CochainComplex (ModuleCat.{v} R) ℤ)
    (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    koszulBraidingSummand R X Y p q j h ≫ (Y ⊗ X).d j (j + 1) =
      HomologicalComplex.ιMapBifunctor X Y (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) p q j h ≫ (X ⊗ Y).d j (j + 1) ≫
        HomologicalComplex.mapBifunctorDesc (koszulBraidingSummand R X Y · · (j + 1) ·) := by
  replace h : p + q = j := h
  have hdYX : (Y ⊗ X).d j (j + 1) =
      HomologicalComplex.mapBifunctor.D₁ Y X (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) j (j + 1) +
        HomologicalComplex.mapBifunctor.D₂ Y X (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) j (j + 1) :=
    HomologicalComplex.mapBifunctor.d_eq _ _ _ _ j (j + 1)
  have hdXY : (X ⊗ Y).d j (j + 1) =
      HomologicalComplex.mapBifunctor.D₁ X Y (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) j (j + 1) +
        HomologicalComplex.mapBifunctor.D₂ X Y (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) j (j + 1) :=
    HomologicalComplex.mapBifunctor.d_eq _ _ _ _ j (j + 1)
  rw [hdYX, hdXY, koszulBraidingSummand]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Linear.units_smul_comp,
    Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (ComplexShape.up_mk q (q + 1) rfl) p (j + 1) (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ q
      (ComplexShape.up_mk p (p + 1) rfl) (j + 1) (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (ComplexShape.up_mk p (p + 1) rfl) q (j + 1) (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
      (ComplexShape.up_mk q (q + 1) rfl) (j + 1) (by dsimp; omega)]
  simp only [ComplexShape.ε₁_def, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ, one_smul,
    curriedTensor_map_app, curriedTensor_obj_map,
    Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
    HomologicalComplex.ι_mapBifunctorDesc, koszulBraidingSummand, smul_smul]
  have hs₁ : ((p + 1) * q).negOnePow = (p * q).negOnePow * q.negOnePow := by
    rw [show (p + 1) * q = p * q + q by ring, Int.negOnePow_add]
  have hs₂ : p.negOnePow * (p * (q + 1)).negOnePow = (p * q).negOnePow := by
    rw [show p * (q + 1) = p * q + p by ring, Int.negOnePow_add, ← mul_assoc,
      mul_comm p.negOnePow (p * q).negOnePow, mul_assoc, ← Int.negOnePow_add,
      Int.negOnePow_even _ ⟨p, rfl⟩, mul_one]
  rw [hs₁, hs₂, ← BraidedCategory.braiding_naturality_left_assoc,
    ← BraidedCategory.braiding_naturality_right_assoc]
  exact add_comm _ _

/-- The Koszul braiding `X ⊗ Y ⟶ Y ⊗ X`. -/
noncomputable def koszulBraidingHom (X Y : CochainComplex (ModuleCat.{v} R) ℤ) :
    X ⊗ Y ⟶ Y ⊗ X where
  f j := HomologicalComplex.mapBifunctorDesc (koszulBraidingSummand R X Y · · j ·)
  comm' j j' hjj' := by
    replace hjj' : j + 1 = j' := hjj'
    subst hjj'
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    exact koszulBraidingSummand_comm R X Y p q j h

private lemma koszulBraidingHom_f (X Y : CochainComplex (ModuleCat.{v} R) ℤ) (j : ℤ) :
    (koszulBraidingHom R X Y).f j =
      HomologicalComplex.mapBifunctorDesc (koszulBraidingSummand R X Y · · j ·) :=
  rfl

@[reassoc (attr := simp)]
lemma ι_koszulBraidingHom (X Y : CochainComplex (ModuleCat.{v} R) ℤ) (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    HomologicalComplex.ιMapBifunctor X Y (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℤ) p q j h ≫ (koszulBraidingHom R X Y).f j =
      koszulBraidingSummand R X Y p q j h := by
  rw [koszulBraidingHom_f]
  apply HomologicalComplex.ι_mapBifunctorDesc

/-- Composing the Koszul braiding with the braiding of the swapped factors is the identity. -/
lemma koszulBraidingHom_comp (X Y : CochainComplex (ModuleCat.{v} R) ℤ) :
    koszulBraidingHom R X Y ≫ koszulBraidingHom R Y X = 𝟙 _ := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [HomologicalComplex.comp_f, ← Category.assoc, ι_koszulBraidingHom,
    koszulBraidingSummand, Linear.units_smul_comp, Category.assoc,
    ι_koszulBraidingHom, koszulBraidingSummand, Linear.comp_units_smul, smul_smul,
    SymmetricCategory.symmetry_assoc]
  rw [mul_comm q p, ← Int.negOnePow_add, Int.negOnePow_even _ ⟨p * q, rfl⟩, one_smul,
    HomologicalComplex.id_f]
  exact (Category.comp_id _).symm

/-- The Koszul braiding is natural in the left-hand factor. -/
lemma koszulBraidingHom_naturality_left {X Y : CochainComplex (ModuleCat.{v} R) ℤ} (f : X ⟶ Y)
    (Z : CochainComplex (ModuleCat.{v} R) ℤ) :
    f ▷ Z ≫ koszulBraidingHom R Y Z = koszulBraidingHom R X Z ≫ Z ◁ f := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    whiskerRight_eq_mapBifunctorMap, whiskerLeft_eq_mapBifunctorMap]
  simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, ι_koszulBraidingHom_assoc,
    ι_koszulBraidingHom, koszulBraidingSummand, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.assoc,
    Linear.units_smul_comp, Linear.comp_units_smul, HomologicalComplex.ι_mapBifunctorMap]
  simp only [curriedTensor_map_app, curriedTensor_obj_map]
  rw [BraidedCategory.braiding_naturality_left_assoc]

/-- The Koszul braiding is natural in the right-hand factor. -/
lemma koszulBraidingHom_naturality_right (X : CochainComplex (ModuleCat.{v} R) ℤ)
    {Y Z : CochainComplex (ModuleCat.{v} R) ℤ} (f : Y ⟶ Z) :
    X ◁ f ≫ koszulBraidingHom R X Z = koszulBraidingHom R X Y ≫ f ▷ X := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    whiskerLeft_eq_mapBifunctorMap, whiskerRight_eq_mapBifunctorMap]
  simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, ι_koszulBraidingHom_assoc,
    ι_koszulBraidingHom, koszulBraidingSummand, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.assoc,
    Linear.units_smul_comp, Linear.comp_units_smul, HomologicalComplex.ι_mapBifunctorMap]
  simp only [curriedTensor_map_app, curriedTensor_obj_map]
  rw [BraidedCategory.braiding_naturality_right_assoc]

/- Mathlib's `MonoidalPreadditive` gives additivity of the whiskerings but no lemma for a negated
or `ℤˣ`-scaled morphism; the Koszul sign is a `ℤˣ`, so these four bridges are needed to move it
through a whiskering. -/
private lemma neg_whiskerRight {A B : ModuleCat.{v} R} (f : A ⟶ B) (W : ModuleCat.{v} R) :
    (-f) ▷ W = -(f ▷ W) :=
  eq_neg_of_add_eq_zero_left (by
    rw [← MonoidalPreadditive.add_whiskerRight, neg_add_cancel,
      MonoidalPreadditive.zero_whiskerRight])

private lemma whiskerLeft_neg (W : ModuleCat.{v} R) {A B : ModuleCat.{v} R} (f : A ⟶ B) :
    W ◁ (-f) = -(W ◁ f) :=
  eq_neg_of_add_eq_zero_left (by
    rw [← MonoidalPreadditive.whiskerLeft_add, neg_add_cancel,
      MonoidalPreadditive.whiskerLeft_zero])

private lemma units_smul_whiskerRight (u : ℤˣ) {A B : ModuleCat.{v} R} (f : A ⟶ B)
    (W : ModuleCat.{v} R) : (u • f) ▷ W = u • (f ▷ W) := by
  obtain h | h := Int.units_eq_one_or u <;> subst h <;> simp [neg_whiskerRight]

private lemma whiskerLeft_units_smul (W : ModuleCat.{v} R) (u : ℤˣ) {A B : ModuleCat.{v} R}
    (f : A ⟶ B) : W ◁ (u • f) = u • (W ◁ f) := by
  obtain h | h := Int.units_eq_one_or u <;> subst h <;> simp [whiskerLeft_neg]

/- Composing a left whiskering into the braiding summand: the braiding of `ModuleCat R` is natural,
so a map into the second factor passes through it and becomes a right whiskering.  Stating this
with a general `g` avoids rewriting under the two different spellings (`⊗` and
`HomologicalComplex.mapBifunctor`) of a totalized tensor product. -/
@[reassoc]
private lemma whiskerLeft_comp_koszulBraidingSummand (X W : CochainComplex (ModuleCat.{v} R) ℤ)
    (A : ModuleCat.{v} R) (p m j : ℤ) (g : A ⟶ W.X m)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, m) = j) :
    (X.X p ◁ g) ≫ koszulBraidingSummand R X W p m j h =
      (p * m).negOnePow • ((β_ (X.X p) A).hom ≫ (g ▷ X.X p) ≫
        HomologicalComplex.ιMapBifunctor W X (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) m p j (by dsimp at h ⊢; omega)) := by
  rw [koszulBraidingSummand, Linear.comp_units_smul,
    BraidedCategory.braiding_naturality_right_assoc]

/- The counterpart of `whiskerLeft_comp_koszulBraidingSummand` for a right whiskering. -/
@[reassoc]
private lemma whiskerRight_comp_koszulBraidingSummand (W X : CochainComplex (ModuleCat.{v} R) ℤ)
    (A : ModuleCat.{v} R) (m p j : ℤ) (g : A ⟶ W.X m)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (m, p) = j) :
    (g ▷ X.X p) ≫ koszulBraidingSummand R W X m p j h =
      (m * p).negOnePow • ((β_ A (X.X p)).hom ≫ (X.X p ◁ g) ≫
        HomologicalComplex.ιMapBifunctor X W (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) p m j (by dsimp at h ⊢; omega)) := by
  rw [koszulBraidingSummand, Linear.comp_units_smul,
    BraidedCategory.braiding_naturality_left_assoc]

section Hexagon

variable (X Y Z : CochainComplex (ModuleCat.{v} R) ℤ)

/- `ComplexShape.r` at `ComplexShape.up ℤ` is addition of the three degrees; Mathlib has no named
specialization reducing it. -/
private lemma up_r_eq {p q r j : ℤ}
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) : p + q + r = j := h

private lemma up_r_of {p q r j : ℤ} (h : p + q + r = j) :
    ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j := h

private lemma associator_hom_f (j : ℤ) :
    (α_ X Y Z).hom.f j =
      (HomologicalComplex.mapBifunctorAssociatorX
        (curriedAssociatorNatIso (ModuleCat.{v} R)) X Y Z (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) j).hom :=
  rfl

/- Mathlib's `mapBifunctor₁₂.ι_eq` and `mapBifunctor₂₃.ι_eq` are stated for the raw totalization
`HomologicalComplex.mapBifunctor`; these two restatements spell the same equations with the
monoidal `⊗`, which is the form in which the hexagon and its ingredients occur. -/
@[reassoc]
private lemma ι₁₂_eq (p q r pq j : ℤ) (hpq : p + q = pq) (hj : p + q + r = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R))
        (curriedTensor (ModuleCat.{v} R)) X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        p q r j (up_r_of hj) =
      (HomologicalComplex.ιMapBifunctor X Y (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) p q pq hpq ▷ Z.X r) ≫
        HomologicalComplex.ιMapBifunctor (X ⊗ Y) Z (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) pq r j (by dsimp; omega) := by
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor (ModuleCat.{v} R))
    (curriedTensor (ModuleCat.{v} R)) X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    p q r pq j hpq (by dsimp; omega)]
  rfl

@[reassoc]
private lemma ι₂₃_eq (p q r qr j : ℤ) (hqr : q + r = qr) (hj : p + q + r = j) :
    HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor (ModuleCat.{v} R))
        (curriedTensor (ModuleCat.{v} R)) X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) p q r j (up_r_of hj) =
      (X.X p ◁ HomologicalComplex.ιMapBifunctor Y Z (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) q r qr hqr) ≫
        HomologicalComplex.ιMapBifunctor X (Y ⊗ Z) (curriedTensor (ModuleCat.{v} R))
          (ComplexShape.up ℤ) p qr j (by dsimp; omega) := by
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq (curriedTensor (ModuleCat.{v} R))
    (curriedTensor (ModuleCat.{v} R)) X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) p q r qr j hqr (by dsimp; omega)]
  rfl

private lemma ι₁₂_hexagon_forward_lhs (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R))
        (curriedTensor (ModuleCat.{v} R)) X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        p q r j h ≫
      ((α_ X Y Z).hom ≫ koszulBraidingHom R X (Y ⊗ Z) ≫ (α_ Y Z X).hom).f j =
      (p * (q + r)).negOnePow • ((α_ (X.X p) (Y.X q) (Z.X r)).hom ≫
        (β_ (X.X p) (Y.X q ⊗ Z.X r)).hom ≫ (α_ (Y.X q) (Z.X r) (X.X p)).hom ≫
          HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor (ModuleCat.{v} R))
            (curriedTensor (ModuleCat.{v} R)) Y Z X (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) q r p j (up_r_of (by have := up_r_eq h; omega))) := by
  have h' := up_r_eq h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, associator_hom_f,
    HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc]
  dsimp only [bifunctorComp₁₂, bifunctorComp₂₃, bifunctorComp₁₂Obj, bifunctorComp₂₃Obj]
  rw [MonoidalCategory.curriedAssociatorNatIso_hom_app_app_app,
    ι₂₃_eq R X Y Z p q r (q + r) j rfl h',
    Category.assoc, ι_koszulBraidingHom_assoc,
    whiskerLeft_comp_koszulBraidingSummand_assoc R X (Y ⊗ Z) _ p (q + r) j
      (HomologicalComplex.ιMapBifunctor Y Z (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℤ) q r (q + r) rfl),
    ← ι₁₂_eq R Y Z X q r p (q + r) j rfl (by omega),
    associator_hom_f]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [HomologicalComplex.ι_mapBifunctorAssociatorX_hom,
    MonoidalCategory.curriedAssociatorNatIso_hom_app_app_app, Linear.comp_units_smul]
  rfl

private lemma ι₁₂_hexagon_forward_rhs (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R))
        (curriedTensor (ModuleCat.{v} R)) X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        p q r j h ≫
      ((koszulBraidingHom R X Y ▷ Z) ≫ (α_ Y X Z).hom ≫
        (Y ◁ koszulBraidingHom R X Z)).f j =
      (p * (q + r)).negOnePow • (((β_ (X.X p) (Y.X q)).hom ▷ Z.X r) ≫
        (α_ (Y.X q) (X.X p) (Z.X r)).hom ≫ (Y.X q ◁ (β_ (X.X p) (Z.X r)).hom) ≫
          HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor (ModuleCat.{v} R))
            (curriedTensor (ModuleCat.{v} R)) Y Z X (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) q r p j (up_r_of (by have := up_r_eq h; omega))) := by
  have h' := up_r_eq h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ι₁₂_eq R X Y Z p q r (p + q) j rfl h',
    Category.assoc, whiskerRight_eq_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [curriedTensor_map_app]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, ι_koszulBraidingHom, koszulBraidingSummand,
    units_smul_whiskerRight, MonoidalCategory.comp_whiskerRight,
    Linear.units_smul_comp, Category.assoc,
    ← ι₁₂_eq_assoc R Y X Z q p r (p + q) j (by omega) (by omega),
    associator_hom_f, HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc]
  dsimp only [bifunctorComp₁₂, bifunctorComp₂₃, bifunctorComp₁₂Obj, bifunctorComp₂₃Obj]
  rw [ι₂₃_eq_assoc R Y X Z q p r (p + r) j (by omega) (by omega),
    MonoidalCategory.curriedAssociatorNatIso_hom_app_app_app,
    whiskerLeft_eq_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp]
  simp only [curriedTensor_obj_map]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ι_koszulBraidingHom, koszulBraidingSummand,
    whiskerLeft_units_smul, MonoidalCategory.whiskerLeft_comp,
    Linear.units_smul_comp, Category.assoc,
    ← ι₂₃_eq R Y Z X q r p (p + r) j (by omega) (by omega),
    Linear.comp_units_smul, Linear.comp_units_smul, smul_smul, ← Int.negOnePow_add,
    show p * q + p * r = p * (q + r) by ring]

/-- **The first hexagon identity** for the Koszul braiding. -/
lemma koszulBraidingHom_hexagon_forward :
    (α_ X Y Z).hom ≫ koszulBraidingHom R X (Y ⊗ Z) ≫ (α_ Y Z X).hom =
      (koszulBraidingHom R X Y ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ koszulBraidingHom R X Z) := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  rw [ι₁₂_hexagon_forward_lhs, ι₁₂_hexagon_forward_rhs]
  congr 1
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  exact BraidedCategory.hexagon_forward (X.X p) (Y.X q) (Z.X r)

end Hexagon

/-- The Koszul braiding of two cochain complexes of `R`-modules, as an isomorphism.  It is its own
inverse up to swapping the factors, since `ModuleCat R` is symmetric and the Koszul sign is. -/
noncomputable def koszulBraiding (X Y : CochainComplex (ModuleCat.{v} R) ℤ) : X ⊗ Y ≅ Y ⊗ X where
  hom := koszulBraidingHom R X Y
  inv := koszulBraidingHom R Y X
  hom_inv_id := koszulBraidingHom_comp R X Y
  inv_hom_id := koszulBraidingHom_comp R Y X

/-- **The second hexagon identity** for the Koszul braiding.  It follows from the first one applied
to `Z`, `X`, `Y` by inverting every isomorphism involved, because the braiding is symmetric. -/
lemma koszulBraidingHom_hexagon_reverse (X Y Z : CochainComplex (ModuleCat.{v} R) ℤ) :
    (α_ X Y Z).inv ≫ koszulBraidingHom R (X ⊗ Y) Z ≫ (α_ Z X Y).inv =
      (X ◁ koszulBraidingHom R Y Z) ≫ (α_ X Z Y).inv ≫ (koszulBraidingHom R X Z ▷ Y) :=
  (Iso.inv_eq_inv
      ((α_ X Y Z).symm ≪≫ koszulBraiding R (X ⊗ Y) Z ≪≫ (α_ Z X Y).symm)
      (whiskerLeftIso X (koszulBraiding R Y Z) ≪≫ (α_ X Z Y).symm ≪≫
        whiskerRightIso (koszulBraiding R X Z) Y)).1
    (koszulBraidingHom_hexagon_forward R Z X Y)

/-- The forward direction of the Koszul braiding isomorphism. -/
@[simp]
lemma koszulBraiding_hom (X Y : CochainComplex (ModuleCat.{v} R) ℤ) :
    (koszulBraiding R X Y).hom = koszulBraidingHom R X Y :=
  (rfl)

/-- The inverse of the Koszul braiding isomorphism is the Koszul braiding of the two complexes in
the other order. -/
@[simp]
lemma koszulBraiding_inv (X Y : CochainComplex (ModuleCat.{v} R) ℤ) :
    (koszulBraiding R X Y).inv = koszulBraidingHom R Y X :=
  (rfl)

/-- Cochain complexes of `R`-modules form a braided monoidal category, with the Koszul braiding
`x ⊗ y ↦ (-1)^{|x| * |y|} y ⊗ x` on the degreewise summands of Mathlib's totalized tensor
product. -/
noncomputable instance koszulBraidedCategory :
    BraidedCategory (CochainComplex (ModuleCat.{v} R) ℤ) where
  braiding X Y := koszulBraiding R X Y
  braiding_naturality_right X _ _ f := by
    simp only [koszulBraiding_hom]
    exact koszulBraidingHom_naturality_right R X f
  braiding_naturality_left f Z := by
    simp only [koszulBraiding_hom]
    exact koszulBraidingHom_naturality_left R f Z
  hexagon_forward X Y Z := by
    simp only [koszulBraiding_hom]
    exact koszulBraidingHom_hexagon_forward R X Y Z
  hexagon_reverse X Y Z := by
    simp only [koszulBraiding_hom]
    exact koszulBraidingHom_hexagon_reverse R X Y Z

/-- The braiding of the monoidal category `CochainComplex (ModuleCat R) ℤ` is the Koszul
braiding. -/
lemma braiding_eq_koszulBraiding (X Y : CochainComplex (ModuleCat.{v} R) ℤ) :
    β_ X Y = koszulBraiding R X Y :=
  (rfl)

/-- The Koszul braiding is symmetric. -/
noncomputable instance koszulSymmetricCategory :
    SymmetricCategory (CochainComplex (ModuleCat.{v} R) ℤ) where
  symmetry X Y := by
    rw [braiding_eq_koszulBraiding, braiding_eq_koszulBraiding, koszulBraiding_hom,
      koszulBraiding_hom]
    exact koszulBraidingHom_comp R X Y

end TauCeti
