/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Product

/-!
# Decomposition of homomorphisms into a product of abelian varieties

Homomorphisms of abelian varieties into a product decompose componentwise: pairing with the two
projections is a group isomorphism `(C ⟶ prod A B) ≃* ((C ⟶ A) × (C ⟶ B))`. This packages the
universal property of `AbelianVariety.prod` at the level of the pointwise group law on hom-sets
recorded in `TauCeti.AlgebraicGeometry.AbelianVariety.MorphismGroup`.

## Main declarations

* `AbelianVariety.Hom.prod_lift_one`, `prod_lift_mul`, `prod_lift_inv`, `prod_lift_div`,
  `prod_lift_zpow`: pairing is a homomorphism for the pointwise group law of the target;
* `AbelianVariety.Hom.prodMulEquiv`: the resulting group isomorphism
  `(C ⟶ prod A B) ≃* ((C ⟶ A) × (C ⟶ B))`, together with `_apply` and `_symm_apply`
  characterizing its action;
* `AbelianVariety.Hom.prodMulEquiv_naturality`: naturality of the equivalence in the source, i.e.
  precomposition by `h : D ⟶ C` and componentwise precomposition intertwine.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API", by combining Layer E's
categorical binary products with its pointwise group law on homomorphism sets. Layer F's
universal property of the Abel–Jacobi map compares homomorphisms into products of abelian
varieties, and equality there becomes componentwise equality via this equivalence.

No external mathematics is vendored; the equivalence is a direct combination of the categorical
universal property already recorded by `AbelianVariety.prod.lift_fst`, `prod.lift_snd`,
`prod.lift_comp_fst_snd`, and the bimultiplicativity of composition (`Hom.mul_comp`,
`Hom.one_comp`, `Hom.inv_comp`, `Hom.div_comp`) from
`TauCeti.AlgebraicGeometry.AbelianVariety.MorphismGroup`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

open scoped Hom

variable {K : Type u} [Field K]

noncomputable section

namespace Hom

variable {A B C D : AbelianVariety K}

/-! ### Pairing is a homomorphism for the pointwise group law

The pairing `prod.lift : (C ⟶ A) → (C ⟶ B) → (C ⟶ prod A B)` is a homomorphism in each variable
for the pointwise group law of the target. -/

/-- Pairing the two identity elements gives the identity element of the pointwise group law on
homomorphisms into a product. -/
@[simp]
lemma prod_lift_one (A B C : AbelianVariety K) :
    prod.lift (1 : C ⟶ A) (1 : C ⟶ B) = 1 := by
  apply prod.hom_ext <;>
    simp only [prod.lift_fst, prod.lift_snd, Hom.one_comp]

/-- Pairing distributes over the pointwise product: `prod.lift (f * f') (g * g')` is the pointwise
product of the two pairings. -/
@[simp]
lemma prod_lift_mul (f f' : C ⟶ A) (g g' : C ⟶ B) :
    prod.lift (f * f') (g * g') = prod.lift f g * prod.lift f' g' := by
  apply prod.hom_ext
  · simp only [prod.lift_fst, Hom.mul_comp]
  · simp only [prod.lift_snd, Hom.mul_comp]

/-- Pairing preserves pointwise inverses: `prod.lift f⁻¹ g⁻¹` is the pointwise inverse of the
pairing. -/
@[simp]
lemma prod_lift_inv (f : C ⟶ A) (g : C ⟶ B) :
    prod.lift f⁻¹ g⁻¹ = (prod.lift f g)⁻¹ := by
  apply prod.hom_ext
  · simp only [prod.lift_fst, Hom.inv_comp]
  · simp only [prod.lift_snd, Hom.inv_comp]

/-- Pairing preserves pointwise quotients: `prod.lift (f / f') (g / g')` is the pointwise quotient
of the two pairings. -/
@[simp]
lemma prod_lift_div (f f' : C ⟶ A) (g g' : C ⟶ B) :
    prod.lift (f / f') (g / g') = prod.lift f g / prod.lift f' g' := by
  apply prod.hom_ext
  · simp only [prod.lift_fst, Hom.div_comp]
  · simp only [prod.lift_snd, Hom.div_comp]

/-! ### The equivalence

Pairing with the two projections is a group isomorphism from `C ⟶ prod A B` to the direct product
of the two hom-groups. -/

/-- Homomorphisms of abelian varieties into a product decompose componentwise as a group
isomorphism: pair with the two projections, invert by `prod.lift`.

The forward map is `f ↦ (f ≫ prod.fst A B, f ≫ prod.snd A B)`, its inverse is `⟨g, h⟩ ↦
prod.lift g h`, and the two are group homomorphisms for the pointwise group law by
`prod_lift_mul` and the bimultiplicativity `Hom.mul_comp`. -/
def prodMulEquiv (A B C : AbelianVariety K) :
    (C ⟶ prod A B) ≃* ((C ⟶ A) × (C ⟶ B)) where
  toFun f := (f ≫ prod.fst A B, f ≫ prod.snd A B)
  invFun p := prod.lift p.1 p.2
  left_inv f := prod.lift_comp_fst_snd f
  right_inv p := Prod.ext (prod.lift_fst p.1 p.2) (prod.lift_snd p.1 p.2)
  map_mul' f f' :=
    Prod.ext (Hom.mul_comp f f' (prod.fst A B)) (Hom.mul_comp f f' (prod.snd A B))

@[simp]
lemma prodMulEquiv_apply (f : C ⟶ prod A B) :
    prodMulEquiv A B C f = (f ≫ prod.fst A B, f ≫ prod.snd A B) :=
  (rfl)

@[simp]
lemma prodMulEquiv_symm_apply (p : (C ⟶ A) × (C ⟶ B)) :
    (prodMulEquiv A B C).symm p = prod.lift p.1 p.2 :=
  (rfl)

/-! ### Pointwise integer powers

`prod_lift_zpow` and `zpow_prodMulEquiv_symm` transport pointwise `zpow` across the equivalence;
they are the group-power-map corollaries of `prod_lift_mul` and `prod_lift_inv`. -/

/-- Pairing preserves pointwise integer powers: `prod.lift (f ^ n) (g ^ n)` is the `n`-th
pointwise power of the pairing. -/
@[simp]
lemma prod_lift_zpow (f : C ⟶ A) (g : C ⟶ B) (n : ℤ) :
    prod.lift (f ^ n) (g ^ n) = (prod.lift f g) ^ n := by
  apply prod.hom_ext
  · simp only [prod.lift_fst, Hom.zpow_comp]
  · simp only [prod.lift_snd, Hom.zpow_comp]

/-! ### Naturality in the source

Precomposition by `h : D ⟶ C` intertwines the equivalence with componentwise precomposition, so
the decomposition of a homomorphism into a product is a natural transformation in the source. -/

/-- Naturality of the equivalence in the source: precomposition by `h : D ⟶ C` corresponds to
componentwise precomposition by `h`. -/
lemma prodMulEquiv_naturality (h : D ⟶ C) (f : C ⟶ prod A B) :
    prodMulEquiv A B D (h ≫ f) =
      (h ≫ (prodMulEquiv A B C f).1, h ≫ (prodMulEquiv A B C f).2) := by
  simp only [prodMulEquiv_apply, Category.assoc]

/-- The `prod.lift` form of naturality: pulling a precomposition through pairing distributes into
each argument. This is the categorical `prod.comp_lift` re-stated for direct symmetry with
`prodMulEquiv_naturality`. -/
lemma prodMulEquiv_symm_naturality (h : D ⟶ C) (p : (C ⟶ A) × (C ⟶ B)) :
    (prodMulEquiv A B D).symm (h ≫ p.1, h ≫ p.2) =
      h ≫ (prodMulEquiv A B C).symm p := by
  simp only [prodMulEquiv_symm_apply, prod.comp_lift]

end Hom

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
