/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic

/-!
# The maximal elementary-2 quotient distributes over products

The maximal elementary-2 quotient `G / G²` of `TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic`
sends a product of commutative groups to the product of the quotients, `ZMod 2`-linearly: `(G ×
H)/(G × H)²` is `G/G² × H/H²`, and the same holds for an arbitrary indexed product. Reading `ZMod
2`-dimensions over a finite index, the **2-rank is additive**:

`TauCeti.twoRank (G × H) = TauCeti.twoRank G + TauCeti.twoRank H`

and `TauCeti.twoRank (∀ i, G i) = ∑ i, TauCeti.twoRank (G i)`.

Both structural equivalences are transported from Mathlib's product-quotient API for quotients by
the range of the doubling map (`QuotientAddGroup.prodAddEquiv` and
`QuotientAddGroup.addEquivPiModRangeNSMulAddMonoidHom`) through the identification of the `ModN`
model of `G/G²` with the quotient by the range of doubling, rather than rebuilt by hand.

This is the structural tool behind computing a class group's 2-rank from a decomposition: a finite
abelian group is a product of cyclic groups, and its 2-rank is the number of even-order factors.
This product additivity supports the Layer 2 class-group quotient API and the later Layer 3
genus-field/2-rank theorem in the multiquadratic roadmap. For instance the class group `(ℤ/2)²`
of `ℚ(√-21)` has 2-rank `1 + 1 = 2`, matching the `t - 1 = 3 - 1` count of ramified primes in the
worked examples.

## Main results

* `TauCeti.elementaryTwoQuotientProdLinearEquiv`: the `ZMod 2`-linear equivalence
  `(G × H)/(G × H)² ≃ₗ G/G² × H/H²`, with `TauCeti.twoRank_prod` and
  `TauCeti.card_elementaryTwoQuotient_prod` its dimension and cardinality readings.
* `TauCeti.elementaryTwoQuotientPiLinearEquiv`: the `ZMod 2`-linear equivalence
  `(∀ i, G i)/(…)² ≃ₗ ∀ i, (G i)/(G i)²` over an arbitrary index, with `TauCeti.twoRank_pi` and
  `TauCeti.card_elementaryTwoQuotient_pi` its dimension and cardinality readings over a finite
  index.
-/

public section

namespace TauCeti

/-- The doubling submodule `range (lsmul ℤ _ 2)` of `Additive G`, whose quotient is the `ModN` model
of `G/G²`, is the range of the doubling monoid hom `nsmulAddMonoidHom 2` as an additive subgroup.
This is the identity that matches the `ModN` model against Mathlib's quotient-by-range API. -/
private theorem range_lsmul_two_toAddSubgroup_eq_range_nsmul (G : Type*) [CommGroup G] :
    (LinearMap.range (LinearMap.lsmul ℤ (Additive G) ((2 : ℕ) : ℤ))).toAddSubgroup =
      (nsmulAddMonoidHom (α := Additive G) 2).range := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_range, LinearMap.lsmul_apply,
    AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, by rw [natCast_zsmul]⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, by rw [natCast_zsmul]⟩

/-- The `ModN` model `G/G²` as the quotient of `Additive G` by the range of the doubling monoid hom
`nsmulAddMonoidHom 2`, matching the shape of Mathlib's product-quotient equivalences. -/
private noncomputable def bridgeModRangeNSMul (G : Type*) [CommGroup G] :
    ElementaryTwoQuotient G ≃+ Additive G ⧸ (nsmulAddMonoidHom (α := Additive G) 2).range :=
  QuotientAddGroup.quotientAddEquivOfEq (range_lsmul_two_toAddSubgroup_eq_range_nsmul G)

/-- The bridge sends the class of `g` to the coset of `Additive.ofMul g`. -/
private theorem bridgeModRangeNSMul_mk (G : Type*) [CommGroup G] (g : G) :
    bridgeModRangeNSMul G (elementaryTwoQuotientMk g) = QuotientAddGroup.mk (Additive.ofMul g) := by
  rw [elementaryTwoQuotientMk_eq_mkQ]; rfl

section Prod

variable (G H : Type*) [CommGroup G] [CommGroup H]

/-- The doubling submodule of `Additive (G × H)` splits as the product of the doubling ranges of the
factors, matching the shape of `QuotientAddGroup.prodAddEquiv`. -/
private theorem range_lsmul_two_toAddSubgroup_prod_eq :
    (LinearMap.range (LinearMap.lsmul ℤ (Additive G × Additive H) ((2 : ℕ) : ℤ))).toAddSubgroup =
      (nsmulAddMonoidHom (α := Additive G) 2).range.prod
        (nsmulAddMonoidHom (α := Additive H) 2).range := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_range, LinearMap.lsmul_apply,
    AddSubgroup.mem_prod, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, natCast_zsmul,
    Prod.exists, Prod.smul_mk, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rintro ⟨u, v, hu, hv⟩; exact ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩; exact ⟨u, v, hu, hv⟩

/-- The product equivalence as an additive equivalence, transported from
`QuotientAddGroup.prodAddEquiv` through the bridge to the `ModN` model on each factor. -/
private noncomputable def elementaryTwoQuotientProdAddEquiv :
    ElementaryTwoQuotient (G × H) ≃+
      ElementaryTwoQuotient G × ElementaryTwoQuotient H :=
  (QuotientAddGroup.quotientAddEquivOfEq (range_lsmul_two_toAddSubgroup_prod_eq G H)).trans <|
    (QuotientAddGroup.prodAddEquiv _ _).trans
      ((bridgeModRangeNSMul G).symm.prodCongr (bridgeModRangeNSMul H).symm)

private theorem elementaryTwoQuotientProdAddEquiv_mk (p : G × H) :
    elementaryTwoQuotientProdAddEquiv G H (elementaryTwoQuotientMk p) =
      (elementaryTwoQuotientMk p.1, elementaryTwoQuotientMk p.2) := by
  simp only [elementaryTwoQuotientMk_eq_mkQ]
  rfl

/-- **The elementary-2 quotient of a product is the product of the elementary-2 quotients.** For
commutative groups `G` and `H`, the class map identifies `(G × H)/(G × H)²` with `G/G² × H/H²`
`ZMod 2`-linearly. It is transported from Mathlib's `QuotientAddGroup.prodAddEquiv` through the
identification of the `ModN` model of the quotient with the quotient by the doubling range. -/
noncomputable def elementaryTwoQuotientProdLinearEquiv (G H : Type*) [CommGroup G] [CommGroup H] :
    ElementaryTwoQuotient (G × H) ≃ₗ[ZMod 2]
      ElementaryTwoQuotient G × ElementaryTwoQuotient H :=
  { elementaryTwoQuotientProdAddEquiv G H with
    map_smul' := fun c x => ZMod.map_smul (elementaryTwoQuotientProdAddEquiv G H) c x }

/-- The product equivalence sends the class of `(a, b)` to the pair of classes. -/
@[simp] theorem elementaryTwoQuotientProdLinearEquiv_mk (G H : Type*) [CommGroup G] [CommGroup H]
    (p : G × H) :
    elementaryTwoQuotientProdLinearEquiv G H (elementaryTwoQuotientMk p) =
      (elementaryTwoQuotientMk p.1, elementaryTwoQuotientMk p.2) :=
  elementaryTwoQuotientProdAddEquiv_mk G H p

/-- The inverse product equivalence sends a pair of classes to the class of the pair. -/
@[simp] theorem elementaryTwoQuotientProdLinearEquiv_symm_mk (G H : Type*)
    [CommGroup G] [CommGroup H] (a : G) (b : H) :
    (elementaryTwoQuotientProdLinearEquiv G H).symm
        (elementaryTwoQuotientMk a, elementaryTwoQuotientMk b) =
      elementaryTwoQuotientMk (a, b) := by
  rw [LinearEquiv.symm_apply_eq, elementaryTwoQuotientProdLinearEquiv_mk]

/-- **The 2-rank is additive over products.** For commutative groups whose elementary-2 quotients
are finite-dimensional, `twoRank (G × H) = twoRank G + twoRank H`. -/
theorem twoRank_prod (G H : Type*) [CommGroup G] [CommGroup H]
    [Module.Finite (ZMod 2) (ElementaryTwoQuotient G)]
    [Module.Finite (ZMod 2) (ElementaryTwoQuotient H)] :
    twoRank (G × H) = twoRank G + twoRank H := by
  rw [twoRank_def, (elementaryTwoQuotientProdLinearEquiv G H).finrank_eq, Module.finrank_prod,
    ← twoRank_def, ← twoRank_def]

/-- The cardinality reading of `TauCeti.elementaryTwoQuotientProdLinearEquiv`:
`|(G × H)/(G × H)²| = |G/G²| · |H/H²|`. -/
theorem card_elementaryTwoQuotient_prod (G H : Type*) [CommGroup G] [CommGroup H] :
    Nat.card (ElementaryTwoQuotient (G × H)) =
      Nat.card (ElementaryTwoQuotient G) * Nat.card (ElementaryTwoQuotient H) := by
  rw [Nat.card_congr (elementaryTwoQuotientProdLinearEquiv G H).toEquiv, Nat.card_prod]

end Prod

section Pi

variable {ι : Type*} (G : ι → Type*) [∀ i, CommGroup (G i)]

/-- The indexed-product equivalence as an additive equivalence, transported from
`QuotientAddGroup.addEquivPiModRangeNSMulAddMonoidHom` through the bridge to the `ModN` model on
each factor. -/
private noncomputable def elementaryTwoQuotientPiAddEquiv :
    ElementaryTwoQuotient (∀ i, G i) ≃+ ∀ i, ElementaryTwoQuotient (G i) :=
  (bridgeModRangeNSMul (∀ i, G i)).trans <|
    (QuotientAddGroup.addEquivPiModRangeNSMulAddMonoidHom (fun i => Additive (G i)) 2).trans
      (AddEquiv.piCongrRight fun i => (bridgeModRangeNSMul (G i)).symm)

private theorem elementaryTwoQuotientPiAddEquiv_mk (g : ∀ i, G i) :
    elementaryTwoQuotientPiAddEquiv G (elementaryTwoQuotientMk g) =
      fun i => elementaryTwoQuotientMk (g i) := by
  funext i
  simp only [elementaryTwoQuotientMk_eq_mkQ]
  rfl

/-- **The elementary-2 quotient of an indexed product is the product of the elementary-2
quotients.** For a family of commutative groups `G i` over an arbitrary index, the class map
identifies `(∀ i, G i)/(…)²` with `∀ i, (G i)/(G i)²` `ZMod 2`-linearly. It is transported from
Mathlib's `QuotientAddGroup.addEquivPiModRangeNSMulAddMonoidHom` through the identification of the
`ModN` model of the quotient with the quotient by the doubling range. -/
noncomputable def elementaryTwoQuotientPiLinearEquiv :
    ElementaryTwoQuotient (∀ i, G i) ≃ₗ[ZMod 2] ∀ i, ElementaryTwoQuotient (G i) :=
  { elementaryTwoQuotientPiAddEquiv G with
    map_smul' := fun c x => ZMod.map_smul (elementaryTwoQuotientPiAddEquiv G) c x }

/-- The indexed-product equivalence sends the class of `g` to the family of componentwise
classes. -/
@[simp] theorem elementaryTwoQuotientPiLinearEquiv_mk (g : ∀ i, G i) :
    elementaryTwoQuotientPiLinearEquiv G (elementaryTwoQuotientMk g) =
      fun i => elementaryTwoQuotientMk (g i) :=
  elementaryTwoQuotientPiAddEquiv_mk G g

/-- The inverse indexed-product equivalence sends a family of componentwise classes to the class
of the assembled family. -/
@[simp] theorem elementaryTwoQuotientPiLinearEquiv_symm_mk (g : ∀ i, G i) :
    (elementaryTwoQuotientPiLinearEquiv G).symm (fun i => elementaryTwoQuotientMk (g i)) =
      elementaryTwoQuotientMk g := by
  rw [LinearEquiv.symm_apply_eq, elementaryTwoQuotientPiLinearEquiv_mk]

/-- **The 2-rank is additive over finite indexed products.** For a finite family of commutative
groups whose elementary-2 quotients are finite-dimensional,
`twoRank (∀ i, G i) = ∑ i, twoRank (G i)`. -/
theorem twoRank_pi [Fintype ι] [∀ i, Module.Finite (ZMod 2) (ElementaryTwoQuotient (G i))] :
    twoRank (∀ i, G i) = ∑ i, twoRank (G i) := by
  rw [twoRank_def, (elementaryTwoQuotientPiLinearEquiv G).finrank_eq, Module.finrank_pi_fintype]
  simp only [twoRank_def]

/-- The cardinality reading of `TauCeti.elementaryTwoQuotientPiLinearEquiv`:
`|(∀ i, G i)/(…)²| = ∏ i, |(G i)/(G i)²|`. -/
theorem card_elementaryTwoQuotient_pi [Fintype ι] :
    Nat.card (ElementaryTwoQuotient (∀ i, G i)) =
      ∏ i, Nat.card (ElementaryTwoQuotient (G i)) := by
  rw [Nat.card_congr (elementaryTwoQuotientPiLinearEquiv G).toEquiv, Nat.card_pi]

end Pi

end TauCeti
