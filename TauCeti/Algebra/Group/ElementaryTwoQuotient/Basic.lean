/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import TauCeti.Algebra.Group.PowMonoidHom

/-!
# The maximal elementary-2 quotient `G / G²` of a commutative group

For a commutative group `G`, the quotient by its subgroup of squares, `G / G²`, has every element
of order dividing `2`, so it is a vector space over `𝔽₂ = ZMod 2`. When `G` is finite its dimension
is the **2-rank** of `G`. This file develops that construction at the level of an arbitrary
commutative group; the genus-theory specialization to a class group lives in
`TauCeti.NumberTheory.ClassGroup.ElementaryTwoQuotient`, and the square-class group `Kˣ ⧸ (Kˣ)²` of
`TauCeti.FieldTheory.SquareClassGroup` is the same construction for `G = Kˣ`.

⚠ This quotient is the **maximal elementary-2 quotient** of `G`, *not* its 2-torsion subgroup
`{g | g² = 1}`. The two are different objects — a quotient and a subgroup — but for a finite group
they have the same cardinality, because the squaring endomorphism `g ↦ g²` has `G²` as its range and
the 2-torsion as its kernel, and a finite group has the same cardinality as the product of the range
and kernel of any endomorphism. We keep the two distinct in names and statements and record the
cardinality identity as `card_elementaryTwoQuotient_eq_card_twoTorsion`.

This file uses Mathlib's additive quotient `ModN (Additive G) 2` and adds multiplicative-square
names around it. The cardinality identity is still expressed through the squaring homomorphism
`powMonoidHom 2` and `Subgroup.index_range`.

## Main definitions and results

* `TauCeti.ElementaryTwoQuotient`: the quotient `G ⧸ G²`, a `ZMod 2`-module.
* `TauCeti.elementaryTwoQuotientMkAdd`, `TauCeti.elementaryTwoQuotientMk`, and
  `TauCeti.elementaryTwoQuotientMk_eq_zero_iff`: the quotient map and the class of an element,
  trivial iff the element is a square; `elementaryTwoQuotientMk_mul`,
  `elementaryTwoQuotientMk_one`, `elementaryTwoQuotientMk_inv`,
  `elementaryTwoQuotientMk_div`, `elementaryTwoQuotientMk_pow`, and
  `elementaryTwoQuotientMk_prod` record its additivity.
* `TauCeti.elementaryTwoQuotientMk_surjective` and `TauCeti.elementaryTwoQuotientMk_eq_iff`: the
  class map is surjective, and two elements have the same class iff they differ by a square.
* `TauCeti.elementaryTwoQuotientLiftEquiv` and `TauCeti.elementaryTwoQuotientLinearLiftEquiv`: the
  universal property for maps out of `G/G²`, inherited from `ModN.liftEquiv`.
* `TauCeti.elementaryTwoQuotientMap` and `TauCeti.elementaryTwoQuotientCongr`: transport along
  homomorphisms and equivalences of commutative groups.
* `TauCeti.elementaryTwoQuotientMap_apply_eq_self_of_isSquare_div`,
  `TauCeti.elementaryTwoQuotientMap_apply_eq_self_of_apply_eq_inv`, and
  `TauCeti.elementaryTwoQuotientCongr_apply_eq_self_of_apply_eq_inv`: inversion acts trivially on
  the elementary-2 quotient.
* `TauCeti.elementaryTwoQuotientEquivSquareQuotient`: the equivalence between Mathlib's `ModN`
  model and the quotient by the additive form of `G²`.
* `TauCeti.card_elementaryTwoQuotient_eq_index_square`: the quotient cardinality as the index of
  the subgroup of squares.
* `TauCeti.card_elementaryTwoQuotient_eq_card_twoTorsion`: `|G/G²| = |{g | g² = 1}|`.
* `TauCeti.twoRank` and `TauCeti.card_elementaryTwoQuotient_eq_two_pow_twoRank`: the 2-rank, with
  `|G/G²| = 2 ^ twoRank`, and `TauCeti.twoRank_eq_of_card_elementaryTwoQuotient_eq_two_pow` its
  inversion (`|G/G²| = 2 ^ n → twoRank G = n`).
* `TauCeti.card_elementaryTwoQuotient_of_odd_card` and `TauCeti.twoRank_of_odd_card`: a group of
  odd order has a single square class.
* `TauCeti.card_elementaryTwoQuotient_dvd_card` and
  `TauCeti.two_pow_twoRank_dvd_card`: the quotient cardinality and its rank form divide `|G|`.
-/

public section

namespace TauCeti

variable (G : Type*) [CommGroup G]

/-- **The maximal elementary-2 quotient `G / G²`** of a commutative group, written additively on
`Additive G`. -/
abbrev ElementaryTwoQuotient : Type _ :=
  ModN (Additive G) 2

instance [Finite G] : Finite (ElementaryTwoQuotient G) :=
  Finite.of_surjective _ (QuotientAddGroup.mk'_surjective _)

variable {G}

/-- The quotient homomorphism `Additive G →+ G/G²`, exposed in the `ModN` additive form. -/
def elementaryTwoQuotientMkAdd : Additive G →+ ElementaryTwoQuotient G :=
  ModN.mkQ 2

/-- The class of an element of `G` in the maximal elementary-2 quotient `G / G²`. -/
def elementaryTwoQuotientMk (g : G) : ElementaryTwoQuotient G :=
  elementaryTwoQuotientMkAdd (Additive.ofMul g)

/-- The class map `G → G/G²` is the quotient map of the `ModN` model: the class of `g` is the image
of `Additive.ofMul g` under the quotient by the doubling submodule. This exposes the `ModN`
representative so downstream files can match `G/G²` against Mathlib's quotient-by-range API. -/
theorem elementaryTwoQuotientMk_eq_mkQ (g : G) :
    elementaryTwoQuotientMk g = Submodule.Quotient.mk (Additive.ofMul g) := by
  rw [elementaryTwoQuotientMk, elementaryTwoQuotientMkAdd, ModN.mkQ]
  rfl

/-- An element of `Additive G` lies in the doubling submodule `range (lsmul ℤ _ 2)` iff its
multiplicative form is a square. This is the shared core relating the `ModN`/`lsmul` model of the
quotient to the multiplicative subgroup of squares, used both by the zero-characterization and by
the subgroup identification, and is kept private to the file. -/
private theorem mem_range_lsmul_two_iff (a : Additive G) :
    a ∈ LinearMap.range (LinearMap.lsmul ℤ (Additive G) ↑(2 : ℕ)) ↔
      IsSquare (Additive.toMul a) := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨Additive.toMul b, ?_⟩
    have hmul := congr_arg Additive.toMul hb
    simpa [toMul_zsmul, zpow_two, pow_two] using hmul.symm
  · rintro ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    apply Additive.toMul.injective
    simpa [toMul_zsmul, zpow_two, pow_two] using hb.symm

/-- An element has trivial class in `G / G²` iff it is a square. -/
@[simp] theorem elementaryTwoQuotientMk_eq_zero_iff (g : G) :
    elementaryTwoQuotientMk g = 0 ↔ IsSquare g := by
  -- `elementaryTwoQuotientMk g = ModN.mkQ 2 (ofMul g)` is the quotient map of `ofMul g`, so it
  -- vanishes iff `ofMul g` lies in the doubling subgroup `range (lsmul ℤ _ 2)`.
  rw [elementaryTwoQuotientMk, elementaryTwoQuotientMkAdd, ModN.mkQ]
  simp only [AddMonoidHom.coe_coe, Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_range_lsmul_two_iff (Additive.ofMul g)

/-- The universal property of `G/G²` for additive homomorphisms: maps out of the quotient are
additive homomorphisms from `Additive G` whose values are killed by `2`. -/
protected def elementaryTwoQuotientLiftEquiv [AddMonoid M] :
    (ElementaryTwoQuotient G →+ M) ≃
      {φ : Additive G →+ M // ∀ g, 2 • φ g = 0} :=
  ModN.liftEquiv

/-- The universal property of `G/G²` for `ZMod 2`-linear maps: linear maps out of the quotient are
additive homomorphisms from `Additive G` whose values are killed by `2`. -/
protected def elementaryTwoQuotientLinearLiftEquiv [AddCommGroup H] [Module (ZMod 2) H] :
    (ElementaryTwoQuotient G →ₗ[ZMod 2] H) ≃
      {φ : Additive G →+ H // ∀ g, 2 • φ g = 0} :=
  ModN.liftEquiv'

/-- The class map to `G / G²` sends a product to the sum of the classes. -/
@[simp] theorem elementaryTwoQuotientMk_mul (g h : G) :
    elementaryTwoQuotientMk (g * h) = elementaryTwoQuotientMk g + elementaryTwoQuotientMk h := by
  simp only [elementaryTwoQuotientMk, ofMul_mul, AddMonoidHom.map_add]

/-- The class map to `G / G²` sends `1` to `0`. -/
@[simp] theorem elementaryTwoQuotientMk_one : elementaryTwoQuotientMk (1 : G) = 0 := by
  simp only [elementaryTwoQuotientMk, ofMul_one, AddMonoidHom.map_zero]

/-- The class map to `G / G²` sends inverses to negatives. -/
@[simp] theorem elementaryTwoQuotientMk_inv (g : G) :
    elementaryTwoQuotientMk g⁻¹ = -elementaryTwoQuotientMk g := by
  simp only [elementaryTwoQuotientMk, ofMul_inv, map_neg]

/-- The class map to `G / G²` sends quotients to differences. -/
@[simp] theorem elementaryTwoQuotientMk_div (g h : G) :
    elementaryTwoQuotientMk (g / h) = elementaryTwoQuotientMk g - elementaryTwoQuotientMk h := by
  simp only [elementaryTwoQuotientMk, ofMul_div, map_sub]

/-- The class map to `G / G²` sends powers to scalar multiples. -/
@[simp] theorem elementaryTwoQuotientMk_pow (g : G) (n : ℕ) :
    elementaryTwoQuotientMk (g ^ n) = n • elementaryTwoQuotientMk g := by
  simp only [elementaryTwoQuotientMk, ofMul_pow, map_nsmul]

/-- The class map to `G / G²` sends a finite product to the sum of the classes. -/
theorem elementaryTwoQuotientMk_prod {ι : Type*} (S : Finset ι) (g : ι → G) :
    elementaryTwoQuotientMk (∏ i ∈ S, g i) = ∑ i ∈ S, elementaryTwoQuotientMk (g i) := by
  simp only [elementaryTwoQuotientMk, ofMul_prod]
  rw [map_sum]

/-- Every element of `G / G²` is the class of some element of `G`. -/
theorem elementaryTwoQuotientMk_surjective :
    Function.Surjective (elementaryTwoQuotientMk : G → ElementaryTwoQuotient G) := by
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Additive.toMul a, rfl⟩

/-- Two elements have the same class in `G / G²` iff they differ by a square. -/
theorem elementaryTwoQuotientMk_eq_iff (g h : G) :
    elementaryTwoQuotientMk g = elementaryTwoQuotientMk h ↔ IsSquare (g / h) := by
  rw [← elementaryTwoQuotientMk_eq_zero_iff, elementaryTwoQuotientMk_div, sub_eq_zero]

variable {H : Type*} [CommGroup H]

/-- A homomorphism of commutative groups induces a `ZMod 2`-linear map on maximal elementary-2
quotients. -/
noncomputable def elementaryTwoQuotientMap (f : G →* H) :
    ElementaryTwoQuotient G →ₗ[ZMod 2] ElementaryTwoQuotient H :=
  (TauCeti.elementaryTwoQuotientLinearLiftEquiv (G := G) (H := ElementaryTwoQuotient H)).symm
    ⟨{ toFun := fun g => elementaryTwoQuotientMk (f (Additive.toMul g))
       map_zero' := by
        -- The source is written additively as `Additive G`; expose its multiplicative zero.
        change elementaryTwoQuotientMk (f 1) = 0
        simp
       map_add' := by
        intro g h
        -- The source addition is multiplication in `G`, so the quotient map is additive.
        change elementaryTwoQuotientMk (f (Additive.toMul (g + h))) =
          elementaryTwoQuotientMk (f (Additive.toMul g)) +
            elementaryTwoQuotientMk (f (Additive.toMul h))
        simp },
      fun g => by
        -- `G/G²` is killed by `2` because the square of any representative maps to zero.
        change 2 • elementaryTwoQuotientMk (f (Additive.toMul g)) = 0
        rw [← elementaryTwoQuotientMk_pow]
        exact (elementaryTwoQuotientMk_eq_zero_iff _).2
          ⟨f (Additive.toMul g), by rw [pow_two]⟩⟩

/-- The induced map on `G/G²` sends the class of `g` to the class of `f g`. -/
@[simp] theorem elementaryTwoQuotientMap_mk (f : G →* H) (g : G) :
    elementaryTwoQuotientMap f (elementaryTwoQuotientMk g) =
      elementaryTwoQuotientMk (f g) := by
  rfl

/-- The map induced by the identity homomorphism fixes each class in the elementary-2 quotient. -/
@[simp] theorem elementaryTwoQuotientMap_id_apply (x : ElementaryTwoQuotient G) :
    elementaryTwoQuotientMap (MonoidHom.id G) x = x := by
  obtain ⟨g, rfl⟩ := elementaryTwoQuotientMk_surjective (G := G) x
  simp

/-- A group endomorphism induces the identity on the maximal elementary-2 quotient if it sends
each element to the same square class. -/
theorem elementaryTwoQuotientMap_apply_eq_self_of_isSquare_div (f : G →* G)
    (hf : ∀ g, IsSquare (f g / g)) (x : ElementaryTwoQuotient G) :
    elementaryTwoQuotientMap f x = x := by
  obtain ⟨g, rfl⟩ := elementaryTwoQuotientMk_surjective (G := G) x
  rw [elementaryTwoQuotientMap_mk]
  exact (elementaryTwoQuotientMk_eq_iff _ _).2 (hf g)

/-- A group endomorphism that acts pointwise by inversion induces the identity on the maximal
elementary-2 quotient. This is the abstract step used when quadratic conjugation acts on an ideal
class group by inversion. -/
theorem elementaryTwoQuotientMap_apply_eq_self_of_apply_eq_inv (f : G →* G)
    (hf : ∀ g, f g = g⁻¹) (x : ElementaryTwoQuotient G) :
    elementaryTwoQuotientMap f x = x := by
  apply elementaryTwoQuotientMap_apply_eq_self_of_isSquare_div f _ x
  intro g
  refine ⟨g⁻¹, ?_⟩
  rw [hf, div_eq_mul_inv]

variable {K : Type*} [CommGroup K]

/-- Induced maps on elementary-2 quotients compose pointwise. -/
@[simp] theorem elementaryTwoQuotientMap_comp_apply (f : G →* H) (g : H →* K)
    (x : ElementaryTwoQuotient G) :
    elementaryTwoQuotientMap (g.comp f) x =
      elementaryTwoQuotientMap g (elementaryTwoQuotientMap f x) := by
  obtain ⟨a, rfl⟩ := elementaryTwoQuotientMk_surjective (G := G) x
  simp

/-- A multiplicative equivalence of commutative groups induces a `ZMod 2`-linear equivalence of
their maximal elementary-2 quotients. -/
noncomputable def elementaryTwoQuotientCongr (e : G ≃* H) :
    ElementaryTwoQuotient G ≃ₗ[ZMod 2] ElementaryTwoQuotient H where
  toLinearMap := elementaryTwoQuotientMap e.toMonoidHom
  invFun := elementaryTwoQuotientMap e.symm.toMonoidHom
  left_inv x := by
    obtain ⟨g, rfl⟩ := elementaryTwoQuotientMk_surjective (G := G) x
    simp
  right_inv x := by
    obtain ⟨h, rfl⟩ := elementaryTwoQuotientMk_surjective (G := H) x
    simp

/-- The induced equivalence on `G/G²` sends the class of `g` to the class of `e g`. -/
@[simp] theorem elementaryTwoQuotientCongr_mk (e : G ≃* H) (g : G) :
    elementaryTwoQuotientCongr e (elementaryTwoQuotientMk g) = elementaryTwoQuotientMk (e g) := by
  exact elementaryTwoQuotientMap_mk e.toMonoidHom g

/-- The inverse induced equivalence on `G/G²` sends the class of `h` to the class of `e.symm h`. -/
@[simp] theorem elementaryTwoQuotientCongr_symm_mk (e : G ≃* H) (h : H) :
    (elementaryTwoQuotientCongr e).symm (elementaryTwoQuotientMk h) =
      elementaryTwoQuotientMk (e.symm h) := by
  exact elementaryTwoQuotientMap_mk e.symm.toMonoidHom h

/-- The identity equivalence induces the identity equivalence on the elementary-2 quotient. -/
@[simp] theorem elementaryTwoQuotientCongr_refl_apply (x : ElementaryTwoQuotient G) :
    elementaryTwoQuotientCongr (MulEquiv.refl G) x = x :=
  elementaryTwoQuotientMap_id_apply x

/-- Induced equivalences on elementary-2 quotients compose functorially. -/
@[simp] theorem elementaryTwoQuotientCongr_trans_apply (e : G ≃* H) (e' : H ≃* K)
    (x : ElementaryTwoQuotient G) :
    elementaryTwoQuotientCongr (e.trans e') x =
      elementaryTwoQuotientCongr e' (elementaryTwoQuotientCongr e x) :=
  elementaryTwoQuotientMap_comp_apply e.toMonoidHom e'.toMonoidHom x

/-- A multiplicative automorphism that acts pointwise by inversion induces the identity on the
maximal elementary-2 quotient. In genus theory this applies to the action of quadratic
conjugation on `Cl(K)/Cl(K)²`. -/
theorem elementaryTwoQuotientCongr_apply_eq_self_of_apply_eq_inv (e : G ≃* G)
    (he : ∀ g, e g = g⁻¹) (x : ElementaryTwoQuotient G) :
    elementaryTwoQuotientCongr e x = x :=
  elementaryTwoQuotientMap_apply_eq_self_of_apply_eq_inv e.toMonoidHom he x

variable (G)

/-- The doubling subgroup of `Additive G` is the additive form of the subgroup of squares of `G`.
This is the implementation detail relating the `ModN`/`lsmul` model of the quotient to the
multiplicative subgroup of squares, and is kept private to the file. -/
private theorem range_lsmul_two_toAddSubgroup_eq_square_toAddSubgroup :
    (LinearMap.range (LinearMap.lsmul ℤ (Additive G) ↑(2 : ℕ))).toAddSubgroup =
      (Subgroup.square G).toAddSubgroup := by
  ext g
  rw [Submodule.mem_toAddSubgroup, mem_range_lsmul_two_iff, Additive.mem_toAddSubgroup,
    Subgroup.mem_square]

/-- Mathlib's `ModN (Additive G) 2` model of `G/G²` agrees with the direct quotient by the
additive form of the square subgroup. -/
noncomputable def elementaryTwoQuotientEquivSquareQuotient :
    ElementaryTwoQuotient G ≃+ Additive G ⧸ (Subgroup.square G).toAddSubgroup :=
  QuotientAddGroup.congr _ _ (AddEquiv.refl (Additive G)) <| by
    simpa using range_lsmul_two_toAddSubgroup_eq_square_toAddSubgroup G

/-- The cardinality of `G/G²` is the index of the subgroup of squares. -/
theorem card_elementaryTwoQuotient_eq_index_square :
    Nat.card (ElementaryTwoQuotient G) = (Subgroup.square G).index := by
  calc
    Nat.card (ElementaryTwoQuotient G)
        = Nat.card (Additive G ⧸ (Subgroup.square G).toAddSubgroup) :=
            Nat.card_congr (elementaryTwoQuotientEquivSquareQuotient (G := G)).toEquiv
    _ = (Subgroup.square G).index := by
          rw [← AddSubgroup.index_eq_card, Subgroup.index_toAddSubgroup]

/-- **The maximal elementary-2 quotient and the 2-torsion subgroup have the same cardinality.**
`|G/G²| = |{g | g² = 1}|`. The squaring endomorphism `g ↦ g²` has range `G²` and kernel the
2-torsion; when its kernel has finite index, the index of the range equals the cardinality of the
kernel. -/
theorem card_elementaryTwoQuotient_eq_card_twoTorsion
    [(powMonoidHom 2 : G →* G).ker.FiniteIndex] :
    Nat.card (ElementaryTwoQuotient G) = Nat.card {g : G // g ^ 2 = 1} := by
  rw [card_elementaryTwoQuotient_eq_index_square, square_eq_powMonoidHom_two_range,
    Subgroup.index_range]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [MonoidHom.mem_ker])

/-- **The 2-rank of a commutative group**: the `ZMod 2`-dimension of the maximal elementary-2
quotient `G / G²` (zero, by convention of `Module.finrank`, when the quotient is
infinite-dimensional). -/
@[expose] noncomputable def twoRank : ℕ :=
  Module.finrank (ZMod 2) (ElementaryTwoQuotient G)

/-- The 2-rank of `G` is the `ZMod 2` dimension of its maximal elementary-2 quotient `G / G²`. -/
@[simp] theorem twoRank_def :
    twoRank G = Module.finrank (ZMod 2) (ElementaryTwoQuotient G) := rfl

/-- The maximal elementary-2 quotient has cardinality `2 ^ twoRank`: it is a finite `𝔽₂`-vector
space of dimension the 2-rank. -/
theorem card_elementaryTwoQuotient_eq_two_pow_twoRank
    [Module.Finite (ZMod 2) (ElementaryTwoQuotient G)] :
    Nat.card (ElementaryTwoQuotient G) = 2 ^ twoRank G := by
  rw [twoRank, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

/-- Reading the 2-rank off a cardinality computation: if `G/G²` has `2 ^ n` elements, the 2-rank
of `G` is `n`. This is the inversion of
`TauCeti.card_elementaryTwoQuotient_eq_two_pow_twoRank` used to convert each concrete counting
result into its rank form. The hypothesis already forces `G/G²` to be a finite `ZMod 2`-module,
so no finiteness instance need be supplied. -/
theorem twoRank_eq_of_card_elementaryTwoQuotient_eq_two_pow
    {n : ℕ} (h : Nat.card (ElementaryTwoQuotient G) = 2 ^ n) : twoRank G = n := by
  have : Finite (ElementaryTwoQuotient G) := Nat.finite_of_card_ne_zero (by simp [h])
  rw [card_elementaryTwoQuotient_eq_two_pow_twoRank] at h
  exact Nat.pow_right_injective le_rfl h

/-- **A group of odd order has a single square class.** For a finite commutative group of odd
order, squaring is bijective (the exponent `2` is coprime to `|G|`), so `G/G²` is trivial. This
is the odd-order half of the 2-rank computation — the even case genuinely needs more structure
(a cyclic factor); this half holds for any commutative group. -/
theorem card_elementaryTwoQuotient_of_odd_card (h : Odd (Nat.card G)) :
    Nat.card (ElementaryTwoQuotient G) = 1 := by
  rw [card_elementaryTwoQuotient_eq_index_square, square_eq_powMonoidHom_two_range]
  have hbij : Function.Surjective (powMonoidHom 2 : G →* G) :=
    (Nat.Coprime.pow_left_bijective (Nat.coprime_two_right.mpr h)).surjective
  rw [MonoidHom.range_eq_top.mpr hbij, Subgroup.index_top]

/-- A group of odd order has 2-rank zero. -/
theorem twoRank_of_odd_card (h : Odd (Nat.card G)) : twoRank G = 0 :=
  twoRank_eq_of_card_elementaryTwoQuotient_eq_two_pow G
    ((card_elementaryTwoQuotient_of_odd_card G h).trans (pow_zero 2).symm)

/-- The cardinality of the maximal elementary-2 quotient of a commutative group divides the group
cardinality. -/
theorem card_elementaryTwoQuotient_dvd_card :
    Nat.card (ElementaryTwoQuotient G) ∣ Nat.card G := by
  rw [card_elementaryTwoQuotient_eq_index_square]
  exact Subgroup.index_dvd_card (Subgroup.square G)

/-- Rank form of `TauCeti.card_elementaryTwoQuotient_dvd_card`: when `G / G²` is a finite
`ZMod 2`-vector space, `2 ^ TauCeti.twoRank G` divides `|G|`. -/
theorem two_pow_twoRank_dvd_card [Module.Finite (ZMod 2) (ElementaryTwoQuotient G)] :
    2 ^ twoRank G ∣ Nat.card G := by
  rw [← card_elementaryTwoQuotient_eq_two_pow_twoRank]
  exact card_elementaryTwoQuotient_dvd_card G

section FiniteCardinality

variable [Finite G]

/-- The maximal elementary-2 quotient of a finite commutative group has cardinality at most the
group cardinality. -/
theorem card_elementaryTwoQuotient_le_card :
    Nat.card (ElementaryTwoQuotient G) ≤ Nat.card G :=
  Nat.le_of_dvd Nat.card_pos (card_elementaryTwoQuotient_dvd_card G)

/-- Rank form of `TauCeti.card_elementaryTwoQuotient_le_card`: for a finite commutative group
`G`, `2 ^ TauCeti.twoRank G` is at most `|G|`. -/
theorem two_pow_twoRank_le_card :
    2 ^ twoRank G ≤ Nat.card G := by
  rw [← card_elementaryTwoQuotient_eq_two_pow_twoRank]
  exact card_elementaryTwoQuotient_le_card G

end FiniteCardinality

/-- Multiplicatively equivalent commutative groups have elementary-2 quotients with the same
`ZMod 2` finrank. -/
theorem finrank_elementaryTwoQuotient_eq_of_mulEquiv (e : G ≃* H) :
    Module.finrank (ZMod 2) (ElementaryTwoQuotient G) =
      Module.finrank (ZMod 2) (ElementaryTwoQuotient H) :=
  (elementaryTwoQuotientCongr e).finrank_eq

/-- Multiplicatively equivalent commutative groups have the same elementary-2 rank. -/
theorem twoRank_eq_of_mulEquiv (e : G ≃* H) : twoRank G = twoRank H :=
  finrank_elementaryTwoQuotient_eq_of_mulEquiv (G := G) (H := H) e

end TauCeti
