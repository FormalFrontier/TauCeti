/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoxeterMatrix

public section

/-!
# The order of a product of two simple reflections

The product of the reflections in two roots `αᵢ`, `αⱼ` moves every weight inside the span of the
two roots, and its order is therefore read off the Cartan product `c = ⟨αᵢ, αⱼ^∨⟩⟨αⱼ, αᵢ^∨⟩`: the
values `1`, `2`, `3` give the orders `3`, `4`, `6`. This file proves that, and — for two simple
roots of a base of a finite crystallographic pairing, where `c = 0` is the remaining possibility
and gives the order `2` — that the entries of `TauCeti.coxeterMatrixOfBase` really are the orders
they are named for, so that the braid relations of the Coxeter presentation of a Weyl group hold in
the Weyl group.

The route is elementary and diagonalises nothing. Writing `g` for the product of the two
reflections, `g` fixes the common kernel of the two coroots pointwise, and on the two coroot
coordinates it acts with determinant `1` and trace `c - 2`. So `g` is annihilated by the cubic
`(X - 1)(X² - (c - 2)X + 1)`, which
`TauCeti.RootPairing.weylGroup.pow_add_three_ofIdx_mul_ofIdx_smul` states as a three-term
recursion for the iterates of `g`. Substituting `c = 1, 2, 3` and chasing the recursion a few steps
gives `g³ = 1`, `g⁴ = 1`, `g⁶ = 1`; the remaining value `c = 0` is the orthogonal case, already
settled in `TauCeti.LinearAlgebra.RootSystem.CoxeterMatrix`, where the two reflections commute, and
where the order is pinned to `2` only for two distinct simple roots of a base.

That the order is no smaller is checked on the single vector `αᵢ`: its `αᵢ^∨`-coordinate along the
orbit of `g` is a polynomial in `c`, and for the relevant powers that polynomial avoids the value
`⟨αᵢ, αᵢ^∨⟩ = 2`.

Everything before the last section is stated for an arbitrary pair of roots of an arbitrary root
pairing, the Cartan product entering only as a hypothesis on `RootPairing.pairing`; no finiteness,
crystallographic or reducedness assumption is used there. The last section specialises to a pair of
simple roots of a base, where `TauCeti.cartanMatrix_mul_cartanMatrix_mem_of_ne` confines the Cartan
product to `{0, 1, 2, 3}` and the case analysis closes.

## Main results

* `TauCeti.RootPairing.weylGroup.pow_add_three_ofIdx_mul_ofIdx_smul`: the three-term recursion
  satisfied by the iterates of a product of two reflections.
* `TauCeti.RootPairing.weylGroup.pow_three_ofIdx_mul_ofIdx_eq_one`,
  `TauCeti.RootPairing.weylGroup.pow_four_ofIdx_mul_ofIdx_eq_one`,
  `TauCeti.RootPairing.weylGroup.pow_six_ofIdx_mul_ofIdx_eq_one`: the braid relations at Cartan
  product `1`, `2`, `3`, and
  `TauCeti.RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_three`,
  `TauCeti.RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_four`,
  `TauCeti.RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_six`: the matching exact orders.
* `TauCeti.RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase`: **the entries of
  the Coxeter matrix of a base are the orders of the products of the corresponding simple
  reflections.**
* `TauCeti.RootPairing.weylGroup.pow_coxeterMatrixOfBase_ofIdx_mul_ofIdx_eq_one`: the braid
  relations of that Coxeter matrix hold in the Weyl group.

## References

This file supplies “the order of a product of two simple reflections” in Layer 2 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, the input the roadmap earmarks for the
braid relations of `weylCoxeterSystem`. The rank-two computation is Bourbaki, *Lie Groups and Lie
Algebras*, Chapters 4--6, Ch. VI, §1.3, and Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §9.
-/

namespace TauCeti

open Set

universe u v w x

namespace RootPairing.weylGroup

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (i j : ι)

/-! ## The rank-two computation -/

/-- **The product of two reflections on the weight space.** The two reflections move `x` inside the
span of the two roots, by an amount recorded by the two coroot functionals. -/
theorem ofIdx_mul_ofIdx_smul (x : M) :
    (_root_.RootPairing.weylGroup.ofIdx P i * _root_.RootPairing.weylGroup.ofIdx P j) • x =
      x - P.coroot' j x • P.root j -
        (P.coroot' i x - P.pairing j i * P.coroot' j x) • P.root i := by
  rw [mul_smul]
  simp only [_root_.RootPairing.weylGroup.ofIdx_smul, _root_.RootPairing.Equiv.reflection_smul,
    _root_.RootPairing.reflection_apply, map_sub, map_smul,
    _root_.RootPairing.root_coroot'_eq_pairing]
  module

/-- The `αᵢ^∨`-coordinate of the product of the reflections in `αᵢ` and `αⱼ`. -/
theorem coroot'_left_ofIdx_mul_ofIdx_smul (x : M) :
    P.coroot' i ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) • x) =
      P.pairing j i * P.coroot' j x - P.coroot' i x := by
  rw [ofIdx_mul_ofIdx_smul]
  simp only [map_sub, map_smul, smul_eq_mul, _root_.RootPairing.root_coroot'_eq_pairing,
    _root_.RootPairing.pairing_same]
  ring

/-- The `αⱼ^∨`-coordinate of the product of the reflections in `αᵢ` and `αⱼ`. Together with
`TauCeti.RootPairing.weylGroup.coroot'_left_ofIdx_mul_ofIdx_smul` this is the matrix of the action
on the two coroot coordinates: determinant `1` and trace `⟨αᵢ, αⱼ^∨⟩⟨αⱼ, αᵢ^∨⟩ - 2`. -/
theorem coroot'_right_ofIdx_mul_ofIdx_smul (x : M) :
    P.coroot' j ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) • x) =
      (P.pairing i j * P.pairing j i - 1) * P.coroot' j x - P.pairing i j * P.coroot' i x := by
  rw [ofIdx_mul_ofIdx_smul]
  simp only [map_sub, map_smul, smul_eq_mul, _root_.RootPairing.root_coroot'_eq_pairing,
    _root_.RootPairing.pairing_same]
  ring

/-- **The cubic annihilating a product of two reflections.** The product fixes the common kernel of
the two coroots and acts on the two coroot coordinates with determinant `1` and trace `c - 2`, so
it is annihilated by `(X - 1)(X² - (c - 2)X + 1)`. -/
theorem pow_three_ofIdx_mul_ofIdx_smul (x : M) :
    ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) ^ 3) • x =
      (P.pairing i j * P.pairing j i - 1) •
          (((_root_.RootPairing.weylGroup.ofIdx P i *
            _root_.RootPairing.weylGroup.ofIdx P j) ^ 2) • x) -
        (P.pairing i j * P.pairing j i - 1) •
          ((_root_.RootPairing.weylGroup.ofIdx P i *
            _root_.RootPairing.weylGroup.ofIdx P j) • x) + x := by
  have hA := ofIdx_mul_ofIdx_smul P i j
  set g := _root_.RootPairing.weylGroup.ofIdx P i * _root_.RootPairing.weylGroup.ofIdx P j
  have h2 : ∀ y : M, (g ^ 2) • y = g • (g • y) := fun y ↦ by rw [sq, mul_smul]
  have h3 : (g ^ 3) • x = g • (g • (g • x)) := by rw [pow_succ', mul_smul, h2]
  -- Unfold the three applications of `g`, expand the coroot functionals of the results, and
  -- compare the coefficients of `x`, `αᵢ` and `αⱼ` on the two sides.
  rw [h3, h2]
  simp only [hA, map_sub, map_smul, smul_eq_mul, _root_.RootPairing.root_coroot'_eq_pairing,
    _root_.RootPairing.pairing_same]
  module

/-- **The three-term recursion for the iterates of a product of two reflections**, obtained by
applying the annihilating cubic to `gⁿ • x`. This is the engine of every braid relation below. -/
theorem pow_add_three_ofIdx_mul_ofIdx_smul (n : ℕ) (x : M) :
    ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) ^ (n + 3)) • x =
      (P.pairing i j * P.pairing j i - 1) •
          (((_root_.RootPairing.weylGroup.ofIdx P i *
            _root_.RootPairing.weylGroup.ofIdx P j) ^ (n + 2)) • x) -
        (P.pairing i j * P.pairing j i - 1) •
          (((_root_.RootPairing.weylGroup.ofIdx P i *
            _root_.RootPairing.weylGroup.ofIdx P j) ^ (n + 1)) • x) +
        ((_root_.RootPairing.weylGroup.ofIdx P i *
          _root_.RootPairing.weylGroup.ofIdx P j) ^ n) • x := by
  set g := _root_.RootPairing.weylGroup.ofIdx P i * _root_.RootPairing.weylGroup.ofIdx P j
  have key : ∀ m : ℕ, (g ^ (n + m)) • x = (g ^ m) • ((g ^ n) • x) := fun m ↦ by
    rw [add_comm n m, pow_add, mul_smul]
  rw [key 3, key 2, key 1, pow_one]
  exact pow_three_ofIdx_mul_ofIdx_smul P i j ((g ^ n) • x)

/-! ## The braid relations -/

/-- **The braid relation at Cartan product `1`**: the product of the two reflections has order
dividing `3`, the `A₂` configuration. -/
theorem pow_three_ofIdx_mul_ofIdx_eq_one (h : P.pairing i j * P.pairing j i = 1) :
    (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 3 = 1 := by
  refine eq_one_of_smul_eq_self fun x ↦ ?_
  have h₀ := pow_add_three_ofIdx_mul_ofIdx_smul P i j 0 x
  rw [h] at h₀
  simp only [Nat.reduceAdd, pow_zero, one_smul, pow_one] at h₀
  rw [h₀]
  -- The remaining identity is linear over `R` in the two surviving iterates, which are generalised
  -- away because the weight space carries a second scalar action, by the Weyl group itself.
  generalize ((_root_.RootPairing.weylGroup.ofIdx P i *
    _root_.RootPairing.weylGroup.ofIdx P j) ^ 2) • x = y
  generalize (_root_.RootPairing.weylGroup.ofIdx P i *
    _root_.RootPairing.weylGroup.ofIdx P j) • x = z
  module

/-- **The braid relation at Cartan product `2`**: the product of the two reflections has order
dividing `4`, the `B₂` configuration. -/
theorem pow_four_ofIdx_mul_ofIdx_eq_one (h : P.pairing i j * P.pairing j i = 2) :
    (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 4 = 1 := by
  refine eq_one_of_smul_eq_self fun x ↦ ?_
  have h₀ := pow_add_three_ofIdx_mul_ofIdx_smul P i j 0 x
  have h₁ := pow_add_three_ofIdx_mul_ofIdx_smul P i j 1 x
  rw [h] at h₀ h₁
  simp only [Nat.reduceAdd, pow_zero, one_smul, pow_one] at h₀ h₁
  rw [h₁, h₀]
  -- The remaining identity is linear over `R` in the two surviving iterates, which are generalised
  -- away because the weight space carries a second scalar action, by the Weyl group itself.
  generalize ((_root_.RootPairing.weylGroup.ofIdx P i *
    _root_.RootPairing.weylGroup.ofIdx P j) ^ 2) • x = y
  generalize (_root_.RootPairing.weylGroup.ofIdx P i *
    _root_.RootPairing.weylGroup.ofIdx P j) • x = z
  module

/-- **The braid relation at Cartan product `3`**: the product of the two reflections has order
dividing `6`, the `G₂` configuration. -/
theorem pow_six_ofIdx_mul_ofIdx_eq_one (h : P.pairing i j * P.pairing j i = 3) :
    (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 6 = 1 := by
  refine eq_one_of_smul_eq_self fun x ↦ ?_
  have h₀ := pow_add_three_ofIdx_mul_ofIdx_smul P i j 0 x
  have h₁ := pow_add_three_ofIdx_mul_ofIdx_smul P i j 1 x
  have h₂ := pow_add_three_ofIdx_mul_ofIdx_smul P i j 2 x
  have h₃ := pow_add_three_ofIdx_mul_ofIdx_smul P i j 3 x
  rw [h] at h₀ h₁ h₂ h₃
  simp only [Nat.reduceAdd, pow_zero, one_smul, pow_one] at h₀ h₁ h₂ h₃
  rw [h₃, h₂, h₁, h₀]
  -- The remaining identity is linear over `R` in the two surviving iterates, which are generalised
  -- away because the weight space carries a second scalar action, by the Weyl group itself.
  generalize ((_root_.RootPairing.weylGroup.ofIdx P i *
    _root_.RootPairing.weylGroup.ofIdx P j) ^ 2) • x = y
  generalize (_root_.RootPairing.weylGroup.ofIdx P i *
    _root_.RootPairing.weylGroup.ofIdx P j) • x = z
  module

/-! ## The order is no smaller

The lower bounds are read off a single vector: the `αᵢ^∨`-coordinate of `gⁿ • αᵢ` is a polynomial
in the Cartan product `c`, and comparing it with `⟨αᵢ, αᵢ^∨⟩ = 2` rules out `gⁿ = 1`. -/

section LowerBound

private lemma pow_ne_one_of_coroot'_left_ne (n : ℕ)
    (h : P.coroot' i (((_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ n) • P.root i) ≠ 2) :
    (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ n ≠ 1 := by
  intro hpow
  rw [hpow, one_smul, _root_.RootPairing.root_coroot'_eq_pairing,
    _root_.RootPairing.pairing_same] at h
  exact h rfl

private lemma coroot'_left_smul_root :
    P.coroot' i ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) • P.root i) =
      P.pairing i j * P.pairing j i - 2 := by
  rw [coroot'_left_ofIdx_mul_ofIdx_smul]
  simp only [_root_.RootPairing.root_coroot'_eq_pairing, _root_.RootPairing.pairing_same]
  ring

private lemma coroot'_right_smul_root :
    P.coroot' j ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) • P.root i) =
      (P.pairing i j * P.pairing j i - 3) * P.pairing i j := by
  rw [coroot'_right_ofIdx_mul_ofIdx_smul]
  simp only [_root_.RootPairing.root_coroot'_eq_pairing, _root_.RootPairing.pairing_same]
  ring

private lemma coroot'_left_pow_two_smul_root :
    P.coroot' i (((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) ^ 2) • P.root i) =
      (P.pairing i j * P.pairing j i) ^ 2 - 4 * (P.pairing i j * P.pairing j i) + 2 := by
  rw [sq, mul_smul, coroot'_left_ofIdx_mul_ofIdx_smul, coroot'_left_smul_root,
    coroot'_right_smul_root]
  ring

private lemma coroot'_right_pow_two_smul_root :
    P.coroot' j (((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) ^ 2) • P.root i) =
      ((P.pairing i j * P.pairing j i) ^ 2 - 5 * (P.pairing i j * P.pairing j i) + 5) *
        P.pairing i j := by
  rw [sq, mul_smul, coroot'_right_ofIdx_mul_ofIdx_smul, coroot'_left_smul_root,
    coroot'_right_smul_root]
  ring

private lemma coroot'_left_pow_three_smul_root :
    P.coroot' i (((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) ^ 3) • P.root i) =
      (P.pairing i j * P.pairing j i) ^ 3 - 6 * (P.pairing i j * P.pairing j i) ^ 2 +
        9 * (P.pairing i j * P.pairing j i) - 2 := by
  rw [pow_succ', mul_smul, coroot'_left_ofIdx_mul_ofIdx_smul,
    coroot'_left_pow_two_smul_root, coroot'_right_pow_two_smul_root]
  ring

variable [CharZero R]

/-- **At Cartan product `1` the product of the two reflections has order exactly `3`.** -/
theorem orderOf_ofIdx_mul_ofIdx_eq_three (h : P.pairing i j * P.pairing j i = 1) :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) = 3 := by
  have hne : (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 1 ≠ 1 := by
    refine pow_ne_one_of_coroot'_left_ne P i j 1 ?_
    rw [pow_one, coroot'_left_smul_root, h]
    norm_num
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
    (pow_three_ofIdx_mul_ofIdx_eq_one P i j h) fun p hp hpd ↦ ?_
  have hp' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpd
  subst hp'
  exact hne

/-- **At Cartan product `2` the product of the two reflections has order exactly `4`.** -/
theorem orderOf_ofIdx_mul_ofIdx_eq_four (h : P.pairing i j * P.pairing j i = 2) :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) = 4 := by
  have hne : (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 2 ≠ 1 := by
    refine pow_ne_one_of_coroot'_left_ne P i j 2 ?_
    rw [coroot'_left_pow_two_smul_root, h]
    norm_num
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
    (pow_four_ofIdx_mul_ofIdx_eq_one P i j h) fun p hp hpd ↦ ?_
  have hp' : p = 2 := by
    have hpd' : p ∣ 2 ^ 2 := by simpa using hpd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd')
  subst hp'
  exact hne

/-- **At Cartan product `3` the product of the two reflections has order exactly `6`.** -/
theorem orderOf_ofIdx_mul_ofIdx_eq_six (h : P.pairing i j * P.pairing j i = 3) :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) = 6 := by
  have hne₂ : (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 2 ≠ 1 := by
    refine pow_ne_one_of_coroot'_left_ne P i j 2 ?_
    rw [coroot'_left_pow_two_smul_root, h]
    norm_num
  have hne₃ : (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 3 ≠ 1 := by
    refine pow_ne_one_of_coroot'_left_ne P i j 3 ?_
    rw [coroot'_left_pow_three_smul_root, h]
    norm_num
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
    (pow_six_ofIdx_mul_ofIdx_eq_one P i j h) fun p hp hpd ↦ ?_
  have hp' : p = 2 ∨ p = 3 := by
    have hpd' : p ∣ 2 * 3 := by simpa using hpd
    rcases (Nat.Prime.dvd_mul hp).mp hpd' with h' | h'
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')
  rcases hp' with rfl | rfl
  · exact hne₃
  · exact hne₂

end LowerBound

/-! ## The entries of the Coxeter matrix of a base -/

section Base

variable [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] (b : P.Base)

omit [Finite ι] [CharZero R] [IsDomain R] in
private lemma pairing_mul_pairing_eq_cast (k l : b.support) :
    P.pairing k l * P.pairing l k =
      ((b.cartanMatrix k l * b.cartanMatrix l k : ℤ) : R) := by
  have hk : ∀ m n : b.support, ((b.cartanMatrix m n : ℤ) : R) = P.pairing m n := fun m n ↦ by
    simpa using b.algebraMap_cartanMatrixIn_apply (S := ℤ) m n
  push_cast
  rw [hk, hk]

/-- **The entries of the Coxeter matrix of a base are the orders of the products of the
corresponding simple reflections.** On the diagonal both sides are `1`, a simple reflection being
an involution; off the diagonal the four Cartan products `0`, `1`, `2`, `3` give the four dihedral
orders `2`, `3`, `4`, `6`. -/
@[simp]
theorem orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase (k l : b.support) :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P (k : ι) *
      _root_.RootPairing.weylGroup.ofIdx P (l : ι)) = coxeterMatrixOfBase P b k l := by
  rcases eq_or_ne k l with rfl | hkl
  · rw [ofIdx_mul_self, orderOf_one]
    simp
  have hmem := cartanMatrix_mul_cartanMatrix_mem_of_ne P b hkl
  have hcast := pairing_mul_pairing_eq_cast P b k l
  simp only [mem_insert_iff, mem_singleton_iff] at hmem
  rcases hmem with hc | hc | hc | hc <;> rw [hc] at hcast <;> push_cast at hcast
  · have h₂ : coxeterMatrixOfBase P b k l = 2 := by
      rw [coxeterMatrixOfBase_apply, hc, coxeterOrder_zero]
    rw [h₂]
    exact orderOf_ofIdx_mul_ofIdx_eq_two_of_coxeterMatrixOfBase_eq_two P b h₂
  · rw [coxeterMatrixOfBase_apply, hc, coxeterOrder_one]
    exact orderOf_ofIdx_mul_ofIdx_eq_three P _ _ hcast
  · rw [coxeterMatrixOfBase_apply, hc, coxeterOrder_two]
    exact orderOf_ofIdx_mul_ofIdx_eq_four P _ _ hcast
  · rw [coxeterMatrixOfBase_apply, hc, coxeterOrder_three]
    exact orderOf_ofIdx_mul_ofIdx_eq_six P _ _ hcast

/-- **The braid relations of the Coxeter matrix of a base hold in the Weyl group.** This is the
relation half of the Coxeter presentation of the Weyl group. -/
theorem pow_coxeterMatrixOfBase_ofIdx_mul_ofIdx_eq_one (k l : b.support) :
    (_root_.RootPairing.weylGroup.ofIdx P (k : ι) *
      _root_.RootPairing.weylGroup.ofIdx P (l : ι)) ^ coxeterMatrixOfBase P b k l = 1 := by
  rw [← orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase P b k l, pow_orderOf_eq_one]

end Base

end RootPairing.weylGroup

end TauCeti
