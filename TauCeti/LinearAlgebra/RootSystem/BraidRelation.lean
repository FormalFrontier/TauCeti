/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoxeterMatrix

public section

/-!
# The order of a product of two simple reflections

The product of the reflections in two roots `αᵢ`, `αⱼ` changes every weight by an element of the
span of the two roots, and its order is therefore read off the Cartan product
`c = ⟨αᵢ, αⱼ^∨⟩⟨αⱼ, αᵢ^∨⟩`: the values `1`, `2`, `3` give the orders `3`, `4`, `6`. This file
proves that, and — for two simple roots of a base of a finite crystallographic pairing, where
`c = 0` is the remaining possibility and gives the order `2` — that the entries of
`TauCeti.coxeterMatrixOfBase` really are the orders they are named for, so that the braid relations
of the Coxeter presentation of a Weyl group hold in the Weyl group.

The iterates of the product are supplied by Mathlib's
`Module.reflection_mul_reflection_pow_apply` and `Module.reflection_mul_reflection_pow_apply_self`,
which express `(r₁r₂)ⁿ` over an arbitrary commutative ring through the Chebyshev `S`-polynomials
(`Polynomial.Chebyshev.S`) evaluated at `t = c - 2`;
`TauCeti.RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul` and
`TauCeti.RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul_root` are those formulas for a product of
two reflections of a root pairing, read as elements of the Weyl group. Substituting `c = 1, 2, 3`,
that is `t = -1, 0, 1`, makes the two Chebyshev coefficients of the general formula vanish at the
exponents `3`, `4`, `6`, which gives `g³ = 1`, `g⁴ = 1`, `g⁶ = 1`; the remaining value `c = 0` is
the orthogonal case, already settled in `TauCeti.LinearAlgebra.RootSystem.CoxeterMatrix`, where the
two reflections commute, and where the order is pinned to `2` only for two distinct simple roots of
a base.

That the order is no smaller is checked on the single vector `αᵢ`: its `αᵢ^∨`-coordinate along the
orbit of `g` is again a Chebyshev expression in `c`, and for the relevant powers that expression
avoids the value `⟨αᵢ, αᵢ^∨⟩ = 2`.

Everything before the last section is stated for an arbitrary pair of roots of an arbitrary root
pairing, the Cartan product entering only as a hypothesis on `RootPairing.pairing`; no finiteness,
crystallographic or reducedness assumption is used there. The last section specialises to a pair of
simple roots of a base, where `TauCeti.cartanMatrix_mul_cartanMatrix_mem_of_ne` confines the Cartan
product to `{0, 1, 2, 3}` and the case analysis closes.

## Main results

* `TauCeti.RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul` and
  `TauCeti.RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul_root`: the iterates of a product of two
  reflections, acting on a weight and on the first of the two roots.
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

open Set Polynomial.Chebyshev

universe u v w x

namespace RootPairing.weylGroup

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (i j : ι)

/-! ## The rank-two computation -/

/-- **The product of two reflections on the weight space.** The product changes `x` by an element
of the span of the two roots, with coefficients recorded by the two coroot functionals. -/
@[grind =]
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
@[grind =]
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
on the two coroot coordinates: determinant `1` and trace `⟨αᵢ, αⱼ^∨⟩⟨αⱼ, αᵢ^∨⟩ - 2`, the value at
which `TauCeti.RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul` evaluates its Chebyshev
polynomials. -/
@[grind =]
theorem coroot'_right_ofIdx_mul_ofIdx_smul (x : M) :
    P.coroot' j ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) • x) =
      (P.pairing i j * P.pairing j i - 1) * P.coroot' j x - P.pairing i j * P.coroot' i x := by
  rw [ofIdx_mul_ofIdx_smul]
  simp only [map_sub, map_smul, smul_eq_mul, _root_.RootPairing.root_coroot'_eq_pairing,
    _root_.RootPairing.pairing_same]
  ring

/-- The action of an iterate of the product of the two reflections is the action of the
corresponding iterate of the product of the two linear reflections. -/
private lemma pow_ofIdx_mul_ofIdx_smul_eq (n : ℕ) (x : M) :
    ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) ^ n) • x =
      ((P.reflection i * P.reflection j) ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, pow_succ', LinearEquiv.mul_apply, mul_smul]
    simp [_root_.RootPairing.reflection_apply]

/-- **The iterates of a product of two reflections.** This is Mathlib's
`Module.reflection_mul_reflection_pow_apply` for the reflections in two roots `αᵢ`, `αⱼ` of a root
pairing, read in the Weyl group; its Chebyshev polynomials are evaluated at the Cartan product
shifted by `2`, that is at `t = ⟨αᵢ, αⱼ^∨⟩⟨αⱼ, αᵢ^∨⟩ - 2`. -/
theorem pow_ofIdx_mul_ofIdx_smul (n : ℕ) (x : M)
    (t : R := P.pairing i j * P.pairing j i - 2)
    (ht : t = P.pairing i j * P.pairing j i - 2 := by rfl) :
    ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) ^ n) • x =
      x +
        ((S R ((n - 2) / 2)).eval t * ((S R ((n - 1) / 2)).eval t + (S R ((n - 3) / 2)).eval t)) •
          ((P.pairing i j * P.coroot' i x - P.coroot' j x) • P.root j - P.coroot' i x • P.root i) +
        ((S R ((n - 1) / 2)).eval t * ((S R (n / 2)).eval t + (S R ((n - 2) / 2)).eval t)) •
          ((P.pairing j i * P.coroot' j x - P.coroot' i x) • P.root i -
            P.coroot' j x • P.root j) := by
  rw [pow_ofIdx_mul_ofIdx_smul_eq]
  exact Module.reflection_mul_reflection_pow_apply (P.coroot_root_two i) (P.coroot_root_two j) n x t
    (by rw [ht, _root_.RootPairing.root_coroot'_eq_pairing,
      _root_.RootPairing.root_coroot'_eq_pairing]; ring)

/-- **The iterates of a product of two reflections on the first of the two roots.** This is
Mathlib's `Module.reflection_mul_reflection_pow_apply_self` read in the Weyl group; it is the case
`x = αᵢ` of `TauCeti.RootPairing.weylGroup.pow_ofIdx_mul_ofIdx_smul`, in a form where the two
coefficients are single Chebyshev values. -/
theorem pow_ofIdx_mul_ofIdx_smul_root (n : ℕ)
    (t : R := P.pairing i j * P.pairing j i - 2)
    (ht : t = P.pairing i j * P.pairing j i - 2 := by rfl) :
    ((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) ^ n) • P.root i =
      ((S R n).eval t + (S R (n - 1)).eval t) • P.root i +
        ((S R (n - 1)).eval t * -P.pairing i j) • P.root j := by
  rw [pow_ofIdx_mul_ofIdx_smul_eq]
  exact Module.reflection_mul_reflection_pow_apply_self (P.coroot_root_two i)
    (P.coroot_root_two j) n t
    (by rw [ht, _root_.RootPairing.root_coroot'_eq_pairing,
      _root_.RootPairing.root_coroot'_eq_pairing]; ring)

/-! ## The braid relations -/

/-- **The braid relation at Cartan product `1`**: the product of the two reflections has order
dividing `3`, the `A₂` configuration. -/
@[simp, grind =]
theorem pow_three_ofIdx_mul_ofIdx_eq_one (h : P.pairing i j * P.pairing j i = 1) :
    (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 3 = 1 := by
  refine eq_one_of_smul_eq_self fun x ↦ ?_
  -- At `t = -1` the coefficients of the two displacement terms are `S₀(t)(S₁(t) + S₀(t)) = 0`
  -- and `S₁(t)(S₁(t) + S₀(t)) = 0`.
  rw [pow_ofIdx_mul_ofIdx_smul P i j 3 x (-1) (by rw [h]; ring)]
  norm_num [S_zero, S_one]

/-- **The braid relation at Cartan product `2`**: the product of the two reflections has order
dividing `4`, the `B₂` configuration. -/
@[simp, grind =]
theorem pow_four_ofIdx_mul_ofIdx_eq_one (h : P.pairing i j * P.pairing j i = 2) :
    (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 4 = 1 := by
  refine eq_one_of_smul_eq_self fun x ↦ ?_
  -- At `t = 0` both coefficients carry the factor `S₁(t) = t = 0`.
  rw [pow_ofIdx_mul_ofIdx_smul P i j 4 x 0 (by rw [h]; ring)]
  norm_num [S_zero, S_one]

/-- **The braid relation at Cartan product `3`**: the product of the two reflections has order
dividing `6`, the `G₂` configuration. -/
@[simp, grind =]
theorem pow_six_ofIdx_mul_ofIdx_eq_one (h : P.pairing i j * P.pairing j i = 3) :
    (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 6 = 1 := by
  refine eq_one_of_smul_eq_self fun x ↦ ?_
  -- At `t = 1` both coefficients carry the factor `S₂(t) = t² - 1 = 0`.
  rw [pow_ofIdx_mul_ofIdx_smul P i j 6 x 1 (by rw [h]; ring)]
  norm_num [S_two]

/-! ## The order is no smaller

The lower bounds are read off a single vector: the `αᵢ^∨`-coordinate of `gⁿ • αᵢ` is a Chebyshev
expression in the Cartan product `c`, and comparing it with `⟨αᵢ, αᵢ^∨⟩ = 2` rules out `gⁿ = 1`. -/

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

private lemma coroot'_left_pow_smul_root (n : ℕ) (t : R)
    (ht : t = P.pairing i j * P.pairing j i - 2) :
    P.coroot' i (((_root_.RootPairing.weylGroup.ofIdx P i *
        _root_.RootPairing.weylGroup.ofIdx P j) ^ n) • P.root i) =
      2 * ((S R n).eval t + (S R (n - 1)).eval t) -
        (S R (n - 1)).eval t * (P.pairing i j * P.pairing j i) := by
  rw [pow_ofIdx_mul_ofIdx_smul_root P i j n t ht]
  simp only [map_add, map_smul, smul_eq_mul, _root_.RootPairing.root_coroot'_eq_pairing,
    _root_.RootPairing.pairing_same]
  ring

variable [CharZero R]

/-- **At Cartan product `1` the product of the two reflections has order exactly `3`.** -/
@[simp, grind =]
theorem orderOf_ofIdx_mul_ofIdx_eq_three (h : P.pairing i j * P.pairing j i = 1) :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) = 3 := by
  have hne : (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 1 ≠ 1 := by
    refine pow_ne_one_of_coroot'_left_ne P i j 1 ?_
    rw [coroot'_left_pow_smul_root P i j 1 (-1) (by rw [h]; ring), h]
    norm_num [S_zero, S_one]
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
    (pow_three_ofIdx_mul_ofIdx_eq_one P i j h) fun p hp hpd ↦ ?_
  have hp' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpd
  subst hp'
  exact hne

/-- **At Cartan product `2` the product of the two reflections has order exactly `4`.** -/
@[simp, grind =]
theorem orderOf_ofIdx_mul_ofIdx_eq_four (h : P.pairing i j * P.pairing j i = 2) :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) = 4 := by
  have hne : (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 2 ≠ 1 := by
    refine pow_ne_one_of_coroot'_left_ne P i j 2 ?_
    rw [coroot'_left_pow_smul_root P i j 2 0 (by rw [h]; ring), h]
    norm_num [S_one, S_two]
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
    (pow_four_ofIdx_mul_ofIdx_eq_one P i j h) fun p hp hpd ↦ ?_
  have hp' : p = 2 := by
    have hpd' : p ∣ 2 ^ 2 := by simpa using hpd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd')
  subst hp'
  exact hne

/-- **At Cartan product `3` the product of the two reflections has order exactly `6`.** -/
@[simp, grind =]
theorem orderOf_ofIdx_mul_ofIdx_eq_six (h : P.pairing i j * P.pairing j i = 3) :
    orderOf (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) = 6 := by
  have hne₂ : (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 2 ≠ 1 := by
    refine pow_ne_one_of_coroot'_left_ne P i j 2 ?_
    rw [coroot'_left_pow_smul_root P i j 2 1 (by rw [h]; ring), h]
    norm_num [S_one, S_two]
  have hne₃ : (_root_.RootPairing.weylGroup.ofIdx P i *
      _root_.RootPairing.weylGroup.ofIdx P j) ^ 3 ≠ 1 := by
    refine pow_ne_one_of_coroot'_left_ne P i j 3 ?_
    rw [coroot'_left_pow_smul_root P i j 3 1 (by rw [h]; ring), h]
    have h₃ : (S R 3).eval (1 : R) = -1 := by
      have h₃' : S R (3 : ℤ) = Polynomial.X * S R 2 - S R 1 := by simpa using S_add_two R (1 : ℤ)
      simp [h₃', S_one, S_two]
    norm_num [h₃, S_two]
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
@[simp, grind =]
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
relation half of the Coxeter presentation of the Weyl group. It is not a `simp` lemma: its
left-hand side is not in simp normal form, because the exponent `coxeterMatrixOfBase P b k l` is
itself rewritten by `TauCeti.coxeterMatrixOfBase_apply`. -/
@[grind =]
theorem pow_coxeterMatrixOfBase_ofIdx_mul_ofIdx_eq_one (k l : b.support) :
    (_root_.RootPairing.weylGroup.ofIdx P (k : ι) *
      _root_.RootPairing.weylGroup.ofIdx P (l : ι)) ^ coxeterMatrixOfBase P b k l = 1 := by
  rw [← orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase P b k l, pow_orderOf_eq_one]

end Base

end RootPairing.weylGroup

end TauCeti
