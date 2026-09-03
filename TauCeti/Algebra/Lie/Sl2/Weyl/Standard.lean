/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.IntegralLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.Basic

public section

/-!
# The Weyl element of a standard `sl₂`-module

The two ladder operators of `TauCeti.Sl2Std K n`, raising and lowering, are nilpotent over any
characteristic-zero domain `K` equipped with a `ℚ`-algebra structure, so they carry a Weyl element

```text
n = exp e · exp (-f) · exp e
```

in the unit group of `Module.End K (Sl2Std K n)`. This is Chevalley's
`n_α = x_α(1) x_{-α}(-1) x_α(1)` in the rank-one representation `V(n)`. This file computes it.

On the coordinate basis it is the reflection of the weight string, decorated by a sign:

```text
n · vᵢ = (-1) ^ (n - i) · v_{n - i}.
```

The proof is two steps and uses no representation theory. Conjugation by `n` sends the raising
operator to the negated lowering operator, so `n · v₀` is killed by the lowering operator and is
therefore a multiple of the lowest weight vector `vₙ`; its `n`-th coordinate is read off the
exponential series, because the raising operator cannot contribute to that coordinate. That is the
case `i = 0`. Conjugation by `n` in the other direction, sending the lowering operator to the
negated raising operator, turns the string relation `f · vᵢ = (n - i) · vᵢ₊₁` into the induction
step, the coefficient `n - i` being invertible exactly while the string continues.

Squaring the formula gives the relation the pinning of a Chevalley group asks for:

```text
n ^ 2 = (-1) ^ n,
```

the rank-one instance of `n_α ^ 2 = h_α(-1)`, since the torus element `h_α(-1)` acts on a weight
vector of weight `μ` by `(-1) ^ μ(α^∨)` and the weights of `V(n)` are `n - 2i ≡ n (mod 2)`.

Both statements are integral, not merely rational. Over `K = ℚ` the Weyl element permutes the
coordinate basis up to sign, so it preserves the coordinate lattice
`TauCeti.Sl2Std.integralLattice n`. Its restriction is the existing
`TauCeti.UniversalEnvelopingAlgebra.kostantWeylRestrict`, whose square is `(-1) ^ n`; base changing
it along `ℤ → A` gives the same relation for the existing `kostantWeylPoints` over *every*
commutative ring `A`, including characteristics in which the factorials dividing the exponential
series need not be invertible. This is the rank-one input the Chevalley--Demazure construction of
Layer 9 of the reductive-groups roadmap consumes, in the same form as the rank-one straightening
formula and the rank-one admissible lattice.

## Main definitions

* `TauCeti.Sl2Std.weylUnit`: the Weyl element of `V(n)`, a unit of `Module.End K (Sl2Std K n)`.
The integral Weyl element is the existing
`TauCeti.UniversalEnvelopingAlgebra.kostantWeylRestrict`, specialized to `V(n)` over `ℚ` and its
coordinate lattice; its scalar extension is the existing `kostantWeylPoints`.

## Main results

* `TauCeti.Sl2Std.weylUnit_apply_basis`: `n · vᵢ = (-1) ^ (n - i) · v_{n - i}`, with the matrix
  form `TauCeti.Sl2Std.weylUnit_apply_apply` in coordinates.
* `TauCeti.Sl2Std.coe_weylUnit_sq` and `TauCeti.Sl2Std.weylUnit_weylUnit_apply`: `n ^ 2 = (-1) ^ n`.
* `TauCeti.Sl2Std.kostantWeylRestrict_comp_self` and
  `TauCeti.Sl2Std.kostantWeylPoints_comp_self`: the same relation for the canonical Kostant Weyl
  element on the coordinate lattice and on its points over an arbitrary commutative ring.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
-/

open Finset
open TensorProduct
open scoped Nat

namespace TauCeti.Sl2Std

attribute [local instance 100] LieRing.ofAssociativeRing

section CharZeroDomain

variable (K : Type*) [CommRing K] [IsDomain K] [Algebra ℚ K] [CharZero K] (n : ℕ)

/-! ## The Weyl element -/

omit [IsDomain K] [CharZero K] in
/-- **The Weyl element of `V(n)`**, the unit `exp e · exp (-f) · exp e` of
`Module.End K (Sl2Std K n)`. It is Chevalley's `n_α = x_α(1) x_{-α}(-1) x_α(1)` in the rank-one
representation of highest weight `n`. -/
noncomputable def weylUnit : (Module.End K (Sl2Std K n))ˣ :=
  _root_.TauCeti.weylUnit (isNilpotent_raise (K := K) (n := n))
    (isNilpotent_lower (K := K) (n := n))

omit [IsDomain K] [CharZero K] in
/-- The Weyl element of `V(n)` is the threefold product of exponentials. -/
theorem coe_weylUnit :
    ((weylUnit K n : (Module.End K (Sl2Std K n))ˣ) : Module.End K (Sl2Std K n)) =
      IsNilpotent.exp (raise K n) * IsNilpotent.exp (-(lower K n)) *
        IsNilpotent.exp (raise K n) :=
  _root_.TauCeti.coe_weylUnit _ _

omit [IsDomain K] [CharZero K] in
/-- Convert a conjugation identity for the standard Weyl element into a multiplication identity. -/
private theorem weylUnit_mul_of_conj_eq_neg {x y : Module.End K (Sl2Std K n)}
    (h : IsNilpotent.exp (raise K n) * IsNilpotent.exp (-(lower K n)) *
        IsNilpotent.exp (raise K n) * x *
          (IsNilpotent.exp (-(raise K n)) * IsNilpotent.exp (lower K n) *
            IsNilpotent.exp (-(raise K n))) = -y) :
    (weylUnit K n : Module.End K (Sl2Std K n)) * x =
      -(y * (weylUnit K n : Module.End K (Sl2Std K n))) := by
  rw [← _root_.TauCeti.coe_weylUnit (isNilpotent_raise (K := K) (n := n))
      (isNilpotent_lower (K := K) (n := n)),
    ← _root_.TauCeti.coe_inv_weylUnit (isNilpotent_raise (K := K) (n := n))
      (isNilpotent_lower (K := K) (n := n))] at h
  rw [← neg_mul]
  exact (Units.mul_inv_eq_iff_eq_mul _).mp h

omit [IsDomain K] in
/-- **Conjugating the raising operator by the Weyl element.** The relation `n e n⁻¹ = -f`, written
without the inverse. -/
theorem weylUnit_mul_raise :
    (weylUnit K n : Module.End K (Sl2Std K n)) * raise K n =
      -(lower K n * (weylUnit K n : Module.End K (Sl2Std K n))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [raise_zero, lower_zero, mul_zero, zero_mul, neg_zero]
  have h := _root_.TauCeti.weylUnit_conj_e
    (isSl2Triple_diag_raise_lower (K := K) (Nat.cast_ne_zero.mpr hn.ne'))
    (isNilpotent_raise (K := K) (n := n)) (isNilpotent_lower (K := K) (n := n))
  exact weylUnit_mul_of_conj_eq_neg K n h

omit [IsDomain K] in
/-- **Conjugating the lowering operator by the Weyl element.** The relation `n f n⁻¹ = -e`, written
without the inverse. -/
theorem weylUnit_mul_lower :
    (weylUnit K n : Module.End K (Sl2Std K n)) * lower K n =
      -(raise K n * (weylUnit K n : Module.End K (Sl2Std K n))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [raise_zero, lower_zero, mul_zero, zero_mul, neg_zero]
  have h := _root_.TauCeti.weylUnit_conj_f
    (isSl2Triple_diag_raise_lower (K := K) (Nat.cast_ne_zero.mpr hn.ne'))
    (isNilpotent_raise (K := K) (n := n)) (isNilpotent_lower (K := K) (n := n))
  exact weylUnit_mul_of_conj_eq_neg K n h

/-! ## The base case of the string -/

omit [IsDomain K] [CharZero K] in
/-- The exponential series of a nilpotent operator on `V(n)`, with its rational factorial
coefficients mapped to `K`. -/
private theorem exp_eq_sum_algebraMap_smul {x : Module.End K (Sl2Std K n)} {k : ℕ}
    (hx : x ^ k = 0) :
    IsNilpotent.exp x =
      ∑ i ∈ range k, algebraMap ℚ K (((i ! : ℕ) : ℚ)⁻¹) • x ^ i := by
  rw [IsNilpotent.exp_eq_sum hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [algebraMap_smul]

omit [IsDomain K] [CharZero K] in
/-- The exponential of the raising operator differs from the identity by a multiple of the raising
operator, on either side: the series has no constant term beyond `1`. -/
private theorem exists_exp_raise_eq :
    ∃ g : Module.End K (Sl2Std K n),
      IsNilpotent.exp (raise K n) = 1 + raise K n * g ∧
        IsNilpotent.exp (raise K n) = 1 + g * raise K n := by
  refine ⟨∑ i ∈ range n,
    algebraMap ℚ K ((((i + 1)! : ℕ) : ℚ)⁻¹) • (raise K n) ^ i, ?_, ?_⟩
  · rw [exp_eq_sum_algebraMap_smul K n (raise_pow_eq_zero (K := K) (n := n)),
      Finset.sum_range_succ', Nat.factorial_zero, pow_zero, Nat.cast_one, inv_one, map_one,
      one_smul, add_comm]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_succ', mul_smul_comm]
  · rw [exp_eq_sum_algebraMap_smul K n (raise_pow_eq_zero (K := K) (n := n)),
      Finset.sum_range_succ', Nat.factorial_zero, pow_zero, Nat.cast_one, inv_one, map_one,
      one_smul, add_comm]
    congr 1
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_succ, smul_mul_assoc]

omit [IsDomain K] [CharZero K] in
/-- The raising operator does not reach the lowest coordinate, so neither does its exponential. -/
private theorem exp_raise_apply_last (v : Sl2Std K n) :
    (IsNilpotent.exp (raise K n) v) (Fin.last n) = v (Fin.last n) := by
  obtain ⟨g, hg, -⟩ := exists_exp_raise_eq K n
  rw [hg, LinearMap.add_apply, Module.End.one_apply, add_apply, Module.End.mul_apply, raise_apply,
    dite_eq_right (by simp : ¬ ((Fin.last n : Fin (n + 1)) : ℕ) < n), add_zero]

omit [IsDomain K] [CharZero K] in
/-- The exponential of the raising operator fixes the highest weight vector, which it kills. -/
private theorem exp_raise_basis_zero :
    IsNilpotent.exp (raise K n) (basis K n 0) = basis K n 0 := by
  obtain ⟨g, -, hg⟩ := exists_exp_raise_eq K n
  rw [hg, LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, raise_basis_zero,
    g.map_zero, add_zero]

omit [IsDomain K] [CharZero K] in
/-- The lowest coordinate of `exp (-f) · v₀` is the sign `(-1) ^ n`: only the last term of the
exponential series reaches it, and its falling-factorial coefficient cancels the factorial. -/
private theorem exp_neg_lower_basis_zero_apply_last :
    (IsNilpotent.exp (-(lower K n)) (basis K n 0)) (Fin.last n) = (-1 : K) ^ n := by
  have hnil : (-(lower K n)) ^ (n + 1) = 0 := by
    rw [neg_pow, lower_pow_eq_zero, mul_zero]
  have hpow : ∀ k : ℕ, ((-(lower K n)) ^ k) (basis K n 0) =
      ((-1 : K) ^ k) • (((lower K n) ^ k) (basis K n 0)) := by
    intro k
    have : (-(lower K n)) = ((-1 : K) • lower K n) := by
      rw [neg_smul, one_smul]
    rw [this, smul_pow, LinearMap.smul_apply]
  rw [exp_eq_sum_algebraMap_smul K n hnil, LinearMap.sum_apply, TauCeti.Sl2Std.sum_apply,
    Finset.sum_eq_single n]
  · have hlast := lower_pow_basis_zero (K := K) (Fin.last n)
    simp only [Fin.val_last] at hlast
    rw [LinearMap.smul_apply, smul_apply, hpow n, hlast]
    have hfacQ : ((n ! : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hcancel : algebraMap ℚ K (((n ! : ℕ) : ℚ)⁻¹) * ((n ! : ℕ) : K) = 1 := by
      rw [← map_natCast (algebraMap ℚ K) (n !), ← map_mul, inv_mul_cancel₀ hfacQ, map_one]
    have hprod : ∏ j ∈ range n, ((n : K) - j) = (n ! : K) := by
      rw [Finset.prod_range_natCast_sub, ← Nat.descFactorial_eq_prod_range,
        Nat.descFactorial_self]
    simp only [smul_apply, basis_apply, hprod, ite_true]
    calc
      algebraMap ℚ K (((n ! : ℕ) : ℚ)⁻¹) * ((-1 : K) ^ n * (((n ! : ℕ) : K) * 1)) =
          (-1 : K) ^ n *
            (algebraMap ℚ K (((n ! : ℕ) : ℚ)⁻¹) * ((n ! : ℕ) : K)) := by ring
      _ = (-1 : K) ^ n := by rw [hcancel, mul_one]
  · intro b hb hbn
    have hblt : b < n := by
      have := Finset.mem_range.mp hb
      omega
    let i : Fin (n + 1) := ⟨b, by omega⟩
    have hi := lower_pow_basis_zero (K := K) i
    have hi_val : (i : ℕ) = b := by simp [i]
    rw [hi_val] at hi
    rw [LinearMap.smul_apply, smul_apply, hpow b, hi]
    have hne : Fin.last n ≠ i := by
      intro hc
      have := congrArg Fin.val hc
      simp only [Fin.val_last, i] at this
      omega
    simp [hne]
  · intro hc
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hc

/-- **The Weyl element on the highest weight vector.** It carries `v₀` to `(-1) ^ n · vₙ`. -/
private theorem weylUnit_apply_basis_zero :
    (weylUnit K n : Module.End K (Sl2Std K n)) (basis K n 0) =
      ((-1 : K) ^ n) • basis K n (Fin.last n) := by
  set w := (weylUnit K n : Module.End K (Sl2Std K n)) (basis K n 0) with hw
  have hlow : lower K n w = 0 := by
    have := congrArg (fun g : Module.End K (Sl2Std K n) => g (basis K n 0))
      (weylUnit_mul_raise K n)
    simp only [Module.End.mul_apply, raise_basis_zero, map_zero, LinearMap.neg_apply] at this
    rw [hw, ← neg_eq_zero]
    exact this.symm
  have hcoord : w (Fin.last n) = (-1 : K) ^ n := by
    rw [hw, coe_weylUnit, Module.End.mul_apply, Module.End.mul_apply, exp_raise_basis_zero,
      exp_raise_apply_last, exp_neg_lower_basis_zero_apply_last]
  calc w = w (Fin.last n) • basis K n (Fin.last n) :=
        eq_smul_basis_last_of_lower_eq_zero hlow
    _ = ((-1 : K) ^ n) • basis K n (Fin.last n) := by rw [hcoord]

/-! ## The Weyl element reverses the string -/

/-- The successor produced by `lower_basis` agrees with `Fin.succ`. -/
private theorem lower_basis_index_eq_succ (i : Fin n) :
    (⟨(i.castSucc : Fin (n + 1)).val + 1, by
        have hi := i.isLt
        simp only [Fin.val_castSucc]
        omega⟩ : Fin (n + 1)) = i.succ := by
  ext
  simp

/-- Raising the reversal of `i.castSucc` produces the reversal of `i.succ`. -/
private theorem raise_basis_index_rev_castSucc (i : Fin n) :
    (⟨(((i.castSucc : Fin (n + 1)).rev : Fin (n + 1)) : ℕ) - 1, by
        simp only [Fin.val_rev, Fin.val_castSucc]
        omega⟩ : Fin (n + 1)) = i.succ.rev := by
  ext
  simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
  omega

/-- The sign change in the successor step lowers the exponent of `-1` by one. -/
private theorem neg_neg_one_pow_succ_mul {R : Type*} [CommRing R] (m : ℕ) (c : R) :
    -((-1 : R) ^ (m + 1) * c) = c * (-1 : R) ^ m := by
  rw [pow_succ]
  ring

/-- **The Weyl element reverses the weight string with a sign.** It carries the coordinate basis
vector `vᵢ` to `(-1) ^ (n - i) · v_{n - i}`, the reflection `s_α` of the weight lattice realised
inside the group. -/
@[simp]
theorem weylUnit_apply_basis (i : Fin (n + 1)) :
    (weylUnit K n : Module.End K (Sl2Std K n)) (basis K n i) =
      ((-1 : K) ^ (n - (i : ℕ))) • basis K n i.rev := by
  induction i using Fin.induction with
  | zero =>
    rw [Fin.val_zero, Nat.sub_zero, Fin.rev_zero]
    exact weylUnit_apply_basis_zero K n
  | succ i ih =>
    have hlt : (i.castSucc : Fin (n + 1)).val < n := i.isLt
    obtain ⟨m, hm⟩ : ∃ m, n - (i.castSucc : Fin (n + 1)).val = m + 1 :=
      ⟨n - (i.castSucc : Fin (n + 1)).val - 1, by omega⟩
    have hsucc : n - (i.succ : Fin (n + 1)).val = m := by
      simp only [Fin.val_succ, Fin.val_castSucc] at hm ⊢
      omega
    have hcast : (((m + 1 : ℕ) : K)) = (n : K) - (((i.castSucc : Fin (n + 1)).val : ℕ) : K) := by
      rw [← hm]
      simpa only [Fin.val_castSucc] using (Nat.cast_sub (R := K) (le_of_lt i.isLt))
    have hcoef : ((n : K) - (((i.castSucc : Fin (n + 1)).val : ℕ) : K)) ≠ 0 := by
      rw [← hcast]
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    have hstep := congrArg (fun g : Module.End K (Sl2Std K n) => g (basis K n i.castSucc))
      (weylUnit_mul_lower K n)
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at hstep
    rw [lower_basis _ hlt, map_smul, ih, map_smul, raise_basis] at hstep
    have hrevval : (((i.castSucc : Fin (n + 1)).rev : Fin (n + 1)) : ℕ) = m + 1 := by
      rw [Fin.val_rev]; omega
    rw [lower_basis_index_eq_succ, raise_basis_index_rev_castSucc, hm, hrevval] at hstep
    rw [hcast] at hstep
    rw [hsucc]
    have hgoal : ((n : K) - (((i.castSucc : Fin (n + 1)).val : ℕ) : K)) •
          (weylUnit K n : Module.End K (Sl2Std K n)) (basis K n i.succ) =
        ((n : K) - (((i.castSucc : Fin (n + 1)).val : ℕ) : K)) •
          (((-1 : K) ^ m) • basis K n i.succ.rev) := by
      rw [hstep, smul_smul, smul_smul, ← neg_smul]
      congr 1
      rw [neg_neg_one_pow_succ_mul]
    exact smul_right_injective (Sl2Std K n) hcoef hgoal

/-! ## The square of the Weyl element -/

/-- **The square of the Weyl element is the scalar `(-1) ^ n`.** This is the rank-one instance of
Chevalley's relation `n_α ^ 2 = h_α(-1)`: the torus element `h_α(-1)` acts on a weight vector of
weight `μ` by `(-1) ^ μ(α^∨)`, and every weight of `V(n)` is congruent to `n` modulo two. -/
@[simp]
theorem coe_weylUnit_sq :
    ((weylUnit K n : (Module.End K (Sl2Std K n))ˣ) : Module.End K (Sl2Std K n)) ^ 2 =
      ((-1 : K) ^ n) • 1 := by
  refine (basis K n).ext fun i => ?_
  rw [sq, Module.End.mul_apply, weylUnit_apply_basis, map_smul, weylUnit_apply_basis,
    Fin.rev_rev, smul_smul, LinearMap.smul_apply, Module.End.one_apply, ← pow_add]
  congr 2
  have : (i.rev : ℕ) = n - (i : ℕ) := by simp [Fin.val_rev]
  omega

/-- The inverse Weyl element is the Weyl element itself, up to the scalar `(-1) ^ n`. -/
@[simp]
theorem coe_inv_weylUnit :
    (((weylUnit K n)⁻¹ : (Module.End K (Sl2Std K n))ˣ) : Module.End K (Sl2Std K n)) =
      ((-1 : K) ^ n) • (weylUnit K n : Module.End K (Sl2Std K n)) := by
  refine Units.inv_eq_of_mul_eq_one_left ?_
  rw [smul_mul_assoc, ← sq, coe_weylUnit_sq, smul_smul, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_smul]

/-- The Weyl element acts on every vector of `V(n)` by `(-1) ^ n` after two applications. -/
@[simp]
theorem weylUnit_weylUnit_apply (v : Sl2Std K n) :
    (weylUnit K n : Module.End K (Sl2Std K n))
        ((weylUnit K n : Module.End K (Sl2Std K n)) v) = ((-1 : K) ^ n) • v := by
  have := congrArg (fun g : Module.End K (Sl2Std K n) => g v) (coe_weylUnit_sq K n)
  simpa [sq, Module.End.mul_apply] using this

/-! ## The Weyl element in coordinates -/

/-- **The matrix of the Weyl element.** It sends the `i`-th coordinate of the image to the
reversed coordinate of the source, with the sign `(-1) ^ i`. -/
@[simp]
theorem weylUnit_apply_apply (v : Sl2Std K n) (i : Fin (n + 1)) :
    ((weylUnit K n : Module.End K (Sl2Std K n)) v) i = (-1 : K) ^ (i : ℕ) * v i.rev := by
  have hrev : n - (i.rev : ℕ) = (i : ℕ) := by
    have := i.isLt
    simp only [Fin.val_rev]
    omega
  conv_lhs => rw [← (basis K n).sum_repr v]
  rw [map_sum, TauCeti.Sl2Std.sum_apply, Finset.sum_eq_single i.rev]
  · rw [map_smul, weylUnit_apply_basis, Fin.rev_rev, smul_apply, smul_apply, basis_apply,
      ite_eq_left rfl, basis_repr_apply, hrev, mul_one]
    ring
  · intro b _ hb
    have hne : i ≠ b.rev := by
      intro hc
      exact hb (by rw [hc, Fin.rev_rev])
    rw [map_smul, weylUnit_apply_basis, smul_apply, smul_apply, basis_apply, ite_eq_right hne,
      mul_zero, mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ i.rev) hc

end CharZeroDomain

/-! ## The canonical Kostant Weyl element over `ℤ` and its points -/

section Kostant

variable (n : ℕ)

local notation "eStd" => ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1]
local notation "hStd" => ![slFinTwoBasis ℚ 2]
local notation "ρStd" => repEnveloping ℚ n
local notation "MStd" => Submodule.toAddSubgroup (integralLattice n)

private theorem repEnveloping_root_eq_raise :
    ρStd (_root_.UniversalEnvelopingAlgebra.ι ℚ (eStd 0)) = raise ℚ n := by
  simpa using (repEnveloping_ι_slFinTwoBasis (K := ℚ) (n := n) 0)

private theorem repEnveloping_root_eq_lower :
    ρStd (_root_.UniversalEnvelopingAlgebra.ι ℚ (eStd 1)) = lower ℚ n := by
  simpa using (repEnveloping_ι_slFinTwoBasis (K := ℚ) (n := n) 1)

local notation "wℤ" =>
  TauCeti.UniversalEnvelopingAlgebra.kostantWeylRestrict eStd hStd ρStd MStd
    (kostantForm_apply_mem_integralLattice n) (isNilpotent_repEnveloping_root ℚ n 0)
    (isNilpotent_repEnveloping_root ℚ n 1)

local notation "wPts" =>
  TauCeti.UniversalEnvelopingAlgebra.kostantWeylPoints eStd hStd ρStd MStd
    (kostantForm_apply_mem_integralLattice n) (isNilpotent_repEnveloping_root ℚ n 0)
    (isNilpotent_repEnveloping_root ℚ n 1)

private theorem kostantWeylUnit_eq :
    _root_.TauCeti.weylUnit (isNilpotent_repEnveloping_root ℚ n 0)
      (isNilpotent_repEnveloping_root ℚ n 1) = weylUnit ℚ n := by
  apply Units.ext
  rw [_root_.TauCeti.coe_weylUnit, coe_weylUnit, repEnveloping_root_eq_raise,
    repEnveloping_root_eq_lower]
  rfl

/-- On the standard integral lattice, the existing Kostant Weyl automorphism applies the
coordinate Weyl element computed in this file. -/
theorem coe_kostantWeylRestrict_apply (v : MStd) :
    ((wℤ v : MStd) : Sl2Std ℚ n) =
      (weylUnit ℚ n : Module.End ℚ (Sl2Std ℚ n)) (v : Sl2Std ℚ n) := by
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantWeylRestrict_apply,
    kostantWeylUnit_eq]
  rfl

/-- **The integral form of the relation `n ^ 2 = (-1) ^ n`.** The canonical Kostant Weyl
automorphism squares to the integer scalar `(-1) ^ n` on the standard coordinate lattice. -/
theorem kostantWeylRestrict_comp_self :
    (wℤ : MStd →ₗ[ℤ] MStd) ∘ₗ (wℤ : MStd →ₗ[ℤ] MStd) =
      ((-1 : ℤ) ^ n) • LinearMap.id := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, coe_kostantWeylRestrict_apply,
    coe_kostantWeylRestrict_apply, weylUnit_weylUnit_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq, AddSubgroupClass.coe_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
  push_cast
  rfl

/-- **The relation over an arbitrary ring of points.** The canonical Kostant Weyl element on
points squares to `(-1) ^ n` after base change to every commutative ring, including
characteristics in which the factorials dividing the rational exponential need not be invertible. -/
theorem kostantWeylPoints_comp_self (A : Type*) [CommRing A] [Algebra ℤ A] :
    (wPts A).toLinearMap ∘ₗ (wPts A).toLinearMap =
      ((-1 : A) ^ n) • LinearMap.id := by
  rw [TauCeti.UniversalEnvelopingAlgebra.kostantWeylPoints_toLinearMap,
    ← LinearMap.baseChange_comp]
  rcases Nat.even_or_odd n with he | ho
  · have hid : (wℤ : MStd →ₗ[ℤ] MStd) ∘ₗ (wℤ : MStd →ₗ[ℤ] MStd) =
        LinearMap.id := by
      rw [kostantWeylRestrict_comp_self, he.neg_one_pow, one_smul]
    rw [hid, LinearMap.baseChange_id, he.neg_one_pow, one_smul]
  · have hid : (wℤ : MStd →ₗ[ℤ] MStd) ∘ₗ (wℤ : MStd →ₗ[ℤ] MStd) =
        -LinearMap.id := by
      rw [kostantWeylRestrict_comp_self, ho.neg_one_pow, neg_smul, one_smul]
    rw [hid, LinearMap.baseChange_neg, LinearMap.baseChange_id, ho.neg_one_pow]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.neg_apply, LinearMap.id_coe, id_eq, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, neg_one_smul]

end Kostant

end TauCeti.Sl2Std
