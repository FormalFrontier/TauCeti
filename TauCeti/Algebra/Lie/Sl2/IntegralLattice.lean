/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Lie.Sl2.Standard
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Form
public import TauCeti.RingTheory.Binomial
import Mathlib.Tactic.FinCases

/-!
# The admissible integral lattice in a standard `sl₂`-module

The standard irreducible `sl₂`-module `TauCeti.Sl2Std ℚ n` has its coordinate lattice

```text
V(n)ℤ = {v | vᵢ ∈ ℤ for every i}.
```

This file proves that `V(n)ℤ` is an admissible lattice for the rank-one Kostant form. The
divided raising and lowering operators act on coordinates by ordinary binomial coefficients,
while the Cartan binomials act on the `i`-th coordinate by the generalized integer binomial
coefficient `(n - 2i choose k)`. Consequently every element of the Kostant form preserves the
lattice.

The lattice is also identified with `Fin (n + 1) → ℤ`, proving directly that it is finite free
of rank `n + 1` and spans `V(n)` over `ℚ`. This is the rank-one admissible-lattice input to the
Chevalley--Demazure construction in Layer 9 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.Sl2Std.integralLattice`: the coordinate `ℤ`-lattice in `V(n)`.
* `TauCeti.Sl2Std.integerCoordinatesLinearEquiv`: its identification with
  `Fin (n + 1) → ℤ`.
* `TauCeti.Sl2Std.dividedPower_raise_apply` and
  `TauCeti.Sl2Std.dividedPower_lower_apply`: the integral coordinate formulas for the root
  divided powers.
* `TauCeti.Sl2Std.ringChoose_diag_apply`: the coordinate formula for Cartan binomials.
* `TauCeti.Sl2Std.kostantForm_apply_mem_integralLattice`: the rank-one Kostant form preserves
  the lattice.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., II.1.
-/

public section

namespace TauCeti.Sl2Std

open Finset
open Polynomial
open scoped Matrix

attribute [local instance] TauCeti.moduleNNRat

variable (n : ℕ)

/-- The coordinate `ℤ`-lattice in the rational standard `sl₂`-module `V(n)`.

A vector belongs to this submodule exactly when each of its coordinates is an integer viewed in
`ℚ`; see `mem_integralLattice_iff`. -/
def integralLattice : Submodule ℤ (Sl2Std ℚ n) :=
  { carrier := {v | ∀ i, ∃ z : ℤ, (z : ℚ) = v i}
    zero_mem' := fun i => ⟨0, by simp⟩
    add_mem' := fun {v w} hv hw i => by
      obtain ⟨z, hz⟩ := hv i
      obtain ⟨t, ht⟩ := hw i
      exact ⟨z + t, by rw [Int.cast_add, hz, ht, add_apply]⟩
    smul_mem' := fun z v hv i => by
      obtain ⟨t, ht⟩ := hv i
      refine ⟨z * t, ?_⟩
      rw [Int.cast_mul, ht, ← Int.cast_smul_eq_zsmul ℚ, smul_apply] }

/-- A vector belongs to the standard integral lattice exactly when all its coordinates are
integer-valued. -/
@[simp]
theorem mem_integralLattice_iff {v : Sl2Std ℚ n} :
    v ∈ integralLattice n ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = v i := by
  rfl

/-- Cast an integer coordinate vector into the standard integral lattice. -/
def integerCoordinatesLinearMap :
    (Fin (n + 1) → ℤ) →ₗ[ℤ] integralLattice n where
  toFun z := ⟨show Sl2Std ℚ n from fun i => (z i : ℚ), by
    rw [mem_integralLattice_iff]
    exact fun i => ⟨z i, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change (show Sl2Std ℚ n from fun i => ((x + y) i : ℚ)) =
      (show Sl2Std ℚ n from fun i => (x i : ℚ)) +
        (show Sl2Std ℚ n from fun i => (y i : ℚ))
    funext i
    rw [add_apply]
    norm_cast
  map_smul' z x := by
    apply Subtype.ext
    change (show Sl2Std ℚ n from fun i => (((z • x) i : ℤ) : ℚ)) =
      z • (show Sl2Std ℚ n from fun i => (x i : ℚ))
    calc
      (show Sl2Std ℚ n from fun i => (((z • x) i : ℤ) : ℚ)) =
          (z : ℚ) • (show Sl2Std ℚ n from fun i => (x i : ℚ)) := by
        funext i
        rw [smul_apply]
        simp
      _ = z • (show Sl2Std ℚ n from fun i => (x i : ℚ)) :=
        Int.cast_smul_eq_zsmul ℚ z _

/-- Integer coordinate vectors are linearly equivalent to the standard integral lattice. -/
noncomputable def integerCoordinatesLinearEquiv :
    (Fin (n + 1) → ℤ) ≃ₗ[ℤ] integralLattice n :=
  LinearEquiv.ofBijective (integerCoordinatesLinearMap n) ⟨by
    intro x y hxy
    funext i
    have hi := congrArg (fun v : integralLattice n => (v : Sl2Std ℚ n) i) hxy
    change (x i : ℚ) = (y i : ℚ) at hi
    exact Int.cast_injective hi, by
    rintro ⟨v, hv⟩
    rw [mem_integralLattice_iff] at hv
    choose z hz using hv
    refine ⟨z, ?_⟩
    apply Subtype.ext
    funext i
    exact hz i⟩

noncomputable instance : Module.Free ℤ (integralLattice n) :=
  Module.Free.of_equiv (integerCoordinatesLinearEquiv n)

noncomputable instance : Module.Finite ℤ (integralLattice n) :=
  Module.Finite.equiv (integerCoordinatesLinearEquiv n)

/-- The standard integral lattice has rank `n + 1`. -/
@[simp]
theorem finrank_integralLattice : Module.finrank ℤ (integralLattice n) = n + 1 := by
  rw [← (integerCoordinatesLinearEquiv n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

private theorem raise_pow_apply (k : ℕ) (v : Sl2Std ℚ n) (i : Fin (n + 1)) :
    ((raise ℚ n) ^ k) v i =
      if h : (i : ℕ) + k ≤ n then
        (((i : ℕ) + k).descFactorial k : ℚ) * v ⟨(i : ℕ) + k, by omega⟩
      else 0 := by
  induction k generalizing i with
  | zero =>
      have hi : (i : ℕ) ≤ n := by have := i.isLt; omega
      simp [hi]
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, raise_apply]
      by_cases hi : (i : ℕ) < n
      · rw [dite_eq_left hi]
        let j : Fin (n + 1) := ⟨(i : ℕ) + 1, by omega⟩
        rw [ih j]
        change ((i : ℚ) + 1) *
            (if h : (i : ℕ) + 1 + k ≤ n then
              (((i : ℕ) + 1 + k).descFactorial k : ℚ) * v ⟨(i : ℕ) + 1 + k, by omega⟩
            else 0) = _
        by_cases hik : (i : ℕ) + (k + 1) ≤ n
        · rw [dite_eq_left (by omega), dite_eq_left hik]
          rw [Nat.descFactorial_succ]
          have hfactor : (i : ℕ) + (k + 1) - k = (i : ℕ) + 1 := by omega
          rw [hfactor]
          have hidx :
              (⟨(i : ℕ) + 1 + k, by omega⟩ : Fin (n + 1)) =
                ⟨(i : ℕ) + (k + 1), by omega⟩ := by
            simp only [Fin.mk.injEq]
            omega
          rw [hidx]
          push_cast
          ring_nf
        · rw [dite_eq_right (by omega), dite_eq_right hik, mul_zero]
      · rw [dite_eq_right hi, dite_eq_right (by omega)]

private theorem lower_pow_apply (k : ℕ) (v : Sl2Std ℚ n) (i : Fin (n + 1)) :
    ((lower ℚ n) ^ k) v i =
      if h : k ≤ (i : ℕ) then
        ((n - (i : ℕ) + k).descFactorial k : ℚ) *
          v ⟨(i : ℕ) - k, by omega⟩
      else 0 := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, lower_apply]
      by_cases hi : 0 < (i : ℕ)
      · rw [dite_eq_left hi]
        let j : Fin (n + 1) := ⟨(i : ℕ) - 1, by omega⟩
        rw [ih j]
        change ((n : ℚ) - (i : ℕ) + 1) *
            (if h : k ≤ (i : ℕ) - 1 then
              ((n - ((i : ℕ) - 1) + k).descFactorial k : ℚ) *
                v ⟨(i : ℕ) - 1 - k, by omega⟩
            else 0) = _
        by_cases hki : k + 1 ≤ (i : ℕ)
        · rw [dite_eq_left (by omega), dite_eq_left hki]
          rw [Nat.descFactorial_succ]
          have hsub : n - ((i : ℕ) - 1) + k = n - (i : ℕ) + (k + 1) := by omega
          rw [hsub]
          have hfactor : n - (i : ℕ) + (k + 1) - k = n - (i : ℕ) + 1 := by omega
          rw [hfactor]
          have hidx :
              (⟨(i : ℕ) - 1 - k, by omega⟩ : Fin (n + 1)) =
                ⟨(i : ℕ) - (k + 1), by omega⟩ := by
            simp only [Fin.mk.injEq]
            omega
          rw [hidx]
          have hle : (i : ℕ) ≤ n := by have := i.isLt; omega
          have hcoeff : (n : ℚ) - (i : ℕ) + 1 = ((n - (i : ℕ) + 1 : ℕ) : ℚ) := by
            rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_one]
          rw [hcoeff, Nat.cast_mul]
          ring_nf
        · rw [dite_eq_right (by omega), dite_eq_right hki, mul_zero]
      · rw [dite_eq_right hi, dite_eq_right (by omega)]

/-- The `k`-th divided raising operator reads coordinate `i + k` with the integral coefficient
`(i + k choose k)`, and vanishes when that coordinate is past the end of `V(n)`. -/
theorem dividedPower_raise_apply (k : ℕ) (v : Sl2Std ℚ n) (i : Fin (n + 1)) :
    Associative.dividedPower k (raise ℚ n) v i =
      if h : (i : ℕ) + k ≤ n then
        (((i : ℕ) + k).choose k : ℚ) * v ⟨(i : ℕ) + k, by omega⟩
      else 0 := by
  rw [Associative.dividedPower_def, LinearMap.smul_apply, smul_apply, raise_pow_apply]
  by_cases h : (i : ℕ) + k ≤ n
  · rw [dite_eq_left h, dite_eq_left h, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  · rw [dite_eq_right h, dite_eq_right h, mul_zero]

/-- The `k`-th divided lowering operator reads coordinate `i - k` with the integral coefficient
`(n - i + k choose k)`, and vanishes when `k > i`. -/
theorem dividedPower_lower_apply (k : ℕ) (v : Sl2Std ℚ n) (i : Fin (n + 1)) :
    Associative.dividedPower k (lower ℚ n) v i =
      if h : k ≤ (i : ℕ) then
        ((n - (i : ℕ) + k).choose k : ℚ) * v ⟨(i : ℕ) - k, by omega⟩
      else 0 := by
  rw [Associative.dividedPower_def, LinearMap.smul_apply, smul_apply, lower_pow_apply]
  by_cases h : k ≤ (i : ℕ)
  · rw [dite_eq_left h, dite_eq_left h, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  · rw [dite_eq_right h, dite_eq_right h, mul_zero]

private theorem diag_pow_apply (k : ℕ) (v : Sl2Std ℚ n) (i : Fin (n + 1)) :
    ((diag ℚ n) ^ k) v i = ((n : ℚ) - 2 * (i : ℕ)) ^ k * v i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, diag_apply, ih]
      ring_nf

private theorem zsmul_apply (z : ℤ) (v : Sl2Std ℚ n) (i : Fin (n + 1)) :
    (z • v) i = (z : ℚ) * v i := by
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_apply]

private theorem zsmul_end_apply (z : ℤ) (f : Module.End ℚ (Sl2Std ℚ n))
    (v : Sl2Std ℚ n) (i : Fin (n + 1)) :
    (z • f) v i = (z : ℚ) * f v i := by
  rw [← Int.cast_smul_eq_zsmul ℚ, LinearMap.smul_apply, smul_apply]

private theorem smeval_diag_apply (p : ℤ[X]) (v : Sl2Std ℚ n) (i : Fin (n + 1)) :
    p.smeval (diag ℚ n) v i = p.smeval ((n : ℚ) - 2 * (i : ℕ)) * v i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.smeval_add, LinearMap.add_apply, add_apply, hp, hq,
        Polynomial.smeval_add]
      ring_nf
  | monomial k z =>
      rw [Polynomial.smeval_monomial, zsmul_end_apply, diag_pow_apply,
        Polynomial.smeval_monomial]
      rw [← Int.cast_smul_eq_zsmul ℚ]
      simp only [smul_eq_mul]
      ring_nf

/-- The `k`-th Cartan binomial acts diagonally on `V(n)`, with eigenvalue
`(n - 2i choose k)` on coordinate `i`. -/
theorem ringChoose_diag_apply (k : ℕ) (v : Sl2Std ℚ n) (i : Fin (n + 1)) :
    (Ring.choose (diag ℚ n) k : Module.End ℚ (Sl2Std ℚ n)) v i =
      Ring.choose ((n : ℚ) - 2 * (i : ℕ)) k * v i := by
  let weight : ℚ := (n : ℚ) - 2 * (i : ℕ)
  let p := descPochhammer ℤ k
  change (Ring.choose (diag ℚ n) k : Module.End ℚ (Sl2Std ℚ n)) v i =
    Ring.choose weight k * v i
  have hop := Ring.descPochhammer_eq_factorial_smul_choose
    (diag ℚ n) k
  have hop' :
      p.smeval (diag ℚ n) v i =
        (k.factorial : ℚ) *
          ((Ring.choose (diag ℚ n) k : Module.End ℚ (Sl2Std ℚ n)) v i) := by
    rw [show p = descPochhammer ℤ k from rfl, hop,
      ← Nat.cast_smul_eq_nsmul ℚ, LinearMap.smul_apply, smul_apply]
  have hscalar := Ring.descPochhammer_eq_factorial_smul_choose weight k
  have hscalar' : p.smeval weight = (k.factorial : ℚ) * Ring.choose weight k := by
    calc
      p.smeval weight = k.factorial • Ring.choose weight k := hscalar
      _ = (k.factorial : ℚ) • Ring.choose weight k :=
        (Nat.cast_smul_eq_nsmul ℚ _ _).symm
      _ = (k.factorial : ℚ) * Ring.choose weight k := by rw [smul_eq_mul]
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply (mul_left_cancel₀ hk)
  calc
    (k.factorial : ℚ) *
          ((Ring.choose (diag ℚ n) k : Module.End ℚ (Sl2Std ℚ n)) v i) =
        p.smeval (diag ℚ n) v i := hop'.symm
    _ = p.smeval weight * v i := smeval_diag_apply n p v i
    _ = (k.factorial : ℚ) * (Ring.choose weight k * v i) := by
      rw [hscalar']
      ring_nf

/-- Every divided power of the raising operator preserves the standard integral lattice. -/
theorem dividedPower_raise_mem_integralLattice (k : ℕ) {v : Sl2Std ℚ n}
    (hv : v ∈ integralLattice n) :
    Associative.dividedPower k (raise ℚ n) v ∈ integralLattice n := by
  rw [mem_integralLattice_iff] at hv ⊢
  intro i
  rw [dividedPower_raise_apply]
  by_cases h : (i : ℕ) + k ≤ n
  · rw [dite_eq_left h]
    obtain ⟨z, hz⟩ := hv ⟨(i : ℕ) + k, by omega⟩
    refine ⟨(((i : ℕ) + k).choose k : ℤ) * z, ?_⟩
    rw [Int.cast_mul, Int.cast_natCast, hz]
  · rw [dite_eq_right h]
    exact ⟨0, by simp⟩

/-- Every divided power of the lowering operator preserves the standard integral lattice. -/
theorem dividedPower_lower_mem_integralLattice (k : ℕ) {v : Sl2Std ℚ n}
    (hv : v ∈ integralLattice n) :
    Associative.dividedPower k (lower ℚ n) v ∈ integralLattice n := by
  rw [mem_integralLattice_iff] at hv ⊢
  intro i
  rw [dividedPower_lower_apply]
  by_cases h : k ≤ (i : ℕ)
  · rw [dite_eq_left h]
    obtain ⟨z, hz⟩ := hv ⟨(i : ℕ) - k, by omega⟩
    refine ⟨((n - (i : ℕ) + k).choose k : ℤ) * z, ?_⟩
    rw [Int.cast_mul, Int.cast_natCast, hz]
  · rw [dite_eq_right h]
    exact ⟨0, by simp⟩

/-- Every generalized binomial coefficient in the Cartan operator preserves the standard
integral lattice. -/
theorem ringChoose_diag_mem_integralLattice (k : ℕ) {v : Sl2Std ℚ n}
    (hv : v ∈ integralLattice n) :
    (Ring.choose (diag ℚ n) k : Module.End ℚ (Sl2Std ℚ n)) v ∈ integralLattice n := by
  rw [mem_integralLattice_iff] at hv ⊢
  intro i
  rw [ringChoose_diag_apply]
  obtain ⟨z, hz⟩ := hv i
  let weight : ℤ := (n : ℤ) - 2 * (i : ℕ)
  have hweight : (weight : ℚ) = (n : ℚ) - 2 * (i : ℕ) := by
    simp only [weight, Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat]
  refine ⟨Ring.choose weight k * z, ?_⟩
  rw [Int.cast_mul, ← TauCeti.Ring.choose_intCast (R := ℚ), hweight, hz]

/-- The rational span of the standard integral lattice is the whole standard module. -/
theorem span_integralLattice_eq_top :
    Submodule.span ℚ (integralLattice n : Set (Sl2Std ℚ n)) = ⊤ := by
  apply top_unique
  rw [← (basis ℚ n).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  apply (mem_integralLattice_iff (n := n)).2
  intro j
  by_cases hji : j = i
  · exact ⟨1, by simp [basis_apply, hji]⟩
  · exact ⟨0, by simp [basis_apply, hji]⟩

/-! ### The restricted rank-one Kostant action -/

local notation "𝔰𝔩₂" => LieAlgebra.SpecialLinear.sl (Fin 2) ℚ
local notation "U𝔰𝔩₂" => _root_.UniversalEnvelopingAlgebra ℚ 𝔰𝔩₂

/-- The enveloping-algebra representation on the standard module `V(n)`. -/
noncomputable def kostantRepresentation :
    U𝔰𝔩₂ →ₐ[ℚ] Module.End ℚ (Sl2Std ℚ n) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ (rep ℚ n)

/-- The enveloping-algebra representation sends the three standard `sl₂` basis elements to the
raising, lowering, and Cartan operators. -/
theorem kostantRepresentation_ι_slFinTwoBasis (i : Fin 3) :
    kostantRepresentation n
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (slFinTwoBasis ℚ i)) =
      ![raise ℚ n, lower ℚ n, diag ℚ n] i := by
  rw [kostantRepresentation, _root_.UniversalEnvelopingAlgebra.lift_ι_apply,
    rep_apply_basis]

private def integralLatticeStabilizer : Subring U𝔰𝔩₂ where
  carrier := {u | ∀ v ∈ integralLattice n, kostantRepresentation n u v ∈ integralLattice n}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := fun {u w} hu hw v hv => by
    rw [map_add, LinearMap.add_apply]
    exact (integralLattice n).add_mem (hu v hv) (hw v hv)
  neg_mem' := fun {u} hu v hv => by
    rw [map_neg, LinearMap.neg_apply]
    exact (integralLattice n).neg_mem (hu v hv)
  mul_mem' := fun {u w} hu hw v hv => by
    rw [map_mul, Module.End.mul_apply]
    exact hu _ (hw v hv)

/-- The rank-one Kostant integral form acts on the standard integral lattice.

The root-vector family is `(e, f)` and the Cartan family is `(h)`, in the standard basis
`TauCeti.slFinTwoBasis ℚ`. The proof checks exactly the three generator families of the Kostant
form against the coordinate formulas above. -/
theorem kostantForm_apply_mem_integralLattice
    (u : U𝔰𝔩₂)
    (hu : u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm
      ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1] ![slFinTwoBasis ℚ 2])
    {v : Sl2Std ℚ n} (hv : v ∈ integralLattice n) :
    kostantRepresentation n u v ∈ integralLattice n := by
  have hle : TauCeti.UniversalEnvelopingAlgebra.kostantForm
      ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1] ![slFinTwoBasis ℚ 2] ≤
        integralLatticeStabilizer n := by
    rw [TauCeti.UniversalEnvelopingAlgebra.kostantForm_le_iff]
    constructor
    · intro i k
      rw [show Associative.dividedPower k
          (_root_.UniversalEnvelopingAlgebra.ι ℚ
            (![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1] i)) ∈ integralLatticeStabilizer n ↔
          ∀ w ∈ integralLattice n,
            kostantRepresentation n
                (Associative.dividedPower k
                  (_root_.UniversalEnvelopingAlgebra.ι ℚ
                    (![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1] i))) w ∈
              integralLattice n from Iff.rfl]
      intro w hw
      have hrep : kostantRepresentation n
          (_root_.UniversalEnvelopingAlgebra.ι ℚ
            (![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1] i)) =
          ![raise ℚ n, lower ℚ n] i := by
        fin_cases i
        · exact kostantRepresentation_ι_slFinTwoBasis n 0
        · exact kostantRepresentation_ι_slFinTwoBasis n 1
      rw [TauCeti.Associative.map_dividedPower, hrep]
      fin_cases i
      · exact dividedPower_raise_mem_integralLattice n k hw
      · exact dividedPower_lower_mem_integralLattice n k hw
    · intro i k
      rw [show Ring.choose
          (_root_.UniversalEnvelopingAlgebra.ι ℚ (![slFinTwoBasis ℚ 2] i)) k ∈
            integralLatticeStabilizer n ↔
          ∀ w ∈ integralLattice n,
            kostantRepresentation n
                (Ring.choose
                  (_root_.UniversalEnvelopingAlgebra.ι ℚ (![slFinTwoBasis ℚ 2] i)) k) w ∈
              integralLattice n from Iff.rfl]
      intro w hw
      have hrep : kostantRepresentation n
          (_root_.UniversalEnvelopingAlgebra.ι ℚ (![slFinTwoBasis ℚ 2] i)) = diag ℚ n := by
        fin_cases i
        exact kostantRepresentation_ι_slFinTwoBasis n 2
      rw [Ring.map_choose, hrep]
      exact ringChoose_diag_mem_integralLattice n k hw
  exact hle hu v hv

end TauCeti.Sl2Std
