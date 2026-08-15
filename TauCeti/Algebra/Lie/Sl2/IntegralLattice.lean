/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Lattice
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
* `TauCeti.Sl2Std.coe_integerCoordinatesLinearEquiv_apply` and
  `TauCeti.Sl2Std.coe_integerCoordinatesLinearEquiv_symm_apply`: coordinate characterizations
  of the forward and inverse identification.
* `TauCeti.Sl2Std.dividedPower_raise_apply` and
  `TauCeti.Sl2Std.dividedPower_lower_apply`: the integral coordinate formulas for the root
  divided powers.
* `TauCeti.Sl2Std.ringChoose_diag_apply`: the coordinate formula for Cartan binomials.
* `TauCeti.Sl2Std.kostantForm_apply_mem_integralLattice`: the rank-one Kostant form preserves
  the lattice.
* `TauCeti.Sl2Std.kostantRepresentationIntegralLattice`: the canonical `ℤ`-algebra representation
  of the rank-one Kostant form on the integral lattice.

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

section GeneralCoefficients

variable {K : Type*} [CommRing K] {n : ℕ}

private lemma rat_smul_apply [Algebra ℚ K] (q : ℚ) (w : Sl2Std K n) (i : Fin (n + 1)) :
    (q • w) i = algebraMap ℚ K q * w i := by
  have : (q • w) i = q • (w i) := rfl
  rw [this, Algebra.smul_def]

private theorem raise_pow_apply_of_le {k : ℕ}
    (v : Sl2Std K n) (i : Fin (n + 1)) (h : (i : ℕ) + k ≤ n) :
    ((raise K n) ^ k) v i = (((i : ℕ) + k).descFactorial k : K) * v ⟨(i : ℕ) + k, by omega⟩ := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, raise_apply]
      have hi : (i : ℕ) < n := by omega
      rw [dite_eq_left hi]
      let j : Fin (n + 1) := ⟨(i : ℕ) + 1, by omega⟩
      have hj : (j : ℕ) + k ≤ n := by dsimp [j]; omega
      have hj_eq : (j : ℕ) + k = (i : ℕ) + (k + 1) := by dsimp [j]; omega
      rw [ih j hj]
      simp only [hj_eq]
      rw [Nat.descFactorial_succ]
      have hfactor : (i : ℕ) + (k + 1) - k = (i : ℕ) + 1 := by omega
      rw [hfactor]
      push_cast
      ring

private theorem raise_pow_apply (k : ℕ) (v : Sl2Std K n) (i : Fin (n + 1)) :
    ((raise K n) ^ k) v i =
      if h : (i : ℕ) + k ≤ n then
        (((i : ℕ) + k).descFactorial k : K) * v ⟨(i : ℕ) + k, by omega⟩
      else 0 := by
  split_ifs with h
  · exact raise_pow_apply_of_le v i h
  · exact raise_pow_apply_eq_zero k v i (by omega)

private theorem lower_pow_apply_of_le {k : ℕ}
    (v : Sl2Std K n) (i : Fin (n + 1)) (h : k ≤ (i : ℕ)) :
    ((lower K n) ^ k) v i =
      ((n - (i : ℕ) + k).descFactorial k : K) *
        v ⟨(i : ℕ) - k, by omega⟩ := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, lower_apply]
      have hi : 0 < (i : ℕ) := by omega
      rw [dite_eq_left hi]
      let j : Fin (n + 1) := ⟨(i : ℕ) - 1, by omega⟩
      have hj : k ≤ (j : ℕ) := by dsimp [j]; omega
      rw [ih j hj]
      rw [Nat.descFactorial_succ]
      have hsub : n - (j : ℕ) + k = n - (i : ℕ) + (k + 1) := by dsimp [j]; omega
      rw [hsub]
      have hfactor : n - (i : ℕ) + (k + 1) - k = n - (i : ℕ) + 1 := by omega
      rw [hfactor]
      have hidx :
          (⟨(j : ℕ) - k, by dsimp [j]; omega⟩ : Fin (n + 1)) =
            ⟨(i : ℕ) - (k + 1), by omega⟩ := by
        ext
        dsimp [j]
        omega
      rw [hidx]
      have hle : (i : ℕ) ≤ n := by have := i.isLt; omega
      have hcoeff : (n : K) - (i : ℕ) + 1 = ((n - (i : ℕ) + 1 : ℕ) : K) := by
        rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_one]
      rw [hcoeff, Nat.cast_mul]
      ring

private theorem lower_pow_apply_eq_zero (k : ℕ) (v : Sl2Std K n) (i : Fin (n + 1))
    (h : (i : ℕ) < k) :
    ((lower K n) ^ k) v i = 0 := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, lower_apply]
      by_cases hi : 0 < (i : ℕ)
      · rw [dite_eq_left hi]
        let j : Fin (n + 1) := ⟨(i : ℕ) - 1, by omega⟩
        have hj : (j : ℕ) < k := by dsimp [j]; omega
        rw [ih j hj, mul_zero]
      · rw [dite_eq_right hi]

private theorem lower_pow_apply (k : ℕ) (v : Sl2Std K n) (i : Fin (n + 1)) :
    ((lower K n) ^ k) v i =
      if h : k ≤ (i : ℕ) then
        ((n - (i : ℕ) + k).descFactorial k : K) *
          v ⟨(i : ℕ) - k, by omega⟩
      else 0 := by
  split_ifs with h
  · exact lower_pow_apply_of_le v i h
  · exact lower_pow_apply_eq_zero k v i (by omega)

/-- The `k`-th divided raising operator reads coordinate `i + k` with the integral coefficient
`(i + k choose k)`, and vanishes when that coordinate is past the end of `V(n)`. -/
@[simp]
theorem dividedPower_raise_apply [Algebra ℚ K]
    (k : ℕ) (v : Sl2Std K n) (i : Fin (n + 1)) :
    (Associative.dividedPower k (raise K n)) v i =
      if h : (i : ℕ) + k ≤ n then
        (((i : ℕ) + k).choose k : K) * v ⟨(i : ℕ) + k, by omega⟩
      else 0 := by
  rw [Associative.dividedPower_def, LinearMap.smul_apply, rat_smul_apply, raise_pow_apply]
  split_ifs with h
  · rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hfac : (k.factorial : K) = algebraMap ℚ K (k.factorial : ℚ) := by
      simp only [map_natCast]
    calc
      algebraMap ℚ K (k.factorial : ℚ)⁻¹ *
          (((k.factorial : K) * (((i : ℕ) + k).choose k : K)) * v ⟨(i : ℕ) + k, by omega⟩) =
        (algebraMap ℚ K (k.factorial : ℚ)⁻¹ * (k.factorial : K) * (((i : ℕ) + k).choose k : K)) *
          v ⟨(i : ℕ) + k, by omega⟩ := by ring
      _ = (((i : ℕ) + k).choose k : K) * v ⟨(i : ℕ) + k, by omega⟩ := by
        rw [hfac, ← map_mul (algebraMap ℚ K), inv_mul_cancel₀ hk, map_one, one_mul]
  · rw [mul_zero]

/-- The `k`-th divided lowering operator reads coordinate `i - k` with the integral coefficient
`(n - i + k choose k)`, and vanishes when `k > i`. -/
@[simp]
theorem dividedPower_lower_apply [Algebra ℚ K]
    (k : ℕ) (v : Sl2Std K n) (i : Fin (n + 1)) :
    (Associative.dividedPower k (lower K n)) v i =
      if h : k ≤ (i : ℕ) then
        ((n - (i : ℕ) + k).choose k : K) * v ⟨(i : ℕ) - k, by omega⟩
      else 0 := by
  rw [Associative.dividedPower_def, LinearMap.smul_apply, rat_smul_apply, lower_pow_apply]
  split_ifs with h
  · rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hfac : (k.factorial : K) = algebraMap ℚ K (k.factorial : ℚ) := by
      simp only [map_natCast]
    calc
      algebraMap ℚ K (k.factorial : ℚ)⁻¹ *
          (((k.factorial : K) * ((n - (i : ℕ) + k).choose k : K)) * v ⟨(i : ℕ) - k, by omega⟩) =
        (algebraMap ℚ K (k.factorial : ℚ)⁻¹ * (k.factorial : K) *
          ((n - (i : ℕ) + k).choose k : K)) * v ⟨(i : ℕ) - k, by omega⟩ := by ring
      _ = ((n - (i : ℕ) + k).choose k : K) * v ⟨(i : ℕ) - k, by omega⟩ := by
        rw [hfac, ← map_mul (algebraMap ℚ K), inv_mul_cancel₀ hk, map_one, one_mul]
  · rw [mul_zero]

private theorem diag_pow_apply
    (k : ℕ) (v : Sl2Std K n) (i : Fin (n + 1)) :
    ((diag K n) ^ k) v i = ((n : K) - 2 * (i : ℕ)) ^ k * v i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, diag_apply, ih]
      ring

private theorem zsmul_end_apply
    (z : ℤ) (f : Module.End K (Sl2Std K n))
    (v : Sl2Std K n) (i : Fin (n + 1)) :
    (z • f) v i = (z : K) * f v i := by
  rw [LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul K, smul_apply]

private theorem smeval_diag_apply
    (p : ℤ[X]) (v : Sl2Std K n) (i : Fin (n + 1)) :
    p.smeval (diag K n) v i = p.smeval ((n : K) - 2 * (i : ℕ)) * v i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.smeval_add, LinearMap.add_apply, add_apply, hp, hq,
        Polynomial.smeval_add]
      ring
  | monomial k z =>
      rw [Polynomial.smeval_monomial, zsmul_end_apply, diag_pow_apply,
        Polynomial.smeval_monomial]
      rw [← Int.cast_smul_eq_zsmul K]
      simp only [smul_eq_mul]
      ring

/-- The `k`-th Cartan binomial acts diagonally on `V(n)`, with eigenvalue
`(n - 2i choose k)` on coordinate `i`. -/
@[simp]
theorem ringChoose_diag_apply [Algebra ℚ K]
    (k : ℕ) (v : Sl2Std K n) (i : Fin (n + 1)) :
    (Ring.choose (diag K n) k) v i =
      Ring.choose ((n : K) - 2 * (i : ℕ)) k * v i := by
  let weight : K := (n : K) - 2 * (i : ℕ)
  let p := descPochhammer ℤ k
  have hop := Ring.descPochhammer_eq_factorial_smul_choose (diag K n) k
  have hop' : p.smeval (diag K n) v i =
      k.factorial • ((Ring.choose (diag K n) k : Module.End K (Sl2Std K n)) v i) := by
    rw [hop, LinearMap.smul_apply]
    rfl
  have hscalar := Ring.descPochhammer_eq_factorial_smul_choose weight k
  have hscalar' : p.smeval weight * v i =
      k.factorial • (Ring.choose weight k * v i) := by
    rw [hscalar, smul_mul_assoc]
  have heq : k.factorial • ((Ring.choose (diag K n) k : Module.End K (Sl2Std K n)) v i) =
      k.factorial • (Ring.choose weight k * v i) := by
    rw [← hop', smeval_diag_apply, hscalar']
  have : IsAddTorsionFree K := .of_module_rat K
  exact (nsmul_right_inj (Nat.factorial_ne_zero k)).mp heq

end GeneralCoefficients

variable (n : ℕ)

/-- The coordinate `ℤ`-lattice in the rational standard `sl₂`-module `V(n)`.

A vector belongs to this submodule exactly when each of its coordinates is an integer viewed in
`ℚ`; see `mem_integralLattice_iff`. -/
def integralLattice : Submodule ℤ (Sl2Std ℚ n) :=
  Submodule.span ℤ (Set.range (basis ℚ n))

/-- A vector belongs to the standard integral lattice exactly when all its coordinates are
integer-valued. -/
@[simp]
theorem mem_integralLattice_iff {v : Sl2Std ℚ n} :
    v ∈ integralLattice n ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = v i := by
  rw [integralLattice, Module.Basis.mem_span_iff_repr_mem]
  simp only [basis_repr_apply, Set.mem_range, eq_comm]
  rfl

/-- Integer coordinate vectors are linearly equivalent to the standard integral lattice. -/
noncomputable def integerCoordinatesLinearEquiv :
    (Fin (n + 1) → ℤ) ≃ₗ[ℤ] integralLattice n :=
  ((basis ℚ n).restrictScalars ℤ).equivFun.symm

/-- Inverse evaluation of the coordinate linear equivalence yields the integer coordinates. -/
@[simp]
theorem coe_integerCoordinatesLinearEquiv_symm_apply (v : integralLattice n) (i : Fin (n + 1)) :
    (((integerCoordinatesLinearEquiv n).symm v i : ℤ) : ℚ) = (v : Sl2Std ℚ n) i := by
  have h := Module.Basis.restrictScalars_repr_apply ℤ (basis ℚ n) v i
  have hequiv : (integerCoordinatesLinearEquiv n).symm v i =
      ((basis ℚ n).restrictScalars ℤ).repr v i := rfl
  rw [hequiv]
  exact h.trans (basis_repr_apply (v : Sl2Std ℚ n) i)

/-- Forward evaluation of the coordinate linear equivalence on a coordinate vector. -/
@[simp]
theorem coe_integerCoordinatesLinearEquiv_apply (z : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    ((integerCoordinatesLinearEquiv n z : integralLattice n) : Sl2Std ℚ n) i = (z i : ℚ) := by
  have h := coe_integerCoordinatesLinearEquiv_symm_apply n (integerCoordinatesLinearEquiv n z) i
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

noncomputable instance : Module.Free ℤ (integralLattice n) :=
  Module.Free.of_basis ((basis ℚ n).restrictScalars ℤ)

noncomputable instance : Module.Finite ℤ (integralLattice n) :=
  Module.Finite.of_basis ((basis ℚ n).restrictScalars ℤ)

/-- The standard integral lattice has rank `n + 1`. -/
@[simp]
theorem finrank_integralLattice : Module.finrank ℤ (integralLattice n) = n + 1 := by
  have h := Module.finrank_eq_card_basis ((basis ℚ n).restrictScalars ℤ)
  rw [Fintype.card_fin] at h
  exact h

/-- Every divided power of the raising operator preserves the standard integral lattice. -/
theorem dividedPower_raise_mem_integralLattice (k : ℕ) {v : Sl2Std ℚ n}
    (hv : v ∈ integralLattice n) :
    Associative.dividedPower k (raise ℚ n) v ∈ integralLattice n := by
  rw [mem_integralLattice_iff]
  intro i
  rw [mem_integralLattice_iff] at hv
  have hstep := dividedPower_raise_apply (K := ℚ) k v i
  by_cases h : (i : ℕ) + k ≤ n
  · obtain ⟨z, hz⟩ := hv ⟨(i : ℕ) + k, by omega⟩
    refine ⟨(((i : ℕ) + k).choose k : ℤ) * z, ?_⟩
    erw [hstep]
    rw [dite_eq_left h, Int.cast_mul, Int.cast_natCast, hz]
  · refine ⟨0, ?_⟩
    erw [hstep]
    rw [dite_eq_right h, Int.cast_zero]

/-- Every divided power of the lowering operator preserves the standard integral lattice. -/
theorem dividedPower_lower_mem_integralLattice (k : ℕ) {v : Sl2Std ℚ n}
    (hv : v ∈ integralLattice n) :
    Associative.dividedPower k (lower ℚ n) v ∈ integralLattice n := by
  rw [mem_integralLattice_iff]
  intro i
  rw [mem_integralLattice_iff] at hv
  have hstep := dividedPower_lower_apply (K := ℚ) k v i
  by_cases h : k ≤ (i : ℕ)
  · obtain ⟨z, hz⟩ := hv ⟨(i : ℕ) - k, by omega⟩
    refine ⟨((n - (i : ℕ) + k).choose k : ℤ) * z, ?_⟩
    erw [hstep]
    rw [dite_eq_left h, Int.cast_mul, Int.cast_natCast, hz]
  · refine ⟨0, ?_⟩
    erw [hstep]
    rw [dite_eq_right h, Int.cast_zero]

/-- Every generalized binomial coefficient in the Cartan operator preserves the standard
integral lattice. -/
theorem ringChoose_diag_mem_integralLattice (k : ℕ) {v : Sl2Std ℚ n}
    (hv : v ∈ integralLattice n) :
    (Ring.choose (diag ℚ n) k : Module.End ℚ (Sl2Std ℚ n)) v ∈ integralLattice n := by
  rw [mem_integralLattice_iff]
  intro i
  rw [mem_integralLattice_iff] at hv
  obtain ⟨z, hz⟩ := hv i
  let weight : ℤ := (n : ℤ) - 2 * (i : ℕ)
  have hweight : (weight : ℚ) = (n : ℚ) - 2 * (i : ℕ) := by
    simp only [weight, Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat]
  refine ⟨Ring.choose weight k * z, ?_⟩
  have hstep := ringChoose_diag_apply (K := ℚ) k v i
  erw [hstep]
  rw [Int.cast_mul, ← TauCeti.Ring.choose_intCast (R := ℚ), hweight, hz]

/-- The rational span of the standard integral lattice is the whole standard module. -/
theorem span_integralLattice_eq_top :
    Submodule.span ℚ (integralLattice n : Set (Sl2Std ℚ n)) = ⊤ := by
  rw [integralLattice, Submodule.span_span_of_tower, (basis ℚ n).span_eq]

instance : Submodule.IsLattice ℚ (integralLattice n) where
  fg := by
    rw [← Module.Finite.iff_fg]
    infer_instance
  span_eq_top := span_integralLattice_eq_top n

/-! ### The restricted rank-one Kostant action -/

local notation "𝔰𝔩₂" => LieAlgebra.SpecialLinear.sl (Fin 2) ℚ
local notation "U𝔰𝔩₂" => _root_.UniversalEnvelopingAlgebra ℚ 𝔰𝔩₂

/-- The enveloping-algebra representation on the standard module `V(n)`. -/
noncomputable def kostantRepresentation :
    U𝔰𝔩₂ →ₐ[ℚ] Module.End ℚ (Sl2Std ℚ n) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ (rep ℚ n)

/-- The enveloping-algebra representation extends the standard `sl₂` representation. -/
@[simp]
theorem kostantRepresentation_ι_apply (x : 𝔰𝔩₂) :
    kostantRepresentation n
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ 𝔰𝔩₂ (TensorAlgebra.ι ℚ x)) =
      rep ℚ n x := by
  rw [kostantRepresentation, _root_.UniversalEnvelopingAlgebra.lift_ι_apply']

/-- The enveloping-algebra representation sends the three standard `sl₂` basis elements to the
raising, lowering, and Cartan operators. -/
theorem kostantRepresentation_ι_slFinTwoBasis (i : Fin 3) :
    kostantRepresentation n
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (slFinTwoBasis ℚ i)) =
      ![raise ℚ n, lower ℚ n, diag ℚ n] i := by
  rw [_root_.UniversalEnvelopingAlgebra.ι_apply, kostantRepresentation_ι_apply,
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

private theorem mem_integralLatticeStabilizer_iff (u : U𝔰𝔩₂) :
    u ∈ integralLatticeStabilizer n ↔
      ∀ v ∈ integralLattice n, kostantRepresentation n u v ∈ integralLattice n :=
  Iff.rfl

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
      rw [mem_integralLatticeStabilizer_iff]
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
      rw [mem_integralLatticeStabilizer_iff]
      intro w hw
      have hrep : kostantRepresentation n
          (_root_.UniversalEnvelopingAlgebra.ι ℚ (![slFinTwoBasis ℚ 2] i)) = diag ℚ n := by
        fin_cases i
        exact kostantRepresentation_ι_slFinTwoBasis n 2
      rw [Ring.map_choose, hrep]
      exact ringChoose_diag_mem_integralLattice n k hw
  exact hle hu v hv

/-- The canonical representation of the rank-one Kostant integral form on the standard
integral lattice `V(n)ℤ`. -/
noncomputable def kostantRepresentationIntegralLattice :
    TauCeti.UniversalEnvelopingAlgebra.kostantForm
        ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1] ![slFinTwoBasis ℚ 2] →ₐ[ℤ]
      Module.End ℤ (integralLattice n) where
  toFun u := {
    toFun v := ⟨kostantRepresentation n (u : U𝔰𝔩₂) (v : Sl2Std ℚ n),
      kostantForm_apply_mem_integralLattice n (u : U𝔰𝔩₂) u.2 v.2⟩
    map_add' v w := Subtype.ext (by simp)
    map_smul' z v := Subtype.ext (by
      dsimp
      rw [← Int.cast_smul_eq_zsmul ℚ z (v : Sl2Std ℚ n)]
      exact (kostantRepresentation n (u : U𝔰𝔩₂)).map_smul z (v : Sl2Std ℚ n))
  }
  map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
  map_mul' u w := LinearMap.ext fun v => Subtype.ext (by simp)
  map_zero' := LinearMap.ext fun v => Subtype.ext (by simp)
  map_add' u w := LinearMap.ext fun v => Subtype.ext (by simp)
  commutes' z := LinearMap.ext fun v => Subtype.ext (by
    have h1 : kostantRepresentation n (↑(algebraMap ℤ
        (TauCeti.UniversalEnvelopingAlgebra.kostantForm
          ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1] ![slFinTwoBasis ℚ 2]) z) : U𝔰𝔩₂)
        (v : Sl2Std ℚ n) = z • (v : Sl2Std ℚ n) := by
      have : (↑(algebraMap ℤ (TauCeti.UniversalEnvelopingAlgebra.kostantForm
        ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1] ![slFinTwoBasis ℚ 2]) z) : U𝔰𝔩₂) = (z : U𝔰𝔩₂) := rfl
      rw [this, map_intCast, Module.End.intCast_apply]
    have h2 : ((algebraMap ℤ (Module.End ℤ (integralLattice n)) z v :
        integralLattice n) : Sl2Std ℚ n) = z • (v : Sl2Std ℚ n) := by
      have : (algebraMap ℤ (Module.End ℤ (integralLattice n)) z) =
          (z : Module.End ℤ (integralLattice n)) := rfl
      rw [this, Module.End.intCast_apply]
      rfl
    exact h1.trans h2.symm)

/-- The ambient action of the restricted Kostant representation agrees with the enveloping-algebra
representation on the standard module. -/
@[simp]
theorem coe_kostantRepresentationIntegralLattice_apply
    (u : TauCeti.UniversalEnvelopingAlgebra.kostantForm
      ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1] ![slFinTwoBasis ℚ 2])
    (v : integralLattice n) :
    ((kostantRepresentationIntegralLattice n u v : integralLattice n) : Sl2Std ℚ n) =
      kostantRepresentation n (u : U𝔰𝔩₂) (v : Sl2Std ℚ n) :=
  (rfl)

end TauCeti.Sl2Std
