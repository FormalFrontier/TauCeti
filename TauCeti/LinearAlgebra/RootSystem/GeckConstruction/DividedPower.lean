/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Semisimple
public import TauCeti.RingTheory.DividedPowers.Associative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Integral divided powers in Geck's representation

For a crystallographic reduced root pairing, Geck's construction gives numbered raising and
lowering matrices `RootPairing.GeckConstruction.e` and `RootPairing.GeckConstruction.f` over
`\mathbb{Q}`. This file proves that every divided power of either matrix has integer entries.

On a root vector, the `n`-th power of a raising matrix has coefficient
`(p + 1).ascFactorial n`, where `p` is the distance to the bottom of its root string. Dividing by
`n!` leaves the binomial coefficient `(p + n).choose n`. The exceptional three-dimensional
string through the simple root is handled separately. The lowering result is transported through
Geck's involution `RootPairing.GeckConstruction.ω`.

The coefficient-tracking root-string induction refines the proof pattern of Mathlib's private
nilpotence helper `RootPairing.GeckConstruction.isNilpotent_e_aux` in
`Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Semisimple`. The matrices and their relations
come from Geck's construction in [Geck](Geck2017).

## Main declarations

* `TauCeti.RootPairing.GeckConstruction.exists_intCast_dividedPower_e_apply`: divided powers of
  raising matrices have integer entries.
* `TauCeti.RootPairing.GeckConstruction.exists_intCast_dividedPower_f_apply`: divided powers of
  lowering matrices have integer entries.
-/

open Set
open scoped Matrix

open RootPairing
open RootPairing.GeckConstruction

namespace TauCeti

noncomputable section
public section

variable {ι M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  {P : RootPairing ι ℚ M N} [P.IsCrystallographic] [P.IsReduced] {b : P.Base}
  [Fintype ι] [DecidableEq ι]

omit [P.IsReduced] in
private lemma e_mulVec_v_eq_zero (s : b.support) {j : ι} (hj : P.root j + P.root s ≠ 0)
    (hroot : P.root s + P.root j ∉ range P.root) :
    e s *ᵥ v b j = 0 := by
  let _i := P.indexNeg
  have hneg : j ≠ -s := by
    intro h
    apply hj
    rw [h, indexNeg_neg, root_reflectionPerm, reflection_apply_self, neg_add_cancel]
  have hneg' : j ≠ P.reflectionPerm s s := by
    simpa only [indexNeg_neg] using hneg
  ext (k | k)
  · simp [e, v, hneg']
  · have hk : P.root k ≠ P.root s + P.root j := fun hk => hroot ⟨k, hk⟩
    simp [e, v, hk]

private lemma e_pow_mulVec_v_eq_zero_or_exists (s : b.support) {j : ι}
    (hj : let _i := P.indexNeg; j ≠ -s) (n : ℕ) :
    (e s ^ n) *ᵥ v b j = 0 ∨
      ∃ k : ι, P.root k = P.root j + n • P.root s ∧
        P.chainBotCoeff s k = P.chainBotCoeff s j + n ∧
        (e s ^ n) *ᵥ v b j =
          ((P.chainBotCoeff s j + 1).ascFactorial n : ℚ) • v b k := by
  have : Module.IsReflexive ℚ M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree ℚ M
  let _i := P.indexNeg
  -- Keep the root index and its coefficient in the induction invariant: the successor step needs
  -- both dependent witnesses, so splitting it off would merely restate the whole invariant.
  induction n with
  | zero =>
      refine Or.inr ⟨j, by simp, by simp, ?_⟩
      rw [pow_zero, Matrix.one_mulVec]
      simp
  | succ n ih =>
      rcases ih with h0 | ⟨k, hkroot, hkbot, hkpow⟩
      -- Once an iterate vanishes, every later iterate vanishes as well.
      · left
        rw [pow_succ', ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
      -- The ordinary root-string formula excludes the exceptional string through `-s`.
      have hks : k ≠ -s := by
        rintro rfl
        replace hkroot : P.root (-j) = (n + 1) • P.root s := by
          simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self,
            neg_eq_iff_add_eq_zero, add_smul, one_smul] at hkroot ⊢
          rw [← hkroot]
          module
        rcases n.eq_zero_or_pos with rfl | hn
        · apply hj
          rw [zero_add, one_smul, EmbeddingLike.apply_eq_iff_eq] at hkroot
          simp [← hkroot, -indexNeg_neg]
        · have _i : (n + 1).AtLeastTwo := ⟨by omega⟩
          exact P.nsmul_notMem_range_root (n := n + 1) (i := s) ⟨-j, hkroot⟩
      rw [pow_succ', ← Matrix.mulVec_mulVec, hkpow, Matrix.mulVec_smul]
      by_cases hmem : P.root j + (n + 1) • P.root s ∈ range P.root
      -- If the next root exists, advance its index and the rising-factorial coefficient together.
      · obtain ⟨l, hl⟩ := hmem
        have hlstep : P.root l = P.root s + P.root k := by
          rw [hl, hkroot]
          module
        have hlin : LinearIndependent ℚ ![P.root s, P.root k] := by
          apply IsReduced.linearIndependent P
          · intro hsk
            apply P.nsmul_notMem_range_root (n := 2) (i := s)
            refine ⟨l, ?_⟩
            rw [hlstep, ← hsk, two_smul]
          · intro h
            apply hks
            apply P.root.injective
            rw [indexNeg_neg, root_reflectionPerm, reflection_apply_self]
            exact neg_eq_iff_eq_neg.mp h.symm
        have hlbot : P.chainBotCoeff s l = P.chainBotCoeff s k + 1 :=
          P.chainBotCoeff_of_add hlin (by simpa [add_comm] using hlstep)
        right
        refine ⟨l, hl, by omega, ?_⟩
        rw [show e s *ᵥ v b k = (P.chainBotCoeff s k + 1 : ℚ) • v b l by
          simpa only [Matrix.lie_apply] using e_lie_v_ne (R := ℚ) hlstep]
        rw [smul_smul, hkbot, Nat.ascFactorial_succ]
        push_cast
        module
      -- Otherwise the raising operator kills the current root vector.
      · left
        have hzero : P.root k + P.root s ≠ 0 := by
          intro h
          apply hks
          apply P.root.injective
          rw [indexNeg_neg, root_reflectionPerm, reflection_apply_self]
          exact eq_neg_of_add_eq_zero_left h
        have hroot : P.root s + P.root k ∉ range P.root := by
          rintro ⟨q, hq⟩
          apply hmem
          refine ⟨q, ?_⟩
          rw [hq, hkroot]
          module
        rw [e_mulVec_v_eq_zero s hzero hroot, smul_zero]

private lemma e_mulVec_v_self_eq_zero (s : b.support) : e s *ᵥ v b s = 0 := by
  have : IsAddTorsionFree M := .of_isTorsionFree ℚ M
  have hzero : P.root s + P.root s ≠ 0 := by
    intro h
    apply P.ne_zero s
    have htwo : (2 : ℚ) • P.root s = 0 := by simpa [two_smul] using h
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hroot : P.root s + P.root s ∉ range P.root := by
    rintro ⟨k, hk⟩
    apply P.nsmul_notMem_range_root (n := 2) (i := s)
    exact ⟨k, by simpa [two_smul] using hk⟩
  exact e_mulVec_v_eq_zero s hzero hroot

private lemma e_pow_mulVec_u (s j : b.support) : ∀ n : ℕ,
    (e s ^ n) *ᵥ u j =
      match n with
      | 0 => u j
      | 1 => |b.cartanMatrix s j| • v b s
      | _ + 2 => 0
  | 0 => by rw [pow_zero, Matrix.one_mulVec]
  | 1 => by simpa only [pow_one, Matrix.lie_apply] using e_lie_u (R := ℚ) s j
  | n + 2 => by
      have h2 : e s ^ 2 *ᵥ u j = 0 := by
        rw [show 2 = 1 + 1 by omega, pow_succ, ← Matrix.mulVec_mulVec,
          show e s *ᵥ u j = |b.cartanMatrix s j| • v b s by
          simpa only [Matrix.lie_apply] using e_lie_u (R := ℚ) s j,
          Matrix.mulVec_smul, pow_one, e_mulVec_v_self_eq_zero, smul_zero]
      rw [pow_add, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]

private lemma e_pow_mulVec_v_neg (s : b.support) (n : ℕ) :
    let _i := P.indexNeg
    (e s ^ n) *ᵥ v b (-s : ι) =
      match n with
      | 0 => v b (-s : ι)
      | .succ 0 => u s
      | .succ (.succ 0) => (2 : ℚ) • v b s
      | .succ (.succ (.succ _)) => 0 := by
  dsimp only
  let _i := P.indexNeg
  have hneg : e s *ᵥ v b (-s : ι) = u s := by
    ext (j | j)
    · simp [e, u, v, Pi.single_apply, -indexNeg_neg]
    · by_cases h : P.root j = P.root s + P.root (-s : ι)
      · exfalso
        exact P.ne_zero j (by simpa using h)
      · simp [e, u, v, -indexNeg_neg, h]
  have hu : e s *ᵥ u s = (2 : ℚ) • v b s := by
    ext (j | j)
    · simp [e, u, v]
    · simp [e, u, v, Pi.single_apply]
  match n with
  | 0 => rw [pow_zero, Matrix.one_mulVec]
  | .succ 0 => simpa only [pow_one] using hneg
  | .succ (.succ 0) =>
      -- Pattern matching leaves the exponent in successor form; expose the numeral used below.
      change e s ^ 2 *ᵥ v b (-s : ι) = (2 : ℚ) • v b s
      rw [show 2 = 1 + 1 by omega, pow_succ, ← Matrix.mulVec_mulVec, pow_one, hneg, hu]
  | .succ (.succ (.succ k)) =>
      have h3 : e s ^ 3 *ᵥ v b (-s : ι) = 0 := by
        rw [show 3 = 2 + 1 by omega, pow_succ, ← Matrix.mulVec_mulVec, hneg,
          show e s ^ 2 *ᵥ u s = 0 by simpa using e_pow_mulVec_u s s 2]
      -- The final match branch has exponent `k + 3` only after normalizing its successors.
      change e s ^ (k + 3) *ᵥ v b (-s : ι) = 0
      rw [pow_add, ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]

private theorem exists_intCast_dividedPower_e_mulVec_single (s : b.support) (n : ℕ)
    (j q : b.support ⊕ ι) :
    ∃ z : ℤ, (z : ℚ) = (TauCeti.Associative.dividedPower n (e s) *ᵥ Pi.single j 1) q := by
  have hu (j : b.support) (q : b.support ⊕ ι) :
      ∃ z : ℤ, (z : ℚ) = (u j) q := by
    refine ⟨if q = Sum.inl j then 1 else 0, ?_⟩
    simp [u, Pi.single_apply]
  have hv (c : ℤ) (j : ι) (q : b.support ⊕ ι) :
      ∃ z : ℤ, (z : ℚ) = ((c : ℚ) • v b j) q := by
    refine ⟨if q = Sum.inr j then c else 0, ?_⟩
    simp [v, Pi.single_apply]
  rw [TauCeti.Associative.dividedPower_def, Matrix.smul_mulVec,
    show Pi.single j 1 = match j with | Sum.inl j => u j | Sum.inr j => v b j by
      cases j <;> rfl]
  rcases j with j | j
  · rw [e_pow_mulVec_u]
    match n with
    | 0 => simpa using hu j q
    | 1 => simpa using hv |b.cartanMatrix s j| s q
    | n + 2 => exact ⟨0, by simp⟩
  · let _i := P.indexNeg
    by_cases hj : j = -s
    · subst j
      rw [e_pow_mulVec_v_neg]
      match n with
      | 0 => simpa using hv 1 (-s : ι) q
      | 1 => simpa using hu s q
      | 2 => simpa using hv 1 s q
      | n + 3 => exact ⟨0, by simp⟩
    · rcases e_pow_mulVec_v_eq_zero_or_exists s hj n with h0 | ⟨k, -, -, hk⟩
      · rw [h0, smul_zero]
        exact ⟨0, rfl⟩
      · rw [hk, smul_smul, Nat.ascFactorial_eq_factorial_mul_choose]
        have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        have hcoeff : (n.factorial : ℚ)⁻¹ *
            (n.factorial * (P.chainBotCoeff s j + n).choose n : ℕ) =
            ((P.chainBotCoeff s j + n).choose n : ℚ) := by
          push_cast
          field_simp
        rw [hcoeff]
        exact hv ((P.chainBotCoeff s j + n).choose n) k q

omit [P.IsReduced] in
private lemma dividedPower_f_eq_omega_mul_dividedPower_e_mul_omega (s : b.support) (n : ℕ) :
    TauCeti.Associative.dividedPower n (f s) =
      ω b * TauCeti.Associative.dividedPower n (e s) * ω b := by
  have hp : ω b * f s ^ n = e s ^ n * ω b := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, ω_mul_f, ← mul_assoc]
  rw [TauCeti.Associative.dividedPower_def, TauCeti.Associative.dividedPower_def]
  calc
    (n.factorial : ℚ)⁻¹ • f s ^ n =
        (n.factorial : ℚ)⁻¹ • (ω b * (ω b * f s ^ n)) := by
          rw [← mul_assoc, ω_mul_ω, one_mul]
    _ = (n.factorial : ℚ)⁻¹ • (ω b * (e s ^ n * ω b)) := by rw [hp]
    _ = ω b * ((n.factorial : ℚ)⁻¹ • e s ^ n) * ω b := by
      rw [← smul_mul_assoc, ← mul_assoc, smul_mul_assoc, ← mul_smul_comm]

omit [P.IsCrystallographic] [P.IsReduced] [DecidableEq ι] in
private lemma omega_mulVec_apply (x : b.support ⊕ ι → ℚ) (q : b.support ⊕ ι) :
    let _i := P.indexNeg
    (ω b *ᵥ x) q = match q with
      | Sum.inl q => x (.inl q)
      | Sum.inr q => x (.inr (-q)) := by
  classical
  let _i := P.indexNeg
  rcases q with q | q
  · simp [ω, Matrix.mulVec, dotProduct, Matrix.one_apply]
  · simp only [ω, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add, Matrix.of_apply, ite_mul, one_mul]
    have hiff (a : ι) : q = -a ↔ a = -q := by
      rw [eq_comm, neg_eq_iff_eq_neg]
    simp_rw [hiff]
    simp

omit [P.IsCrystallographic] [P.IsReduced] in
private lemma omega_mulVec_single (j : b.support ⊕ ι) :
    let _i := P.indexNeg
    ω b *ᵥ Pi.single j 1 = match j with
      | Sum.inl j => Pi.single (.inl j) 1
      | Sum.inr j => Pi.single (.inr (-j)) 1 := by
  classical
  let _i := P.indexNeg
  ext q
  rw [omega_mulVec_apply]
  rcases j with j | j <;> rcases q with q | q <;>
    simp [Pi.single_apply, -indexNeg_neg, neg_eq_iff_eq_neg]

private theorem exists_intCast_dividedPower_f_mulVec_single (s : b.support) (n : ℕ)
    (j q : b.support ⊕ ι) :
    ∃ z : ℤ, (z : ℚ) = (TauCeti.Associative.dividedPower n (f s) *ᵥ Pi.single j 1) q := by
  let _i := P.indexNeg
  rw [dividedPower_f_eq_omega_mul_dividedPower_e_mul_omega, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, omega_mulVec_single, omega_mulVec_apply]
  rcases j with j | j <;> rcases q with q | q
  · exact exists_intCast_dividedPower_e_mulVec_single s n (.inl j) (.inl q)
  · exact exists_intCast_dividedPower_e_mulVec_single s n (.inl j) (.inr (-q))
  · exact exists_intCast_dividedPower_e_mulVec_single s n (.inr (-j)) (.inl q)
  · exact exists_intCast_dividedPower_e_mulVec_single s n (.inr (-j)) (.inr (-q))

namespace RootPairing.GeckConstruction

/-- Every entry of a divided power of a numbered raising operator in Geck's representation is
an integer. -/
theorem exists_intCast_dividedPower_e_apply (s : b.support) (n : ℕ)
    (i j : b.support ⊕ ι) :
    ∃ z : ℤ, (z : ℚ) = TauCeti.Associative.dividedPower n (e s) i j := by
  obtain ⟨z, hz⟩ := exists_intCast_dividedPower_e_mulVec_single s n j i
  rw [Matrix.mulVec_single_one] at hz
  exact ⟨z, hz⟩

/-- Every entry of a divided power of a numbered lowering operator in Geck's representation is
an integer. -/
theorem exists_intCast_dividedPower_f_apply (s : b.support) (n : ℕ)
    (i j : b.support ⊕ ι) :
    ∃ z : ℤ, (z : ℚ) = TauCeti.Associative.dividedPower n (f s) i j := by
  obtain ⟨z, hz⟩ := exists_intCast_dividedPower_f_mulVec_single s n j i
  rw [Matrix.mulVec_single_one] at hz
  exact ⟨z, hz⟩

end RootPairing.GeckConstruction

end
end
end TauCeti
