/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets

/-!
# The degree of a constant diagonal double coset

A constant tuple `a = (c, ..., c)` has `natDiagGL n a` a scalar matrix, which is central in
`GL_n(ℚ)` and so normalizes `SL_n(ℤ)`; the double coset `T(c, ..., c)` is therefore a single
coset and `deg T(c, ..., c) = 1`, at every rank.

The rank-two computation `deg T(a₀, a₁) = [SL₂(ℤ) : Γ₀(a₁ / a₀)]`, which is not rank-general,
is in `TauCeti/NumberTheory/HeckeRing/GL2/DiagonalCosetDegree.lean`.

## Main results

* `degree_diagCoset_const`: `deg T(c, ..., c) = 1`, at every rank and for every `c : ℕ` —
  unconditionally, since a non-positive entry sends `natDiagGL` to its junk value `1`, whose
  double coset is the identity.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/Degree.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), keeping only the rank-general constant case; the rank-two
computation is split into `GL2/DiagonalCosetDegree.lean`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.14.
-/

public section

open HeckeRing Matrix.SpecialLinearGroup Matrix
open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn

variable (n : ℕ)

private lemma natDiagGL_const_eq_scalar {c : ℕ} (hc : 0 < c) :
    natDiagGL n (fun _ ↦ c) =
      Matrix.GeneralLinearGroup.scalar (Fin n)
        (Units.mk0 (c : ℚ) (by exact_mod_cast hc.ne')) := by
  apply Units.ext
  ext i j
  simp only [natDiagGL_coe n _ fun _ ↦ hc, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply, Units.val_mk0]

/-- A constant diagonal matrix is a scalar, hence commutes with everything — unconditionally
in the constant, since `c = 0` sends `natDiagGL` to its junk value `1`. -/
private lemma natDiagGL_const_comm (c : ℕ) (g : GL (Fin n) ℚ) :
    natDiagGL n (fun _ ↦ c) * g = g * natDiagGL n (fun _ ↦ c) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  -- at rank zero `GL (Fin 0) ℚ` is trivial
  · exact Subsingleton.elim _ _
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [natDiagGL_of_not_pos n (not_forall.mpr ⟨⟨0, hn⟩, by simp⟩), one_mul, mul_one]
  · rw [natDiagGL_const_eq_scalar n hc]
    exact Matrix.GeneralLinearGroup.scalar_commute _ _

/-- **The constant degree**: a constant diagonal matrix is scalar, hence central, so its
double coset is a single coset and `deg T(c, ..., c) = 1`.

The statement is unconditional in `c`: for `c = 0` the value comes from `natDiagGL`'s junk
branch, which is `1`, whose double coset is the identity — not from centrality. -/
@[simp]
theorem degree_diagCoset_const (c : ℕ) : (diagCoset (fun _ : Fin n ↦ c)).degree = 1 := by
  rw [diagCoset_def, HeckeCoset.degree_mk]
  -- a central element normalizes every subgroup, so Mathlib's lemma applies
  have hnorm : natDiagGL n (fun _ ↦ c) ∈ Subgroup.normalizer (SLnZ n) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [natDiagGL_const_comm n c x, mul_assoc, mul_inv_cancel, mul_one]
  rw [Subgroup.conjAct_pointwise_smul_eq_self hnorm, Subgroup.relIndex_self]

end HeckeRing.GLn
