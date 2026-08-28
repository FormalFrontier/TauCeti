/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Matrix.NegTranspose
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier

/-!
# The pinned graph automorphism of the type-A Lie algebra

For the standard matrix model of `sl_{r+1}`, type `A_r` diagram reversal is realized by negative
transpose, reversal of the coordinate order, and conjugation by the alternating diagonal matrix.
The alternating signs are what normalize the simple root vectors exactly:

```text
e_i = E_{i,i+1}  ↦  e_{r-1-i},
f_i = E_{i+1,i}  ↦  f_{r-1-i}.
```

Thus the automorphism acts on the Bourbaki-numbered Chevalley generators by `Fin.revPerm`, with no
rescaling of the simple-root parameters. It is involutive, preserves the trace-zero subalgebra,
and also reverses the numbered Cartan generators.

This is the Lie-algebra input to the pinned type-`A` graph automorphism of the full-weight
Chevalley carrier. Lifting the corresponding signed reverse-inverse-transpose map to that carrier
and proving its equation on the root-subgroup maps remains the next step toward the `²A` Steinberg
endomorphism.

## Main declarations

* `TauCeti.SlStd.lieGraphAutomorphism`: the involutive automorphism of `sl_{r+1}`.
* `TauCeti.SlStd.lieGraphAutomorphism_rootGenerator`: its exact action on all numbered positive
  and negative simple-root generators.
* `TauCeti.SlStd.lieGraphAutomorphism_cartanGenerator`: its action on the numbered Cartan
  generators.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 12.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 14.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.

This advances the graph-automorphism and pinning targets in Layer 9 of the ReductiveGroups
roadmap. Milestone L1 of the CFSGStatement roadmap consumes the resulting pinned group
automorphism for the `²A` Steinberg map.
-/

public section

namespace TauCeti.SlStd

open LieAlgebra.SpecialLinear
open scoped Matrix

variable (r : ℕ)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The alternating diagonal matrix `diag(1, -1, 1, ...)` used to normalize type-`A` diagram
reversal on the simple root vectors. -/
private def alternatingDiagonal : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ :=
  Matrix.diagonal fun i => (-1 : ℚ) ^ i.val

private theorem alternatingDiagonal_mul_self :
    alternatingDiagonal r * alternatingDiagonal r = 1 := by
  rw [alternatingDiagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [← pow_add]
    norm_num [two_mul]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

@[instance_reducible]
private noncomputable def invertibleAlternatingDiagonal : Invertible (alternatingDiagonal r) :=
  invertibleOfRightInverse _ _ (alternatingDiagonal_mul_self r)

private theorem alternatingDiagonal_nonsing_inv :
    (alternatingDiagonal r)⁻¹ = alternatingDiagonal r :=
  Matrix.inv_eq_right_inv (alternatingDiagonal_mul_self r)

/-- The ambient matrix automorphism underlying type-`A` diagram reversal: negative transpose,
coordinate reversal, and alternating-diagonal conjugation. -/
private noncomputable def ambientLieGraphAutomorphism :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ ≃ₗ⁅ℚ⁆
      Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ :=
  ((Matrix.negTransposeLieEquiv (Fin (r + 1)) ℚ).trans
    (Matrix.reindexLieEquiv Fin.revPerm)).trans
      ((alternatingDiagonal r).lieConj (invertibleAlternatingDiagonal r))

private theorem ambientLieGraphAutomorphism_apply
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) :
    ambientLieGraphAutomorphism r X =
      alternatingDiagonal r * Matrix.reindex Fin.revPerm Fin.revPerm (-Xᵀ) *
        alternatingDiagonal r := by
  rw [ambientLieGraphAutomorphism, LieEquiv.trans_apply, LieEquiv.trans_apply,
    Matrix.negTransposeLieEquiv_apply, Matrix.reindexLieEquiv_apply, Matrix.lieConj_apply,
    alternatingDiagonal_nonsing_inv]

private theorem ambientLieGraphAutomorphism_apply_apply
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) (i j : Fin (r + 1)) :
    ambientLieGraphAutomorphism r X i j =
      ((-1 : ℚ) ^ i.val) * (-Xᵀ (i.rev) (j.rev)) * ((-1 : ℚ) ^ j.val) := by
  rw [ambientLieGraphAutomorphism_apply, alternatingDiagonal]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.reindex_apply,
    Matrix.transpose_apply]
  simp

private theorem trace_ambientLieGraphAutomorphism
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) :
    Matrix.trace (ambientLieGraphAutomorphism r X) = -Matrix.trace X := by
  rw [ambientLieGraphAutomorphism_apply, Matrix.trace_mul_cycle]
  rw [alternatingDiagonal_mul_self, Matrix.one_mul]
  rw [Matrix.trace, Matrix.trace]
  change (∑ i, (fun j : Fin (r + 1) => -X j j) ((Fin.revPerm).symm i)) =
    -∑ i, X i i
  calc
    _ = ∑ i, -X i i := Equiv.sum_comp (Fin.revPerm).symm (fun i => -X i i)
    _ = -∑ i, X i i := by simp

private theorem ambientLieGraphAutomorphism_map_sl :
    (sl (Fin (r + 1)) ℚ).map (ambientLieGraphAutomorphism r) = sl (Fin (r + 1)) ℚ := by
  apply LieSubalgebra.toSubmodule_injective
  ext X
  change X ∈ (sl (Fin (r + 1)) ℚ).map (ambientLieGraphAutomorphism r) ↔
    X ∈ sl (Fin (r + 1)) ℚ
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    change Matrix.trace Y = 0 at hY
    change Matrix.trace (ambientLieGraphAutomorphism r Y) = 0
    rw [trace_ambientLieGraphAutomorphism, hY, neg_zero]
  · intro hX
    change Matrix.trace X = 0 at hX
    refine ⟨(ambientLieGraphAutomorphism r).symm X, ?_, by simp⟩
    change Matrix.trace ((ambientLieGraphAutomorphism r).symm X) = 0
    have htrace := trace_ambientLieGraphAutomorphism r
      ((ambientLieGraphAutomorphism r).symm X)
    rw [LieEquiv.apply_symm_apply, hX] at htrace
    exact neg_eq_zero.mp htrace.symm

/-- The type-`A_r` graph automorphism of `sl_{r+1}`, normalized to carry every numbered simple
root generator exactly to the generator numbered by diagram reversal. -/
noncomputable def lieGraphAutomorphism :
    sl (Fin (r + 1)) ℚ ≃ₗ⁅ℚ⁆ sl (Fin (r + 1)) ℚ :=
  (ambientLieGraphAutomorphism r).ofSubalgebras _ _ (ambientLieGraphAutomorphism_map_sl r)

/-- Entrywise formula for the type-`A` Lie graph automorphism. -/
theorem val_lieGraphAutomorphism_apply (X : sl (Fin (r + 1)) ℚ)
    (i j : Fin (r + 1)) :
    (lieGraphAutomorphism r X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ) i j =
      ((-1 : ℚ) ^ i.val) * (-(X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ)ᵀ
        (i.rev) (j.rev)) * ((-1 : ℚ) ^ j.val) := by
  change ambientLieGraphAutomorphism r X i j = _
  rw [ambientLieGraphAutomorphism_apply_apply]

private theorem neg_negOnePow_mul_negOnePow_succ (n : ℕ) :
    -((-1 : ℚ) ^ n * (-1 : ℚ) ^ (n + 1)) = 1 := by
  rw [← pow_add, show n + (n + 1) = (n + n) + 1 by omega, pow_succ,
    (Even.add_self n).neg_one_pow]
  norm_num

private theorem negOnePow_val_mul_rev (i : Fin (r + 1)) :
    (-1 : ℚ) ^ i.val * (-1 : ℚ) ^ i.rev.val = (-1 : ℚ) ^ r := by
  rw [← pow_add]
  congr 1
  simp only [Fin.val_rev]
  omega

private theorem negOnePow_mul_self (n : ℕ) :
    (-1 : ℚ) ^ n * (-1 : ℚ) ^ n = 1 := by
  rw [← pow_add, (Even.add_self n).neg_one_pow]

/-- The pinned type-`A` Lie graph automorphism has order two. -/
@[simp]
theorem lieGraphAutomorphism_apply_apply (X : sl (Fin (r + 1)) ℚ) :
    lieGraphAutomorphism r (lieGraphAutomorphism r X) = X := by
  apply SetCoe.ext
  ext i j
  rw [val_lieGraphAutomorphism_apply]
  simp only [Matrix.transpose_apply]
  rw [val_lieGraphAutomorphism_apply]
  simp only [Matrix.transpose_apply, Fin.rev_rev]
  calc
    (-1 : ℚ) ^ i.val *
          -((-1 : ℚ) ^ j.rev.val * -((X : Matrix _ _ ℚ) i j) *
            (-1 : ℚ) ^ i.rev.val) *
        (-1 : ℚ) ^ j.val =
        (((-1 : ℚ) ^ i.val * (-1 : ℚ) ^ i.rev.val) *
          ((-1 : ℚ) ^ j.val * (-1 : ℚ) ^ j.rev.val)) *
            (X : Matrix _ _ ℚ) i j := by ring
    _ = (((-1 : ℚ) ^ r) * (-1 : ℚ) ^ r) * (X : Matrix _ _ ℚ) i j := by
      rw [negOnePow_val_mul_rev, negOnePow_val_mul_rev]
    _ = (X : Matrix _ _ ℚ) i j := by rw [negOnePow_mul_self, one_mul]

/-- The inverse of the pinned type-`A` Lie graph automorphism is itself. -/
@[simp]
theorem lieGraphAutomorphism_symm :
    (lieGraphAutomorphism r).symm = lieGraphAutomorphism r := by
  apply LieEquiv.ext
  intro X
  apply (lieGraphAutomorphism r).injective
  simp

/-- The type-`A` Lie graph automorphism sends a numbered positive or negative simple-root
generator to the generator with reversed Bourbaki number, preserving its sign. -/
@[simp]
theorem lieGraphAutomorphism_rootGenerator (k : Fin r ⊕ Fin r) :
    lieGraphAutomorphism r (rootGenerator r k) =
      rootGenerator r (k.map Fin.revPerm Fin.revPerm) := by
  apply SetCoe.ext
  ext a b
  cases k with
  | inl i =>
      suffices
          -(if i.val = r - b.val ∧ i.val + 1 = r - a.val then
              (-1 : ℚ) ^ a.val * (-1 : ℚ) ^ b.val else 0) =
            if r - (i.val + 1) = a.val ∧ r - (i.val + 1) + 1 = b.val then 1 else 0 by
        simpa [val_lieGraphAutomorphism_apply, val_rootGenerator, Matrix.single_apply,
          Fin.ext_iff]
      split_ifs with h₁ h₂
      · rw [show b.val = a.val + 1 by omega]
        exact neg_negOnePow_mul_negOnePow_succ a.val
      · omega
      · omega
      · rfl
  | inr i =>
      suffices
          -(if i.val + 1 = r - b.val ∧ i.val = r - a.val then
              (-1 : ℚ) ^ a.val * (-1 : ℚ) ^ b.val else 0) =
            if r - (i.val + 1) + 1 = a.val ∧ r - (i.val + 1) = b.val then 1 else 0 by
        simpa [val_lieGraphAutomorphism_apply, val_rootGenerator, Matrix.single_apply,
          Fin.ext_iff]
      split_ifs with h₁ h₂
      · rw [mul_comm, show a.val = b.val + 1 by omega]
        exact neg_negOnePow_mul_negOnePow_succ b.val
      · omega
      · omega
      · rfl

private theorem lie_rootGenerator_pos_neg (i : Fin r) :
    ⁅rootGenerator r (.inl i), rootGenerator r (.inr i)⁆ = cartanGenerator r i := by
  apply SetCoe.ext
  rw [LieSubalgebra.coe_bracket, val_rootGenerator, val_rootGenerator, val_cartanGenerator,
    rootTarget_inl, rootSource_inl, rootTarget_inr, rootSource_inr,
    LieRing.of_associative_ring_bracket, Matrix.single_mul_single_same,
    Matrix.single_mul_single_same]
  norm_num

/-- The type-`A` Lie graph automorphism reverses the numbered Cartan generators. -/
@[simp]
theorem lieGraphAutomorphism_cartanGenerator (i : Fin r) :
    lieGraphAutomorphism r (cartanGenerator r i) = cartanGenerator r i.rev := by
  calc
    lieGraphAutomorphism r (cartanGenerator r i) =
        lieGraphAutomorphism r ⁅rootGenerator r (.inl i), rootGenerator r (.inr i)⁆ := by
      rw [lie_rootGenerator_pos_neg]
    _ = ⁅lieGraphAutomorphism r (rootGenerator r (.inl i)),
        lieGraphAutomorphism r (rootGenerator r (.inr i))⁆ :=
      (lieGraphAutomorphism r).map_lie _ _
    _ = ⁅rootGenerator r (.inl i.rev), rootGenerator r (.inr i.rev)⁆ := by simp
    _ = cartanGenerator r i.rev := lie_rootGenerator_pos_neg r i.rev

end TauCeti.SlStd
