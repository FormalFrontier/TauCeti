/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Matrix.NegTranspose
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier
import TauCeti.Algebra.Lie.Sl2.Basic

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

universe u

variable (r : ℕ)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The alternating diagonal matrix `diag(1, -1, 1, ...)` used to normalize type-`A` diagram
reversal on the simple root vectors. -/
private def alternatingDiagonal (R : Type u) [CommRing R] :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.diagonal fun i => (-1 : R) ^ i.val

private theorem alternatingDiagonal_mul_self (R : Type u) [CommRing R] :
    alternatingDiagonal r R * alternatingDiagonal r R = 1 := by
  rw [alternatingDiagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [← pow_add]
    norm_num [two_mul]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

@[instance_reducible]
private noncomputable def invertibleAlternatingDiagonal (R : Type u) [CommRing R] :
    Invertible (alternatingDiagonal r R) :=
  invertibleOfRightInverse _ _ (alternatingDiagonal_mul_self r R)

private theorem alternatingDiagonal_nonsing_inv (R : Type u) [CommRing R] :
    (alternatingDiagonal r R)⁻¹ = alternatingDiagonal r R :=
  Matrix.inv_eq_right_inv (alternatingDiagonal_mul_self r R)

/-- The ambient matrix automorphism underlying type-`A` diagram reversal: negative transpose,
coordinate reversal, and alternating-diagonal conjugation. -/
private noncomputable def ambientLieGraphAutomorphism (R : Type u) [CommRing R] :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R ≃ₗ⁅R⁆
      Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  ((Matrix.negTransposeLieEquiv (Fin (r + 1)) R).trans
    (Matrix.reindexLieEquiv Fin.revPerm)).trans
      ((alternatingDiagonal r R).lieConj (invertibleAlternatingDiagonal r R))

private theorem ambientLieGraphAutomorphism_apply
    (R : Type u) [CommRing R] (X : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    ambientLieGraphAutomorphism r R X =
      alternatingDiagonal r R * Matrix.reindex Fin.revPerm Fin.revPerm (-Xᵀ) *
        alternatingDiagonal r R := by
  rw [ambientLieGraphAutomorphism, LieEquiv.trans_apply, LieEquiv.trans_apply,
    Matrix.negTransposeLieEquiv_apply, Matrix.reindexLieEquiv_apply, Matrix.lieConj_apply,
    alternatingDiagonal_nonsing_inv]

private theorem ambientLieGraphAutomorphism_apply_apply
    (R : Type u) [CommRing R] (X : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (i j : Fin (r + 1)) :
    ambientLieGraphAutomorphism r R X i j =
      ((-1 : R) ^ i.val) * (-Xᵀ (i.rev) (j.rev)) * ((-1 : R) ^ j.val) := by
  rw [ambientLieGraphAutomorphism_apply, alternatingDiagonal]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.reindex_apply,
    Matrix.transpose_apply]
  simp

private theorem trace_ambientLieGraphAutomorphism
    (R : Type u) [CommRing R] (X : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    Matrix.trace (ambientLieGraphAutomorphism r R X) = -Matrix.trace X := by
  rw [ambientLieGraphAutomorphism_apply, Matrix.trace_mul_cycle]
  rw [alternatingDiagonal_mul_self, Matrix.one_mul]
  rw [Matrix.trace, Matrix.trace]
  -- Unfolding `trace` leaves the diagonal of the reindexed negative transpose; expose that
  -- function composition so `Equiv.sum_comp` can remove the coordinate permutation.
  change (∑ i, (fun j : Fin (r + 1) => -X j j) ((Fin.revPerm).symm i)) =
    -∑ i, X i i
  calc
    _ = ∑ i, -X i i := Equiv.sum_comp (Fin.revPerm).symm (fun i => -X i i)
    _ = -∑ i, X i i := by simp

private theorem ambientLieGraphAutomorphism_map_sl (R : Type u) [CommRing R] :
    (sl (Fin (r + 1)) R).map (ambientLieGraphAutomorphism r R) = sl (Fin (r + 1)) R := by
  apply LieSubalgebra.toSubmodule_injective
  ext X
  -- `LieSubalgebra.toSubmodule_injective` presents equality as submodule membership; unfold only
  -- that representation before using the Lie-subalgebra map API.
  change X ∈ (sl (Fin (r + 1)) R).map (ambientLieGraphAutomorphism r R) ↔
    X ∈ sl (Fin (r + 1)) R
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    -- Membership in `sl` is definitionally membership in the kernel of the matrix trace map.
    change Matrix.trace Y = 0 at hY
    change Matrix.trace (ambientLieGraphAutomorphism r R Y) = 0
    rw [trace_ambientLieGraphAutomorphism, hY, neg_zero]
  · intro hX
    change Matrix.trace X = 0 at hX
    refine ⟨(ambientLieGraphAutomorphism r R).symm X, ?_, by simp⟩
    -- As above, reduce the preimage's `sl` membership to its trace equation.
    change Matrix.trace ((ambientLieGraphAutomorphism r R).symm X) = 0
    have htrace := trace_ambientLieGraphAutomorphism r R
      ((ambientLieGraphAutomorphism r R).symm X)
    rw [LieEquiv.apply_symm_apply, hX] at htrace
    exact neg_eq_zero.mp htrace.symm

/-- The type-`A_r` graph automorphism of `sl_{r+1}` over a commutative ring. Over `ℚ`, its
normalization carries every numbered simple root generator exactly to the generator numbered by
diagram reversal. -/
noncomputable def lieGraphAutomorphism {R : Type u} [CommRing R] :
    sl (Fin (r + 1)) R ≃ₗ⁅R⁆ sl (Fin (r + 1)) R :=
  (ambientLieGraphAutomorphism r R).ofSubalgebras _ _
    (ambientLieGraphAutomorphism_map_sl r R)

/-- Entrywise formula for the type-`A` Lie graph automorphism. -/
@[simp]
theorem val_lieGraphAutomorphism_apply {R : Type u} [CommRing R]
    (X : sl (Fin (r + 1)) R)
    (i j : Fin (r + 1)) :
    (lieGraphAutomorphism r X : Matrix (Fin (r + 1)) (Fin (r + 1)) R) i j =
      ((-1 : R) ^ i.val) * (-(X : Matrix (Fin (r + 1)) (Fin (r + 1)) R)ᵀ
        (i.rev) (j.rev)) * ((-1 : R) ^ j.val) := by
  -- The restricted equivalence coerces definitionally to the ambient matrix equivalence.
  change ambientLieGraphAutomorphism r R X i j = _
  rw [ambientLieGraphAutomorphism_apply_apply]

private theorem neg_negOnePow_mul_negOnePow_succ (R : Type u) [CommRing R] (n : ℕ) :
    -((-1 : R) ^ n * (-1 : R) ^ (n + 1)) = 1 := by
  have hsum : n + (n + 1) = (n + n) + 1 := by omega
  rw [← pow_add, hsum, pow_succ,
    (Even.add_self n).neg_one_pow]
  norm_num

private theorem negOnePow_val_mul_rev (R : Type u) [CommRing R] (i : Fin (r + 1)) :
    (-1 : R) ^ i.val * (-1 : R) ^ i.rev.val = (-1 : R) ^ r := by
  rw [← pow_add]
  congr 1
  simp only [Fin.val_rev]
  omega

private theorem negOnePow_mul_self (R : Type u) [CommRing R] (n : ℕ) :
    (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
  rw [← pow_add, (Even.add_self n).neg_one_pow]

/-- The pinned type-`A` Lie graph automorphism has order two. -/
@[simp]
theorem lieGraphAutomorphism_apply_apply {R : Type u} [CommRing R]
    (X : sl (Fin (r + 1)) R) :
    lieGraphAutomorphism r (lieGraphAutomorphism r X) = X := by
  apply SetCoe.ext
  ext i j
  rw [val_lieGraphAutomorphism_apply]
  simp only [Matrix.transpose_apply]
  rw [val_lieGraphAutomorphism_apply]
  simp only [Matrix.transpose_apply, Fin.rev_rev]
  calc
    (-1 : R) ^ i.val *
          -((-1 : R) ^ j.rev.val * -((X : Matrix _ _ R) i j) *
            (-1 : R) ^ i.rev.val) *
        (-1 : R) ^ j.val =
        (((-1 : R) ^ i.val * (-1 : R) ^ i.rev.val) *
          ((-1 : R) ^ j.val * (-1 : R) ^ j.rev.val)) *
            (X : Matrix _ _ R) i j := by ring
    _ = (((-1 : R) ^ r) * (-1 : R) ^ r) * (X : Matrix _ _ R) i j := by
      rw [negOnePow_val_mul_rev, negOnePow_val_mul_rev]
    _ = (X : Matrix _ _ R) i j := by rw [negOnePow_mul_self, one_mul]

/-- The inverse of the pinned type-`A` Lie graph automorphism is itself. -/
@[simp]
theorem lieGraphAutomorphism_symm {R : Type u} [CommRing R] :
    (lieGraphAutomorphism (R := R) r).symm = lieGraphAutomorphism r := by
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
  -- Expanding the subtype coercions and matrix units turns each summand case into the displayed
  -- scalar `if` identity; the four branches then contain only index arithmetic and signs.
  cases k with
  | inl i =>
      suffices
          -(if i.val = r - b.val ∧ i.val + 1 = r - a.val then
              (-1 : ℚ) ^ a.val * (-1 : ℚ) ^ b.val else 0) =
            if r - (i.val + 1) = a.val ∧ r - (i.val + 1) + 1 = b.val then 1 else 0 by
        simpa [val_lieGraphAutomorphism_apply, val_rootGenerator, Matrix.single_apply,
          Fin.ext_iff]
      split_ifs with h₁ h₂
      · have hab : b.val = a.val + 1 := by omega
        rw [hab]
        exact neg_negOnePow_mul_negOnePow_succ ℚ a.val
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
      · have hab : a.val = b.val + 1 := by omega
        rw [mul_comm, hab]
        exact neg_negOnePow_mul_negOnePow_succ ℚ b.val
      · omega
      · omega
      · rfl

/-- The type-`A` Lie graph automorphism reverses the numbered Cartan generators. -/
@[simp]
theorem lieGraphAutomorphism_cartanGenerator (i : Fin r) :
    lieGraphAutomorphism r (cartanGenerator r i) = cartanGenerator r i.rev := by
  calc
    lieGraphAutomorphism r (cartanGenerator r i) =
        lieGraphAutomorphism r ⁅rootGenerator r (.inl i), rootGenerator r (.inr i)⁆ := by
      congr 1
      symm
      convert TauCeti.lie_single_single_eq_singleSubSingle i.castSucc_lt_succ.ne (1 : ℚ) using 1
      · congr 1
        · apply SetCoe.ext
          rw [val_rootGenerator, val_single, rootTarget_inl, rootSource_inl]
        · apply SetCoe.ext
          rw [val_rootGenerator, val_single, rootTarget_inr, rootSource_inr]
      · apply SetCoe.ext
        rw [val_cartanGenerator, val_singleSubSingle]
    _ = ⁅lieGraphAutomorphism r (rootGenerator r (.inl i)),
        lieGraphAutomorphism r (rootGenerator r (.inr i))⁆ :=
      (lieGraphAutomorphism r).map_lie _ _
    _ = ⁅rootGenerator r (.inl i.rev), rootGenerator r (.inr i.rev)⁆ := by simp
    _ = cartanGenerator r i.rev := by
      convert TauCeti.lie_single_single_eq_singleSubSingle i.rev.castSucc_lt_succ.ne (1 : ℚ)
      · apply SetCoe.ext
        rw [val_rootGenerator, val_single, rootTarget_inl, rootSource_inl]
      · apply SetCoe.ext
        rw [val_rootGenerator, val_single, rootTarget_inr, rootSource_inr]
      · apply SetCoe.ext
        rw [val_cartanGenerator, val_singleSubSingle]

end TauCeti.SlStd
