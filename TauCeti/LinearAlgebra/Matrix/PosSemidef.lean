/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive-semidefinite matrix algebra

This file supplements Mathlib's `Matrix.PosSemidef` API for matrices indexed by arbitrary types.
It provides rank-one and constant matrices, finite pointwise sums and Schur products, Schur powers,
and the quadratic-form characterization.

The results apply in particular to positive-definite kernels, represented directly as matrices,
but do not depend on Tau Ceti's positive-definite-function theory.

They supply the matrix prerequisites for Part C of the `OneParameterSemigroups` roadmap, including
the positive-definite-function/kernel correspondence and the GNS/Kolmogorov decomposition. No
Mathlib code is vendored.

## Main declarations

* `TauCeti.posSemidef_rankOne`: rank-one positive-semidefinite matrices.
* `TauCeti.posSemidef_const_one` and `TauCeti.posSemidef_const_of_nonneg`: constant matrices.
* `TauCeti.posSemidef_iff_finite_sum`: the quadratic-form characterization.
* `TauCeti.posSemidef_finset_sum`: finite pointwise sums.
* `TauCeti.posSemidef_schur_finset_prod` and `TauCeti.posSemidef_schur_pow`: finite Schur
  products and Schur powers.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace TauCeti

universe u v w

variable {α : Type v}

private theorem posSemidef_of_support_posSemidef {R : Type u}
    [Ring R] [PartialOrder R] [StarRing R] (K : α → α → R)
    (hHerm : (Matrix.of fun a b => K a b).IsHermitian) (hgram : ∀ x : α →₀ R,
      (Matrix.of fun i j : x.support => K (i : α) (j : α)).PosSemidef) :
    (Matrix.of fun a b => K a b).PosSemidef := by
  classical
  refine ⟨hHerm, fun x => ?_⟩
  let y : x.support → R := fun i => x i
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hgram x)).2 y
  have h' :
      0 ≤ ∑ i : x.support, ∑ j : x.support,
        star (x (i : α)) * (K (i : α) (j : α) * x (j : α)) := by
    simpa only [y, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
      Finset.mul_sum, mul_assoc] using h
  have h'' :
      0 ≤ ∑ i ∈ x.support, ∑ j ∈ x.support,
        star (x i) * (K i j * x j) := by
    convert h' using 1
    rw [Finset.sum_subtype x.support (by intro a; rfl)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_subtype x.support (by intro a; rfl)]
  simpa only [Matrix.of_apply, Finsupp.sum, mul_assoc] using h''

private theorem matrixOf_star_mul_eq_vecMulVec {R : Type u}
    [Ring R] [StarRing R] (g : α → R) :
    Matrix.of (fun a b => star (g a) * g b) = Matrix.vecMulVec (star g) g := by
  ext a b
  simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply]

private theorem star_mul_matrix_isHermitian {R : Type u}
    [Ring R] [StarRing R] (g : α → R) :
    (Matrix.of fun a b => star (g a) * g b).IsHermitian := by
  rw [matrixOf_star_mul_eq_vecMulVec]
  ext a b
  simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Pi.star_apply]

/-- The rank-one matrix `(a, b) ↦ star (g a) · g b` is positive semidefinite for an arbitrary
index type. Such matrices are elementary building blocks for positive-semidefinite matrices;
taking `g ≡ 1` gives the constant matrix `1`. -/
theorem posSemidef_rankOne {R : Type u}
    [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] (g : α → R) :
    Matrix.PosSemidef (fun a b => star (g a) * g b) := by
  refine posSemidef_of_support_posSemidef _ (star_mul_matrix_isHermitian g) ?_
  intro x
  exact (matrixOf_star_mul_eq_vecMulVec (g := fun i : x.support => g (i : α))).symm ▸
    Matrix.posSemidef_vecMulVec_star_self _

/-- The constant matrix with value `1` is positive semidefinite. -/
theorem posSemidef_const_one {R : Type u}
    [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] :
    Matrix.PosSemidef (fun _ _ : α => (1 : R)) := by
  simpa using posSemidef_rankOne (R := R) (α := α) (fun _ => (1 : R))

/-- A nonnegative constant gives a positive-semidefinite constant matrix. -/
theorem posSemidef_const_of_nonneg {R : Type u}
    [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    {c : R} (hc : 0 ≤ c) : Matrix.PosSemidef (fun _ _ : α => c) := by
  have h := (posSemidef_const_one (R := R) (α := α)).smul hc
  have heq : c • (fun _ _ : α => (1 : R)) = fun _ _ : α => c := by
    ext
    simp
  exact heq ▸ h

/-- The quadratic-form characterization of an arbitrary-index positive-semidefinite matrix. The
reverse direction constructs positivity from conjugate symmetry and finite quadratic-form
nonnegativity without unfolding `Matrix.PosSemidef`. -/
theorem posSemidef_iff_finite_sum {R : Type u} [Ring R] [PartialOrder R] [StarRing R]
    {K : α → α → R} :
    Matrix.PosSemidef K ↔
      (∀ a b, star (K a b) = K b a) ∧
        ∀ {ι : Type*} [Fintype ι] (v : ι → α) (x : ι → R),
          0 ≤ ∑ i, ∑ j, star (x i) * K (v i) (v j) * x j := by
  classical
  refine ⟨fun hK => ⟨fun a b => ?_, ?_⟩, fun ⟨hsymm, hpos⟩ => ?_⟩
  · exact hK.isHermitian.apply b a
  · intro ι _ v x
    have hgram : Matrix.PosSemidef fun i j => K (v i) (v j) := by
      have h := hK.submatrix v
      have heq : Matrix.submatrix (Matrix.of K) v v = fun i j => K (v i) (v j) := by
        apply Matrix.ext
        intro i j
        rw [Matrix.submatrix_apply, Matrix.of_apply]
      exact heq ▸ h
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hgram).2 x
    simpa [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm] using h
  refine posSemidef_of_support_posSemidef K ?_ ?_
  · ext a b
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply]
    exact hsymm b a
  · intro x
    let e : ULift (Fin (Fintype.card x.support)) ≃ x.support :=
      Equiv.ulift.trans (Fintype.equivFin x.support).symm
    refine (Matrix.posSemidef_submatrix_equiv e).mp ?_
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun y => ?_⟩
    · ext i j
      rw [Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.submatrix_apply,
        Matrix.of_apply, Matrix.of_apply]
      exact hsymm (e j : α) (e i : α)
    · refine (hpos (ι := ULift (Fin (Fintype.card x.support)))
        (fun i => (e i : α)) y).trans_eq ?_
      simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Matrix.of_apply,
        Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      exact mul_assoc _ _ _

/-- Finite pointwise sums of positive-semidefinite matrices are positive semidefinite. -/
theorem posSemidef_finset_sum {R : Type u}
    [Ring R] [PartialOrder R] [StarRing R] [AddLeftMono R]
    {ι : Type w} {s : Finset ι}
    {K : ι → α → α → R} (hK : ∀ i ∈ s, Matrix.PosSemidef (K i)) :
    Matrix.PosSemidef (fun a b => ∑ i ∈ s, K i a b) := by
  have h := Matrix.posSemidef_sum s hK
  have heq : (∑ i ∈ s, K i) = fun a b => ∑ i ∈ s, K i a b := by
    apply Matrix.ext
    intro a b
    simp
  exact heq ▸ h

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Finite pointwise Schur products of positive-semidefinite matrices are positive semidefinite. -/
theorem posSemidef_schur_finset_prod {ι : Type w} {s : Finset ι}
    {K : ι → α → α → 𝕜} (hK : ∀ i ∈ s, Matrix.PosSemidef (K i)) :
    Matrix.PosSemidef (fun a b => ∏ i ∈ s, K i a b) := by
  have h := Finset.prod_induction K Matrix.PosSemidef
    (fun _ _ hA hB => hA.hadamard hB) posSemidef_const_one hK
  have heq : (∏ i ∈ s, K i) = fun a b => ∏ i ∈ s, K i a b := by ext; simp
  exact heq ▸ h

/-- Schur powers of a positive-semidefinite matrix are positive semidefinite. -/
theorem posSemidef_schur_pow {K : α → α → 𝕜} (hK : Matrix.PosSemidef K) (n : ℕ) :
    Matrix.PosSemidef (fun a b => K a b ^ n) := by
  induction n with
  | zero =>
      simpa using posSemidef_const_one (R := 𝕜) (α := α)
  | succ n ih =>
      have heq : (fun a b => K a b ^ (n + 1)) =
          Matrix.hadamard (Matrix.of fun a b => K a b ^ n) (Matrix.of K) := by
        apply Matrix.ext
        intro a b
        rw [Matrix.hadamard_apply, Matrix.of_apply, Matrix.of_apply, pow_succ]
      exact heq.symm ▸ ih.hadamard hK

end TauCeti
