/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order.OrderClosed

/-!
# Positive-semidefinite matrix API

This file supplements Mathlib's `Matrix.PosSemidef` API for matrices indexed by arbitrary types.
It provides rank-one and constant matrices, finite Schur products and powers, the quadratic-form
characterization, scalar Cauchy--Schwarz bounds, and closure under pointwise limits.

The results apply in particular to positive-definite kernels, represented directly as matrices,
but do not depend on Tau Ceti's positive-definite-function theory.

They supply the matrix prerequisites for Part C of the `OneParameterSemigroups` roadmap, including
the positive-definite-function/kernel correspondence and the GNS/Kolmogorov decomposition. No
Mathlib code is vendored.

## Main declarations

* `TauCeti.posSemidef_star_mul`: rank-one positive-semidefinite matrices.
* `TauCeti.posSemidef_one` and `TauCeti.posSemidef_const_of_nonneg`: constant matrices.
* `TauCeti.posSemidef_iff`: the quadratic-form characterization.
* `TauCeti.posSemidef_prod` and `TauCeti.posSemidef_pow`: finite Schur products and powers.
* `TauCeti.normSq_le_of_posSemidef`: scalar Cauchy--Schwarz.
* `TauCeti.posSemidef_of_tendsto`: closure under pointwise limits.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open Filter Matrix
open scoped ComplexConjugate ComplexOrder Topology

namespace TauCeti

universe u v w

variable {α : Type v}

private theorem posSemidef_of_support_posSemidef {R : Type u}
    [CommRing R] [PartialOrder R] [StarRing R] (K : α → α → R)
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
    [CommRing R] [StarRing R] (g : α → R) :
    Matrix.of (fun a b => star (g a) * g b) = Matrix.vecMulVec (star g) g := by
  ext a b
  simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply]

private theorem star_mul_matrix_isHermitian {R : Type u}
    [CommRing R] [StarRing R] (g : α → R) :
    (Matrix.of fun a b => star (g a) * g b).IsHermitian := by
  rw [matrixOf_star_mul_eq_vecMulVec]
  ext a b
  simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Pi.star_apply, mul_comm]

/-- The rank-one matrix `(a, b) ↦ star (g a) · g b` is positive semidefinite for an arbitrary
index type. Such matrices are elementary building blocks for positive-semidefinite matrices;
taking `g ≡ 1` gives the constant matrix `1`. -/
theorem posSemidef_star_mul {R : Type u}
    [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R] (g : α → R) :
    Matrix.PosSemidef (fun a b => star (g a) * g b) := by
  refine posSemidef_of_support_posSemidef _ (star_mul_matrix_isHermitian g) ?_
  intro x
  exact (matrixOf_star_mul_eq_vecMulVec (g := fun i : x.support => g (i : α))).symm ▸
    Matrix.posSemidef_vecMulVec_star_self _

/-- The constant matrix with value `1` is positive semidefinite. -/
theorem posSemidef_one {R : Type u}
    [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R] :
    Matrix.PosSemidef (fun _ _ : α => (1 : R)) := by
  simpa using posSemidef_star_mul (R := R) (α := α) (fun _ => (1 : R))

/-- A nonnegative constant gives a positive-semidefinite constant matrix. -/
theorem posSemidef_const_of_nonneg {R : Type u}
    [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    {c : R} (hc : 0 ≤ c) : Matrix.PosSemidef (fun _ _ : α => c) := by
  refine ⟨?_, fun x => ?_⟩
  · have hHerm : (Matrix.of fun _ _ : α => c).IsHermitian := by
      ext a b
      rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply]
      exact hc.star_eq
    exact hHerm
  · let s := x.sum fun _ xi => xi
    have hs := star_left_conjugate_nonneg hc s
    dsimp only [s] at hs
    simp only [Finsupp.sum] at hs ⊢
    rw [star_sum] at hs
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc] at hs
    rw [Finset.sum_comm] at hs
    simpa only [mul_assoc] using hs

/-- The quadratic-form characterization of an arbitrary-index positive-semidefinite matrix. The
reverse direction constructs positivity from conjugate symmetry and finite quadratic-form
nonnegativity without unfolding `Matrix.PosSemidef`. -/
theorem posSemidef_iff {R : Type u} [CommRing R] [PartialOrder R] [StarRing R]
    {K : α → α → R} :
    Matrix.PosSemidef K ↔
      (∀ a b, star (K a b) = K b a) ∧
        ∀ {ι : Type*} [Fintype ι] (v : ι → α) (x : ι → R),
          0 ≤ ∑ i, ∑ j, star (x i) * x j * K (v i) (v j) := by
  classical
  refine ⟨fun hK => ⟨fun a b => ?_, ?_⟩, fun ⟨hsymm, hpos⟩ => ?_⟩
  · exact hK.isHermitian.apply b a
  · intro ι _ v x
    have hgram : (Matrix.of fun i j => K (v i) (v j)).PosSemidef := by
      simpa [Matrix.submatrix, Function.comp_def] using hK.submatrix v
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
      ring

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Finite pointwise products of positive-semidefinite matrices are positive semidefinite. -/
theorem posSemidef_prod {ι : Type w} {s : Finset ι}
    {K : ι → α → α → 𝕜} (hK : ∀ i ∈ s, Matrix.PosSemidef (K i)) :
    Matrix.PosSemidef (fun a b => ∏ i ∈ s, K i a b) := by
  have h := Finset.prod_induction K Matrix.PosSemidef
    (fun _ _ hA hB => hA.hadamard hB) posSemidef_one hK
  have heq : (∏ i ∈ s, K i) = fun a b => ∏ i ∈ s, K i a b := by
    ext a b
    simp
  rwa [heq] at h

/-- Schur powers of a positive-semidefinite matrix are positive semidefinite. -/
theorem posSemidef_pow {K : α → α → 𝕜} (hK : Matrix.PosSemidef K) (n : ℕ) :
    Matrix.PosSemidef (fun a b => K a b ^ n) := by
  induction n with
  | zero =>
      simpa using posSemidef_one (R := 𝕜) (α := α)
  | succ n ih =>
      have h := ih.hadamard hK
      have heq : Matrix.hadamard (fun a b => K a b ^ n) K =
          fun a b => K a b ^ n * K a b := by
        ext a b
        rfl
      rw [heq] at h
      simpa [pow_succ] using h

/-- The `2 × 2` principal submatrix at two indices is positive semidefinite. -/
private theorem finTwo_posSemidef {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) (a b : α) :
    (Matrix.of fun i j : Fin 2 => K (![a, b] i) (![a, b] j)).PosSemidef := by
  simpa [Matrix.submatrix, Function.comp_def] using hK.submatrix (fun i : Fin 2 => ![a, b] i)

/-- Scalar Cauchy--Schwarz for an `RCLike`-valued positive-semidefinite matrix. -/
theorem normSq_le_of_posSemidef {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) (a b : α) :
    RCLike.normSq (K a b) ≤ RCLike.re (K a a) * RCLike.re (K b b) := by
  have hsymm (x y : α) : conj (K x y) = K y x := by
    simpa only [starRingEnd_apply] using hK.isHermitian.apply y x
  let A : Matrix (Fin 2) (Fin 2) 𝕜 := Matrix.of fun i j => K (![a, b] i) (![a, b] j)
  have hA : A.PosSemidef := finTwo_posSemidef hK a b
  have hdet : 0 ≤ A.det := Matrix.PosSemidef.det_nonneg hA
  have hdet_re : 0 ≤ RCLike.re A.det := by
    simpa using (RCLike.le_iff_re_im.mp hdet).1
  have hconj : K b a = conj (K a b) := (hsymm a b).symm
  have haa_im : RCLike.im (K a a) = 0 := RCLike.conj_eq_iff_im.mp (hsymm a a)
  have hbb_im : RCLike.im (K b b) = 0 := RCLike.conj_eq_iff_im.mp (hsymm b b)
  have hdet_eval :
      RCLike.re A.det =
        RCLike.re (K a a) * RCLike.re (K b b) - RCLike.normSq (K a b) := by
    simp [A, Matrix.det_fin_two, hconj, RCLike.normSq_apply, haa_im, hbb_im]
  nlinarith

/-- A zero diagonal entry forces the corresponding row entry to vanish. -/
theorem eq_zero_of_apply_self_eq_zero_left_of_posSemidef {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) {a b : α} (ha : K a a = 0) : K a b = 0 := by
  have hnorm := normSq_le_of_posSemidef hK a b
  have hdiag : RCLike.re (K a a) * RCLike.re (K b b) = 0 := by simp [ha]
  have hnorm_zero : RCLike.normSq (K a b) = 0 :=
    le_antisymm (by simpa [hdiag] using hnorm) (RCLike.normSq_nonneg _)
  exact RCLike.normSq_eq_zero.mp hnorm_zero

/-- A zero diagonal entry forces the corresponding column entry to vanish. -/
theorem eq_zero_of_apply_self_eq_zero_right_of_posSemidef {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) {a b : α} (hb : K b b = 0) : K a b = 0 := by
  have hba := eq_zero_of_apply_self_eq_zero_left_of_posSemidef hK (a := b) (b := a) hb
  have hconj : conj (K a b) = K b a := by
    simpa only [starRingEnd_apply] using hK.isHermitian.apply b a
  rw [hba] at hconj
  have := congrArg conj hconj
  simpa using this

/-- If two diagonal entries are `1`, then the corresponding off-diagonal entry has norm at most
`1`. -/
theorem norm_le_one_of_apply_self_eq_one_of_posSemidef {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) {a b : α} (ha : K a a = 1) (hb : K b b = 1) :
    ‖K a b‖ ≤ 1 := by
  refine le_of_sq_le_sq ?_ zero_le_one
  simpa [RCLike.normSq_eq_def', pow_two, ha, hb] using normSq_le_of_posSemidef hK a b

/-- Positive-semidefinite matrices are preserved under pointwise limits along a nontrivial
filter. The positivity hypothesis need only hold eventually. -/
theorem posSemidef_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    {K : ι → α → α → 𝕜} {L : α → α → 𝕜} (hK : ∀ᶠ i in l, Matrix.PosSemidef (K i))
    (hlim : ∀ a b : α, Tendsto (fun i => K i a b) l (𝓝 (L a b))) :
    Matrix.PosSemidef L := by
  exact Matrix.posSemidef_is_closed.mem_of_tendsto
    (tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 (hlim a)) hK

end TauCeti
