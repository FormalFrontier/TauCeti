/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Finite.Basic
public import TauCeti.LowDimTopology.Plumbing.IntersectionForm

/-!
# Negative-definiteness of the plumbing intersection form

This file records what the negative-definiteness hypothesis buys at the level of the integral
intersection form, rather than only at the level of its matrix. Lattice homology is built on a
*negative-definite* plumbing, and the property used throughout the theory is that the form is
strictly negative on every nonzero lattice vector, which in particular implies that it is
nondegenerate, so the plumbing lattice carries no isotropic directions and the lattice points it
indexes are separated by the form.

The matrix-level definition `PlumbingGraph.IsNegativeDefinite` says that the negated intersection
matrix is positive definite, i.e. `0 < xᵀ (-A) x` for every nonzero integer vector `x`. Here we
transport that statement through `Matrix.toBilin'` to the bilinear form
`PlumbingGraph.intersectionForm`, obtaining the self-pairing sign, the resulting vanishing
criterion, nondegeneracy, and the injectivity of multiplication by the intersection matrix. As a
self-validating example the `A₂` plumbing (two `-2`-framed spheres joined by an edge) is shown to
be negative definite.

Three further results are the quantitative half of the same hypothesis: nonvanishing of `det A`,
Cauchy--Schwarz, and finiteness of the superlevel sets of the self-pairing. Cauchy--Schwarz for
the form — which needs only that the self-pairing is nonpositive, so it is stated for that
hypothesis alone — bounds every pairing by the two self-pairings, and applying it to the basis
spheres bounds each coordinate of `A x` in terms of `P.intersectionForm x x`. Since `A` acts
injectively, only finitely many lattice points can have their self-pairing above a fixed bound:
the self-pairing is a proper function to `-∞`. This finiteness is what makes the sublevel sets of
Némethi's weight function finite, hence what makes lattice homology a limit of finite
computations.

## Main results

* `TauCeti.PlumbingGraph.IsNegativeDefinite.intersectionForm_self_neg`: the intersection form is
  strictly negative on every nonzero lattice vector.
* `TauCeti.PlumbingGraph.isNegativeDefinite_iff_forall_intersectionForm_self_neg`: this strict
  self-pairing inequality characterizes negative-definiteness.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.intersectionForm_self_nonpos`: the self-pairing is
  always nonpositive.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.intersectionForm_self_eq_zero_iff`: the self-pairing
  vanishes exactly at the origin.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.intersectionForm_nondegenerate`: the form is
  nondegenerate.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.mulVec_injective`: multiplication by the intersection
  matrix is injective, so the lattice embeds along the form.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.det_intersectionMatrix_ne_zero`: the intersection
  matrix has nonzero determinant.
* `TauCeti.PlumbingGraph.sq_intersectionForm_le`: Cauchy--Schwarz for the intersection form.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.finite_setOfPred_le_intersectionForm_self`: only
  finitely many lattice points have self-pairing above a fixed bound.
* `TauCeti.a2Plumbing_isNegativeDefinite`: the `A₂` plumbing is negative definite.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose standing hypothesis is a negative-definite plumbing: Némethi's
lattice homology `ℍ⁻`/`ℍ⁰` and its weight functions are defined on, and finite because of, the
negative-definite intersection lattice. See Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

open scoped Matrix

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {P : PlumbingGraph V}

/-- On a negative-definite plumbing the intersection form is strictly negative on every nonzero
lattice vector: the defining inequality `0 < xᵀ (-A) x` of the negated matrix is exactly
`P.intersectionForm x x < 0`. -/
theorem IsNegativeDefinite.intersectionForm_self_neg (h : P.IsNegativeDefinite) {x : V → ℤ}
    (hx : x ≠ 0) : P.intersectionForm x x < 0 := by
  have hpos := Matrix.PosDef.dotProduct_mulVec_pos (P.isNegativeDefinite_iff.mp h) hx
  rw [Matrix.neg_mulVec, dotProduct_neg, star_trivial] at hpos
  rw [P.intersectionForm_apply]
  rw [← Matrix.toBilin'_apply' P.intersectionMatrix x x, Matrix.toBilin'_apply] at hpos
  linarith

/-- A plumbing is negative definite exactly when its intersection-form self-pairing is strictly
negative on every nonzero lattice vector. -/
@[grind =]
theorem isNegativeDefinite_iff_forall_intersectionForm_self_neg :
    P.IsNegativeDefinite ↔ ∀ x : V → ℤ, x ≠ 0 → P.intersectionForm x x < 0 := by
  refine ⟨fun h x hx => h.intersectionForm_self_neg hx, fun h => ?_⟩
  rw [isNegativeDefinite_iff, Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨(Matrix.isHermitian_iff_isSymm.mpr P.intersectionMatrix_isSymm).neg, fun x hx => ?_⟩
  have hconv : star x ⬝ᵥ ((-P.intersectionMatrix) *ᵥ x) = -P.intersectionForm x x := by
    rw [Matrix.neg_mulVec, dotProduct_neg, star_trivial, P.intersectionForm_apply,
      ← Matrix.toBilin'_apply P.intersectionMatrix x x, Matrix.toBilin'_apply']
  rw [hconv]
  linarith [h x hx]

/-- On a negative-definite plumbing the intersection form self-pairing is always nonpositive: it
is strictly negative away from the origin and zero at it. -/
theorem IsNegativeDefinite.intersectionForm_self_nonpos (h : P.IsNegativeDefinite) (x : V → ℤ) :
    P.intersectionForm x x ≤ 0 := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (h.intersectionForm_self_neg hx).le

/-- On a negative-definite plumbing the intersection form self-pairing vanishes exactly at the
origin: negative-definiteness rules out nonzero isotropic vectors. -/
@[simp]
theorem IsNegativeDefinite.intersectionForm_self_eq_zero_iff (h : P.IsNegativeDefinite)
    (x : V → ℤ) : P.intersectionForm x x = 0 ↔ x = 0 := by
  refine ⟨fun hzero => ?_, ?_⟩
  · by_contra hx
    exact (h.intersectionForm_self_neg hx).ne hzero
  · rintro rfl
    simp

/-- The intersection form of a negative-definite plumbing is nondegenerate: a lattice vector that
pairs to zero with every vector — in particular with itself — is zero, on either side. -/
theorem IsNegativeDefinite.intersectionForm_nondegenerate (h : P.IsNegativeDefinite) :
    P.intersectionForm.Nondegenerate :=
  (LinearMap.IsRefl.nondegenerate_iff_separatingLeft P.intersectionForm_isSymm.isRefl).mpr
    fun x hx => (h.intersectionForm_self_eq_zero_iff x).mp (hx x)

/-- A left-kernel form of `IsNegativeDefinite.intersectionForm_nondegenerate`: a lattice vector
pairing to zero with every vector is zero. -/
theorem IsNegativeDefinite.eq_zero_of_intersectionForm_left (h : P.IsNegativeDefinite) {x : V → ℤ}
    (hx : ∀ y, P.intersectionForm x y = 0) : x = 0 :=
  h.intersectionForm_nondegenerate.1 x hx

/-- A right-kernel form of `IsNegativeDefinite.intersectionForm_nondegenerate`: a lattice vector
paired to zero by every vector is zero. -/
theorem IsNegativeDefinite.eq_zero_of_intersectionForm_right (h : P.IsNegativeDefinite)
    {x : V → ℤ} (hx : ∀ y, P.intersectionForm y x = 0) : x = 0 :=
  h.intersectionForm_nondegenerate.2 x hx

/-- On a negative-definite plumbing, multiplication by the intersection matrix is injective: the
lattice embeds along its intersection form, with no kernel. -/
theorem IsNegativeDefinite.mulVec_injective (h : P.IsNegativeDefinite) :
    Function.Injective (P.intersectionMatrix *ᵥ ·) := by
  intro x y hxy
  have hxy' : P.intersectionMatrix *ᵥ x = P.intersectionMatrix *ᵥ y := hxy
  have hz : P.intersectionMatrix *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy', sub_self]
  have hzero : P.intersectionForm (x - y) (x - y) = 0 := by
    rw [P.intersectionForm_apply, ← Matrix.toBilin'_apply P.intersectionMatrix (x - y) (x - y),
      Matrix.toBilin'_apply', hz]
    simp
  exact sub_eq_zero.mp ((h.intersectionForm_self_eq_zero_iff (x - y)).mp hzero)

/-- The intersection matrix of a negative-definite plumbing has nonzero determinant: it kills no
nonzero lattice vector. -/
theorem IsNegativeDefinite.det_intersectionMatrix_ne_zero (h : P.IsNegativeDefinite) :
    P.intersectionMatrix.det ≠ 0 := by
  refine LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mp ?_
  -- `intersectionForm` is `Matrix.toBilin'` of the intersection matrix, but its body is not
  -- exposed outside `IntersectionForm.lean`, so the two forms are identified on values
  have hbil : Matrix.toBilin' P.intersectionMatrix = P.intersectionForm :=
    LinearMap.ext fun x => LinearMap.ext fun y => by
      rw [Matrix.toBilin'_apply, P.intersectionForm_apply]
  rw [hbil]
  exact h.intersectionForm_nondegenerate

/-- Cauchy--Schwarz for the intersection form: on a plumbing whose self-pairing is everywhere
nonpositive, the square of a pairing is at most the product of the two self-pairings.

Only semidefiniteness is needed, so the hypothesis is the nonpositivity of the self-pairing
rather than negative-definiteness; on a negative-definite plumbing it is supplied by
`IsNegativeDefinite.intersectionForm_self_nonpos`. Both self-pairings being nonpositive, the
right-hand side is a product of two nonpositive integers. -/
theorem sq_intersectionForm_le (hnonpos : ∀ u : V → ℤ, P.intersectionForm u u ≤ 0)
    (x y : V → ℤ) :
    P.intersectionForm x y ^ 2 ≤ P.intersectionForm x x * P.intersectionForm y y := by
  have hsymm : LinearMap.IsSymm (-P.intersectionForm) :=
    LinearMap.BilinForm.isSymm_iff.mp P.intersectionForm_isSymm.neg
  have hnonneg : ∀ u : V → ℤ, 0 ≤ (-P.intersectionForm) u u := fun u => by
    simpa using hnonpos u
  have hcs := LinearMap.BilinForm.apply_sq_le_of_symm (-P.intersectionForm) hnonneg hsymm x y
  simpa using hcs

/-- On a negative-definite plumbing only finitely many lattice points have intersection-form
self-pairing above a fixed bound.

Cauchy--Schwarz against the basis sphere `e v` bounds the square of the `v`-th coordinate of
`A x` by `P.intersectionForm x x * P.weight v`, hence by a constant depending only on `c`; so
`A x` ranges over a finite box, and `x ↦ A x` is injective. Equivalently, the self-pairing is a
proper function `(V → ℤ) → ℤ` tending to `-∞`. -/
theorem IsNegativeDefinite.finite_setOfPred_le_intersectionForm_self (h : P.IsNegativeDefinite)
    (c : ℤ) : {x : V → ℤ | c ≤ P.intersectionForm x x}.Finite := by
  classical
  set N : ℤ := ∑ v, |c * P.weight v| with hN
  have hbox : {y : V → ℤ | ∀ v, y v ∈ Set.Icc (-N) N}.Finite :=
    Set.Finite.pi' fun _ => Set.finite_Icc _ _
  refine (Set.Finite.preimage (f := P.intersectionMatrix.mulVec)
    h.mulVec_injective.injOn hbox).subset fun x hx => ?_
  simp only [Set.mem_ofPred_eq] at hx
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  intro v
  refine Set.mem_Icc.mpr (abs_le.mp ?_)
  have hweight : P.weight v < 0 := IsNegativeDefinite.weight_neg P h v
  -- the square of the `v`-th coordinate of `A x` is bounded by a constant depending on `c`
  have hcs : (P.intersectionMatrix *ᵥ x) v ^ 2 ≤ P.intersectionForm x x * P.weight v := by
    have hle := sq_intersectionForm_le h.intersectionForm_self_nonpos x (Pi.single v 1)
    rwa [P.intersectionForm_single_right_eq_mulVec_apply x v, P.intersectionForm_single v v,
      P.intersectionMatrix_diag] at hle
  have hbound : (P.intersectionMatrix *ᵥ x) v ^ 2 ≤ N := by
    refine hcs.trans ((mul_le_mul_of_nonpos_right hx hweight.le).trans ?_)
    refine le_trans (le_abs_self _) ?_
    exact Finset.single_le_sum (f := fun w => |c * P.weight w|)
      (fun w _ => abs_nonneg _) (Finset.mem_univ v)
  calc |(P.intersectionMatrix *ᵥ x) v|
      = ((P.intersectionMatrix *ᵥ x) v).natAbs := Int.abs_eq_natAbs _
    _ ≤ (P.intersectionMatrix *ᵥ x) v ^ 2 := Int.natAbs_le_self_sq _
    _ ≤ N := hbound

end PlumbingGraph

/-- The `A₂` plumbing is negative definite: its negated intersection matrix is the `A₂` Cartan
matrix `!![2, -1; -1, 2]`, whose quadratic form `2x₀² - 2x₀x₁ + 2x₁² = (x₀ - x₁)² + x₀² + x₁²` is
positive on every nonzero integer vector. A self-validating instance of the negative-definite
hypothesis used in Lane L. -/
theorem a2Plumbing_isNegativeDefinite : a2Plumbing.IsNegativeDefinite := by
  rw [PlumbingGraph.isNegativeDefinite_iff_forall_intersectionForm_self_neg]
  intro x hx
  have hIF : a2Plumbing.intersectionForm x x
      = -2 * x 0 ^ 2 + 2 * (x 0 * x 1) - 2 * x 1 ^ 2 := by
    rw [a2Plumbing.intersectionForm_apply, a2Plumbing_intersectionMatrix]
    simp [Fin.sum_univ_two]
    ring
  rw [hIF]
  have hx2 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hx (funext_iff.mpr (Fin.forall_fin_two.mpr ⟨hcon.1, hcon.2⟩))
  have hsum : 0 < x 0 ^ 2 + x 1 ^ 2 := by
    rcases hx2 with hne | hne
    · have := (sq_nonneg (x 0)).lt_of_ne (Ne.symm (pow_ne_zero 2 hne))
      nlinarith [sq_nonneg (x 1)]
    · have := (sq_nonneg (x 1)).lt_of_ne (Ne.symm (pow_ne_zero 2 hne))
      nlinarith [sq_nonneg (x 0)]
  nlinarith [sq_nonneg (x 0 - x 1), hsum]

end TauCeti
