/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Data.Int.Interval

/-!
# Vectors of bounded value for a positive definite integral quadratic form

A positive definite quadratic form on a finitely generated free `ℤ`-module takes each of its values
only finitely often: the sets `{x | q x ≤ n}` and `{x | q x = n}` are finite. This is the
finiteness that makes "the vectors of norm `n`" of a positive definite lattice a finite list, and
the one that turns an orbit lying in a level set into a periodic orbit.

## Main results

* `QuadraticMap.PosDef.finite_setOf_apply_le`: a positive definite quadratic form on a
  finitely generated free `ℤ`-module has only finitely many vectors of value at most `n`.
* `QuadraticMap.PosDef.finite_setOf_apply_eq`: consequently only finitely many vectors of
  value exactly `n`.

Both live in the root `QuadraticMap.PosDef` namespace so that they are available by dot notation
on a `QuadraticForm.PosDef` hypothesis.

## Implementation notes

The argument stays inside `ℤ`; no rational or real coefficients, no compactness, and no
diagonalization enter. Write `B` for the polar form, which is symmetric with `B x x = 2 * q x`,
hence nonnegative, and let `b` be a basis. The coordinates of `x` in the dual-like map
`T x = fun i ↦ B x (b i)` are bounded by Cauchy-Schwarz for a positive semidefinite symmetric form
(`LinearMap.BilinForm.apply_sq_le_of_symm`), since `(B x (b i)) ^ 2 ≤ B x x * B (b i) (b i)` and
the right-hand side is bounded once `q x` is. The map `T` is injective: a vector it kills is
orthogonal to a basis, hence to itself, hence isotropic, hence zero. So the set in question is the
preimage under an injective map of a box of integer vectors.

Note that `T` is *not* claimed to be surjective, and need not be: the polar form of a positive
definite integral quadratic form is generally not unimodular. Injectivity is all the argument
uses.
-/

public section

namespace TauCeti

/-- Over `ℤ` a bound on the square is a bound on the absolute value: a nonzero integer is at most
its own square in absolute value. -/
private theorem abs_le_of_sq_le {y c : ℤ} (h : y ^ 2 ≤ c) : |y| ≤ c := by
  rcases eq_or_ne y 0 with rfl | hy
  · simpa using h
  · have h1 : 1 ≤ |y| := by
      rcases hy.lt_or_gt with h' | h'
      · rw [abs_of_neg h']; omega
      · rw [abs_of_pos h']; omega
    calc |y| ≤ |y| * |y| := le_mul_of_one_le_left (abs_nonneg y) h1
      _ = y ^ 2 := by rw [← sq, sq_abs]
      _ ≤ c := h

end TauCeti

namespace QuadraticMap.PosDef

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- **A positive definite integral quadratic form has finitely many vectors of bounded value.**
For a positive definite quadratic form `q` on a finitely generated free `ℤ`-module and any integer
`n`, only finitely many vectors satisfy `q x ≤ n`. -/
theorem finite_setOf_apply_le {q : QuadraticForm ℤ M} (hq : q.PosDef) (n : ℤ) :
    {x : M | q x ≤ n}.Finite := by
  classical
  set b := Module.Free.chooseBasis ℤ M
  set B : LinearMap.BilinForm ℤ M := q.polarBilin with hBdef
  have hBself : ∀ x : M, B x x = 2 * q x := fun x ↦ by
    rw [hBdef, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul]
    ring
  have hBnonneg : ∀ x : M, 0 ≤ B x x := fun x ↦ by
    rw [hBself]
    exact mul_nonneg (by norm_num) (hq.nonneg x)
  have hsymm : LinearMap.IsSymm B :=
    LinearMap.BilinForm.isSymm_iff.mp <| LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ by
      rw [hBdef, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
        QuadraticMap.polar_comm]
  -- Pairing against the basis is injective, because the polar form detects isotropy.
  set T : M →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ M → ℤ) :=
    LinearMap.pi fun i ↦ B.flip (b i)
  have hTapply : ∀ (x : M) (i : Module.Free.ChooseBasisIndex ℤ M), T x i = B x (b i) :=
    fun x i ↦ by simp only [T, LinearMap.pi_apply, LinearMap.BilinForm.flip_apply]
  have hTinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).mpr fun x hx ↦ ?_
    have hzero : B x = 0 := b.ext fun i ↦ by
      simpa [hTapply] using congrFun hx i
    refine hq.anisotropic x ?_
    have : B x x = 0 := by rw [hzero, LinearMap.zero_apply]
    rw [hBself] at this
    omega
  -- Cauchy-Schwarz bounds each coordinate of `T x` in terms of `n` alone.
  set C : Module.Free.ChooseBasisIndex ℤ M → ℤ := fun i ↦ 2 * n * (2 * q (b i))
  refine Set.Finite.subset
    (Set.Finite.preimage hTinj.injOn (Set.Finite.pi' fun i ↦ Set.finite_Icc (-(C i)) (C i)))
    fun x hx ↦ ?_
  simp only [Set.mem_ofPred_eq] at hx
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc]
  intro i
  have hcs : (T x i) ^ 2 ≤ B x x * B (b i) (b i) := by
    rw [hTapply]
    exact B.apply_sq_le_of_symm hBnonneg hsymm x (b i)
  have hle : B x x * B (b i) (b i) ≤ C i := by
    have h2 : (0 : ℤ) ≤ 2 * q (b i) := by
      have := hq.nonneg (b i); omega
    calc B x x * B (b i) (b i) = 2 * q x * (2 * q (b i)) := by rw [hBself, hBself]
      _ ≤ 2 * n * (2 * q (b i)) := by
          exact mul_le_mul_of_nonneg_right (by omega) h2
      _ = C i := rfl
  exact abs_le.mp (TauCeti.abs_le_of_sq_le (hcs.trans hle))

/-- **A positive definite integral quadratic form takes each value finitely often.** For a
positive definite quadratic form `q` on a finitely generated free `ℤ`-module, only finitely many
vectors satisfy `q x = n`; for a positive definite lattice this is the finiteness of the set of
vectors of a given norm. -/
theorem finite_setOf_apply_eq {q : QuadraticForm ℤ M} (hq : q.PosDef) (n : ℤ) :
    {x : M | q x = n}.Finite :=
  (finite_setOf_apply_le hq n).subset fun _ hx ↦ le_of_eq hx

end QuadraticMap.PosDef
