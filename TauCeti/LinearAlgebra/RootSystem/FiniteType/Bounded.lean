/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic

public section

/-!
# A finite-type Cartan inequality has finitely many natural solutions

Let `A` be an integer matrix of finite type, that is a generalized Cartan matrix carrying a
positive symmetrizer whose symmetrization is positive definite (`TauCeti.IsFiniteType`). This file
proves that for every integer vector `y` the system of inequalities

`∑ j, A i j * c j ≤ y i`  (for every index `i`)

has only finitely many solutions `c` in the **nonnegative** integers.

The system is the shape in which dominance bounds a weight from below. A weight `mu` lying under
`lam` is `lam - ∑ j, c j • αⱼ` for natural numbers `c j`, and its value on the simple coroot
`αᵢ^∨` is `lam (αᵢ^∨) - ∑ j, c j * ⟨αⱼ, αᵢ^∨⟩`; asking that value to be a natural number is exactly
the displayed inequality for the transposed Cartan matrix. Finiteness of the solution set is
therefore finiteness of the set of dominant weights under `lam`, which is how
`TauCeti/LinearAlgebra/RootSystem/DominantCone.lean` uses it.

## Main results

* `TauCeti.IsFiniteType.finite_setOf_forall_sum_mul_le`: **a finite-type Cartan inequality has
  finitely many natural solutions.**

## The argument

Everything happens in the rational bilinear form `F u v = u ⬝ᵥ S *ᵥ v` of the symmetrization
`S i j = d i * A i j`, which is symmetric and positive definite. Positive definiteness makes `S`
invertible, so every linear functional on `B → ℚ` is `F (·) w` for some `w`; the two functionals
this file represents that way are `c ↦ ∑ i, d i * y i * c i` and, for each index `k`, the `k`-th
coordinate.

* Because the entries of `c` are nonnegative and the symmetrizer is positive, the inequalities sum
  to `F x x ≤ F x z`, where `x` is `c` viewed rationally and `z` represents the first functional.
  Cauchy-Schwarz for a positive semidefinite symmetric form
  (`LinearMap.BilinForm.apply_sq_le_of_symm`) turns that into `F x x ≤ F z z`: a bound on the
  length of `x` that does not depend on `c`.
* Cauchy-Schwarz applied a second time, against the vector representing the `k`-th coordinate,
  bounds each `c k` in terms of `F x x`. So the solutions lie in a product of finite intervals.

No compactness, completeness or eigenvalue theory enters; the two applications of Cauchy-Schwarz
replace them, which is what keeps the argument inside `ℚ`.

## References

This supplies the root-system half of the "weight-cone bound" milestone of Layer 4, "the
classification of finite-dimensional irreducibles", of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §13.2, Lemma B.
-/

open scoped Matrix

namespace TauCeti

namespace IsFiniteType

variable {B : Type*} [Fintype B] {A : Matrix B B ℤ}

/-- **A finite-type Cartan inequality has finitely many natural solutions.** For a finite-type
integer matrix `A` and any integer vector `y`, only finitely many vectors `c` of natural numbers
satisfy `∑ j, A i j * c j ≤ y i` at every index `i`.

Positive definiteness of the symmetrization of `A` is what makes the solution set bounded: the
inequalities force the length of `c` in the symmetrized form to stay below a bound read off from
`y` alone. -/
theorem finite_setOf_forall_sum_mul_le (h : IsFiniteType A) (y : B → ℤ) :
    {c : B → ℕ | ∀ i, ∑ j, A i j * (c j : ℤ) ≤ y i}.Finite := by
  classical
  obtain ⟨d, hd, hpd⟩ := h.exists_symmetrizer
  set S : Matrix B B ℚ := Matrix.of fun i j ↦ d i * (A i j : ℚ) with hSdef
  set F : LinearMap.BilinForm ℚ (B → ℚ) := Matrix.toBilin' S with hFdef
  have hFapply : ∀ u v : B → ℚ, F u v = u ⬝ᵥ S *ᵥ v := fun u v ↦ Matrix.toBilin'_apply' S u v
  -- The symmetrization is symmetric, being positive definite, and nonnegative on the diagonal.
  have hST : Sᵀ = S := by
    ext p q
    simpa using hpd.isHermitian.apply p q
  have hnonneg : ∀ u : B → ℚ, 0 ≤ F u u := fun u ↦ by
    simpa [hFapply] using hpd.posSemidef.dotProduct_mulVec_nonneg u
  have hsymm : LinearMap.IsSymm F := LinearMap.isSymm_def.mpr fun u v ↦ by
    rw [RingHom.id_apply, hFapply, hFapply, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      hST]
    exact dotProduct_comm _ _
  -- Positive definiteness makes `S` invertible, so every functional is represented by the form.
  have hsolve : ∀ w : B → ℚ, ∃ z : B → ℚ, S *ᵥ z = w := fun w ↦
    ⟨S⁻¹ *ᵥ w, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S
        ((Matrix.isUnit_iff_isUnit_det S).mp hpd.isUnit), Matrix.one_mulVec]⟩
  obtain ⟨z, hz⟩ := hsolve fun i ↦ d i * (y i : ℚ)
  have hdual : ∀ k : B, ∃ u : B → ℚ, ∀ x : B → ℚ, F x u = x k := by
    intro k
    obtain ⟨u, hu⟩ := hsolve (Pi.single k 1)
    exact ⟨u, fun x ↦ by rw [hFapply, hu]; simp⟩
  choose u hu using hdual
  refine Set.Finite.subset
    (Set.Finite.pi fun _ : B ↦ Set.finite_Iic ⌈max 1 (F z z * ∑ k, F (u k) (u k))⌉₊)
    fun c hc ↦ ?_
  simp only [Set.mem_ofPred_eq] at hc
  rw [Set.mem_univ_pi]
  intro k
  -- Summing the inequalities against the nonnegative vector `c` gives `F x x ≤ F x z`.
  have hrow : ∀ i, (S *ᵥ fun j ↦ (c j : ℚ)) i = d i * ((∑ j, A i j * (c j : ℤ) : ℤ) : ℚ) := by
    intro i
    have hexp : (S *ᵥ fun j ↦ (c j : ℚ)) i = ∑ j, d i * (A i j : ℚ) * (c j : ℚ) := rfl
    rw [hexp]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hxz : F (fun j ↦ (c j : ℚ)) z = ∑ i, (c i : ℚ) * (d i * (y i : ℚ)) := by
    rw [hFapply, hz]
    rfl
  have hxx : F (fun j ↦ (c j : ℚ)) (fun j ↦ (c j : ℚ))
      = ∑ i, (c i : ℚ) * (S *ᵥ fun j ↦ (c j : ℚ)) i := by
    rw [hFapply]
    rfl
  have hle : F (fun j ↦ (c j : ℚ)) (fun j ↦ (c j : ℚ)) ≤ F (fun j ↦ (c j : ℚ)) z := by
    rw [hxx, hxz]
    refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hrow i]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc i) (hd i).le
  -- Cauchy-Schwarz turns that into a bound on `F x x` independent of `c`.
  have hbound : F (fun j ↦ (c j : ℚ)) (fun j ↦ (c j : ℚ)) ≤ F z z := by
    rcases eq_or_lt_of_le (hnonneg fun j ↦ (c j : ℚ)) with h0 | h0
    · exact h0 ▸ hnonneg z
    · refine le_of_mul_le_mul_left ?_ h0
      refine (mul_self_le_mul_self h0.le hle).trans ?_
      rw [← pow_two]
      exact F.apply_sq_le_of_symm hnonneg hsymm _ z
  -- Cauchy-Schwarz against the `k`-th coordinate vector bounds the `k`-th entry of `c`.
  have hcoord : (c k : ℚ) ^ 2 ≤ F z z * ∑ k, F (u k) (u k) := by
    calc (c k : ℚ) ^ 2 = (F (fun j ↦ (c j : ℚ)) (u k)) ^ 2 := by rw [hu k]
      _ ≤ F (fun j ↦ (c j : ℚ)) (fun j ↦ (c j : ℚ)) * F (u k) (u k) :=
          F.apply_sq_le_of_symm hnonneg hsymm _ (u k)
      _ ≤ F z z * ∑ k, F (u k) (u k) := by
          refine mul_le_mul hbound ?_ (hnonneg (u k)) (hnonneg z)
          exact Finset.single_le_sum (fun j _ ↦ hnonneg (u j)) (Finset.mem_univ k)
  have hck : (c k : ℚ) ≤ max 1 (F z z * ∑ k, F (u k) (u k)) := by
    rcases le_or_gt (c k : ℚ) 1 with hsmall | hlarge
    · exact hsmall.trans (le_max_left _ _)
    · have hsq : (c k : ℚ) ≤ (c k : ℚ) ^ 2 := by nlinarith
      exact (hsq.trans hcoord).trans (le_max_right _ _)
  rw [Set.mem_Iic, ← Nat.cast_le (α := ℚ)]
  exact hck.trans (Nat.le_ceil _)

end IsFiniteType

end TauCeti
