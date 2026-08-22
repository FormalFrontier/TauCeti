/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PosSemidef

/-!
# Bounded positive-definite kernels decrease along a symmetric shift

Let `K` be a positive-definite kernel on a type `α` and let `σ : α → α` be a *symmetric shift*,
meaning `K (σ p) q = K p (σ q)`. If the diagonal of `K` is bounded — which by Cauchy--Schwarz is
the same as `K` being bounded — then the shifted kernel is dominated by `K`: the difference

`(p, q) ↦ K p q - K (σ p) q`

is again positive definite. Boundedness cannot be dropped — for `K p q = exp (p + q)` on `ℝ` and
`σ = (· + 1)` the difference is *negative* definite — and it is exactly what the proof consumes.

The mechanism is a moment-problem estimate. Fixing a finite family of points and coefficients, the
numbers `a n = ∑ᵢⱼ conj (cᵢ) K (σⁿ pᵢ) (pⱼ) c ⱼ` form a positive-semidefinite Hankel matrix
`(m, n) ↦ a (m + n)`, because the shift can be moved from one argument to the other, and they are
bounded above. The matrix estimate `TauCeti.sub_nonneg_of_posSemidef_hankel` then gives
`a 0 - a 1 ≥ 0`, which is the quadratic form of the difference kernel.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
("BCR semigroup--Bochner"): applied to the Berg--Christensen--Ressel kernel of a bounded
positive-definite function on `[0,∞) × V` with the time shift, it is the step that turns positive
definiteness into complete monotonicity in the time variable.

## Main declarations

* `TauCeti.posSemidef_sub_comp_shift`: the difference of a bounded positive-definite kernel and its
  shift by a symmetric shift is positive definite.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open scoped ComplexOrder

namespace TauCeti

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]

/-! ## Positive-definite kernels and symmetric shifts -/

section Shift

variable {α : Type v} {K : α → α → 𝕜} {σ : α → α}

omit [RCLike 𝕜] in
/-- A symmetric shift can be split between the two arguments of the kernel:
`K (σ^[m + n] p) q = K (σ^[m] p) (σ^[n] q)`. -/
private theorem apply_iterate_add (hshift : ∀ p q, K (σ p) q = K p (σ q)) (m n : ℕ) (p q : α) :
    K (σ^[m + n] p) q = K (σ^[m] p) (σ^[n] q) := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
      have hassoc : m + (n + 1) = m + n + 1 := (Nat.add_assoc m n 1).symm
      rw [hassoc, Function.iterate_succ_apply', hshift, ih, ← Function.iterate_succ_apply]

omit [RCLike 𝕜] in
/-- Moving the whole iterated shift onto the left argument. -/
private theorem apply_iterate_right (hshift : ∀ p q, K (σ p) q = K p (σ q)) (n : ℕ) (p q : α) :
    K p (σ^[n] q) = K (σ^[n] p) q := by
  simpa using (apply_iterate_add hshift 0 n p q).symm

/-- The quadratic forms of a positive-definite kernel along the iterates of a symmetric shift
assemble into a positive-semidefinite **Hankel** matrix: for a fixed finite family of points `v`
and coefficients `c`, the sequence `a n = ∑ᵢⱼ conj (cᵢ) · K (σⁿ (v i)) (v j) · cⱼ` has
`(m, n) ↦ a (m + n)` positive semidefinite. Its entries are real because `K` is Hermitian and the
shift can be moved between the two arguments, and its quadratic forms are quadratic forms of `K`
itself, taken at the shifted points. -/
private theorem posSemidef_hankel_of_iterate_shift {ι : Type v} [Fintype ι] {a : ℕ → 𝕜}
    (hK : Matrix.PosSemidef K) (hshift : ∀ p q, K (σ p) q = K p (σ q)) {v : ι → α} {c : ι → 𝕜}
    (hadef : ∀ n, a n = ∑ i, ∑ j, star (c i) * K (σ^[n] (v i)) (v j) * c j) :
    Matrix.PosSemidef fun m n : ℕ => a (m + n) := by
  have hherm : ∀ p q : α, star (K p q) = K q p :=
    (posSemidef_iff_finite_sum.{u, v, v}.mp hK).1
  refine posSemidef_iff_finite_sum.{u, 0, v}.mpr ⟨fun m n => ?_, ?_⟩
  · -- the entries are real, by Hermitian symmetry of `K` and the shift symmetry
    have hstar : ∀ k : ℕ, star (a k) = a k := by
      intro k
      simp only [hadef, star_sum, star_mul', star_star]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hherm, apply_iterate_right hshift]
      ring
    rw [hstar, Nat.add_comm]
  · intro κ _ w e
    have h := (posSemidef_iff_finite_sum.{u, v, v}.mp hK).2 (ι := κ × ι)
      (fun p => σ^[w p.1] (v p.2)) (fun p => e p.1 * c p.2)
    have hexp : ∀ s t : κ, star (e s) * a (w s + w t) * e t =
        ∑ i, ∑ j, star (e s * c i) *
          K (σ^[w s] (v i)) (σ^[w t] (v j)) * (e t * c j) := by
      intro s t
      simp only [hadef, Finset.mul_sum, Finset.sum_mul, star_mul',
        apply_iterate_add hshift (w s) (w t)]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    calc (0 : 𝕜) ≤ ∑ p : κ × ι, ∑ q : κ × ι, star (e p.1 * c p.2) *
          K (σ^[w p.1] (v p.2)) (σ^[w q.1] (v q.2)) * (e q.1 * c q.2) := h
      _ = ∑ s, ∑ i, ∑ t, ∑ j, star (e s * c i) *
            K (σ^[w s] (v i)) (σ^[w t] (v j)) * (e t * c j) := by
          simp only [Fintype.sum_prod_type]
      _ = ∑ s, ∑ t, ∑ i, ∑ j, star (e s * c i) *
            K (σ^[w s] (v i)) (σ^[w t] (v j)) * (e t * c j) := by
          exact Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ s, ∑ t, star (e s) * a (w s + w t) * e t := by
          simp only [hexp]

/-- **The difference of a bounded positive-definite kernel and its shift is positive definite.**
Here `σ` is a *symmetric* shift, `K (σ p) q = K p (σ q)`, and the diagonal of `K` is bounded in
norm by `C` — which by Cauchy--Schwarz bounds `K` everywhere. Boundedness is essential: for the
(unbounded) kernel `(p, q) ↦ exp (p + q)` on `ℝ` and the shift `σ = (· + 1)` the difference below
is the negative of a positive-definite kernel. -/
theorem posSemidef_sub_comp_shift {C : ℝ} (hK : Matrix.PosSemidef K)
    (hshift : ∀ p q, K (σ p) q = K p (σ q)) (hbdd : ∀ p, ‖K p p‖ ≤ C) :
    Matrix.PosSemidef fun p q : α => K p q - K (σ p) q := by
  have hherm : ∀ p q : α, star (K p q) = K q p :=
    (posSemidef_iff_finite_sum.{u, v, v}.mp hK).1
  refine posSemidef_iff_finite_sum.{u, v, v}.mpr ⟨fun p q => ?_, ?_⟩
  · rw [star_sub, hherm, hherm, hshift]
  intro ι _ v c
  -- the Hankel sequence attached to the finite family `(v, c)`
  let a : ℕ → 𝕜 := fun n => ∑ i, ∑ j, star (c i) * K (σ^[n] (v i)) (v j) * c j
  have hadef : ∀ n, a n = ∑ i, ∑ j, star (c i) * K (σ^[n] (v i)) (v j) * c j := fun _ => rfl
  have hHankel := posSemidef_hankel_of_iterate_shift hK hshift hadef
  have hbda : ∀ n, RCLike.re (a n) ≤ ∑ i, ∑ j, ‖c i‖ * ‖c j‖ * C := by
    intro n
    refine (RCLike.re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    calc ‖star (c i) * K (σ^[n] (v i)) (v j) * c j‖
        = ‖c i‖ * ‖K (σ^[n] (v i)) (v j)‖ * ‖c j‖ := by simp [norm_mul]
      _ ≤ ‖c i‖ * C * ‖c j‖ := by
          gcongr
          exact hK.norm_le_of_norm_apply_self_le hbdd _ _
      _ = ‖c i‖ * ‖c j‖ * C := by ring
  have hstep := sub_nonneg_of_posSemidef_hankel hHankel hbda
  have hsub : a 0 - a 1 = ∑ i, ∑ j, star (c i) * (K (v i) (v j) - K (σ (v i)) (v j)) * c j := by
    simp only [hadef, Function.iterate_zero, Function.iterate_one, id_eq, mul_sub, sub_mul,
      ← Finset.sum_sub_distrib]
  rwa [hsub] at hstep

end Shift

end TauCeti
