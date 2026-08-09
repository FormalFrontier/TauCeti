/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.FieldTheory.Galois.Basic
public import TauCeti.LinearAlgebra.Matrix.CharpolyFinTwo

/-!
# Trace and norm in a separable quadratic extension

For a separable quadratic extension `L/K` the trace and norm are the two elementary symmetric
functions of the pair `{x, σx}`, where `σ` is the nontrivial automorphism: `tr x = x + σx` and
`N x = x · σx` (`algebraMap_trace_eq_add`, `algebraMap_norm_eq_mul`). Everything else here is a
consequence, except the two evaluations of `b + aθ`, which need no separability at all:

* `trace_algebraMap_add_algebraMap_mul` and `norm_algebraMap_add_algebraMap_mul` evaluate the
  trace and norm of `b + aθ` over any quadratic extension, separable or not — the first by
  `K`-linearity of the trace, the second from the `2 × 2` identity
  `det (b • 1 + a • M) = b² + ab · tr M + a² · det M`. This is how a statement about one
  generator transfers to another;
* `discrim_ne_zero`: for `θ` outside `K`, the discriminant `t² - 4n` of its minimal polynomial
  `X² - tX + n` is nonzero, since it equals `(θ - σθ)²` and `σ` moves `θ`.

In characteristic two `discrim_ne_zero` says `t ≠ 0`, reflecting that a separable quadratic
extension is then Artin–Schreier rather than Kummer.

These are consumed by the extension quadratic twist in
`TauCeti/AlgebraicGeometry/EllipticCurve/QuadraticTwist.lean`, which advances
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 5 (twists): `discrim_ne_zero` is exactly what
makes the twist by a generator elliptic.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/RingTheory/Norm/Quadratic.lean` at the roadmap's pin `bc2fe8ff7396`, FLT PR #1088,
Apache 2.0). That file's own header reads `Authors: Kevin Buzzard, Claude`; following this
repository's convention for adapted material, the upstream authorship is credited here rather
than in the copyright header. Ported with the source's `@[expose]` dropped, and with the two
square-root lemmas left to the PR that consumes them.
-/

public section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L]

namespace Algebra.IsQuadraticExtension

/-- The trace of `b + aθ` in a quadratic extension is `a·tr(θ) + 2b`. Separability is not
needed: this is `K`-linearity of the trace together with `tr(b) = [L : K]·b = 2b`. -/
@[simp]
theorem trace_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.trace K L (algebraMap K L b + algebraMap K L a * θ)
      = a * Algebra.trace K L θ + 2 * b := by
  rw [map_add, Algebra.trace_algebraMap, ← Algebra.smul_def, map_smul,
    Algebra.IsQuadraticExtension.finrank_eq_two]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The norm of `b + aθ` in a quadratic extension is `b² + ab·tr(θ) + a²·N(θ)`. Separability is
not needed: in any `K`-basis of `L`, multiplication by `b + aθ` has matrix `a • M - (-b) • 1`
where `M` is the matrix of multiplication by `θ`, and
`TauCeti.Matrix.det_smul_sub_smul_one_fin_two` evaluates that pencil determinant as
`det M · a² + tr M · ab + b²`. -/
@[simp]
theorem norm_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.norm K (algebraMap K L b + algebraMap K L a * θ)
      = b ^ 2 + a * b * Algebra.trace K L θ + a ^ 2 * Algebra.norm K θ := by
  classical
  let bs : Module.Basis (Fin 2) K L :=
    Module.finBasisOfFinrankEq K L (finrank_eq_two K L)
  have key : Algebra.leftMulMatrix bs (algebraMap K L b + algebraMap K L a * θ)
      = a • Algebra.leftMulMatrix bs θ - (-b) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [neg_smul, sub_neg_eq_add, add_comm, map_add, map_mul, AlgHom.commutes, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, Algebra.smul_def]
    simp [Algebra.smul_def]
  rw [Algebra.norm_eq_matrix_det bs, Algebra.trace_eq_matrix_trace bs,
    Algebra.norm_eq_matrix_det bs, key, TauCeti.Matrix.det_smul_sub_smul_one_fin_two]
  ring

variable [Algebra.IsSeparable K L]

/-- In a separable quadratic extension, the trace of `x` is `x + σx`, where `σ` is the
nontrivial automorphism. -/
theorem algebraMap_trace_eq_add {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (x : L) :
    algebraMap K L (Algebra.trace K L x) = x + σ x := by
  classical
  rw [trace_eq_sum_automorphisms, univ_eq_pair K L hσ, Finset.sum_pair (Ne.symm hσ)]
  simp

/-- In a separable quadratic extension, the norm of `x` is `x * σx`, where `σ` is the
nontrivial automorphism. -/
theorem algebraMap_norm_eq_mul {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (x : L) :
    algebraMap K L (Algebra.norm K x) = x * σ x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, univ_eq_pair K L hσ, Finset.prod_pair (Ne.symm hσ)]
  simp

/-- If `θ` generates a separable quadratic extension of `K` — that is, lies outside `K` — and
`t`, `n` denote its trace and norm, so that `θ² = tθ - n`, then the discriminant `t² - 4n` of
the minimal polynomial of `θ` is nonzero: over the nontrivial automorphism `σ` it equals
`(θ - σθ)²`, and `σθ ≠ θ`. -/
theorem discrim_ne_zero {θ : L} (hθ : θ ∉ Set.range (algebraMap K L)) :
    Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  intro h0
  have h1 : (θ - σ θ) ^ 2 = 0 := by
    have h2 := congrArg (algebraMap K L) h0
    simp only [map_sub, map_pow, map_mul, map_zero, map_ofNat,
      algebraMap_trace_eq_add K L hσ, algebraMap_norm_eq_mul K L hσ] at h2
    linear_combination h2
  exact hθ (mem_range_algebraMap_of_apply_eq K L hσ
    (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1)).symm)

end Algebra.IsQuadraticExtension

end
