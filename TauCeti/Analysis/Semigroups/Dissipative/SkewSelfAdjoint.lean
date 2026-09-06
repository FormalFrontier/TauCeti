/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.LinearPMap.RestrictScalars
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.Analysis.Semigroups.Dissipative.Basic
import TauCeti.Analysis.Semigroups.Dissipative.Hilbert

/-!
# Skew multiples of self-adjoint operators are m-dissipative

Multiplication by a nonzero purely imaginary scalar `c` turns a self-adjoint partial linear map
`A` on a complex Hilbert space into an m-dissipative real partial linear map: the quadratic form
of `c • A` is purely imaginary, so its real restriction is dissipative, and the range condition,
surjectivity of `1 - c • A`, is the surjectivity of the nonreal shift `c⁻¹ - A` of `A`, since
`1 - c • A = c • (c⁻¹ - A)`.  Together with the density of the domain of a self-adjoint operator
(`IsSelfAdjoint.dense_domain`), this is the hypothesis set of the Lumer--Phillips theorem; at
`c = ± i` it produces the two contraction semigroups whose gluing is the unitary group `e^{itA}`.

## Main results

* `LinearPMap.IsFormalAdjoint.isDissipative_smul_restrictScalars`: for a symmetric `A` and a
  purely imaginary `c`, the real restriction of `c • A` is dissipative.
* `IsSelfAdjoint.one_smul_sub_smul_restrictScalars_surjective`: for self-adjoint `A` and
  nonreal `c`, `1 - c • A` is surjective.
* `IsSelfAdjoint.isMDissipative_smul_restrictScalars`: for self-adjoint `A` and a nonzero purely
  imaginary `c`, the real restriction of `c • A` is m-dissipative.

The statements are in the simp-normal form `c • A.restrictScalars ℝ` of
`LinearPMap.restrictScalars_smul`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Theorem II.3.24 (Stone's theorem) and the surrounding discussion.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Theorem 1.10.8.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The real restriction of a purely imaginary multiple of a formally self-adjoint (symmetric)
partial linear map is dissipative: its real quadratic form vanishes. -/
theorem IsFormalAdjoint.isDissipative_smul_restrictScalars {A : E →ₗ.[ℂ] E}
    (hA : A.IsFormalAdjoint A) {c : ℂ} (hc : c.re = 0) :
    TauCeti.Semigroups.IsDissipative (c • A.restrictScalars ℝ) := by
  rw [← LinearPMap.restrictScalars_smul]
  -- The real inner product of `rclikeToReal` sits over `NormedSpace.restrictScalars ℝ ℂ E`, the
  -- ambient real normed structure in which `IsDissipative` is stated, so the local instance only
  -- supplies the inner product and does not change the meaning of the statement.
  let _ : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  apply (TauCeti.Semigroups.isDissipative_iff_real_inner_nonpos _).mpr
  intro x
  rw [real_inner_eq_re_inner, (c • A).restrictScalars_apply ℝ x, LinearPMap.smul_apply,
    hA.re_inner_smul_apply_self c, RCLike.re_to_complex, hc, zero_mul]

/-- The range condition for a nonreal multiple `c • A` of a self-adjoint partial linear map:
`1 - c • A = c • (c⁻¹ - A)` is surjective because the nonreal shift `c⁻¹ - A` is. -/
theorem _root_.IsSelfAdjoint.one_smul_sub_smul_restrictScalars_surjective {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.im ≠ 0) :
    Function.Surjective fun x : (c • A.restrictScalars ℝ).domain =>
      (1 : ℝ) • (x : E) - (c • A.restrictScalars ℝ) x := by
  rw [← LinearPMap.restrictScalars_smul]
  intro y
  have hc0 : c ≠ 0 := fun h => hc (by rw [h, Complex.zero_im])
  have hinv : (c⁻¹).im ≠ 0 := by
    rw [Complex.inv_im, neg_div, neg_ne_zero]
    exact div_ne_zero hc (Complex.normSq_pos.mpr hc0).ne'
  obtain ⟨x, hx⟩ := hA.smul_sub_surjective hinv (c⁻¹ • y)
  refine ⟨⟨x, ((c • A).mem_restrictScalars_domain ℝ).mpr x.property⟩, ?_⟩
  -- Beta-reduce the applied lambdas, then evaluate the restricted operator at `x`.
  dsimp only at hx ⊢
  rw [(c • A).restrictScalars_apply ℝ, LinearPMap.smul_apply, one_smul]
  have hcx : c • (c⁻¹ • (x : E) - A x) = c • (c⁻¹ • y) := congrArg (c • ·) hx
  rw [smul_sub, smul_smul, mul_inv_cancel₀ hc0, one_smul, smul_inv_smul₀ hc0] at hcx
  exact hcx

/-- **`c • A` is m-dissipative for self-adjoint `A` and nonzero purely imaginary `c`.** The real
restriction of `c • A` is dissipative, because its quadratic form is purely imaginary, and
`1 - c • A` is surjective, because the nonreal shift `c⁻¹ - A` is. -/
theorem _root_.IsSelfAdjoint.isMDissipative_smul_restrictScalars {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0) :
    TauCeti.Semigroups.IsMDissipative (c • A.restrictScalars ℝ) :=
  (hA.isFormalAdjoint.isDissipative_smul_restrictScalars hc).isMDissipative one_pos
    (hA.one_smul_sub_smul_restrictScalars_surjective
      fun h => hc0 (Complex.ext (by simpa using hc) (by simpa using h)))

end LinearPMap

end
