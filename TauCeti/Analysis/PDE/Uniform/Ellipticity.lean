/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Uniform ellipticity for divergence-form PDE coefficients

This file records the explicit-constant matrix inequalities used for uniformly elliptic
divergence-form operators. For a coefficient field
`a : X → Matrix n n ℝ` on a domain `Ω : Set X`, the predicate
`UniformlyEllipticOn Ω a λ Λ` means

`λ ‖ξ‖² ≤ ξᵀ a(x) ξ` and `|ηᵀ a(x) ξ| ≤ Λ ‖η‖ ‖ξ‖`

for every `x ∈ Ω` and all vectors `η`, `ξ`, together with the quantitative side conditions
`0 < λ` and `λ ≤ Λ`. The lower bound is the coercivity hypothesis; the bilinear upper bound
controls nonsymmetric coefficient fields for weak-form boundedness.

This is the coefficient hypothesis named in the PDE roadmap before the energy bilinear form
and Lax--Milgram arguments: constants are parameters, not hidden existential data.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn`: uniform lower and upper ellipticity bounds on a set.
* `TauCeti.PDE.uniformlyEllipticOn_const_one`: the identity matrix is uniformly elliptic.
* `TauCeti.PDE.UniformlyEllipticOn.mono_constants`: weakening constants preserves the
  predicate.
* `TauCeti.PDE.UniformlyEllipticOn.mono_set`: restriction to a smaller domain preserves the
  predicate.
* `TauCeti.PDE.UniformlyEllipticOn.congr`: replace a coefficient field by one that agrees
  on the domain.
* `TauCeti.PDE.matrixBilinearForm`: the bounded bilinear form `η, ξ ↦ ηᵀ A ξ` attached to
  a coefficient matrix.
* `TauCeti.PDE.matrixBilinearFormLinear`: the coefficient matrix-to-bilinear-form map as a
  continuous linear map.
* `TauCeti.PDE.matrixBilinearForm_opNorm_le_of_upper_bound`: a pointwise bilinear upper
  bound controls the operator norm of the attached matrix bilinear form.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_matrixBilinearForm`: pointwise coercivity of
  the bilinear form attached to a uniformly elliptic coefficient field.
* `TauCeti.PDE.UniformlyEllipticOn.opNorm_matrixBilinearForm_le`: pointwise operator-norm
  boundedness of the bilinear form attached to a uniformly elliptic coefficient field.
* `TauCeti.PDE.uniformlyEllipticOn_smul_one`: scalar, isotropic coefficient fields are
  uniformly elliptic when their scalar coefficient lies between the ellipticity constants.
* `TauCeti.PDE.UniformlyEllipticOn.add_nonneg`: adding a nonnegative bounded
  coefficient field preserves the lower ellipticity constant and adds upper constants.
* `TauCeti.PDE.UniformlyEllipticOn.add_bounded`: adding a bounded coefficient
  perturbation preserves uniform ellipticity with lower constant `λ - μ` when the
  perturbation size `μ` is smaller than `λ`.
* `TauCeti.PDE.coefficientSymmetricPart`: the symmetric part `(A + Aᵀ) / 2` of a
  coefficient matrix.
* `TauCeti.PDE.UniformlyEllipticOn.transpose` and
  `TauCeti.PDE.UniformlyEllipticOn.coefficientSymmetricPart`: transposing or replacing a
  coefficient field by its symmetric part preserves uniform ellipticity with the same
  constants.

The vectors are `EuclideanSpace ℝ n`, matching the roadmap's bounded open subsets of
`ℝⁿ`; this type is reducibly a finite `L²` product, so Mathlib's matrix-vector API applies
directly.
-/

public section

namespace TauCeti

namespace PDE

open Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- Mathlib's matrix quadratic form is the dot-product expression `ξᵀ A ξ`. -/
lemma toQuadraticForm'_eq_dotProduct (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    A.toQuadraticForm' ξ = ξ ⬝ᵥ (A *ᵥ ξ) := by
  rw [Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']

/-- The identity matrix has quadratic form `‖ξ‖²`. -/
@[simp]
lemma toQuadraticForm'_one (ξ : EuclideanSpace ℝ n) :
    (1 : Matrix n n ℝ).toQuadraticForm' ξ = ‖ξ‖ ^ 2 := by
  rw [toQuadraticForm'_eq_dotProduct, one_mulVec]
  simpa [dotProduct, sq] using (EuclideanSpace.real_norm_sq_eq ξ).symm

omit [DecidableEq n] in
/-- The continuous bilinear form attached to a real matrix on Euclidean space.

For a coefficient matrix `A`, this is the pointwise weak-form integrand
`(η, ξ) ↦ ηᵀ A ξ`. It is bundled as a continuous bilinear map so it can feed directly into
Mathlib's bounded-bilinear-form and Lax--Milgram APIs once the corresponding Sobolev spaces
are available. -/
noncomputable def matrixBilinearForm (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  LinearMap.toContinuousBilinearMap
    ((Matrix.toBilin'Aux A).comp (EuclideanSpace.equiv n ℝ).toLinearEquiv.toLinearMap
      (EuclideanSpace.equiv n ℝ).toLinearEquiv.toLinearMap)

omit [DecidableEq n] in
/-- The matrix bilinear form is the dot-product expression `ηᵀ A ξ`. -/
@[simp]
lemma matrixBilinearForm_apply (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm A η ξ = η ⬝ᵥ (A *ᵥ ξ) := by
  rw [matrixBilinearForm, LinearMap.toContinuousBilinearMap_apply, LinearMap.BilinForm.comp_apply]
  simp [Matrix.toBilin'Aux, Matrix.toLinearMap₂'Aux, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_left_comm, mul_comm]

/-- The matrix bilinear form associated to the identity matrix is the Euclidean dot product. -/
lemma matrixBilinearForm_one_apply (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (1 : Matrix n n ℝ) η ξ = η ⬝ᵥ ξ := by
  rw [matrixBilinearForm_apply, one_mulVec]

/-- Matrix quadratic forms are linear in scalar multiplication of the coefficient matrix. -/
@[simp]
lemma toQuadraticForm'_smul (c : ℝ) (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (c • A).toQuadraticForm' ξ = c * A.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct, smul_mulVec,
    dotProduct_smul]
  simp [smul_eq_mul]

/-- The scalar identity matrix has quadratic form `c ‖ξ‖²`. -/
lemma toQuadraticForm'_smul_one (c : ℝ) (ξ : EuclideanSpace ℝ n) :
    (c • (1 : Matrix n n ℝ)).toQuadraticForm' ξ = c * ‖ξ‖ ^ 2 := by
  rw [toQuadraticForm'_smul, toQuadraticForm'_one]

/-- Matrix quadratic forms are additive in the coefficient matrix. -/
@[simp]
lemma toQuadraticForm'_add (A B : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (A + B).toQuadraticForm' ξ = A.toQuadraticForm' ξ + B.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct,
    toQuadraticForm'_eq_dotProduct, add_mulVec, dotProduct_add]

omit [DecidableEq n] in
/-- Matrix bilinear forms are linear in scalar multiplication of the coefficient matrix. -/
lemma matrixBilinearForm_smul_apply (c : ℝ) (A : Matrix n n ℝ)
    (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (c • A) η ξ = c * matrixBilinearForm A η ξ := by
  rw [matrixBilinearForm_apply, matrixBilinearForm_apply, smul_mulVec, dotProduct_smul]
  simp [smul_eq_mul]

omit [DecidableEq n] in
/-- Matrix bilinear forms are additive in the coefficient matrix. -/
lemma matrixBilinearForm_add_apply (A B : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (A + B) η ξ = matrixBilinearForm A η ξ + matrixBilinearForm B η ξ := by
  rw [matrixBilinearForm_apply, matrixBilinearForm_apply, matrixBilinearForm_apply,
    add_mulVec, dotProduct_add]

/-- Transposing the coefficient matrix does not change its quadratic form. -/
@[simp]
lemma toQuadraticForm'_transpose (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    Aᵀ.toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct,
    Matrix.dotProduct_transpose_mulVec]

omit [DecidableEq n] in
/-- Transposing the coefficient matrix swaps the arguments of the bundled matrix bilinear
form. -/
lemma matrixBilinearForm_transpose_apply (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm Aᵀ η ξ = matrixBilinearForm A ξ η := by
  rw [matrixBilinearForm_apply, matrixBilinearForm_apply, Matrix.dotProduct_transpose_mulVec]

/-- The matrix bilinear form associated to `c • 1` is `c` times the Euclidean dot product. -/
lemma matrixBilinearForm_smul_one_apply (c : ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (c • (1 : Matrix n n ℝ)) η ξ = c * (η ⬝ᵥ ξ) := by
  rw [matrixBilinearForm_smul_apply, matrixBilinearForm_one_apply]

/-- The quadratic part of the matrix bilinear form is the matrix quadratic form. -/
lemma matrixBilinearForm_self (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm A ξ ξ = A.toQuadraticForm' ξ := by
  rw [matrixBilinearForm_apply, toQuadraticForm'_eq_dotProduct]

omit [DecidableEq n] in
/-- The principal coefficient matrix-to-bilinear-form map as a continuous linear map. -/
noncomputable def matrixBilinearFormLinear :
    Matrix n n ℝ →L[ℝ] EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        matrixBilinearForm A
      map_add' := by
        intro A B
        ext η ξ
        exact matrixBilinearForm_add_apply A B η ξ
      map_smul' := by
        intro r A
        ext η ξ
        exact matrixBilinearForm_smul_apply r A η ξ }

omit [DecidableEq n] in
/-- Applying `matrixBilinearFormLinear` recovers `matrixBilinearForm`. -/
@[simp]
lemma matrixBilinearFormLinear_apply (A : Matrix n n ℝ) :
    matrixBilinearFormLinear (n := n) A = matrixBilinearForm A :=
  by
    ext η ξ
    simp [matrixBilinearFormLinear]

omit [DecidableEq n] in
/-- The principal coefficient-to-bilinear-form map is continuous. -/
lemma continuous_matrixBilinearForm :
    Continuous (fun A : Matrix n n ℝ => matrixBilinearForm A) :=
  (matrixBilinearFormLinear (n := n)).continuous.congr fun A =>
    matrixBilinearFormLinear_apply A

section Continuity

variable [TopologicalSpace X]

namespace Continuous

omit [DecidableEq n] in
/-- A continuous principal coefficient field gives a continuous field of principal bilinear
forms. -/
lemma matrixBilinearForm {a : X → Matrix n n ℝ} (ha : Continuous a) :
    Continuous (fun x => PDE.matrixBilinearForm (a x)) :=
  continuous_matrixBilinearForm.comp ha

end Continuous

namespace ContinuousOn

omit [DecidableEq n] in
/-- A continuous principal coefficient field on a set gives a continuous field of principal
bilinear forms on that set. -/
lemma matrixBilinearForm {s : Set X} {a : X → Matrix n n ℝ} (ha : ContinuousOn a s) :
    ContinuousOn (fun x => PDE.matrixBilinearForm (a x)) s :=
  continuous_matrixBilinearForm.comp_continuousOn ha

end ContinuousOn

end Continuity

/-- The symmetric part `(A + Aᵀ) / 2` of a coefficient matrix.

For energy estimates the diagonal quadratic form of `A` agrees with that of
`coefficientSymmetricPart A`, while the resulting matrix is symmetric. This is the
finite-dimensional bookkeeping needed before the integrated energy form is specialized to
self-adjoint elliptic operators. -/
noncomputable def coefficientSymmetricPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (A + Aᵀ)

omit [Fintype n] [DecidableEq n] in
/-- The symmetric part of a coefficient matrix is symmetric. -/
lemma coefficientSymmetricPart_isSymm (A : Matrix n n ℝ) :
    (coefficientSymmetricPart A).IsSymm :=
  (isSymm_add_transpose_self A).smul (1 / 2 : ℝ)

omit [Fintype n] [DecidableEq n] in
/-- The entries of the symmetric part are the averages of opposite entries. -/
@[simp]
lemma coefficientSymmetricPart_apply (A : Matrix n n ℝ) (i j : n) :
    coefficientSymmetricPart A i j = (A i j + A j i) / 2 := by
  simp [coefficientSymmetricPart, div_eq_mul_inv, mul_comm]

omit [Fintype n] [DecidableEq n] in
/-- A symmetric coefficient matrix is unchanged by taking its symmetric part. -/
@[simp]
lemma coefficientSymmetricPart_eq_self_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm) :
    coefficientSymmetricPart A = A := by
  ext i j
  rw [coefficientSymmetricPart_apply, hA.apply i j]
  ring

/-- The symmetric part has the same quadratic form as the original coefficient matrix. -/
@[simp]
lemma toQuadraticForm'_coefficientSymmetricPart (A : Matrix n n ℝ)
    (ξ : EuclideanSpace ℝ n) :
    (coefficientSymmetricPart A).toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [coefficientSymmetricPart, toQuadraticForm'_smul, toQuadraticForm'_add,
    toQuadraticForm'_transpose]
  ring

omit [DecidableEq n] in
/-- The bundled bilinear form of the symmetric part is the average of the original bilinear
form and its transpose. -/
lemma matrixBilinearForm_coefficientSymmetricPart_apply (A : Matrix n n ℝ)
    (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (coefficientSymmetricPart A) η ξ =
      (matrixBilinearForm A η ξ + matrixBilinearForm A ξ η) / 2 := by
  rw [coefficientSymmetricPart, matrixBilinearForm_smul_apply, matrixBilinearForm_add_apply,
    matrixBilinearForm_transpose_apply]
  ring

omit [DecidableEq n] in
/-- A pointwise bilinear upper bound gives the corresponding norm estimate for the bundled
continuous bilinear form. -/
lemma norm_matrixBilinearForm_le_of_upper_bound (A : Matrix n n ℝ) {Lam : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    ‖matrixBilinearForm A η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ := by
  simpa [Real.norm_eq_abs] using hA η ξ

omit [DecidableEq n] in
/-- A pointwise bilinear upper bound controls the operator norm of the bundled matrix
bilinear form.

This is the matrix-coefficient specialization of Mathlib's
`ContinuousLinearMap.opNorm_le_bound₂`. -/
lemma matrixBilinearForm_opNorm_le_of_upper_bound (A : Matrix n n ℝ) {Lam : ℝ}
    (hLam_nonneg : 0 ≤ Lam)
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) :
    ‖matrixBilinearForm A‖ ≤ Lam := by
  refine (matrixBilinearForm A).opNorm_le_bound₂ hLam_nonneg ?_
  intro η ξ
  exact norm_matrixBilinearForm_le_of_upper_bound A hA η ξ

omit [DecidableEq n] in
/-- A pointwise bilinear upper bound gives a radius-restricted estimate for the bundled
matrix bilinear form. -/
lemma matrixBilinearForm_apply_norm_le_of_upper_bound {A : Matrix n n ℝ} {Lam R S : ℝ}
    (hLam_nonneg : 0 ≤ Lam)
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    {η ξ : EuclideanSpace ℝ n} (hη : ‖η‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖matrixBilinearForm A η ξ‖ ≤ Lam * R * S :=
  (matrixBilinearForm A).le_of_opNorm₂_le_of_le
    (matrixBilinearForm_opNorm_le_of_upper_bound A hLam_nonneg hA) hη hξ

/-- A scalar multiple of the identity has operator integrand bounded by any upper bound for
the absolute value of the scalar. -/
lemma abs_dotProduct_smul_one_mulVec_le_of_abs_le {c Lam : ℝ} (hc : |c| ≤ Lam)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((c • (1 : Matrix n n ℝ)) *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  rw [smul_mulVec, one_mulVec, dotProduct_smul]
  simp only [smul_eq_mul, abs_mul]
  calc
    |c| * |η ⬝ᵥ ξ| ≤ |c| * (‖η‖ * ‖ξ‖) := by
      gcongr
      simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
        abs_real_inner_le_norm η ξ
    _ ≤ Lam * ‖η‖ * ‖ξ‖ := by
      have hnorm : 0 ≤ ‖η‖ * ‖ξ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hc hnorm

/-- A scalar multiple of the identity has operator integrand bounded by any upper bound for
the absolute value of the scalar. -/
lemma norm_matrixBilinearForm_smul_one_le_of_abs_le {c Lam : ℝ} (hc : |c| ≤ Lam)
    (η ξ : EuclideanSpace ℝ n) :
    ‖matrixBilinearForm (c • (1 : Matrix n n ℝ)) η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ :=
  norm_matrixBilinearForm_le_of_upper_bound (c • (1 : Matrix n n ℝ))
    (abs_dotProduct_smul_one_mulVec_le_of_abs_le hc) η ξ

omit [DecidableEq n] in
/-- Adding two pointwise bilinear upper bounds adds the constants. -/
lemma abs_dotProduct_add_mulVec_le {A B : Matrix n n ℝ} {Lam Mu : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hB : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (B *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((A + B) *ᵥ ξ)| ≤ (Lam + Mu) * ‖η‖ * ‖ξ‖ := by
  rw [add_mulVec, dotProduct_add]
  calc
    |η ⬝ᵥ (A *ᵥ ξ) + η ⬝ᵥ (B *ᵥ ξ)|
        ≤ |η ⬝ᵥ (A *ᵥ ξ)| + |η ⬝ᵥ (B *ᵥ ξ)| := abs_add_le _ _
    _ ≤ Lam * ‖η‖ * ‖ξ‖ + Mu * ‖η‖ * ‖ξ‖ := add_le_add (hA η ξ) (hB η ξ)
    _ = (Lam + Mu) * ‖η‖ * ‖ξ‖ := by ring

omit [DecidableEq n] in
/-- The symmetric part of a pointwise bounded coefficient matrix satisfies the same bilinear
upper bound. -/
lemma abs_dotProduct_coefficientSymmetricPart_mulVec_le {A : Matrix n n ℝ} {Lam : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ (coefficientSymmetricPart A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  classical
  rw [← matrixBilinearForm_apply, matrixBilinearForm_coefficientSymmetricPart_apply]
  have hηξ : ‖matrixBilinearForm A η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ :=
    norm_matrixBilinearForm_le_of_upper_bound A hA η ξ
  have hξη : ‖matrixBilinearForm A ξ η‖ ≤ Lam * ‖η‖ * ‖ξ‖ := by
    rw [mul_right_comm]
    exact norm_matrixBilinearForm_le_of_upper_bound A hA ξ η
  have hsum :
      ‖matrixBilinearForm A η ξ + matrixBilinearForm A ξ η‖
        ≤ 2 * (Lam * ‖η‖ * ‖ξ‖) := by
    calc
      ‖matrixBilinearForm A η ξ + matrixBilinearForm A ξ η‖
          ≤ ‖matrixBilinearForm A η ξ‖ + ‖matrixBilinearForm A ξ η‖ := norm_add_le _ _
      _ ≤ Lam * ‖η‖ * ‖ξ‖ + Lam * ‖η‖ * ‖ξ‖ := add_le_add hηξ hξη
      _ = 2 * (Lam * ‖η‖ * ‖ξ‖) := by ring
  rw [abs_div]
  rw [abs_of_pos (a := (2 : ℝ)) two_pos]
  exact (div_le_iff₀' two_pos).2 (by
    simpa [Real.norm_eq_abs] using hsum)

/-- Adding a nonnegative quadratic form preserves a lower quadratic bound. -/
lemma lower_bound_toQuadraticForm'_add {A B : Matrix n n ℝ} {lam : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ)
    (ξ : EuclideanSpace ℝ n) :
    lam * ‖ξ‖ ^ 2 ≤ (A + B).toQuadraticForm' ξ := by
  rw [toQuadraticForm'_add]
  exact (hA ξ).trans (le_add_of_nonneg_right (hB ξ))

/-- Adding a coefficient with a one-sided quadratic lower bound lowers a quadratic lower
bound by the size of that perturbation. -/
lemma lower_bound_toQuadraticForm'_add_of_lower_bound {A B : Matrix n n ℝ} {lam Mu : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hB : ∀ ξ : EuclideanSpace ℝ n, -(Mu * ‖ξ‖ ^ 2) ≤ B.toQuadraticForm' ξ)
    (ξ : EuclideanSpace ℝ n) :
    (lam - Mu) * ‖ξ‖ ^ 2 ≤ (A + B).toQuadraticForm' ξ := by
  rw [toQuadraticForm'_add]
  have hA_lower := hA ξ
  have hB_lower := hB ξ
  nlinarith

/-- A bilinear upper bound for a coefficient matrix bounds its quadratic form in absolute
value by the same constant. -/
lemma abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le {B : Matrix n n ℝ} {Mu : ℝ}
    (hB : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (B *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (ξ : EuclideanSpace ℝ n) :
    |B.toQuadraticForm' ξ| ≤ Mu * ‖ξ‖ ^ 2 := by
  rw [toQuadraticForm'_eq_dotProduct]
  have h := hB ξ ξ
  simpa [sq, mul_assoc] using h

/-- A pointwise quadratic lower bound makes the associated matrix bilinear form coercive in
Mathlib's Lax--Milgram sense. -/
lemma isCoercive_matrixBilinearForm_of_lower_bound (A : Matrix n n ℝ) {lam : ℝ}
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) :
    IsCoercive (matrixBilinearForm A) := by
  refine ⟨lam, hlam, fun ξ => ?_⟩
  rw [matrixBilinearForm_self]
  simpa [sq, pow_two, mul_assoc] using hA ξ

/-- The identity matrix bilinear form is coercive with constant `1`. -/
lemma isCoercive_matrixBilinearForm_one :
    IsCoercive (matrixBilinearForm (1 : Matrix n n ℝ)) := by
  refine isCoercive_matrixBilinearForm_of_lower_bound (1 : Matrix n n ℝ) zero_lt_one ?_
  intro ξ
  simp

/-- A positive scalar multiple of the identity matrix gives a coercive bilinear form. -/
lemma isCoercive_matrixBilinearForm_smul_one {c : ℝ} (hc : 0 < c) :
    IsCoercive (matrixBilinearForm (c • (1 : Matrix n n ℝ))) := by
  refine isCoercive_matrixBilinearForm_of_lower_bound (c • (1 : Matrix n n ℝ)) hc ?_
  intro ξ
  simp

/-- Uniform ellipticity and boundedness with explicit constants on a domain.

The predicate says that for every `x ∈ Ω`, the matrix `a x` has quadratic form bounded below
by `λ‖ξ‖²` and bilinear form bounded above by `Λ‖η‖‖ξ‖`, uniformly in `x`, `η`, and `ξ`.
The side conditions `0 < λ` and `λ ≤ Λ` are part of the predicate so later energy estimates can
recover them directly. -/
def UniformlyEllipticOn (Ω : Set X) (a : X → Matrix n n ℝ) (lam Lam : ℝ) : Prop :=
  0 < lam ∧ lam ≤ Lam ∧
    ∀ ⦃x⦄, x ∈ Ω →
      (∀ ξ : EuclideanSpace ℝ n,
        lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) ∧
        ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖

/-- Characteristic restatement of uniform ellipticity and boundedness on a domain. -/
lemma uniformlyEllipticOn_iff :
    UniformlyEllipticOn Ω a lam Lam ↔
      0 < lam ∧ lam ≤ Lam ∧
        ∀ ⦃x⦄, x ∈ Ω →
          (∀ ξ : EuclideanSpace ℝ n,
            lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) ∧
            ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ :=
  Iff.rfl

namespace UniformlyEllipticOn

variable {Ω Ω' : Set X} {a b : X → Matrix n n ℝ}
  {lam Lam lam' Lam' : ℝ}

/-- The lower ellipticity constant is positive. -/
@[grind →]
lemma pos (h : UniformlyEllipticOn Ω a lam Lam) : 0 < lam :=
  h.1

/-- The lower ellipticity constant is no larger than the upper constant. -/
@[grind →]
lemma le (h : UniformlyEllipticOn Ω a lam Lam) : lam ≤ Lam :=
  h.2.1

/-- The upper ellipticity constant is nonnegative. -/
lemma upper_nonneg (h : UniformlyEllipticOn Ω a lam Lam) : 0 ≤ Lam :=
  h.pos.le.trans h.le

/-- The lower quadratic-form bound supplied by uniform ellipticity. -/
@[grind =>]
lemma lower_bound (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (ξ : EuclideanSpace ℝ n) :
    lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ :=
  (h.2.2 hx).1 ξ

/-- The bilinear upper bound supplied by uniform ellipticity. -/
@[grind =>]
lemma upper_bound (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ :=
  (h.2.2 hx).2 η ξ

/-- Uniform ellipticity implies pointwise nonnegativity of the coefficient quadratic form. -/
lemma quadraticForm_nonneg (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (ξ : EuclideanSpace ℝ n) :
    0 ≤ (a x).toQuadraticForm' ξ := by
  exact (mul_nonneg h.pos.le (sq_nonneg ‖ξ‖)).trans (h.lower_bound hx ξ)

/-- Uniform ellipticity gives a positive quadratic form on every nonzero vector. -/
lemma quadraticForm_pos (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    {ξ : EuclideanSpace ℝ n} (hξ : ξ ≠ 0) :
    0 < (a x).toQuadraticForm' ξ := by
  exact (mul_pos h.pos (sq_pos_of_ne_zero (by simpa using hξ))).trans_le
    (h.lower_bound hx ξ)

/-- Restricting the domain preserves uniform ellipticity with the same constants. -/
lemma mono_set (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : Ω' ⊆ Ω) :
    UniformlyEllipticOn Ω' a lam Lam :=
  ⟨h.pos, h.le, fun {_} hx => h.2.2 (hΩ hx)⟩

/-- Weakening the lower constant and increasing the upper constant preserves uniform
ellipticity. -/
lemma mono_constants (h : UniformlyEllipticOn Ω a lam Lam) (hlam' : 0 < lam')
    (hlam'_le : lam' ≤ lam) (hLam_le : Lam ≤ Lam') :
    UniformlyEllipticOn Ω a lam' Lam' := by
  refine ⟨hlam', hlam'_le.trans (h.le.trans hLam_le), fun {x} hx => ?_⟩
  refine ⟨fun ξ => ?_, fun η ξ => ?_⟩
  · have hnorm : 0 ≤ (‖ξ‖ : ℝ) ^ 2 := sq_nonneg ‖ξ‖
    exact (mul_le_mul_of_nonneg_right hlam'_le hnorm).trans (h.lower_bound hx ξ)
  · exact (h.upper_bound hx η ξ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLam_le (norm_nonneg _))
        (norm_nonneg _))

/-- A constructor when the side conditions and pointwise quadratic-form bounds are already
available separately. -/
lemma of_bounds (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hbounds : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hupper : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) :
    UniformlyEllipticOn Ω a lam Lam :=
  ⟨hlam, hlamLam, fun {_} hx => ⟨hbounds hx, hupper hx⟩⟩

/-- Uniform ellipticity depends only on the coefficient values on the domain. -/
lemma congr (h : UniformlyEllipticOn Ω a lam Lam) (hab : Set.EqOn b a Ω) :
    UniformlyEllipticOn Ω b lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · rw [hab hx]
    exact h.lower_bound hx ξ
  · rw [hab hx]
    exact h.upper_bound hx η ξ

/-- At every point of the domain, uniform ellipticity gives a norm bound for the attached
matrix bilinear form. -/
@[grind =>]
lemma norm_point_matrixBilinearForm_le (h : UniformlyEllipticOn Ω a lam Lam) {x : X}
    (hx : x ∈ Ω) (η ξ : EuclideanSpace ℝ n) :
    ‖matrixBilinearForm (a x) η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ :=
  norm_matrixBilinearForm_le_of_upper_bound (a x) (h.upper_bound hx) η ξ

/-- At every point of the domain, uniform ellipticity bounds the operator norm of the
attached matrix bilinear form by the upper ellipticity constant. -/
@[grind =>]
lemma opNorm_matrixBilinearForm_le (h : UniformlyEllipticOn Ω a lam Lam) {x : X}
    (hx : x ∈ Ω) :
    ‖matrixBilinearForm (a x)‖ ≤ Lam :=
  matrixBilinearForm_opNorm_le_of_upper_bound (a x) h.upper_nonneg (h.upper_bound hx)

/-- Uniform ellipticity gives a radius-restricted pointwise bound for the coefficient
integrand. -/
@[grind =>]
lemma norm_point_matrixBilinearForm_le_mul_of_norm_le
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) {R S : ℝ}
    {η ξ : EuclideanSpace ℝ n} (hη : ‖η‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖matrixBilinearForm (a x) η ξ‖ ≤ Lam * R * S :=
  (matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le
    (h.opNorm_matrixBilinearForm_le hx) hη hξ

/-- At every point of the domain, uniform ellipticity gives coercivity of the attached matrix
bilinear form. -/
@[grind =>]
lemma isCoercive_matrixBilinearForm (h : UniformlyEllipticOn Ω a lam Lam) {x : X}
    (hx : x ∈ Ω) :
    IsCoercive (matrixBilinearForm (a x)) :=
  isCoercive_matrixBilinearForm_of_lower_bound (a x) h.pos (h.lower_bound hx)

/-- Transposing the coefficient field preserves uniform ellipticity with the same constants.

The quadratic lower bound is unchanged, and the bilinear upper bound follows by swapping the
two Euclidean arguments. -/
lemma transpose (h : UniformlyEllipticOn Ω a lam Lam) :
    UniformlyEllipticOn Ω (fun x => (a x)ᵀ) lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · simpa using h.lower_bound hx ξ
  · rw [Matrix.dotProduct_transpose_mulVec]
    rw [mul_right_comm]
    exact h.upper_bound hx ξ η

/-- Replacing a coefficient field by its symmetric part preserves uniform ellipticity with
the same constants.

This lets the energy-method API pass from a nonsymmetric uniformly elliptic principal
coefficient to the symmetric coefficient with the same diagonal energy, which is the
finite-dimensional prerequisite for self-adjoint model problems. -/
lemma coefficientSymmetricPart (h : UniformlyEllipticOn Ω a lam Lam) :
    UniformlyEllipticOn Ω (fun x => coefficientSymmetricPart (a x)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · simpa using h.lower_bound hx ξ
  · exact abs_dotProduct_coefficientSymmetricPart_mulVec_le (h.upper_bound hx) η ξ

/-- Adding a pointwise nonnegative bounded coefficient field preserves uniform ellipticity.

The lower ellipticity constant is unchanged, while the upper bilinear-form constant is
increased by the upper bound for the perturbation. This is the pointwise matrix estimate
used when an energy form is split into a uniformly elliptic principal part plus a
nonnegative bounded perturbation. -/
lemma add_nonneg (h : UniformlyEllipticOn Ω a lam Lam) {b : X → Matrix n n ℝ}
    {Mu : ℝ} (hMu : 0 ≤ Mu)
    (hb_nonneg : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n,
      0 ≤ (b x).toQuadraticForm' ξ)
    (hb_upper : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (b x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖) :
    UniformlyEllipticOn Ω (fun x => a x + b x) lam (Lam + Mu) := by
  refine UniformlyEllipticOn.of_bounds h.pos ?_ (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · exact h.le.trans (le_add_of_nonneg_right hMu)
  · exact lower_bound_toQuadraticForm'_add (h.lower_bound hx) (hb_nonneg hx) ξ
  · exact abs_dotProduct_add_mulVec_le (h.upper_bound hx) (hb_upper hx) η ξ

/-- Adding a bounded coefficient perturbation preserves uniform ellipticity after reducing
the lower ellipticity constant by the perturbation size.

If `a` is uniformly elliptic with constants `λ, Λ` and `b` has pointwise bilinear bound
`μ`, then `a + b` is uniformly elliptic with constants `λ - μ, Λ + μ`, provided `μ < λ`.
This is the finite-dimensional coefficient stability estimate used when perturbing a
uniformly elliptic divergence-form operator. -/
lemma add_bounded (h : UniformlyEllipticOn Ω a lam Lam) {b : X → Matrix n n ℝ}
    {Mu : ℝ} (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hb_upper : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (b x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖) :
    UniformlyEllipticOn Ω (fun x => a x + b x) (lam - Mu) (Lam + Mu) := by
  refine UniformlyEllipticOn.of_bounds (sub_pos.mpr hMu_lt) ?_ (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · linarith [h.le, hMu_nonneg]
  · refine lower_bound_toQuadraticForm'_add_of_lower_bound (h.lower_bound hx) ?_ ξ
    intro ζ
    exact (neg_le_neg
      (abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le (hb_upper hx) ζ)).trans
      (neg_abs_le ((b x).toQuadraticForm' ζ))
  · exact abs_dotProduct_add_mulVec_le (h.upper_bound hx) (hb_upper hx) η ξ

/-- Adding a bounded scalar multiple of the identity preserves uniform ellipticity after
reducing the lower ellipticity constant by the scalar bound.

This is the scalar-coefficient specialization of `UniformlyEllipticOn.add_bounded`: no sign
condition is imposed on `c`, only the pointwise bound `|c x| ≤ μ`. -/
lemma add_smul_one_bounded (h : UniformlyEllipticOn Ω a lam Lam) {c : X → ℝ} {Mu : ℝ}
    (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hc_abs : ∀ ⦃x⦄, x ∈ Ω → |c x| ≤ Mu) :
    UniformlyEllipticOn Ω (fun x => a x + c x • (1 : Matrix n n ℝ)) (lam - Mu)
      (Lam + Mu) :=
  h.add_bounded hMu_nonneg hMu_lt
    (fun {_} hx η ξ => abs_dotProduct_smul_one_mulVec_le_of_abs_le (hc_abs hx) η ξ)

/-- Adding a constant bounded scalar multiple of the identity preserves uniform ellipticity
after reducing the lower ellipticity constant by the absolute value bound. -/
lemma add_const_smul_one_bounded (h : UniformlyEllipticOn Ω a lam Lam) {c Mu : ℝ}
    (hMu_lt : Mu < lam) (hc_abs : |c| ≤ Mu) :
    UniformlyEllipticOn Ω (fun y => a y + c • (1 : Matrix n n ℝ)) (lam - Mu)
      (Lam + Mu) :=
  h.add_smul_one_bounded ((abs_nonneg c).trans hc_abs) hMu_lt (fun {_} _ => hc_abs)

/-- Adding a bounded nonnegative scalar multiple of the identity preserves uniform
ellipticity, with the upper constant increased by the scalar bound. -/
lemma add_smul_one (h : UniformlyEllipticOn Ω a lam Lam) {c : X → ℝ} {Mu : ℝ}
    (hMu : 0 ≤ Mu) (hc_nonneg : ∀ ⦃x⦄, x ∈ Ω → 0 ≤ c x)
    (hc_upper : ∀ ⦃x⦄, x ∈ Ω → c x ≤ Mu) :
    UniformlyEllipticOn Ω (fun x => a x + c x • (1 : Matrix n n ℝ)) lam (Lam + Mu) := by
  refine h.add_nonneg hMu (fun {x} hx ξ => ?_) (fun {x} hx η ξ => ?_)
  · simp only [toQuadraticForm'_smul_one]
    exact mul_nonneg (hc_nonneg hx) (sq_nonneg ‖ξ‖)
  · have hcx_abs : |c x| ≤ Mu := by
      simpa [abs_of_nonneg (hc_nonneg hx)] using hc_upper hx
    exact abs_dotProduct_smul_one_mulVec_le_of_abs_le hcx_abs η ξ

/-- Adding a constant nonnegative scalar multiple of the identity preserves uniform
ellipticity, with the upper constant increased by that scalar. -/
lemma add_const_smul_one (h : UniformlyEllipticOn Ω a lam Lam) {c : ℝ} (hc : 0 ≤ c) :
    UniformlyEllipticOn Ω (fun x => a x + c • (1 : Matrix n n ℝ)) lam (Lam + c) :=
  h.add_smul_one hc (fun {_} _ => hc) (fun {_} _ => le_rfl)

end UniformlyEllipticOn

variable {Ω : Set X} {a b : X → Matrix n n ℝ}
  {lam Lam : ℝ}

/-- Equal coefficient fields on the domain give equivalent uniform-ellipticity hypotheses. -/
lemma uniformlyEllipticOn_congr (hab : Set.EqOn a b Ω) :
    UniformlyEllipticOn Ω a lam Lam ↔ UniformlyEllipticOn Ω b lam Lam := by
  constructor
  · intro h
    exact h.congr (fun x hx => (hab hx).symm)
  · intro h
    exact h.congr hab

/-- The constant identity coefficient field is uniformly elliptic with any constants
`λ ≤ 1 ≤ Λ` and `0 < λ`. This is the coefficient field of the Laplacian model problem. -/
lemma uniformlyEllipticOn_const_one (Ω : Set X) {lam Lam : ℝ} (hlam : 0 < lam)
    (hlam_one : lam ≤ 1) (hone_Lam : 1 ≤ Lam) :
    UniformlyEllipticOn Ω (fun _ => (1 : Matrix n n ℝ)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds hlam (hlam_one.trans hone_Lam) (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · have hnorm : 0 ≤ (‖ξ‖ : ℝ) ^ 2 := sq_nonneg ‖ξ‖
    simp only [toQuadraticForm'_one]
    simpa using mul_le_mul_of_nonneg_right hlam_one hnorm
  · rw [one_mulVec]
    calc
      |η ⬝ᵥ ξ| ≤ ‖η‖ * ‖ξ‖ := by
        simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
          abs_real_inner_le_norm η ξ
      _ ≤ Lam * ‖η‖ * ‖ξ‖ := by
        have hnorm : 0 ≤ ‖η‖ * ‖ξ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hone_Lam hnorm

/-- In particular, the identity coefficient field is uniformly elliptic with constants
`λ = Λ = 1`. -/
lemma uniformlyEllipticOn_const_one_one (Ω : Set X) :
    UniformlyEllipticOn Ω (fun _ => (1 : Matrix n n ℝ)) 1 1 :=
  uniformlyEllipticOn_const_one Ω zero_lt_one le_rfl le_rfl

/-- An isotropic scalar coefficient field is uniformly elliptic when its scalar coefficient
lies between the lower and upper constants.

This packages the common model `a(x) = c(x) I`: if `λ ≤ c x ≤ Λ` on `Ω`, then `c x • 1`
satisfies the lower quadratic bound and the bilinear upper bound with constants `λ` and `Λ`. -/
lemma uniformlyEllipticOn_smul_one (Ω : Set X) (c : X → ℝ) {lam Lam : ℝ}
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hbound : ∀ ⦃x⦄, x ∈ Ω → lam ≤ c x ∧ c x ≤ Lam) :
    UniformlyEllipticOn Ω (fun x => c x • (1 : Matrix n n ℝ)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds hlam hlamLam (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · simp only [toQuadraticForm'_smul_one]
    exact mul_le_mul_of_nonneg_right (hbound hx).1 (sq_nonneg ‖ξ‖)
  · have hcx_nonneg : 0 ≤ c x := hlam.le.trans (hbound hx).1
    have hcx_abs : |c x| ≤ Lam := by simpa [abs_of_nonneg hcx_nonneg] using (hbound hx).2
    exact abs_dotProduct_smul_one_mulVec_le_of_abs_le hcx_abs η ξ

/-- A constant positive isotropic coefficient field is uniformly elliptic with matching
lower and upper constants. -/
lemma uniformlyEllipticOn_const_smul_one_self (Ω : Set X) {c : ℝ} (hc : 0 < c) :
    UniformlyEllipticOn Ω (fun _ => c • (1 : Matrix n n ℝ)) c c :=
  uniformlyEllipticOn_smul_one Ω (fun _ => c) hc le_rfl (fun {_} _ => ⟨le_rfl, le_rfl⟩)

/-- A constant isotropic coefficient field is uniformly elliptic for any explicit constants
`λ ≤ c ≤ Λ` with `0 < λ`. -/
lemma uniformlyEllipticOn_const_smul_one (Ω : Set X) {c lam Lam : ℝ} (hlam : 0 < lam)
    (hlamc : lam ≤ c) (hcLam : c ≤ Lam) :
    UniformlyEllipticOn Ω (fun _ => c • (1 : Matrix n n ℝ)) lam Lam :=
  uniformlyEllipticOn_smul_one Ω (fun _ => c) hlam (hlamc.trans hcLam)
    (fun {_} _ => ⟨hlamc, hcLam⟩)

end PDE

end TauCeti
