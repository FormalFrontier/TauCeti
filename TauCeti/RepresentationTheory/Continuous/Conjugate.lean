/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Continuous.MatrixCoefficient

/-!
# The conjugate of a continuous representation

Complex conjugation of the matrix entries of a representation gives another representation, the
**conjugate** (equivalently, for a unitary representation, the contragredient). It is what the span
of the matrix coefficients needs in order to be closed under the involution of `C(G, 𝕜)`:
conjugating a matrix coefficient of `π` produces a matrix coefficient of the conjugate of `π`, not
of `π` itself.

There is no canonical conjugation on an abstract inner product space, so the construction takes an
orthonormal basis `e` as data and conjugates the coordinates in it:
`conjugation e x = ∑ i, conj ⟪e i, x⟫ • e i`. This is a conjugate-linear isometric involution of
`V` (`TauCeti.conjugation_conjugation`, `TauCeti.inner_conjugation_conjugation`), and conjugating an
operator by it, `A ↦ J ∘ A ∘ J`, is the coordinate-free description of conjugating the matrix of `A`
entrywise. Different bases give conjugates that are isomorphic representations, so the choice is
immaterial for the uses downstream, which only need one conjugate to exist.

## Main definitions

* `TauCeti.conjugation`: the conjugate-linear isometric involution attached to an orthonormal basis.
* `TauCeti.conjCLM`: conjugation of a continuous linear operator, `A ↦ J ∘ A ∘ J`.
* `TauCeti.ContRepresentation.conjugate`: the conjugate representation.

## Main statements

* `TauCeti.ContRepresentation.continuous_conjugate` and
  `TauCeti.ContRepresentation.IsUnitary.conjugate`: the conjugate of a continuous representation is
  continuous, and of a unitary one is unitary.
* `TauCeti.ContRepresentation.star_matrixCoeff_eq_matrixCoeff_conjugate`: the conjugate of a matrix
  coefficient of `π` is a matrix coefficient of the conjugate of `π`.

This supplies the conjugation half of the representative-ring item of Layer 3 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
whose statement of it is "closed under conjugation (via the contragredient)". The mathematical
development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

section Conjugation

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **Coordinatewise conjugation in an orthonormal basis.** A conjugate-linear isometric involution
of `V`, which on coordinates is `x i ↦ conj (x i)`. -/
noncomputable def conjugation (e : OrthonormalBasis ι 𝕜 V) (x : V) : V :=
  ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i

variable (e : OrthonormalBasis ι 𝕜 V)

/-- Conjugation, expanded as the coordinate sum defining it. -/
theorem conjugation_apply (x : V) :
    conjugation e x = ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i :=
  (rfl)

/-- The coordinates of a conjugate are the conjugated coordinates. -/
@[simp]
theorem inner_conjugation (x : V) (j : ι) :
    ⟪e j, conjugation e x⟫_𝕜 = (starRingEnd 𝕜) ⟪e j, x⟫_𝕜 := by
  classical
  have h : ∀ i, ⟪e j, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 • e i⟫_𝕜 =
      if i = j then (starRingEnd 𝕜) ⟪e j, x⟫_𝕜 else 0 := fun i ↦ by
    rw [inner_smul_right, orthonormal_iff_ite.mp e.orthonormal]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [conjugation_apply, inner_sum]
  simp only [h]
  simp

/-- Conjugation is additive. -/
@[simp]
theorem conjugation_add (x y : V) :
    conjugation e (x + y) = conjugation e x + conjugation e y := by
  simp [conjugation_apply, inner_add_right, add_smul, Finset.sum_add_distrib]

/-- Conjugation is conjugate-linear: a scalar comes out conjugated. -/
@[simp]
theorem conjugation_smul (c : 𝕜) (x : V) :
    conjugation e (c • x) = (starRingEnd 𝕜) c • conjugation e x := by
  simp [conjugation_apply, inner_smul_right, Finset.smul_sum, smul_smul]

/-- Conjugation commutes with subtraction. -/
@[simp]
theorem conjugation_sub (x y : V) :
    conjugation e (x - y) = conjugation e x - conjugation e y := by
  simp [conjugation_apply, inner_sub_right, sub_smul, Finset.sum_sub_distrib]

/-- Conjugation is an involution. -/
@[simp]
theorem conjugation_conjugation (x : V) : conjugation e (conjugation e x) = x := by
  have h : ∀ i, (starRingEnd 𝕜) ⟪e i, conjugation e x⟫_𝕜 = ⟪e i, x⟫_𝕜 := fun i ↦ by
    rw [inner_conjugation]; simp
  rw [conjugation_apply (x := conjugation e x)]
  simp only [h]
  exact e.sum_repr' x

/-- Conjugation reverses the inner product: it is conjugate-linear and isometric. -/
theorem inner_conjugation_conjugation (x y : V) :
    ⟪conjugation e x, conjugation e y⟫_𝕜 = (starRingEnd 𝕜) ⟪x, y⟫_𝕜 := by
  have hxy : ⟪x, y⟫_𝕜 = ∑ i, (starRingEnd 𝕜) ⟪e i, x⟫_𝕜 * ⟪e i, y⟫_𝕜 := by
    conv_lhs => rw [← e.sum_repr' x]
    rw [sum_inner]
    simp [inner_smul_left]
  rw [conjugation_apply e x, sum_inner, hxy, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_smul_left, inner_conjugation]
  simp [mul_comm]

/-- Conjugation is isometric, as the reversal of the inner product shows on the diagonal. -/
@[simp]
theorem norm_conjugation (x : V) : ‖conjugation e x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜) (conjugation e x), norm_eq_sqrt_re_inner (𝕜 := 𝕜) x,
    inner_conjugation_conjugation]
  simp

end Conjugation

section ConjugateOperator

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (e : OrthonormalBasis ι 𝕜 V)

/-- Conjugating an operator, as a linear map: `A ↦ J ∘ A ∘ J` for `J` the conjugation of `e`. The
two conjugate-linearities cancel, so the result is `𝕜`-linear. -/
noncomputable def conjLM (A : V →L[𝕜] V) : V →ₗ[𝕜] V where
  toFun x := conjugation e (A (conjugation e x))
  map_add' x y := by simp
  map_smul' c x := by simp

/-- **Conjugation of a continuous linear operator**, `A ↦ J ∘ A ∘ J`. It is norm-preserving because
`J` is isometric. -/
noncomputable def conjCLM (A : V →L[𝕜] V) : V →L[𝕜] V :=
  LinearMap.mkContinuous (conjLM e A) ‖A‖ fun x ↦ by
    simpa [conjLM] using A.le_opNorm (conjugation e x)

/-- Evaluation of a conjugated operator. -/
@[simp]
theorem conjCLM_apply (A : V →L[𝕜] V) (x : V) :
    conjCLM e A x = conjugation e (A (conjugation e x)) :=
  (rfl)

/-- Conjugation fixes the identity, because `J` is an involution. -/
@[simp]
theorem conjCLM_one : conjCLM e 1 = 1 := by
  ext x
  simp

/-- Conjugation is multiplicative, again because `J` is an involution: the two inner copies of `J`
cancel. -/
@[simp]
theorem conjCLM_mul (A B : V →L[𝕜] V) : conjCLM e (A * B) = conjCLM e A * conjCLM e B := by
  ext x
  simp

/-- Conjugation is additive in the operator. -/
theorem conjCLM_sub (A B : V →L[𝕜] V) : conjCLM e (A - B) = conjCLM e A - conjCLM e B := by
  ext x
  simp

/-- Conjugation does not increase the operator norm. -/
theorem norm_conjCLM_le (A : V →L[𝕜] V) : ‖conjCLM e A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

/-- Conjugation of operators is a contraction, hence continuous. -/
theorem lipschitzWith_one_conjCLM : LipschitzWith 1 (conjCLM e) :=
  LipschitzWith.of_dist_le_mul fun A B ↦ by
    simpa [dist_eq_norm, ← conjCLM_sub] using norm_conjCLM_le e (A - B)

end ConjugateOperator

namespace ContRepresentation

variable {𝕜 ι G V : Type*} [RCLike 𝕜] [Fintype ι] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (e : OrthonormalBasis ι 𝕜 V)

/-- **The conjugate of a continuous representation** with respect to an orthonormal basis: the
action operators are conjugated entrywise in that basis. -/
noncomputable def conjugate (π : ContRepresentation 𝕜 G V) : ContRepresentation 𝕜 G V :=
  .ofMonoidHom
    { toFun g := conjCLM e (π g)
      map_one' := by simp
      map_mul' g h := by rw [map_mul, conjCLM_mul] }

variable (π : ContRepresentation 𝕜 G V)

omit [TopologicalSpace G] in
/-- The action operators of the conjugate representation. -/
@[simp]
theorem conjugate_apply (g : G) : conjugate e π g = conjCLM e (π g) :=
  (rfl)

/-- The conjugate of a continuous representation has a continuous operator-valued action. -/
theorem continuous_conjugate (hπ : Continuous π) : Continuous (conjugate e π) :=
  (lipschitzWith_one_conjCLM e).continuous.comp hπ

omit [TopologicalSpace G] in
/-- The conjugate of a unitary representation is unitary. -/
theorem IsUnitary.conjugate {π : ContRepresentation 𝕜 G V} (hπ : IsUnitary π) :
    IsUnitary (ContRepresentation.conjugate e π) :=
  (isUnitary_iff_norm_map _).mpr fun g x ↦ by simp [hπ.norm_map]

/-- **The conjugate of a matrix coefficient is a matrix coefficient of the conjugate
representation**, at the conjugated vectors. This is the identity that makes the span of all matrix
coefficients stable under the involution of `C(G, 𝕜)`. -/
theorem star_matrixCoeff_eq_matrixCoeff_conjugate (hπ : Continuous π) (v w : V) :
    star (matrixCoeff π hπ v w) =
      matrixCoeff (conjugate e π) (continuous_conjugate e π hπ)
        (conjugation e v) (conjugation e w) := by
  ext g
  simp [inner_conjugation_conjugation, RCLike.star_def]

end ContRepresentation

end TauCeti
