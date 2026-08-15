/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Pointwise and integrated energy for curves into almost complex manifolds

This file lifts the energy theory of $J$-holomorphic curves from normed vector spaces
(`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic` and `Integral.lean`) to smooth manifolds.
Given a manifold $M$ carrying a smooth two-form $\omega$ (`TauCeti.SmoothTwoForm`) and a smooth
almost complex structure $J$ (`TauCeti.SmoothAlmostComplexStructure`), we define:

1. **Pointwise energy density.** For a real-linear map $F : \mathbb{R}^2 \to T_x M$ from the
   standard complex line into a tangent space, its metric energy density is
   $$e(F) = \omega_x(F(\partial_s), J_x(F(\partial_s))) +
     \omega_x(F(\partial_t), J_x(F(\partial_t))).$$
   When $\omega$ is fiberwise nondegenerate, this agrees with
   `TauCeti.SymplecticForm.stdComplexLineEnergyDensity` on the tangent space $T_x M$.

2. **The energy--area identity.** When $F$ is complex-linear (or when $u : \mathbb{R}^2 \to M$ is
   pseudoholomorphic at $z$), the energy density equals twice the symplectic area density:
   $$e(du_z) = 2 \omega_{u(z)}(du_z(\partial_s), du_z(\partial_t)).$$

3. **The Wirtinger identity and inequality on manifolds.** For an invariant pair,
   $$e(F) - 2 \omega_x(F(\partial_s), F(\partial_t)) =
     \omega_x(F(\partial_s) + J_x(F(\partial_t)), J_x(F(\partial_s) + J_x(F(\partial_t)))),$$
   which under tameness/compatibility yields the pointwise bound
   $2 \omega_x(F(\partial_s), F(\partial_t)) \le e(F)$, with equality if and only if $F$ satisfies
   the Cauchy--Riemann equation $F(\partial_t) = J_x(F(\partial_s))$.

4. **Integrated energy.** For a curve $u : \mathbb{R}^2 \to M$, a field of candidate
   differentials $du_z$, and a measure $\mu$, its energy is the lower integral of the positive part
   $$E(u,du) = \int^\ast \operatorname{ofReal}\!\left(\frac{1}{2} e(du_z)\right) \, d\mu(z).$$
   For an almost-everywhere complex-linear differential, this equals the lower integral of the
   positive part of the symplectic area density
   $\operatorname{ofReal}(\omega_{u(z)}(du_z(\partial_s),du_z(\partial_t)))$. Under tameness,
   nothing is truncated on the energy side, and zero energy detects an almost-everywhere vanishing
   differential, assuming the energy integrand is almost everywhere measurable. The area density
   of an arbitrary differential can still be negative even for a compatible pair. The differential
   is kept explicit because Mathlib defines `mfderiv` to be zero where differentiability fails;
   consumers using `mfderiv` must assume differentiability separately when that convention matters.

These are the first manifold-level energy statements needed before the local theory of
$J$-holomorphic curves.

## Main declarations

* `TauCeti.SmoothTwoForm.stdComplexLineEnergyDensity`: the pointwise metric energy density of a
  real-linear map into a tangent fiber.
* `TauCeti.SmoothTwoForm.IsNondegenerate.stdComplexLineEnergyDensity_eq`: identification with the
  linear symplectic energy density when the two-form is fiberwise nondegenerate.
* `TauCeti.SmoothTwoForm.Tames.stdComplexLineEnergyDensity_nonneg`,
  `TauCeti.SmoothTwoForm.Tames.stdComplexLineEnergyDensity_pos`,
  `TauCeti.SmoothTwoForm.Tames.stdComplexLineEnergyDensity_eq_zero_iff`: nonnegativity, positivity,
  and exact nondegeneracy of the density under tameness.
* `TauCeti.IsComplexLinearMap.stdComplexLineEnergyDensity_eq_two_mul_twoForm`: for a complex-linear
  map into a tangent fiber, energy density is twice the symplectic area density.
* `TauCeti.IsPseudoholomorphicAt.mfderiv_stdComplexLineEnergyDensity_eq_two_mul_twoForm`:
  energy--area identity for the manifold derivative of a pseudoholomorphic curve.
* `IsPseudoholomorphicWithinAt.mfderivWithin_stdComplexLineEnergyDensity_eq_two_mul_twoForm`:
  energy--area identity for the within-set derivative of a pseudoholomorphic curve.
* `TauCeti.SmoothTwoForm.Invariant.stdComplexLineEnergyDensity_sub_two_mul_twoForm`: the Wirtinger
  identity on manifolds.
* `TauCeti.SmoothTwoForm.Compatible.two_mul_twoForm_le_stdComplexLineEnergyDensity`: the Wirtinger
  inequality on manifolds, and
  `TauCeti.SmoothTwoForm.Compatible.stdComplexLineEnergyDensity_eq_two_mul_twoForm_iff`:
  characterization of equality in the Wirtinger inequality.
* `TauCeti.SmoothTwoForm.stdComplexLineEnergy`: the integrated energy of a field of differentials
  along a curve $u : \mathbb{R}^2 \to M$.
* `TauCeti.SmoothTwoForm.Compatible.lintegral_twoForm_le_stdComplexLineEnergy`: the integrated
  Wirtinger inequality.
* `TauCeti.SmoothTwoForm.stdComplexLineEnergy_eq_lintegral_twoForm`: equality of integrated energy
  and symplectic area for an almost-everywhere complex-linear differential.
* `TauCeti.SmoothTwoForm.mfderiv_stdComplexLineEnergy_eq_lintegral_twoForm`: the specialization to
  an almost-everywhere pseudoholomorphic curve.
* `TauCeti.SmoothTwoForm.stdComplexLineEnergy_eq_zero_of_ae_eq_zero`: zero energy for an almost
  everywhere vanishing differential.
* `TauCeti.SmoothTwoForm.Tames.stdComplexLineEnergy_eq_zero_iff`: under tameness, zero energy
  characterizes an almost everywhere vanishing differential.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 2.1.
-/

public section

open MeasureTheory
open scoped ENNReal Manifold ContDiff

noncomputable section

namespace TauCeti

variable {E H M : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothTwoForm

variable {form : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M} {x : M}

/-- The pointwise metric energy density of a real-linear map from the standard complex line into
the tangent space at `x`.

For a compatible pair `(form, J)`, this is `g(F ∂s, F ∂s) + g(F ∂t, F ∂t)`, where
`g(v, w) = form x v (J x w)`. -/
def stdComplexLineEnergyDensity (form : SmoothTwoForm I M) (J : SmoothAlmostComplexStructure I M)
    (x : M) (F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I x) : ℝ :=
  form x (F stdComplexLineReal) (J x (F stdComplexLineReal)) +
    form x (F stdComplexLineImag) (J x (F stdComplexLineImag))

/-- Unfolding the definition of standard complex-line energy density on a manifold. -/
lemma stdComplexLineEnergyDensity_def (form : SmoothTwoForm I M)
    (J : SmoothAlmostComplexStructure I M) (x : M) (F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I x) :
    form.stdComplexLineEnergyDensity J x F =
      form x (F stdComplexLineReal) (J x (F stdComplexLineReal)) +
        form x (F stdComplexLineImag) (J x (F stdComplexLineImag)) :=
  (rfl)

attribute [irreducible] stdComplexLineEnergyDensity

/-- The zero real-linear map into a tangent fiber has zero standard complex-line energy density. -/
@[simp]
lemma stdComplexLineEnergyDensity_zero (form : SmoothTwoForm I M)
    (J : SmoothAlmostComplexStructure I M) (x : M) :
    form.stdComplexLineEnergyDensity J x 0 = 0 := by
  simp [stdComplexLineEnergyDensity_def]

/-- When a smooth two-form is fiberwise nondegenerate, the manifold energy density is the linear
symplectic energy density on the tangent fiber. -/
lemma IsNondegenerate.stdComplexLineEnergyDensity_eq (h : form.IsNondegenerate)
    (J : SmoothAlmostComplexStructure I M) (x : M) (F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I x) :
    form.stdComplexLineEnergyDensity J x F =
      (h.symplecticFormAt x).stdComplexLineEnergyDensity (J.almostComplexStructureAt x) F := by
  rw [stdComplexLineEnergyDensity_def, SymplecticForm.stdComplexLineEnergyDensity_def]
  simp only [SymplecticForm.associatedBilinForm_apply,
    IsNondegenerate.symplecticFormAt_apply,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

/-- The standard pointwise energy density of any real-linear map into a tangent fiber is
nonnegative under tameness. -/
lemma Tames.stdComplexLineEnergyDensity_nonneg (htame : form.Tames J)
    (x : M) (F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I x) :
    0 ≤ form.stdComplexLineEnergyDensity J x F := by
  rw [htame.isNondegenerate.stdComplexLineEnergyDensity_eq J x F]
  exact SymplecticForm.stdComplexLineEnergyDensity_nonneg
    (htame.isNondegenerate.tames_iff.mp htame x) F

/-- Under tameness, the standard pointwise energy density of a nonzero real-linear map into a
tangent fiber is positive. -/
lemma Tames.stdComplexLineEnergyDensity_pos (htame : form.Tames J)
    (x : M) {F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I x} (hF : F ≠ 0) :
    0 < form.stdComplexLineEnergyDensity J x F := by
  rw [htame.isNondegenerate.stdComplexLineEnergyDensity_eq J x F]
  exact SymplecticForm.stdComplexLineEnergyDensity_pos
    (htame.isNondegenerate.tames_iff.mp htame x) hF

/-- Under tameness, standard pointwise energy density vanishes exactly for the zero real-linear
map into a tangent fiber. -/
@[simp]
lemma Tames.stdComplexLineEnergyDensity_eq_zero_iff (htame : form.Tames J)
    (x : M) {F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I x} :
    form.stdComplexLineEnergyDensity J x F = 0 ↔ F = 0 := by
  rw [htame.isNondegenerate.stdComplexLineEnergyDensity_eq J x F]
  exact SymplecticForm.stdComplexLineEnergyDensity_eq_zero_iff
    (htame.isNondegenerate.tames_iff.mp htame x)

/-- Under tameness, standard pointwise energy density is positive exactly for nonzero real-linear
maps into a tangent fiber. -/
lemma Tames.stdComplexLineEnergyDensity_pos_iff (htame : form.Tames J)
    (x : M) {F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I x} :
    0 < form.stdComplexLineEnergyDensity J x F ↔ F ≠ 0 := by
  rw [htame.isNondegenerate.stdComplexLineEnergyDensity_eq J x F]
  exact SymplecticForm.stdComplexLineEnergyDensity_pos_iff
    (htame.isNondegenerate.tames_iff.mp htame x)

/-- Under tameness, standard pointwise energy density of a continuous linear map into a tangent
fiber vanishes exactly when the continuous linear map is zero. -/
lemma Tames.stdComplexLineEnergyDensity_toLinearMap_eq_zero_iff (htame : form.Tames J)
    (x : M) (F : (ℝ × ℝ) →L[ℝ] TangentSpace I x) :
    form.stdComplexLineEnergyDensity J x F.toLinearMap = 0 ↔ F = 0 := by
  rw [htame.isNondegenerate.stdComplexLineEnergyDensity_eq J x F.toLinearMap]
  exact SymplecticForm.stdComplexLineEnergyDensity_toLinearMap_eq_zero_iff
    (htame.isNondegenerate.tames_iff.mp htame x) F

/-- Under tameness, the standard pointwise energy density of a continuous linear map into a
tangent fiber is positive exactly when the continuous linear map is nonzero. -/
lemma Tames.stdComplexLineEnergyDensity_toLinearMap_pos_iff (htame : form.Tames J)
    (x : M) (F : (ℝ × ℝ) →L[ℝ] TangentSpace I x) :
    0 < form.stdComplexLineEnergyDensity J x F.toLinearMap ↔ F ≠ 0 := by
  rw [htame.isNondegenerate.stdComplexLineEnergyDensity_eq J x F.toLinearMap]
  exact SymplecticForm.stdComplexLineEnergyDensity_toLinearMap_pos_iff
    (htame.isNondegenerate.tames_iff.mp htame x) F

end SmoothTwoForm

namespace IsComplexLinearMap

variable {form : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M} {x : M}
variable {F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I x}

/-- For a complex-linear map out of the standard complex line into a tangent fiber, the pointwise
energy density is twice the symplectic area density. -/
lemma stdComplexLineEnergyDensity_eq_two_mul_twoForm
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J.almostComplexStructureAt x) F) :
    form.stdComplexLineEnergyDensity J x F =
      2 * form x (F stdComplexLineReal) (F stdComplexLineImag) := by
  rw [SmoothTwoForm.stdComplexLineEnergyDensity_def]
  have himag : F stdComplexLineImag = J x (F stdComplexLineReal) := by
    have h := hF.apply_stdComplexLineImag
    simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using h
  have hreal : J x (F stdComplexLineImag) = - (F stdComplexLineReal) := by
    rw [himag, J.apply_apply]
  rw [← himag, hreal]
  have hneg_right := form.apply_neg_right x (F stdComplexLineImag) (F stdComplexLineReal)
  have halt := congrArg Neg.neg (form.apply_swap x
    (F stdComplexLineImag) (F stdComplexLineReal))
  rw [hneg_right, halt]
  ring

end IsComplexLinearMap

namespace IsPseudoholomorphicAt

variable {form : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
variable {u : ℝ × ℝ → M} {z : ℝ × ℝ}

/-- For a pseudoholomorphic curve from the standard complex line into an almost complex manifold,
the manifold derivative's energy density is twice its symplectic area density. -/
lemma mfderiv_stdComplexLineEnergyDensity_eq_two_mul_twoForm
    (hu : IsPseudoholomorphicAt (SmoothAlmostComplexStructure.product ℝ) J u z) :
    form.stdComplexLineEnergyDensity J (u z)
        (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I u z).toLinearMap =
      2 * form (u z)
        (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I u z stdComplexLineReal)
        (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I u z stdComplexLineImag) := by
  have hz : (SmoothAlmostComplexStructure.product ℝ).almostComplexStructureAt z =
      AlmostComplexStructure.product ℝ :=
    SmoothAlmostComplexStructure.product_almostComplexStructureAt z
  have hlin : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J.almostComplexStructureAt (u z))
      (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I u z).toLinearMap := by
    have h := hu.mfderiv_isComplexLinear
    rwa [hz] at h
  exact hlin.stdComplexLineEnergyDensity_eq_two_mul_twoForm

end IsPseudoholomorphicAt

namespace IsPseudoholomorphicWithinAt

variable {form : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
variable {u : ℝ × ℝ → M} {s : Set (ℝ × ℝ)} {z : ℝ × ℝ}

/-- For a within-set pseudoholomorphic curve from the standard complex line into an almost complex
manifold, the within-set manifold derivative's energy density is twice its symplectic area density,
provided derivatives within the set are unique. -/
lemma mfderivWithin_stdComplexLineEnergyDensity_eq_two_mul_twoForm
    (hu : IsPseudoholomorphicWithinAt (SmoothAlmostComplexStructure.product ℝ) J u s z)
    (hs : UniqueMDiffWithinAt (modelWithCornersSelf ℝ (ℝ × ℝ)) s z) :
    form.stdComplexLineEnergyDensity J (u z)
        (mfderivWithin (modelWithCornersSelf ℝ (ℝ × ℝ)) I u s z).toLinearMap =
      2 * form (u z)
        (mfderivWithin (modelWithCornersSelf ℝ (ℝ × ℝ)) I u s z stdComplexLineReal)
        (mfderivWithin (modelWithCornersSelf ℝ (ℝ × ℝ)) I u s z stdComplexLineImag) := by
  have hz : (SmoothAlmostComplexStructure.product ℝ).almostComplexStructureAt z =
      AlmostComplexStructure.product ℝ :=
    SmoothAlmostComplexStructure.product_almostComplexStructureAt z
  have hlin : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J.almostComplexStructureAt (u z))
      (mfderivWithin (modelWithCornersSelf ℝ (ℝ × ℝ)) I u s z).toLinearMap := by
    have h := hu.mfderivWithin_isComplexLinear hs
    rwa [hz] at h
  exact hlin.stdComplexLineEnergyDensity_eq_two_mul_twoForm

end IsPseudoholomorphicWithinAt

namespace SmoothTwoForm

variable {form : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M} {x : M}

/-- **Wirtinger identity on manifolds.** For an invariant pair `(form, J)`, the standard energy
density minus twice the symplectic area density is the Cauchy--Riemann defect square:
$$e(F) - 2 \omega_x(F \partial_s, F \partial_t) =
  \omega_x(F \partial_s + J_x F \partial_t, J_x(F \partial_s + J_x F \partial_t)).$$ -/
lemma Invariant.stdComplexLineEnergyDensity_sub_two_mul_twoForm (hinv : form.Invariant J)
    (x : M) (F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I x) :
    form.stdComplexLineEnergyDensity J x F -
        2 * form x (F stdComplexLineReal) (F stdComplexLineImag) =
      form x (F stdComplexLineReal + J x (F stdComplexLineImag))
        (J x (F stdComplexLineReal + J x (F stdComplexLineImag))) := by
  rw [stdComplexLineEnergyDensity_def]
  have hJlin : J x (F stdComplexLineReal + J x (F stdComplexLineImag)) =
      J x (F stdComplexLineReal) - F stdComplexLineImag := by
    have h1 := (J.toEndomorphism x).map_add (F stdComplexLineReal) (J x (F stdComplexLineImag))
    have h2 := J.apply_apply x (F stdComplexLineImag)
    have h3 : J x (F stdComplexLineReal + J x (F stdComplexLineImag)) =
        J x (F stdComplexLineReal) + J x (J x (F stdComplexLineImag)) := h1
    rw [h3, h2, sub_eq_add_neg]
  rw [hJlin]
  let v := F stdComplexLineReal
  let w := F stdComplexLineImag
  have h_right : form x (v + J x w) (J x v - w) =
      form x (v + J x w) (J x v) - form x (v + J x w) w :=
    form.apply_sub_right x (v + J x w) (J x v) w
  have h_left1 : form x (v + J x w) (J x v) = form x v (J x v) + form x (J x w) (J x v) :=
    form.apply_add_left x v (J x w) (J x v)
  have h_left2 : form x (v + J x w) w = form x v w + form x (J x w) w :=
    form.apply_add_left x v (J x w) w
  have hinv_step : form x (J x w) (J x v) = form x w v := hinv.apply x w v
  have halt1 := congrArg Neg.neg (form.apply_swap x w v)
  have halt2 := congrArg Neg.neg (form.apply_swap x (J x w) w)
  linarith

/-- **Wirtinger inequality on manifolds.** For a compatible pair `(form, J)`, twice the symplectic
area density of any real-linear map into a tangent fiber is at most its standard energy density. -/
lemma Compatible.two_mul_twoForm_le_stdComplexLineEnergyDensity (hcompat : form.Compatible J)
    (x : M) (F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I x) :
    2 * form x (F stdComplexLineReal) (F stdComplexLineImag) ≤
      form.stdComplexLineEnergyDensity J x F := by
  rw [hcompat.isNondegenerate.stdComplexLineEnergyDensity_eq J x F]
  have hlin := SymplecticForm.two_mul_symplecticForm_le_stdComplexLineEnergyDensity
    (hcompat.compatibleAt x) F
  simp only [IsNondegenerate.symplecticFormAt_apply] at hlin
  exact hlin

/-- The Wirtinger inequality is an equality exactly when the linear map is complex-linear with
respect to `AlmostComplexStructure.product ℝ` and `J.almostComplexStructureAt x`. -/
lemma Compatible.stdComplexLineEnergyDensity_eq_two_mul_twoForm_iff (hcompat : form.Compatible J)
    (x : M) (F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I x) :
    form.stdComplexLineEnergyDensity J x F =
        2 * form x (F stdComplexLineReal) (F stdComplexLineImag) ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J.almostComplexStructureAt x) F := by
  rw [hcompat.isNondegenerate.stdComplexLineEnergyDensity_eq J x F]
  have hlin_compat := hcompat.compatibleAt x
  have hlin_iff := SymplecticForm.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm_iff
    hlin_compat F
  simp only [IsNondegenerate.symplecticFormAt_apply] at hlin_iff
  exact hlin_iff

/-! ### Integrated energy on manifolds -/

/-- The integrated energy of a field of real-linear maps along a curve from the standard complex
line into a manifold: the lower Lebesgue integral of the positive part of half the pointwise
energy density.

Nothing here relates `form` and `J`. For a taming pair the density is nonnegative, so the positive
part loses nothing; for a general pair it can be negative, and `ENNReal.ofReal` truncates it. The
differential field is explicit rather than fixed to `mfderiv`, which Mathlib defines to be zero
where differentiability fails. -/
noncomputable def stdComplexLineEnergy (form : SmoothTwoForm I M)
    (J : SmoothAlmostComplexStructure I M) (u : (ℝ × ℝ) → M)
    (du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] TangentSpace I (u z)) (μ : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (form.stdComplexLineEnergyDensity J (u z) (du z) / 2) ∂μ

/-- Unfolding the definition of integrated energy. -/
lemma stdComplexLineEnergy_def (form : SmoothTwoForm I M)
    (J : SmoothAlmostComplexStructure I M) (u : (ℝ × ℝ) → M)
    (du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] TangentSpace I (u z)) (μ : Measure (ℝ × ℝ)) :
    form.stdComplexLineEnergy J u du μ =
      ∫⁻ z, ENNReal.ofReal (form.stdComplexLineEnergyDensity J (u z) (du z) / 2) ∂μ :=
  (rfl)

attribute [irreducible] stdComplexLineEnergy

/-- Energy depends only on the differential field almost everywhere. -/
lemma stdComplexLineEnergy_congr_ae {u : ℝ × ℝ → M}
    {du dv : ∀ z, (ℝ × ℝ) →ₗ[ℝ] TangentSpace I (u z)} {μ : Measure (ℝ × ℝ)}
    (h : ∀ᵐ z ∂μ, du z = dv z) :
    form.stdComplexLineEnergy J u du μ = form.stdComplexLineEnergy J u dv μ := by
  rw [stdComplexLineEnergy_def, stdComplexLineEnergy_def]
  exact lintegral_congr_ae <| h.mono fun z hz ↦ by
    change ENNReal.ofReal (form.stdComplexLineEnergyDensity J (u z) (du z) / 2) =
      ENNReal.ofReal (form.stdComplexLineEnergyDensity J (u z) (dv z) / 2)
    rw [hz]

/-- Enlarging the source measure cannot decrease the manifold energy. -/
lemma stdComplexLineEnergy_mono_measure {μ ν : Measure (ℝ × ℝ)} (hμν : μ ≤ ν)
    (form : SmoothTwoForm I M) (J : SmoothAlmostComplexStructure I M) (u : (ℝ × ℝ) → M)
    (du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] TangentSpace I (u z)) :
    form.stdComplexLineEnergy J u du μ ≤ form.stdComplexLineEnergy J u du ν := by
  rw [stdComplexLineEnergy_def, stdComplexLineEnergy_def]
  exact lintegral_mono' hμν le_rfl

/-- Every differential field has zero energy with respect to the zero measure. -/
@[simp]
lemma stdComplexLineEnergy_zero_measure (form : SmoothTwoForm I M)
    (J : SmoothAlmostComplexStructure I M) (u : (ℝ × ℝ) → M)
    (du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] TangentSpace I (u z)) :
    form.stdComplexLineEnergy J u du 0 = 0 := by
  simp [stdComplexLineEnergy_def]

/-- The zero differential field has zero energy. -/
@[simp]
lemma stdComplexLineEnergy_zero (form : SmoothTwoForm I M)
    (J : SmoothAlmostComplexStructure I M) (u : (ℝ × ℝ) → M) (μ : Measure (ℝ × ℝ)) :
    form.stdComplexLineEnergy J u (fun _ ↦ 0) μ = 0 := by
  simp [stdComplexLineEnergy_def]

/-- The energy of a constant differential along a constant curve is its normalized pointwise
density times the total mass of the source. -/
lemma stdComplexLineEnergy_const (form : SmoothTwoForm I M)
    (J : SmoothAlmostComplexStructure I M) (c : M)
    (F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I c) (μ : Measure (ℝ × ℝ)) :
    form.stdComplexLineEnergy J (fun _ ↦ c) (fun _ ↦ F) μ =
      ENNReal.ofReal (form.stdComplexLineEnergyDensity J c F / 2) * μ Set.univ := by
  rw [stdComplexLineEnergy_def, lintegral_const]

/-- **Integrated Wirtinger inequality on manifolds.** For a compatible pair `(form, J)`, the
integral of the positive part of the symplectic area density is bounded by the integrated energy. -/
lemma Compatible.lintegral_twoForm_le_stdComplexLineEnergy (hcompat : form.Compatible J)
    (u : ℝ × ℝ → M) (du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] TangentSpace I (u z))
    (μ : Measure (ℝ × ℝ)) :
    (∫⁻ z, ENNReal.ofReal
      (form (u z)
        (du z stdComplexLineReal) (du z stdComplexLineImag)) ∂μ) ≤
      form.stdComplexLineEnergy J u du μ := by
  rw [stdComplexLineEnergy_def]
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  have hpoint := hcompat.two_mul_twoForm_le_stdComplexLineEnergyDensity (u z) (du z)
  linarith

/-- **Equality in the integrated Wirtinger inequality on manifolds.** A differential field that is
complex linear almost everywhere has energy equal to the lower integral of the positive part of
its symplectic area density. For a taming pair the common density is nonnegative, so neither side
is truncated. -/
lemma stdComplexLineEnergy_eq_lintegral_twoForm
    {u : ℝ × ℝ → M} {du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] TangentSpace I (u z)}
    {μ : Measure (ℝ × ℝ)}
    (hdu : ∀ᵐ z ∂μ, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J.almostComplexStructureAt (u z)) (du z)) :
    form.stdComplexLineEnergy J u du μ =
      ∫⁻ z, ENNReal.ofReal
        (form (u z) (du z stdComplexLineReal) (du z stdComplexLineImag)) ∂μ := by
  rw [stdComplexLineEnergy_def]
  apply lintegral_congr_ae
  filter_upwards [hdu] with z hz
  rw [hz.stdComplexLineEnergyDensity_eq_two_mul_twoForm (form := form)]
  congr 1
  ring

/-- The energy of an almost-everywhere pseudoholomorphic curve, computed using `mfderiv`, equals
the lower integral of the positive part of its symplectic area density. -/
lemma mfderiv_stdComplexLineEnergy_eq_lintegral_twoForm
    {u : ℝ × ℝ → M} {μ : Measure (ℝ × ℝ)}
    (hu : ∀ᵐ z ∂μ, IsPseudoholomorphicAt (SmoothAlmostComplexStructure.product ℝ) J u z) :
    form.stdComplexLineEnergy J u
        (fun z ↦ (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I u z).toLinearMap) μ =
      ∫⁻ z, ENNReal.ofReal
        (form (u z)
          (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I u z stdComplexLineReal)
          (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I u z stdComplexLineImag)) ∂μ := by
  apply stdComplexLineEnergy_eq_lintegral_twoForm
  filter_upwards [hu] with z hz
  have hlin := hz.mfderiv_isComplexLinear
  rwa [SmoothAlmostComplexStructure.product_almostComplexStructureAt] at hlin

private lemma energyIntegrand_eq_zero_iff (htame : form.Tames J) (x : M)
    (F : (ℝ × ℝ) →ₗ[ℝ] TangentSpace I x) :
    ENNReal.ofReal (form.stdComplexLineEnergyDensity J x F / 2) = 0 ↔ F = 0 := by
  rw [ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have hzero : form.stdComplexLineEnergyDensity J x F = 0 := by
      have hpos := htame.stdComplexLineEnergyDensity_nonneg x F
      linarith
    exact (htame.stdComplexLineEnergyDensity_eq_zero_iff x).mp hzero
  · rintro rfl
    simp

/-- If a differential field vanishes almost everywhere, its energy is zero. -/
lemma stdComplexLineEnergy_eq_zero_of_ae_eq_zero (form : SmoothTwoForm I M)
    (J : SmoothAlmostComplexStructure I M) {u : ℝ × ℝ → M}
    {du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] TangentSpace I (u z)} {μ : Measure (ℝ × ℝ)}
    (hdu : ∀ᵐ z ∂μ, du z = 0) :
    form.stdComplexLineEnergy J u du μ = 0 :=
  (stdComplexLineEnergy_congr_ae hdu).trans (stdComplexLineEnergy_zero form J u μ)

/-- A constant curve has zero energy when its differential field is `mfderiv`. -/
lemma mfderiv_stdComplexLineEnergy_const (form : SmoothTwoForm I M)
    (J : SmoothAlmostComplexStructure I M) (c : M) (μ : Measure (ℝ × ℝ)) :
    form.stdComplexLineEnergy J (fun _ ↦ c)
      (fun z ↦ (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I
        (fun _ : ℝ × ℝ ↦ c) z).toLinearMap) μ = 0 := by
  apply stdComplexLineEnergy_eq_zero_of_ae_eq_zero form J
  filter_upwards [] with z
  simp only [mfderiv_const, ContinuousLinearMap.toLinearMap_zero]
  rfl

/-- Under tameness, integrated energy vanishes exactly when the differential field vanishes almost
everywhere, assuming the energy integrand is almost everywhere measurable.

For a field built from `mfderiv`, this detects `mfderiv = 0` almost everywhere, not genuine local
constancy: Mathlib assigns `mfderiv` the value zero wherever differentiability fails. -/
lemma Tames.stdComplexLineEnergy_eq_zero_iff (htame : form.Tames J)
    {u : ℝ × ℝ → M} {du : ∀ z, (ℝ × ℝ) →ₗ[ℝ] TangentSpace I (u z)}
    {μ : Measure (ℝ × ℝ)}
    (hmeas : AEMeasurable (fun z ↦ form.stdComplexLineEnergyDensity J (u z) (du z)) μ) :
    form.stdComplexLineEnergy J u du μ = 0 ↔ ∀ᵐ z ∂μ, du z = 0 := by
  rw [stdComplexLineEnergy_def,
    lintegral_eq_zero_iff' (AEMeasurable.ennreal_ofReal (hmeas.div_const 2))]
  constructor
  · intro h
    filter_upwards [h] with z hz
    exact (energyIntegrand_eq_zero_iff (form := form) (J := J) htame (u z) (du z)).mp hz
  · intro h
    filter_upwards [h] with z hz
    exact (energyIntegrand_eq_zero_iff (form := form) (J := J) htame (u z) (du z)).mpr hz

end SmoothTwoForm

end TauCeti

end
