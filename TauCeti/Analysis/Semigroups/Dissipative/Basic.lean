/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Identity

/-!
# Dissipative operators

This file introduces dissipativity for a (possibly unbounded) operator `A : X →ₗ.[ℝ] X` on a
real Banach space, in the *resolvent-range* form

`lambda * ‖x‖ ≤ ‖lambda • x - A x‖` for all `lambda > 0` and all `x ∈ D(A)`,

which is the notion available in a general Banach space (the Hilbert-space characterization
`⟪A x, x⟫ ≤ 0` is a specialization, proved in
`TauCeti/Analysis/Semigroups/Dissipative/Hilbert.lean`).

The elementary API records what the inequality buys: an a priori estimate `‖x‖ ≤ ‖y‖ / lambda`
for solutions of `lambda x - A x = y`, injectivity of `lambda • I - A` on `D(A)`, and stability
under restriction and under nonnegative scalar multiples. Adding the range condition —
`lambda • I - A` onto `X` for *some* `lambda > 0` — gives **m-dissipativity**
(`IsMDissipative`). On a Banach space that single point is enough: inverting `lambda • I - A`
and expanding a Neumann series propagates the range condition from `lambda` to every
`mu ∈ (0, 2 lambda)`, and iterating that step along the geometric sequence `(3/2)^n lambda`
covers all of `(0, ∞)`, so `mu • I - A : D(A) → X` is bijective for every `mu > 0`.

The file then connects dissipativity to C₀-semigroups. For a semigroup with growth bound
`(ω, M)` and `lambda > ω`, the Laplace-transform resolvent turns the bound `‖R(lambda)‖ ≤
M / (lambda - ω)` into the *resolvent-range inequality*

`‖x‖ ≤ M / (lambda - ω) * ‖lambda • x - A x‖` for `x ∈ D(A)`,

so that `lambda • I - A : D(A) → X` is bijective for every `lambda > ω` — that is,
`(ω, ∞)` lies in the resolvent set of the generator. Specializing to `(ω, M) = (0, 1)` gives the
**converse of the Lumer--Phillips theorem**: the generator of a contraction semigroup is
dissipative.

## Main results

* `TauCeti.Semigroups.IsDissipative`, `TauCeti.Semigroups.IsMDissipative`: the dissipativity
  and m-dissipativity predicates.
* `TauCeti.Semigroups.IsDissipative.smul_sub_surjective_of_lt_two_mul` and
  `TauCeti.Semigroups.IsMDissipative.smul_sub_surjective`: on a Banach space the range
  condition at one positive `lambda` propagates to every positive `lambda`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.norm_le_norm_smul_sub_generator`: the
  resolvent-range inequality at a general growth bound `(ω, M)`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.smul_sub_generator_bijective`:
  `lambda • I - A` is bijective from `D(A)` onto `X` for `lambda > ω`.
* `TauCeti.Semigroups.ContractionSemigroup.isDissipative_generator` and
  `TauCeti.Semigroups.ContractionSemigroup.isMDissipative_generator`: the generator of a
  contraction semigroup is dissipative, indeed m-dissipative.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.3.b
(dissipativity and the Lumer--Phillips theorem); Pazy, *Semigroups of Linear Operators and
Applications to Partial Differential Equations*, Chapter 1, Theorem 4.3.
-/

public section

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Dissipativity -/

/-- An unbounded operator `A : X →ₗ.[ℝ] X` is **dissipative** when
`lambda * ‖x‖ ≤ ‖lambda • x - A x‖` for every `lambda > 0` and every `x` in its domain.

This is the Banach-space form of the condition: it says exactly that `lambda • I - A` is
injective on `D(A)` with `‖(lambda • I - A)⁻¹‖ ≤ 1 / lambda` on its range, for every
`lambda > 0`. In a Hilbert space it is equivalent to `⟪A x, x⟫ ≤ 0`. -/
@[expose] def IsDissipative (A : X →ₗ.[ℝ] X) : Prop :=
  ∀ lambda : ℝ, 0 < lambda → ∀ x : A.domain, lambda * ‖(x : X)‖ ≤ ‖lambda • (x : X) - A x‖

/-- `IsDissipative A` unfolds to its defining inequality: `lambda * ‖x‖ ≤ ‖lambda • x - A x‖`
for every `lambda > 0` and every `x ∈ D(A)`. -/
theorem isDissipative_iff {A : X →ₗ.[ℝ] X} :
    IsDissipative A ↔
      ∀ lambda : ℝ, 0 < lambda → ∀ x : A.domain,
        lambda * ‖(x : X)‖ ≤ ‖lambda • (x : X) - A x‖ :=
  Iff.rfl

/-- The a priori estimate carried by dissipativity: a solution of `lambda x - A x = y` obeys
`‖x‖ ≤ ‖y‖ / lambda`. -/
theorem IsDissipative.norm_le_of_smul_sub_eq {A : X →ₗ.[ℝ] X} (hA : IsDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda) {x : A.domain} {y : X}
    (h : lambda • (x : X) - A x = y) : ‖(x : X)‖ ≤ ‖y‖ / lambda := by
  rw [le_div_iff₀ hlambda]
  have := hA lambda hlambda x
  rw [h] at this
  linarith

/-- A dissipative operator has `lambda • I - A` injective on its domain, for every
`lambda > 0`. -/
theorem IsDissipative.smul_sub_injective {A : X →ₗ.[ℝ] X} (hA : IsDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Injective fun x : A.domain => lambda • (x : X) - A x := by
  intro x y hxy
  replace hxy : lambda • (x : X) - A x = lambda • (y : X) - A y := hxy
  have hzero : lambda • ((x - y : A.domain) : X) - A (x - y) = 0 := by
    rw [Submodule.coe_sub, A.map_sub, smul_sub, sub_sub_sub_comm, hxy, sub_self]
  have h := hA lambda hlambda (x - y)
  rw [hzero, norm_zero, ← mul_zero lambda] at h
  have hnorm : ‖((x - y : A.domain) : X)‖ ≤ 0 := le_of_mul_le_mul_left h hlambda
  rw [Submodule.coe_sub] at hnorm
  exact Subtype.ext (sub_eq_zero.mp (norm_le_zero_iff.mp hnorm))

/-- Dissipativity passes to restrictions: if `A ≤ B` as unbounded operators and `B` is
dissipative, then so is `A`. -/
theorem IsDissipative.of_le {A B : X →ₗ.[ℝ] X} (hB : IsDissipative B) (hAB : A ≤ B) :
    IsDissipative A := by
  intro lambda hlambda x
  obtain ⟨y, hy, hAy⟩ := LinearPMap.exists_of_le hAB x
  rw [hAy, hy]
  exact hB lambda hlambda y

/-- The zero operator, defined on all of `X`, is dissipative. -/
theorem isDissipative_zero : IsDissipative (0 : X →ₗ.[ℝ] X) := by
  intro lambda hlambda x
  rw [LinearPMap.zero_apply, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]

/-- A nonnegative scalar multiple of a dissipative operator is dissipative. -/
theorem IsDissipative.smul {A : X →ₗ.[ℝ] X} (hA : IsDissipative A) {c : ℝ} (hc : 0 ≤ c) :
    IsDissipative (c • A) := by
  intro lambda hlambda x
  rw [LinearPMap.smul_apply]
  rcases hc.eq_or_lt with rfl | hcpos
  · rw [zero_smul, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
  · have hkey : lambda • (x : X) - c • A x = c • ((lambda / c) • (x : X) - A x) := by
      rw [smul_sub, smul_smul, mul_div_cancel₀ _ hcpos.ne']
    rw [hkey, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    have h := hA (lambda / c) (div_pos hlambda hcpos) x
    calc lambda * ‖(x : X)‖ = c * (lambda / c * ‖(x : X)‖) := by
          field_simp
      _ ≤ c * ‖(lambda / c) • (x : X) - A x‖ := by gcongr

/-! ## The canonical inverse of `lambda • I - A`

Two developments need the same object: the Neumann-series argument below, which inverts
`lambda • I - A` at a single point of the range condition, and the resolvent of an m-dissipative
operator, which inverts it at every `lambda > 0`. Both want `lambda • I - A` packaged as a linear
map out of `D(A)`, inverted where it is bijective, and read back into `X` as a bounded operator of
norm at most `1 / lambda`. It is constructed once here and consumed by both; the norm bound is
dissipativity (`IsDissipative.norm_le_of_smul_sub_eq`), not the open mapping theorem, so
completeness of `X` is not needed. -/

/-- `lambda • I - A`, as a linear map out of `D(A)`. -/
private def smulSubLinear (A : X →ₗ.[ℝ] X) (lambda : ℝ) : A.domain →ₗ[ℝ] X :=
  lambda • A.domain.subtype - A.toFun

@[simp]
private theorem smulSubLinear_apply (A : X →ₗ.[ℝ] X) (lambda : ℝ) (x : A.domain) :
    smulSubLinear A lambda x = lambda • (x : X) - A x := by
  simp [smulSubLinear]

private theorem coe_smulSubLinear (A : X →ₗ.[ℝ] X) (lambda : ℝ) :
    ⇑(smulSubLinear A lambda) = fun x : A.domain => lambda • (x : X) - A x :=
  funext (smulSubLinear_apply A lambda)

/-- `lambda • I - A` as a linear equivalence `D(A) ≃ₗ[ℝ] X`, at a `lambda` where it is
bijective. -/
private noncomputable def smulSubEquiv (A : X →ₗ.[ℝ] X) {lambda : ℝ}
    (hbij : Function.Bijective fun x : A.domain => lambda • (x : X) - A x) :
    A.domain ≃ₗ[ℝ] X :=
  LinearEquiv.ofBijective (smulSubLinear A lambda) (by rwa [coe_smulSubLinear])

@[simp]
private theorem smulSubEquiv_apply (A : X →ₗ.[ℝ] X) {lambda : ℝ}
    (hbij : Function.Bijective fun x : A.domain => lambda • (x : X) - A x) (x : A.domain) :
    smulSubEquiv A hbij x = lambda • (x : X) - A x :=
  smulSubLinear_apply A lambda x

/-- The inverse of `lambda • I - A` solves `lambda x - A x = y`. -/
private theorem smul_sub_symm_smulSubEquiv (A : X →ₗ.[ℝ] X) {lambda : ℝ}
    (hbij : Function.Bijective fun x : A.domain => lambda • (x : X) - A x) (y : X) :
    lambda • (((smulSubEquiv A hbij).symm y : A.domain) : X)
        - A ((smulSubEquiv A hbij).symm y) = y := by
  rw [← smulSubEquiv_apply A hbij]
  exact (smulSubEquiv A hbij).apply_symm_apply y

/-- The a priori estimate, read on the inverse: `‖(lambda • I - A)⁻¹ y‖ ≤ ‖y‖ / lambda`. -/
private theorem IsDissipative.norm_symm_smulSubEquiv_le {A : X →ₗ.[ℝ] X} (hA : IsDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hbij : Function.Bijective fun x : A.domain => lambda • (x : X) - A x) (y : X) :
    ‖(((smulSubEquiv A hbij).symm y : A.domain) : X)‖ ≤ lambda⁻¹ * ‖y‖ := by
  have h := hA.norm_le_of_smul_sub_eq hlambda (x := (smulSubEquiv A hbij).symm y) (y := y)
    (smul_sub_symm_smulSubEquiv A hbij y)
  rwa [← div_eq_inv_mul]

/-- **The bounded inverse of `lambda • I - A`**, at a `lambda > 0` where it is bijective: a
continuous linear operator on all of `X`, of norm at most `1 / lambda`. -/
private noncomputable def IsDissipative.resolventOfBijective {A : X →ₗ.[ℝ] X} (hA : IsDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hbij : Function.Bijective fun x : A.domain => lambda • (x : X) - A x) : X →L[ℝ] X :=
  (A.domain.subtype ∘ₗ ((smulSubEquiv A hbij).symm : X →ₗ[ℝ] A.domain)).mkContinuous lambda⁻¹
    fun y => by simpa using hA.norm_symm_smulSubEquiv_le hlambda hbij y

private theorem IsDissipative.resolventOfBijective_apply {A : X →ₗ.[ℝ] X} (hA : IsDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hbij : Function.Bijective fun x : A.domain => lambda • (x : X) - A x) (y : X) :
    hA.resolventOfBijective hlambda hbij y = (((smulSubEquiv A hbij).symm y : A.domain) : X) :=
  LinearMap.mkContinuous_apply _ _ _ _

/-- The bounded inverse lands in `D(A)`. -/
private theorem IsDissipative.resolventOfBijective_mem_domain {A : X →ₗ.[ℝ] X}
    (hA : IsDissipative A) {lambda : ℝ} (hlambda : 0 < lambda)
    (hbij : Function.Bijective fun x : A.domain => lambda • (x : X) - A x) (y : X) :
    hA.resolventOfBijective hlambda hbij y ∈ A.domain := by
  rw [hA.resolventOfBijective_apply hlambda hbij]
  exact ((smulSubEquiv A hbij).symm y).property

/-- The bounded inverse is a right inverse of `lambda • I - A`. -/
private theorem IsDissipative.resolventOfBijectiveRightInv {A : X →ₗ.[ℝ] X} (hA : IsDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hbij : Function.Bijective fun x : A.domain => lambda • (x : X) - A x) (y : X) :
    lambda • hA.resolventOfBijective hlambda hbij y
        - A ⟨hA.resolventOfBijective hlambda hbij y,
          hA.resolventOfBijective_mem_domain hlambda hbij y⟩ = y := by
  have hcoe : (⟨hA.resolventOfBijective hlambda hbij y,
      hA.resolventOfBijective_mem_domain hlambda hbij y⟩ : A.domain)
      = (smulSubEquiv A hbij).symm y :=
    Subtype.ext (hA.resolventOfBijective_apply hlambda hbij y)
  rw [hcoe, hA.resolventOfBijective_apply hlambda hbij]
  exact smul_sub_symm_smulSubEquiv A hbij y

/-- The bounded inverse is a left inverse of `lambda • I - A`. -/
private theorem IsDissipative.resolventOfBijectiveLeftInv {A : X →ₗ.[ℝ] X} (hA : IsDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hbij : Function.Bijective fun x : A.domain => lambda • (x : X) - A x) (x : A.domain) :
    hA.resolventOfBijective hlambda hbij (lambda • (x : X) - A x) = (x : X) := by
  rw [hA.resolventOfBijective_apply hlambda hbij, ← smulSubEquiv_apply A hbij,
    (smulSubEquiv A hbij).symm_apply_apply]

/-- The bound `‖(lambda • I - A)⁻¹‖ ≤ 1 / lambda`. -/
private theorem IsDissipative.norm_resolventOfBijective_le {A : X →ₗ.[ℝ] X} (hA : IsDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hbij : Function.Bijective fun x : A.domain => lambda • (x : X) - A x) :
    ‖hA.resolventOfBijective hlambda hbij‖ ≤ lambda⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-! ## Maximal dissipativity -/

/-- An unbounded operator is **m-dissipative** (maximally dissipative) when it is dissipative
and `lambda • I - A` maps `D(A)` onto `X` for *some* `lambda > 0`.

The range condition is what upgrades the one-sided estimate of `IsDissipative` to a genuine
resolvent, and one positive `lambda` already suffices: over a Banach space it propagates to
every `lambda > 0` (`IsMDissipative.smul_sub_surjective`), so that `lambda • I - A : D(A) → X`
is bijective there (`IsMDissipative.smul_sub_bijective`), with inverse bounded by `1 / lambda`
through `IsDissipative.norm_le_of_smul_sub_eq`. Asking for a single `lambda` is the form the
hypothesis takes in the Lumer--Phillips generation theorem — that a densely defined
m-dissipative operator *is* the generator of a contraction semigroup — which is not yet
available in this library; its converse half is `ContractionSemigroup.isMDissipative_generator`
below. -/
@[expose] def IsMDissipative (A : X →ₗ.[ℝ] X) : Prop :=
  IsDissipative A ∧
    ∃ lambda : ℝ, 0 < lambda ∧ Function.Surjective fun x : A.domain => lambda • (x : X) - A x

/-- `IsMDissipative A` unfolds to its defining conjunction: `A` is dissipative and
`lambda • I - A` maps `D(A)` onto `X` for some `lambda > 0`. -/
theorem isMDissipative_iff {A : X →ₗ.[ℝ] X} :
    IsMDissipative A ↔
      IsDissipative A ∧
        ∃ lambda : ℝ, 0 < lambda ∧
          Function.Surjective fun x : A.domain => lambda • (x : X) - A x :=
  Iff.rfl

/-- A dissipative operator whose `lambda • I - A` maps `D(A)` onto `X` for a single `lambda > 0`
is m-dissipative. -/
theorem IsDissipative.isMDissipative {A : X →ₗ.[ℝ] X} (hA : IsDissipative A) {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrange : Function.Surjective fun x : A.domain => lambda • (x : X) - A x) :
    IsMDissipative A :=
  ⟨hA, lambda, hlambda, hrange⟩

/-- An m-dissipative operator is dissipative. -/
theorem IsMDissipative.isDissipative {A : X →ₗ.[ℝ] X} (hA : IsMDissipative A) :
    IsDissipative A :=
  hA.1

/-- The range condition of an m-dissipative operator: `lambda • I - A` maps `D(A)` onto `X` for
at least one `lambda > 0`. -/
theorem IsMDissipative.exists_smul_sub_surjective {A : X →ₗ.[ℝ] X} (hA : IsMDissipative A) :
    ∃ lambda : ℝ, 0 < lambda ∧
      Function.Surjective fun x : A.domain => lambda • (x : X) - A x :=
  hA.2

/-- **A bounded right inverse at a point of the range condition.** If `A` is dissipative and
`lambda • I - A` maps `D(A)` onto `X`, then it admits a right inverse `g` into `D(A)` which, read
as a map into `X`, is a bounded operator `J` of norm at most `1 / lambda`. Keeping `g` separate
from `J` is what lets `A` be applied to the result, since `A` only accepts elements of `D(A)`.

Dissipativity makes `g` a genuine two-sided inverse (`IsDissipative.smul_sub_injective`), but only
the right-inverse property is exposed, that being what the Neumann-series argument consumes.

This is the packaging the Neumann series wants; the inverse itself is
`IsDissipative.resolventOfBijective`. Completeness of `X` is not needed. -/
private theorem IsDissipative.exists_bounded_rightInverse {A : X →ₗ.[ℝ] X} (hA : IsDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hrange : Function.Surjective fun x : A.domain => lambda • (x : X) - A x) :
    ∃ (g : X → A.domain) (J : X →L[ℝ] X), ‖J‖ ≤ lambda⁻¹ ∧ (∀ y : X, (g y : X) = J y) ∧
      ∀ y : X, lambda • (g y : X) - A (g y) = y := by
  have hbij : Function.Bijective fun x : A.domain => lambda • (x : X) - A x :=
    ⟨hA.smul_sub_injective hlambda, hrange⟩
  exact ⟨fun y => (smulSubEquiv A hbij).symm y, hA.resolventOfBijective hlambda hbij,
    hA.norm_resolventOfBijective_le hlambda hbij,
    fun y => (hA.resolventOfBijective_apply hlambda hbij y).symm,
    smul_sub_symm_smulSubEquiv A hbij⟩

section CompleteSpace

variable [CompleteSpace X]

/-- **The range condition propagates along a Neumann series.** If `A` is dissipative and
`lambda • I - A` maps `D(A)` onto `X`, then so does `mu • I - A` for every `mu` in the interval
`(0, 2 lambda)`.

Dissipativity makes `lambda • I - A : D(A) → X` a bijection whose inverse `J` is bounded by
`1 / lambda`, and `mu • I - A = (I - (lambda - mu) • J) ∘ (lambda • I - A)`. The first factor is
invertible because `‖(lambda - mu) • J‖ ≤ |lambda - mu| / lambda < 1`, which is exactly the
constraint `0 < mu < 2 lambda`. -/
theorem IsDissipative.smul_sub_surjective_of_lt_two_mul {A : X →ₗ.[ℝ] X} (hA : IsDissipative A)
    {lambda mu : ℝ} (hlambda : 0 < lambda)
    (hrange : Function.Surjective fun x : A.domain => lambda • (x : X) - A x)
    (hmu : 0 < mu) (hmu' : mu < 2 * lambda) :
    Function.Surjective fun x : A.domain => mu • (x : X) - A x := by
  obtain ⟨g, Jc, hJcnorm, hgJ, he⟩ := hA.exists_bounded_rightInverse hlambda hrange
  -- `I - (lambda - mu) • Jc` is invertible, by the geometric series
  let T : X →L[ℝ] X := (lambda - mu) • Jc
  have hTapp : ∀ y : X, T y = (lambda - mu) • (g y : X) := by
    intro y; simp [T, hgJ]
  have hTnorm : ‖T‖ < 1 := by
    have h1 : ‖T‖ ≤ |lambda - mu| * lambda⁻¹ := by
      have h2 : ‖T‖ = |lambda - mu| * ‖Jc‖ := by simp [T, norm_smul, Real.norm_eq_abs]
      rw [h2]; gcongr
    have h3 : |lambda - mu| < lambda := by rw [abs_lt]; constructor <;> linarith
    calc ‖T‖ ≤ |lambda - mu| * lambda⁻¹ := h1
      _ < lambda * lambda⁻¹ := mul_lt_mul_of_pos_right h3 (by positivity)
      _ = 1 := mul_inv_cancel₀ hlambda.ne'
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hTnorm
  -- solve `y - T y = z` and push the solution through `(lambda • I - A)⁻¹`
  intro z
  obtain ⟨y, hyz⟩ : ∃ y : X, y - T y = z := by
    refine ⟨(↑u⁻¹ : X →L[ℝ] X) z, ?_⟩
    have h1 : ((u : X →L[ℝ] X) * (↑u⁻¹ : X →L[ℝ] X)) z = z := by rw [u.mul_inv]; rfl
    rw [hu] at h1
    simpa using h1
  refine ⟨g y, ?_⟩
  -- the surjectivity goal is the beta-redex `(fun x => mu • ↑x - A x) (g y) = z`, which
  -- `rw` cannot see through; `change` beta-reduces it (the style linter reserves `show` for
  -- goals that are already displayed in this form)
  change mu • (g y : X) - A (g y) = z
  have hsplit : mu • (g y : X) - A (g y)
      = (lambda • (g y : X) - A (g y)) - (lambda - mu) • (g y : X) := by module
  rw [hsplit, he y, ← hTapp y, hyz]

/-- The range condition of an m-dissipative operator holds at *every* positive `lambda`, not
just at the one its definition provides: propagate the given `lambda₀` through
`IsDissipative.smul_sub_surjective_of_lt_two_mul` along the geometric sequence
`(3/2)^n lambda₀`, which passes every positive real. -/
theorem IsMDissipative.smul_sub_surjective {A : X →ₗ.[ℝ] X} (hA : IsMDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Surjective fun x : A.domain => lambda • (x : X) - A x := by
  obtain ⟨lambda₀, hlambda₀, hrange⟩ := hA.exists_smul_sub_surjective
  have hstep : (0 : ℝ) < 3 / 2 := by norm_num
  have key : ∀ n : ℕ, Function.Surjective
      fun x : A.domain => ((3 / 2 : ℝ) ^ n * lambda₀) • (x : X) - A x := by
    intro n
    induction n with
    | zero => simpa using hrange
    | succ n ih =>
        have hpow : (0 : ℝ) < (3 / 2 : ℝ) ^ n := pow_pos hstep n
        refine hA.isDissipative.smul_sub_surjective_of_lt_two_mul (by positivity) ih
          (by positivity) ?_
        rw [pow_succ]
        nlinarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (lambda / (2 * lambda₀)) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ (by positivity)] at hn
  refine hA.isDissipative.smul_sub_surjective_of_lt_two_mul (by positivity) (key n) hlambda ?_
  linarith

/-- For an m-dissipative operator, `lambda • I - A` is a bijection from `D(A)` onto `X` for
every `lambda > 0`: injectivity comes from dissipativity, surjectivity from the propagated
range condition. -/
theorem IsMDissipative.smul_sub_bijective {A : X →ₗ.[ℝ] X} (hA : IsMDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Bijective fun x : A.domain => lambda • (x : X) - A x :=
  ⟨hA.isDissipative.smul_sub_injective hlambda, hA.smul_sub_surjective hlambda⟩

/-- **The resolvent of an m-dissipative operator.** `R(lambda) = (lambda • I - A)⁻¹`, a bounded
operator on all of `X` with `‖R(lambda)‖ ≤ 1 / lambda`, available at *every* `lambda > 0`.

No semigroup is presupposed: this is the resolvent the Hille--Yosida and Lumer--Phillips
generation theorems start from, as opposed to `ContractionSemigroup.resolvent`, which is the
Laplace transform of a semigroup already in hand. Completeness of `X` enters only through
`IsMDissipative.smul_sub_bijective`, which propagates the range condition from the single
`lambda` of the definition to all of them. -/
noncomputable def IsMDissipative.resolvent {A : X →ₗ.[ℝ] X} (hA : IsMDissipative A) (lambda : ℝ)
    (hlambda : 0 < lambda) : X →L[ℝ] X :=
  hA.isDissipative.resolventOfBijective hlambda (hA.smul_sub_bijective hlambda)

/-- The resolvent lands in the domain of `A`: `R(lambda) y ∈ D(A)`. -/
theorem IsMDissipative.resolvent_mem_domain {A : X →ₗ.[ℝ] X} (hA : IsMDissipative A) {lambda : ℝ}
    (hlambda : 0 < lambda) (y : X) : hA.resolvent lambda hlambda y ∈ A.domain :=
  hA.isDissipative.resolventOfBijective_mem_domain hlambda (hA.smul_sub_bijective hlambda) y

/-- **The resolvent is a right inverse of `lambda • I - A`.** -/
theorem IsMDissipative.resolventRightInv {A : X →ₗ.[ℝ] X} (hA : IsMDissipative A) {lambda : ℝ}
    (hlambda : 0 < lambda) (y : X) :
    lambda • hA.resolvent lambda hlambda y
        - A ⟨hA.resolvent lambda hlambda y, hA.resolvent_mem_domain hlambda y⟩ = y :=
  hA.isDissipative.resolventOfBijectiveRightInv hlambda (hA.smul_sub_bijective hlambda) y

/-- **The resolvent is a left inverse of `lambda • I - A`.** -/
theorem IsMDissipative.resolventLeftInv {A : X →ₗ.[ℝ] X} (hA : IsMDissipative A) {lambda : ℝ}
    (hlambda : 0 < lambda) (x : A.domain) :
    hA.resolvent lambda hlambda (lambda • (x : X) - A x) = (x : X) :=
  hA.isDissipative.resolventOfBijectiveLeftInv hlambda (hA.smul_sub_bijective hlambda) x

/-- The resolvent bound `‖R(lambda)‖ ≤ 1 / lambda`, the Hille--Yosida estimate at `M = 1`,
`ω = 0`. -/
theorem IsMDissipative.resolvent_norm_le {A : X →ₗ.[ℝ] X} (hA : IsMDissipative A) {lambda : ℝ}
    (hlambda : 0 < lambda) : ‖hA.resolvent lambda hlambda‖ ≤ 1 / lambda := by
  rw [one_div]
  exact hA.isDissipative.norm_resolventOfBijective_le hlambda (hA.smul_sub_bijective hlambda)

end CompleteSpace

/-! ## The generator of a C₀-semigroup -/

namespace StronglyContinuousSemigroup

variable [CompleteSpace X]

/-- **Resolvent-range inequality.** For a C₀-semigroup with growth bound `(ω, M)` and
`lambda > ω`, every `x ∈ D(A)` satisfies `‖x‖ ≤ M / (lambda - ω) * ‖lambda x - A x‖`.

This is the Hille--Yosida resolvent bound `‖R(lambda)‖ ≤ M / (lambda - ω)` read backwards
through the left-inverse identity `R(lambda) (lambda x - A x) = x`. -/
theorem norm_le_norm_smul_sub_generator (S : StronglyContinuousSemigroup X) {ω M : ℝ}
    (hb : S.HasGrowthBound ω M) {lambda : ℝ} (hlambda : ω < lambda) (x : S.generator.domain) :
    ‖(x : X)‖ ≤ M / (lambda - ω) * ‖lambda • (x : X) - S.generator x‖ := by
  have hx : (x : X) ∈ S.domain := by
    rw [← S.generator_domain]
    exact x.property
  have key : S.resolvent hb lambda hlambda (lambda • (x : X) - S.generator x) = (x : X) :=
    S.resolventLeftInv hb lambda hlambda ⟨(x : X), hx⟩
  calc ‖(x : X)‖ = ‖S.resolvent hb lambda hlambda (lambda • (x : X) - S.generator x)‖ := by
        rw [key]
    _ ≤ ‖S.resolvent hb lambda hlambda‖ * ‖lambda • (x : X) - S.generator x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ M / (lambda - ω) * ‖lambda • (x : X) - S.generator x‖ := by
        gcongr
        exact S.resolvent_norm_le hb lambda hlambda

/-- For `lambda` beyond the growth exponent, `lambda • I - A` is injective on `D(A)`: the
resolvent is a left inverse of it. -/
theorem smul_sub_generator_injective (S : StronglyContinuousSemigroup X) {ω M : ℝ}
    (hb : S.HasGrowthBound ω M) {lambda : ℝ} (hlambda : ω < lambda) :
    Function.Injective fun x : S.generator.domain => lambda • (x : X) - S.generator x := by
  have key : ∀ x : S.generator.domain,
      S.resolvent hb lambda hlambda (lambda • (x : X) - S.generator x) = (x : X) := by
    intro x
    exact S.resolventLeftInv hb lambda hlambda ⟨(x : X), by
      rw [← S.generator_domain]; exact x.property⟩
  intro x y hxy
  replace hxy : lambda • (x : X) - S.generator x = lambda • (y : X) - S.generator y := hxy
  exact Subtype.ext (by rw [← key x, ← key y, hxy])

/-- For `lambda` beyond the growth exponent, `lambda • I - A` maps `D(A)` onto `X`: the
resolvent supplies the preimage. -/
theorem smul_sub_generator_surjective (S : StronglyContinuousSemigroup X) {ω M : ℝ}
    (hb : S.HasGrowthBound ω M) {lambda : ℝ} (hlambda : ω < lambda) :
    Function.Surjective fun x : S.generator.domain => lambda • (x : X) - S.generator x := by
  intro y
  refine ⟨⟨S.resolvent hb lambda hlambda y, ?_⟩, ?_⟩
  · rw [S.generator_domain]
    exact S.resolvent_mem_domain hb lambda hlambda y
  · exact S.resolventRightInv hb lambda hlambda y

/-- Every `lambda` beyond the growth exponent lies in the resolvent set of the generator:
`lambda • I - A : D(A) → X` is bijective. -/
theorem smul_sub_generator_bijective (S : StronglyContinuousSemigroup X) {ω M : ℝ}
    (hb : S.HasGrowthBound ω M) {lambda : ℝ} (hlambda : ω < lambda) :
    Function.Bijective fun x : S.generator.domain => lambda • (x : X) - S.generator x :=
  ⟨S.smul_sub_generator_injective hb hlambda, S.smul_sub_generator_surjective hb hlambda⟩

end StronglyContinuousSemigroup

namespace ContractionSemigroup

variable [CompleteSpace X]

/-- **Converse of the Lumer--Phillips theorem**: the generator of a contraction semigroup is
dissipative.

It is the `(ω, M) = (0, 1)` case of the resolvent-range inequality
`StronglyContinuousSemigroup.norm_le_norm_smul_sub_generator`. Together with
`StronglyContinuousSemigroup.smul_sub_generator_surjective` and the density of the generator
domain, it shows that the hypotheses of the Lumer--Phillips generation theorem are also
necessary. -/
theorem isDissipative_generator (S : ContractionSemigroup X) :
    IsDissipative S.toStronglyContinuousSemigroup.generator := by
  intro lambda hlambda x
  have h := S.toStronglyContinuousSemigroup.norm_le_norm_smul_sub_generator
    S.hasGrowthBound (by simpa using hlambda) x
  rw [sub_zero, one_div] at h
  calc lambda * ‖(x : X)‖
      ≤ lambda * (lambda⁻¹ *
          ‖lambda • (x : X) - S.toStronglyContinuousSemigroup.generator x‖) := by
        gcongr
    _ = ‖lambda • (x : X) - S.toStronglyContinuousSemigroup.generator x‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul]

/-- **The generator of a contraction semigroup is m-dissipative.** This is the full converse of
the Lumer--Phillips theorem apart from the density of the domain (which is
`StronglyContinuousSemigroup.dense_domain`): dissipativity is
`ContractionSemigroup.isDissipative_generator` and the range condition is witnessed at
`lambda = 1` by the surjectivity of `lambda • I - A` that the resolvent supplies (indeed at
every `lambda > 0`, by `StronglyContinuousSemigroup.smul_sub_generator_surjective`). -/
theorem isMDissipative_generator (S : ContractionSemigroup X) :
    IsMDissipative S.toStronglyContinuousSemigroup.generator :=
  S.isDissipative_generator.isMDissipative one_pos
    (S.toStronglyContinuousSemigroup.smul_sub_generator_surjective S.hasGrowthBound
      (by norm_num))

/-- The a priori estimate for the generator of a contraction semigroup: a solution of
`lambda x - A x = y` has `‖x‖ ≤ ‖y‖ / lambda`. -/
theorem norm_le_of_smul_sub_generator_eq (S : ContractionSemigroup X) {lambda : ℝ}
    (hlambda : 0 < lambda) {x : S.toStronglyContinuousSemigroup.generator.domain} {y : X}
    (h : lambda • (x : X) - S.toStronglyContinuousSemigroup.generator x = y) :
    ‖(x : X)‖ ≤ ‖y‖ / lambda :=
  S.isDissipative_generator.norm_le_of_smul_sub_eq hlambda h

end ContractionSemigroup

end TauCeti.Semigroups

end
