/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Tactic.Module

/-!
# The resolvent set of an unbounded operator

Mathlib's `resolventSet` and `resolvent` are Banach-algebra notions: they ask that
`algebraMap R A r - a` be a *unit* of the algebra, which only makes sense for an element `a`
of that algebra. The infinitesimal generator of a C₀-semigroup is not such an element — it is
an unbounded operator, carried here by `LinearPMap` — so it needs its own resolvent notion.

This file supplies it. For `A : X →ₗ.[ℝ] X` and `lambda : ℝ` we say that a *bounded* operator
`R : X →L[ℝ] X` is a resolvent of `A` at `lambda` (`TauCeti.LinearPMap.IsResolventAt`)
when `R` takes values in `D(A)` and is a two-sided inverse of `lambda • I - A : D(A) → X`. Such
an `R` is unique when it exists, so the *resolvent set*
`TauCeti.LinearPMap.resolventSet` and the *resolvent*
`TauCeti.LinearPMap.resolvent` are well defined, and the resolvent obeys the usual
identities.

Nothing here mentions semigroups: the theory is stated for an arbitrary `A : X →ₗ.[ℝ] X`, which
is what makes it usable for an operator not yet known to generate anything — the situation of
the Hille--Yosida generation theorem, whose hypotheses read `(ω, ∞) ⊆ resolventSet A` together
with a bound on `‖resolvent A l ^ n‖`.

Two bridges keep this from being a parallel universe.

* **To Mathlib's bounded notion.** A bounded operator `T : X →L[ℝ] X`, read as the everywhere
  defined unbounded operator `(T : X →ₗ[ℝ] X).toPMap ⊤`, has exactly Mathlib's resolvent set
  and resolvent (`LinearPMap.mem_resolventSet_toPMap_top_iff`,
  `LinearPMap.resolvent_toPMap_top`), proved here.
* **To the Laplace-transform resolvent.** For a C₀-semigroup `S` with growth bound `(ω, M)`,
  every `lambda > ω` lies in the resolvent set of the generator and the resolvent there *is*
  the Laplace transform `∫₀^∞ e^{-λt} S(t) x dt`
  (`StronglyContinuousSemigroup.generator_resolvent_eq`). That bridge is proved downstream, in
  `TauCeti/Analysis/Semigroups/Resolvent/Identity.lean`, which then derives the semigroup
  resolvent identity from the abstract one below.

## Main definitions

* `TauCeti.LinearPMap.IsResolventAt`: `R` inverts `lambda • I - A`.
* `TauCeti.LinearPMap.resolventSet`: the set of `lambda` at which such an `R` exists.
* `TauCeti.LinearPMap.resolvent`: that `R`, chosen by `Classical.choose`.

## Main results

* `TauCeti.LinearPMap.IsResolventAt.unique`: the inverse is unique, so the resolvent
  is well defined.
* `TauCeti.LinearPMap.resolvent_sub_resolvent`: the resolvent identity
  `R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)`, and
  `TauCeti.LinearPMap.resolvent_comm`.
* `TauCeti.LinearPMap.mem_resolventSet_of_norm_mul_lt_one` and
  `TauCeti.LinearPMap.isOpen_resolventSet`: the Neumann-series perturbation of a
  resolvent point, and the openness of the resolvent set it gives.
* `TauCeti.LinearPMap.eq_of_le_of_mem_resolventSet`: an operator has no proper extension
  sharing a resolvent point.
* `TauCeti.LinearPMap.mem_resolventSet_toPMap_top_iff` and
  `TauCeti.LinearPMap.resolvent_toPMap_top`: the bounded bridge.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section IV.1 and
Theorem II.3.5; Pazy, *Semigroups of Linear Operators and Applications to Partial Differential
Equations*, Chapter 1.
-/

public section

noncomputable section

namespace TauCeti

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace LinearPMap

variable {A : X →ₗ.[ℝ] X} {lambda mu : ℝ} {R : X →L[ℝ] X}

/-! ## Inverting `lambda • I - A` -/

/-- `IsResolventAt A lambda R` says that the **bounded** operator `R : X →L[ℝ] X` inverts
`lambda • I - A : D(A) → X`: it takes its values in `D(A)`, is a right inverse of
`lambda • I - A` on all of `X`, and is a left inverse of it on `D(A)`.

For an unbounded `A` this replaces the Banach-algebra condition
`IsUnit (algebraMap ℝ (X →L[ℝ] X) lambda - A)` behind Mathlib's `resolventSet`, which cannot be
formed because `A` is not an element of `X →L[ℝ] X`. The two conditions agree when `A` is a
bounded operator read as an everywhere defined `LinearPMap`; see
`TauCeti.LinearPMap.mem_resolventSet_toPMap_top_iff`. -/
structure IsResolventAt (A : X →ₗ.[ℝ] X) (lambda : ℝ) (R : X →L[ℝ] X) : Prop where
  /-- The inverse takes its values in the domain of `A`. -/
  mem_domain (y : X) : R y ∈ A.domain
  /-- `R` is a right inverse: `(lambda • I - A) (R y) = y` for every `y : X`. -/
  smul_sub_apply (y : X) : lambda • R y - A ⟨R y, mem_domain y⟩ = y
  /-- `R` is a left inverse: `R ((lambda • I - A) x) = x` for every `x ∈ D(A)`. -/
  apply_smul_sub (x : A.domain) : R (lambda • (x : X) - A x) = (x : X)

/-- An inverse of `lambda • I - A` is unique: a left inverse and a right inverse of the same
map agree. -/
theorem IsResolventAt.unique (h : IsResolventAt A lambda R) {R' : X →L[ℝ] X}
    (h' : IsResolventAt A lambda R') : R = R' := by
  ext y
  have hy : R (lambda • R' y - A ⟨R' y, h'.mem_domain y⟩) = R' y :=
    h.apply_smul_sub ⟨R' y, h'.mem_domain y⟩
  rwa [h'.smul_sub_apply y] at hy

/-- `lambda • I - A` is injective on `D(A)` whenever it has a left inverse. -/
theorem IsResolventAt.smul_sub_injective (h : IsResolventAt A lambda R) :
    Function.Injective fun x : A.domain => lambda • (x : X) - A x := by
  intro x y hxy
  replace hxy : lambda • (x : X) - A x = lambda • (y : X) - A y := hxy
  exact Subtype.ext (by rw [← h.apply_smul_sub x, ← h.apply_smul_sub y, hxy])

/-- `lambda • I - A` maps `D(A)` onto `X` whenever it has a right inverse. -/
theorem IsResolventAt.smul_sub_surjective (h : IsResolventAt A lambda R) :
    Function.Surjective fun x : A.domain => lambda • (x : X) - A x :=
  fun y => ⟨⟨R y, h.mem_domain y⟩, h.smul_sub_apply y⟩

/-- `lambda • I - A : D(A) → X` is a bijection at a point of the resolvent set. -/
theorem IsResolventAt.smul_sub_bijective (h : IsResolventAt A lambda R) :
    Function.Bijective fun x : A.domain => lambda • (x : X) - A x :=
  ⟨h.smul_sub_injective, h.smul_sub_surjective⟩

/-! ## The resolvent set and the resolvent -/

/-- The **resolvent set** of an unbounded operator `A : X →ₗ.[ℝ] X`: those `lambda : ℝ` for which
`lambda • I - A : D(A) → X` is a bijection with bounded inverse. -/
def resolventSet (A : X →ₗ.[ℝ] X) : Set ℝ :=
  {lambda | ∃ R : X →L[ℝ] X, IsResolventAt A lambda R}

/-- Membership in the resolvent set unfolds to the existence of a bounded inverse of
`lambda • I - A`. -/
theorem mem_resolventSet_iff :
    lambda ∈ resolventSet A ↔ ∃ R : X →L[ℝ] X, IsResolventAt A lambda R :=
  Iff.rfl

/-- Exhibiting an inverse puts `lambda` in the resolvent set. -/
theorem IsResolventAt.mem_resolventSet (h : IsResolventAt A lambda R) :
    lambda ∈ resolventSet A :=
  ⟨R, h⟩

/-- An inverse of `lambda • I - A` exists conditionally on `lambda` lying in the resolvent set;
this is what lets `TauCeti.LinearPMap.resolvent` be defined by `Classical.choose`
without a decidability side-condition. -/
private theorem exists_isResolventAt_of_mem (A : X →ₗ.[ℝ] X) (lambda : ℝ) :
    ∃ R : X →L[ℝ] X, lambda ∈ resolventSet A → IsResolventAt A lambda R := by
  by_cases h : lambda ∈ resolventSet A
  · exact ⟨h.choose, fun _ => h.choose_spec⟩
  · exact ⟨0, fun h' => absurd h' h⟩

/-- The **resolvent** `R(lambda, A) = (lambda • I - A)⁻¹` of an unbounded operator, as a bounded
operator on `X`.

Off the resolvent set the value is an unspecified junk value; every lemma below carries the
hypothesis `lambda ∈ resolventSet A`. Uniqueness of the inverse
(`TauCeti.LinearPMap.IsResolventAt.unique`) makes the choice immaterial on the
resolvent set: `TauCeti.LinearPMap.resolvent_eq_of_isResolventAt` identifies it with
any inverse one can exhibit. -/
noncomputable def resolvent (A : X →ₗ.[ℝ] X) (lambda : ℝ) : X →L[ℝ] X :=
  (exists_isResolventAt_of_mem A lambda).choose

/-- On the resolvent set, `resolvent A lambda` really does invert `lambda • I - A`. -/
theorem isResolventAt_resolvent (h : lambda ∈ resolventSet A) :
    IsResolventAt A lambda (resolvent A lambda) :=
  (exists_isResolventAt_of_mem A lambda).choose_spec h

/-- Any exhibited inverse of `lambda • I - A` *is* the resolvent. -/
theorem resolvent_eq_of_isResolventAt (h : IsResolventAt A lambda R) :
    resolvent A lambda = R :=
  (isResolventAt_resolvent h.mem_resolventSet).unique h

/-- The resolvent takes its values in `D(A)`. -/
theorem resolvent_mem_domain (h : lambda ∈ resolventSet A) (y : X) :
    resolvent A lambda y ∈ A.domain :=
  (isResolventAt_resolvent h).mem_domain y

/-- The right-inverse identity `(lambda • I - A) R(lambda) y = y`. -/
@[simp] theorem smul_sub_apply_resolvent (h : lambda ∈ resolventSet A) (y : X) :
    lambda • resolvent A lambda y - A ⟨resolvent A lambda y, resolvent_mem_domain h y⟩ = y :=
  (isResolventAt_resolvent h).smul_sub_apply y

/-- The left-inverse identity `R(lambda) (lambda • x - A x) = x` on `D(A)`. -/
@[simp] theorem resolvent_smul_sub_apply (h : lambda ∈ resolventSet A) (x : A.domain) :
    resolvent A lambda (lambda • (x : X) - A x) = (x : X) :=
  (isResolventAt_resolvent h).apply_smul_sub x

/-- The right-inverse identity solved for `A`: `A R(lambda) y = lambda • R(lambda) y - y`. -/
theorem apply_resolvent (h : lambda ∈ resolventSet A) (y : X) :
    A ⟨resolvent A lambda y, resolvent_mem_domain h y⟩ = lambda • resolvent A lambda y - y := by
  calc A ⟨resolvent A lambda y, resolvent_mem_domain h y⟩
      = lambda • resolvent A lambda y -
          (lambda • resolvent A lambda y -
            A ⟨resolvent A lambda y, resolvent_mem_domain h y⟩) := by abel
    _ = lambda • resolvent A lambda y - y := by rw [smul_sub_apply_resolvent h y]

/-- At a point of the resolvent set, `lambda • I - A : D(A) → X` is a bijection. -/
theorem smul_sub_bijective (h : lambda ∈ resolventSet A) :
    Function.Bijective fun x : A.domain => lambda • (x : X) - A x :=
  (isResolventAt_resolvent h).smul_sub_bijective

/-- **An operator has no proper extension sharing a resolvent point.** If `A ≤ B` and some
`lambda` lies in the resolvent set of both, then `A = B`.

A vector `y ∈ D(B)` has `lambda • y - B y = lambda • x - A x` for a unique `x ∈ D(A)`, by
surjectivity for `A`; injectivity for `B` then forces `y = x`, so `D(B) ⊆ D(A)`.

This is the step that upgrades "`A` is a restriction of the generator" to "`A` *is* the
generator" in the generation theorems. -/
theorem eq_of_le_of_mem_resolventSet {A B : X →ₗ.[ℝ] X} (hAB : A ≤ B)
    (hA : lambda ∈ resolventSet A) (hB : lambda ∈ resolventSet B) : A = B := by
  refine LinearPMap.eq_of_le_of_domain_eq hAB (le_antisymm hAB.1 fun y hy => ?_)
  obtain ⟨x, hx⟩ := (smul_sub_bijective hA).surjective (lambda • y - B ⟨y, hy⟩)
  obtain ⟨x', hx'coe, hx'val⟩ := LinearPMap.exists_of_le hAB x
  have hxy : x' = (⟨y, hy⟩ : B.domain) := by
    refine (smul_sub_bijective hB).injective ?_
    simp only [← hx'coe, ← hx'val]
    exact hx
  have hcoe : (x : X) = y := by rw [hx'coe, hxy]
  rw [← hcoe]
  exact x.property

/-- The resolvent commutes with `A` on `D(A)`: `R(lambda) (A x) = A (R(lambda) x)`. -/
theorem resolvent_apply_comm (h : lambda ∈ resolventSet A) (x : A.domain) :
    resolvent A lambda (A x) =
      A ⟨resolvent A lambda (x : X), resolvent_mem_domain h (x : X)⟩ := by
  have hx : lambda • resolvent A lambda (x : X) - resolvent A lambda (A x) = (x : X) := by
    have := resolvent_smul_sub_apply h x
    rwa [map_sub, map_smul] at this
  rw [apply_resolvent h (x : X)]
  calc resolvent A lambda (A x)
      = lambda • resolvent A lambda (x : X) -
          (lambda • resolvent A lambda (x : X) - resolvent A lambda (A x)) := by abel
    _ = lambda • resolvent A lambda (x : X) - (x : X) := by rw [hx]

/-! ## The resolvent identity -/

/-- Pointwise form of the **resolvent identity**
`R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)`. -/
theorem resolvent_sub_resolvent_apply (hl : lambda ∈ resolventSet A)
    (hm : mu ∈ resolventSet A) (y : X) :
    resolvent A lambda y - resolvent A mu y
      = (mu - lambda) • resolvent A lambda (resolvent A mu y) := by
  have hmem := resolvent_mem_domain hm y
  have hy : mu • resolvent A mu y - A ⟨resolvent A mu y, hmem⟩ = y :=
    smul_sub_apply_resolvent hm y
  have hleft : resolvent A lambda
      (lambda • resolvent A mu y - A ⟨resolvent A mu y, hmem⟩) = resolvent A mu y :=
    resolvent_smul_sub_apply hl ⟨resolvent A mu y, hmem⟩
  have hkey : resolvent A lambda (mu • resolvent A mu y - A ⟨resolvent A mu y, hmem⟩)
      = resolvent A mu y + (mu - lambda) • resolvent A lambda (resolvent A mu y) := by
    have hsplit : mu • resolvent A mu y - A ⟨resolvent A mu y, hmem⟩
        = (lambda • resolvent A mu y - A ⟨resolvent A mu y, hmem⟩)
          + (mu - lambda) • resolvent A mu y := by module
    rw [hsplit, map_add, map_smul, hleft]
  rw [hy] at hkey
  rw [hkey]
  abel

/-- The **resolvent identity** `R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)`, as an
equality of bounded operators. -/
theorem resolvent_sub_resolvent (hl : lambda ∈ resolventSet A) (hm : mu ∈ resolventSet A) :
    resolvent A lambda - resolvent A mu
      = (mu - lambda) • (resolvent A lambda ∘L resolvent A mu) := by
  ext y
  simpa using resolvent_sub_resolvent_apply hl hm y

/-- Resolvents at two points of the resolvent set commute. -/
theorem resolvent_comm (hl : lambda ∈ resolventSet A) (hm : mu ∈ resolventSet A) :
    resolvent A lambda ∘L resolvent A mu = resolvent A mu ∘L resolvent A lambda := by
  rcases eq_or_ne lambda mu with rfl | hne
  · rfl
  · have hsub : (mu - lambda) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h1 := resolvent_sub_resolvent hl hm
    have h2 := resolvent_sub_resolvent hm hl
    have h3 : (mu - lambda) • (resolvent A lambda ∘L resolvent A mu)
        = (mu - lambda) • (resolvent A mu ∘L resolvent A lambda) := by
      rw [← h1, ← neg_sub lambda mu, neg_smul, ← h2]
      abel
    have h4 := congrArg (fun T : X →L[ℝ] X => (mu - lambda)⁻¹ • T) h3
    simpa only [smul_smul, inv_mul_cancel₀ hsub, one_smul] using h4

/-! ## Openness of the resolvent set -/

section CompleteSpace

variable [CompleteSpace X]

/-- The Neumann inverse. When `|mu - lambda| * ‖R(lambda)‖ < 1`, the operator
`1 - (lambda - mu) • R(lambda)` is invertible, and its inverse `U` is two-sided and commutes with
`R(lambda)` — the latter because `1 - (lambda - mu) • R(lambda)` is a polynomial in `R(lambda)`.

Nothing here needs `lambda` to be in the resolvent set: the statement is about the bounded operator
`resolvent A lambda` alone. -/
private theorem exists_inverse_one_sub_smul_resolvent
    (hmu : |mu - lambda| * ‖resolvent A lambda‖ < 1) :
    ∃ U : X →L[ℝ] X,
      (∀ y : X, U y - (lambda - mu) • resolvent A lambda (U y) = y) ∧
      (∀ y : X, U (y - (lambda - mu) • resolvent A lambda y) = y) ∧
      ∀ y : X, resolvent A lambda (U y) = U (resolvent A lambda y) := by
  have hnorm : ‖(lambda - mu) • resolvent A lambda‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
    exact hmu
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hnorm
  set B : X →L[ℝ] X := (lambda - mu) • resolvent A lambda with hB
  refine ⟨((u⁻¹ : (X →L[ℝ] X)ˣ) : X →L[ℝ] X), fun y => ?_, fun y => ?_, fun y => ?_⟩
  · have h1 : ((u : X →L[ℝ] X) * (u⁻¹ : (X →L[ℝ] X)ˣ)) = 1 := u.mul_inv
    rw [hu] at h1
    simpa [hB] using congrArg (fun S : X →L[ℝ] X => S y) h1
  · have h1 : (((u⁻¹ : (X →L[ℝ] X)ˣ) : X →L[ℝ] X) * (u : X →L[ℝ] X)) = 1 := u.inv_mul
    rw [hu] at h1
    simpa [hB] using congrArg (fun S : X →L[ℝ] X => S y) h1
  · -- `1 - (lambda - mu) • R(lambda)` is a polynomial in `R(lambda)`, hence commutes with it.
    have hcomm : Commute ((u : X →L[ℝ] X)) (resolvent A lambda) := by
      rw [hu, hB]
      exact (Commute.one_left _).sub_left
        ((Commute.refl (resolvent A lambda)).smul_left (lambda - mu))
    simpa [mul_apply_eq_comp] using
      congrArg (fun S : X →L[ℝ] X => S y) hcomm.units_inv_left.symm

/-- **The Neumann perturbation of a resolvent point.** If `lambda` lies in the resolvent set and
`|mu - lambda| * ‖R(lambda)‖ < 1`, then `mu` lies in it too.

On `D(A)` one has `mu • I - A = (I - (lambda - mu) R(lambda)) (lambda • I - A)`, and the first
factor is invertible by the geometric series, so `R(lambda) (I - (lambda - mu) R(lambda))⁻¹`
inverts `mu • I - A`. -/
theorem mem_resolventSet_of_norm_mul_lt_one (h : lambda ∈ resolventSet A)
    (hmu : |mu - lambda| * ‖resolvent A lambda‖ < 1) : mu ∈ resolventSet A := by
  obtain ⟨U, hUright, hUleft, hcomm⟩ := exists_inverse_one_sub_smul_resolvent hmu
  refine ⟨resolvent A lambda ∘L U, fun y => resolvent_mem_domain h (U y), fun y => ?_, fun x => ?_⟩
  · have h2 : mu • resolvent A lambda (U y) -
        A ⟨resolvent A lambda (U y), resolvent_mem_domain h (U y)⟩
      = (lambda • resolvent A lambda (U y) -
          A ⟨resolvent A lambda (U y), resolvent_mem_domain h (U y)⟩) -
        (lambda - mu) • resolvent A lambda (U y) := by module
    simp only [ContinuousLinearMap.comp_apply]
    rw [h2, smul_sub_apply_resolvent h (U y)]
    exact hUright y
  · have hsplit : mu • (x : X) - A x
      = (lambda • (x : X) - A x) - (lambda - mu) • (x : X) := by module
    have h1 : resolvent A lambda (mu • (x : X) - A x)
        = (x : X) - (lambda - mu) • resolvent A lambda (x : X) := by
      rw [hsplit, map_sub, map_smul, resolvent_smul_sub_apply h x]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hcomm (mu • (x : X) - A x), h1, hUleft]

/-- **The resolvent set is open.** -/
theorem isOpen_resolventSet (A : X →ₗ.[ℝ] X) : IsOpen (resolventSet A) := by
  rw [Metric.isOpen_iff]
  intro lambda h
  refine ⟨1 / (‖resolvent A lambda‖ + 1), by positivity, fun mu hmu => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq] at hmu
  refine mem_resolventSet_of_norm_mul_lt_one h ?_
  have hlt : |mu - lambda| * (‖resolvent A lambda‖ + 1) < 1 :=
    (lt_div_iff₀ (by positivity)).mp (by simpa using hmu)
  calc |mu - lambda| * ‖resolvent A lambda‖
      ≤ |mu - lambda| * (‖resolvent A lambda‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ < 1 := hlt

end CompleteSpace

/-! ## The bridge to Mathlib's Banach-algebra resolvent

A bounded operator `T : X →L[ℝ] X` becomes an everywhere defined unbounded operator
`(T : X →ₗ[ℝ] X).toPMap ⊤`. Its resolvent set and resolvent in the sense above are Mathlib's
`resolventSet ℝ T` and `resolvent T`, computed in the Banach algebra `X →L[ℝ] X`. -/

section Bounded

variable {T : X →L[ℝ] X}

/-- `lambda • I - T`, formed in the algebra `X →L[ℝ] X`, applied to a vector. -/
private theorem algebraMap_sub_apply (T : X →L[ℝ] X) (lambda : ℝ) (y : X) :
    (algebraMap ℝ (X →L[ℝ] X) lambda - T) y = lambda • y - T y := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- An inverse of `lambda • I - T` in the unbounded sense is a two-sided inverse in the algebra
`X →L[ℝ] X`, so `lambda • I - T` is a unit there. -/
theorem isUnit_of_isResolventAt_toPMap_top
    (h : IsResolventAt ((T : X →ₗ[ℝ] X).toPMap ⊤) lambda R) :
    IsUnit (algebraMap ℝ (X →L[ℝ] X) lambda - T) := by
  have hright : (algebraMap ℝ (X →L[ℝ] X) lambda - T) * R = 1 := by
    ext y
    have h1 : lambda • R y - T (R y) = y := h.smul_sub_apply y
    simpa [algebraMap_sub_apply] using h1
  have hleft : R * (algebraMap ℝ (X →L[ℝ] X) lambda - T) = 1 := by
    ext y
    have h1 : R (lambda • y - T y) = y := h.apply_smul_sub ⟨y, Submodule.mem_top⟩
    simpa [algebraMap_sub_apply] using h1
  exact spectrum.mem_resolventSet_of_left_right_inverse hright hleft

/-- A unit `lambda • I - T` of the algebra `X →L[ℝ] X` inverts `lambda • I - T` in the
unbounded sense, with the algebra inverse as the resolvent. -/
theorem isResolventAt_toPMap_top_of_isUnit
    (h : IsUnit (algebraMap ℝ (X →L[ℝ] X) lambda - T)) :
    IsResolventAt ((T : X →ₗ[ℝ] X).toPMap ⊤) lambda
      ((h.unit⁻¹ : (X →L[ℝ] X)ˣ) : X →L[ℝ] X) where
  mem_domain _ := Submodule.mem_top
  smul_sub_apply y := by
    have h1 : (algebraMap ℝ (X →L[ℝ] X) lambda - T)
        (((h.unit⁻¹ : (X →L[ℝ] X)ˣ) : X →L[ℝ] X) y) = y := by
      rw [← mul_apply_eq_comp, h.mul_val_inv, one_apply_eq_self]
    rwa [algebraMap_sub_apply] at h1
  apply_smul_sub x := by
    have h1 : ((h.unit⁻¹ : (X →L[ℝ] X)ˣ) : X →L[ℝ] X)
        ((algebraMap ℝ (X →L[ℝ] X) lambda - T) (x : X)) = (x : X) := by
      rw [← mul_apply_eq_comp, h.val_inv_mul, one_apply_eq_self]
    rwa [algebraMap_sub_apply] at h1

/-- **The bounded bridge, membership half.** For a bounded operator the unbounded resolvent set
of `T` and Mathlib's Banach-algebra resolvent set agree. -/
theorem mem_resolventSet_toPMap_top_iff (T : X →L[ℝ] X) (lambda : ℝ) :
    lambda ∈ resolventSet ((T : X →ₗ[ℝ] X).toPMap ⊤) ↔ lambda ∈ _root_.resolventSet ℝ T :=
  ⟨fun ⟨_, hR⟩ => isUnit_of_isResolventAt_toPMap_top hR,
    fun h => (isResolventAt_toPMap_top_of_isUnit h).mem_resolventSet⟩

/-- **The bounded bridge, value half.** For a bounded operator the unbounded resolvent is
Mathlib's Banach-algebra resolvent. -/
theorem resolvent_toPMap_top (T : X →L[ℝ] X) {lambda : ℝ}
    (h : lambda ∈ _root_.resolventSet ℝ T) :
    resolvent ((T : X →ₗ[ℝ] X).toPMap ⊤) lambda = _root_.resolvent T lambda := by
  rw [resolvent_eq_of_isResolventAt (isResolventAt_toPMap_top_of_isUnit h),
    spectrum.resolvent_eq h]

end Bounded

end LinearPMap

end TauCeti

end
