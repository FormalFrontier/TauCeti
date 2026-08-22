/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Euler characteristic of a sheaf of modules on a scheme

For a scheme `X` over a field `k`, the finite-dimensional cohomology `Hⁱ(X, M)` of a sheaf of
modules is a `k`-vector space, so the alternating sum of its dimensions can be formed. This file
introduces that alternating sum, truncated at a degree `n`, and proves that it is additive on short
exact sequences as soon as the truncation degree is one past the last nonvanishing degree.

## Main declarations

* `Scheme.Modules.eulerCharBelow k X M n`, the alternating sum
  `∑_{i < n} (-1)ⁱ dim_k Hⁱ(X, M)` for a sheaf with finite-dimensional cohomology. If its
  cohomology also vanishes in degrees `≥ n`, this is the Euler characteristic `χ(X, M)`;
* `Scheme.Modules.eulerCharBelow_sub_sub`, the exact defect of additivity: the failure of
  `eulerCharBelow` to be additive on a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` is, up to
  sign, the dimension of the image of the last connecting map that the truncation cuts off;
* `Scheme.Modules.eulerCharBelow_X₂`, the additivity itself, under the vanishing of
  `Hⁿ(X, M₁)`, and `Scheme.Modules.eulerChar_X₂`, its shape on a curve, where cohomology
  vanishes above degree one so that `χ(X, M) = dim H⁰(X, M) - dim H¹(X, M)`;
* `Scheme.Modules.eulerCharBelow_congr`, the invariance of the truncated Euler characteristic
  under isomorphism, and `Scheme.Modules.finrank_cohomology_zero`, the identification of
  `dim H⁰(X, M)` with the dimension of the space of global sections.

The proof is the usual dimension count in the long exact cohomology sequence: the rank-nullity
theorem turns each of the three cohomology dimensions in degree `i` into a sum of two ranks of
maps of the sequence, and the alternating sum telescopes down to the single rank left over at
the truncation degree.

Additivity of the Euler characteristic is what makes the degree of a line bundle on a curve,
`deg L := χ(L) - χ(𝒪_X)`, behave additively, and it is the step from which Riemann-Roch is
proved by induction on a divisor. It is therefore Layer B infrastructure for
`TauCetiRoadmap/JacobianChallenge/README.md`, "genus, Riemann-Roch, Serre duality".

No formalization is vendored. The alternating-sum bookkeeping reuses Mathlib's
`LinearMap.finrank_range_add_finrank_ker`, `LinearMap.finrank_range_of_inj` and
`Function.Exact.linearMap_ker_eq`; the long exact sequence and the linearity of its maps are
`TauCeti/AlgebraicGeometry/Cohomology/LongExactSequence.lean`.
-/

public section

open CategoryTheory AlgebraicGeometry Scheme.Modules
open Module (finrank)

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The alternating sum `∑_{i < n} (-1)ⁱ dim_k Hⁱ(X, M)` of the dimensions of the
finite-dimensional cohomology of a sheaf of modules on a scheme over a field, truncated at
degree `n`.

For a sheaf whose cohomology vanishes in degrees `≥ n` this is the Euler characteristic
`χ(X, M)`; on a curve, the relevant truncation is `n = 2`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow (M : X.Modules)
    [∀ i, FiniteDimensional k (Cohomology M i)] (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (finrank k (Cohomology M i) : ℤ)

variable {X}

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_zero (M : X.Modules)
    [∀ i, FiniteDimensional k (Cohomology M i)] :
    eulerCharBelow k X M 0 = 0 :=
  Finset.sum_range_zero _

lemma _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_succ (M : X.Modules)
    [∀ i, FiniteDimensional k (Cohomology M i)] (n : ℕ) :
    eulerCharBelow k X M (n + 1) =
      eulerCharBelow k X M n + (-1) ^ n * (finrank k (Cohomology M n) : ℤ) :=
  Finset.sum_range_succ _ _

lemma _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_two (M : X.Modules)
    [∀ i, FiniteDimensional k (Cohomology M i)] :
    eulerCharBelow k X M 2 =
      (finrank k (Cohomology M 0) : ℤ) - (finrank k (Cohomology M 1) : ℤ) := by
  rw [eulerCharBelow_succ, eulerCharBelow_succ, eulerCharBelow_zero]
  ring

/-- The dimension of `H⁰(X, M)` is the dimension of the space of global sections of `M`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.finrank_cohomology_zero (M : X.Modules) :
    finrank k (Cohomology M 0) = finrank k Γ(M, ⊤) :=
  (cohomologyZeroBaseLinearEquiv k X M).finrank_eq

/-- Isomorphic sheaves of modules have the same cohomology dimensions. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.finrank_cohomology_congr {M N : X.Modules}
    (e : M ≅ N) (i : ℕ) :
    finrank k (Cohomology M i) = finrank k (Cohomology N i) :=
  LinearEquiv.finrank_eq <|
    LinearEquiv.ofLinearMap (cohomologyMapBaseLinear k X e.hom i)
      (cohomologyMapBaseLinear k X e.inv i)
      (by rw [← cohomologyMapBaseLinear_comp, e.inv_hom_id, cohomologyMapBaseLinear_id])
      (by rw [← cohomologyMapBaseLinear_comp, e.hom_inv_id, cohomologyMapBaseLinear_id])

/-- The truncated Euler characteristic only depends on the isomorphism class of the sheaf. This
is what makes an invariant such as the degree `χ(L) - χ(𝒪_X)` of a line bundle well defined on
the Picard group. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_congr {M N : X.Modules}
    [∀ i, FiniteDimensional k (Cohomology M i)]
    [∀ i, FiniteDimensional k (Cohomology N i)] (e : M ≅ N) (n : ℕ) :
    eulerCharBelow k X M n = eulerCharBelow k X N n :=
  Finset.sum_congr rfl fun i _ ↦ by rw [finrank_cohomology_congr k e i]

section ShortExact

variable {S : ShortComplex X.Modules} (hS : S.ShortExact)

omit hS in
private lemma coe_cohomologyMapBaseLinear {M N : X.Modules} (f : M ⟶ N) (i : ℕ) :
    ⇑(cohomologyMapBaseLinear k X f i) = ⇑(cohomologyMap f i) := by
  funext x
  rw [cohomologyMapBaseLinear_apply, cohomologyFunctor_map]
  rfl

include hS

private lemma coe_cohomologyδBaseLinear (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ⇑(cohomologyδBaseLinear k X hS n₀ n₁ h) = ⇑(cohomologyδ hS n₀ n₁ h) := by
  funext x
  exact cohomologyδBaseLinear_apply k X hS n₀ n₁ h x

/-- Rank-nullity in degree zero for the first term: the map on `H⁰` is injective, so its image
has the dimension of `H⁰(X, M₁)`. -/
private lemma finrank_X₁_zero :
    finrank k (Cohomology S.X₁ 0) =
      finrank k (LinearMap.range (cohomologyMapBaseLinear k X S.f 0)) := by
  have := hS.mono_f
  have hinj : Function.Injective (cohomologyMapBaseLinear k X S.f 0) := by
    rw [coe_cohomologyMapBaseLinear]
    exact cohomologyMap_injective S.f
  exact (LinearMap.finrank_range_of_inj hinj).symm

/-- Rank-nullity in positive degrees for the first term: the kernel of `Hⁱ⁺¹(M₁) → Hⁱ⁺¹(M₂)` is
the image of the connecting map out of `Hⁱ(M₃)`. -/
private lemma finrank_X₁_succ (i : ℕ) [FiniteDimensional k (Cohomology S.X₁ (i + 1))] :
    finrank k (Cohomology S.X₁ (i + 1)) =
      finrank k (LinearMap.range (cohomologyMapBaseLinear k X S.f (i + 1))) +
        finrank k (LinearMap.range (cohomologyδBaseLinear k X hS i (i + 1) rfl)) := by
  have hex : Function.Exact (cohomologyδBaseLinear k X hS i (i + 1) rfl)
      (cohomologyMapBaseLinear k X S.f (i + 1)) := by
    simpa only [coe_cohomologyδBaseLinear, coe_cohomologyMapBaseLinear] using
      exact_cohomologyδ_cohomologyMap hS i (i + 1) rfl
  rw [← LinearMap.finrank_range_add_finrank_ker (cohomologyMapBaseLinear k X S.f (i + 1)),
    hex.linearMap_ker_eq]

/-- Rank-nullity for the middle term: the kernel of `Hⁱ(M₂) → Hⁱ(M₃)` is the image of
`Hⁱ(M₁) → Hⁱ(M₂)`. -/
private lemma finrank_X₂ (i : ℕ) [FiniteDimensional k (Cohomology S.X₂ i)] :
    finrank k (Cohomology S.X₂ i) =
      finrank k (LinearMap.range (cohomologyMapBaseLinear k X S.g i)) +
        finrank k (LinearMap.range (cohomologyMapBaseLinear k X S.f i)) := by
  have hex : Function.Exact (cohomologyMapBaseLinear k X S.f i)
      (cohomologyMapBaseLinear k X S.g i) := by
    simpa only [coe_cohomologyMapBaseLinear] using exact_cohomologyMap_cohomologyMap hS i
  rw [← LinearMap.finrank_range_add_finrank_ker (cohomologyMapBaseLinear k X S.g i),
    hex.linearMap_ker_eq]

/-- Rank-nullity for the last term: the kernel of the connecting map out of `Hⁱ(M₃)` is the
image of `Hⁱ(M₂) → Hⁱ(M₃)`. -/
private lemma finrank_X₃ (i : ℕ) [FiniteDimensional k (Cohomology S.X₃ i)] :
    finrank k (Cohomology S.X₃ i) =
      finrank k (LinearMap.range (cohomologyδBaseLinear k X hS i (i + 1) rfl)) +
        finrank k (LinearMap.range (cohomologyMapBaseLinear k X S.g i)) := by
  have hex : Function.Exact (cohomologyMapBaseLinear k X S.g i)
      (cohomologyδBaseLinear k X hS i (i + 1) rfl) := by
    simpa only [coe_cohomologyδBaseLinear, coe_cohomologyMapBaseLinear] using
      exact_cohomologyMap_cohomologyδ hS i (i + 1) rfl
  rw [← LinearMap.finrank_range_add_finrank_ker (cohomologyδBaseLinear k X hS i (i + 1) rfl),
    hex.linearMap_ker_eq]

variable [∀ i, FiniteDimensional k (Cohomology S.X₁ i)]
  [∀ i, FiniteDimensional k (Cohomology S.X₂ i)]
  [∀ i, FiniteDimensional k (Cohomology S.X₃ i)]

/-- The defect of additivity of the truncated Euler characteristic on a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` is, up to sign, the dimension of the image of the connecting map
`Hⁿ(X, M₃) → Hⁿ⁺¹(X, M₁)` that the truncation cuts off. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_sub_sub (n : ℕ) :
    eulerCharBelow k X S.X₂ (n + 1) - eulerCharBelow k X S.X₁ (n + 1) -
        eulerCharBelow k X S.X₃ (n + 1) =
      (-1) ^ (n + 1) *
        (finrank k (LinearMap.range (cohomologyδBaseLinear k X hS n (n + 1) rfl)) : ℤ) := by
  induction n with
  | zero =>
    rw [eulerCharBelow_succ k S.X₂ 0, eulerCharBelow_succ k S.X₁ 0,
      eulerCharBelow_succ k S.X₃ 0, eulerCharBelow_zero, eulerCharBelow_zero,
      eulerCharBelow_zero, finrank_X₁_zero k hS, finrank_X₂ k hS 0, finrank_X₃ k hS 0]
    push_cast
    ring
  | succ n ih =>
    rw [eulerCharBelow_succ k S.X₂ (n + 1), eulerCharBelow_succ k S.X₁ (n + 1),
      eulerCharBelow_succ k S.X₃ (n + 1), finrank_X₁_succ k hS n, finrank_X₂ k hS (n + 1),
      finrank_X₃ k hS (n + 1)]
    push_cast
    linear_combination ih

/-- **Additivity of the Euler characteristic.** If `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` is a short exact
sequence of sheaves of modules with finite-dimensional cohomology, and `Hⁿ(X, M₁)` vanishes,
then the Euler characteristics truncated at `n` add up. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_X₂ (n : ℕ)
    (hvan : Subsingleton (Cohomology S.X₁ n)) :
    eulerCharBelow k X S.X₂ n = eulerCharBelow k X S.X₁ n + eulerCharBelow k X S.X₃ n := by
  cases n with
  | zero => simp
  | succ n =>
    have hrange : LinearMap.range (cohomologyδBaseLinear k X hS n (n + 1) rfl) = ⊥ := by
      rw [LinearMap.range_eq_bot]
      exact LinearMap.ext fun _ ↦ Subsingleton.elim _ _
    have h := eulerCharBelow_sub_sub k hS n
    rw [hrange, finrank_bot, Nat.cast_zero, mul_zero] at h
    linarith

/-- **Additivity of the Euler characteristic on a curve.** For a short exact sequence of sheaves
of modules with finite-dimensional cohomology and with `H²(X, M₁)` vanishing, as it does on a
curve, the Euler characteristics `χ(X, M) = dim H⁰(X, M) - dim H¹(X, M)` add up. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.eulerChar_X₂
    (hvan : Subsingleton (Cohomology S.X₁ 2)) :
    (finrank k (Cohomology S.X₂ 0) : ℤ) - (finrank k (Cohomology S.X₂ 1) : ℤ) =
      ((finrank k (Cohomology S.X₁ 0) : ℤ) - (finrank k (Cohomology S.X₁ 1) : ℤ)) +
        ((finrank k (Cohomology S.X₃ 0) : ℤ) - (finrank k (Cohomology S.X₃ 1) : ℤ)) := by
  simpa only [eulerCharBelow_two] using eulerCharBelow_X₂ k hS 2 hvan

end ShortExact

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
