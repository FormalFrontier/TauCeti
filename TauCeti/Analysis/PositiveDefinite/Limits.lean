/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Function.Kernel
public import TauCeti.Analysis.PositiveDefinite.Kernel.Basic
public import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.OrderClosed

/-!
# Limits of positive-definite functions

This file records the pointwise- and locally-uniform-limit closure of positive-definite kernels
and of `TauCeti.IsPositiveDefinite`, the positive-definite function predicate on an involutive
additive monoid.

This is the limit-closure item from Part C of the `OneParameterSemigroups` roadmap. The result is
about positive-definiteness alone for pointwise limits; as the roadmap notes, continuity
additionally requires locally uniform convergence. The locally uniform API records the resulting
preservation of both continuity and positive-definiteness.

## Main declarations

* `TauCeti.isPositiveDefiniteKernel_of_tendsto`: filter-level pointwise-limit closure for
  positive-definite kernels.
* `TauCeti.IsPositiveDefinite.of_tendsto`: filter-level pointwise-limit closure for
  positive-definite functions.
* `TauCeti.IsPositiveDefinite.of_forall_tendsto`: the same result when every function in the
  family is positive definite.
* `TauCeti.IsPositiveDefinite.of_seq_tendsto`: the sequential `atTop` specialization.
* `TauCeti.IsPositiveDefinite.of_tendstoLocallyUniformly`: locally uniform limits of eventually
  positive-definite functions are positive definite.
* `TauCeti.continuous_and_isPositiveDefinite_of_tendstoLocallyUniformly`: locally uniform limits
  of eventually continuous, eventually positive-definite functions retain both properties.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open Filter
open ComplexConjugate
open scoped Topology
open scoped ComplexOrder

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*}

/-- Positive-definite kernels are preserved under pointwise limits along a nontrivial filter. The
hypothesis on positive-definiteness is eventual, so this applies equally to nets that are
eventually positive definite. -/
theorem isPositiveDefiniteKernel_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    {K : ι → α → α → 𝕜} {L : α → α → 𝕜}
    (hK : ∀ᶠ i in l, IsPositiveDefiniteKernel (K i))
    (hlim : ∀ a b : α, Tendsto (fun i => K i a b) l (𝓝 (L a b))) :
    IsPositiveDefiniteKernel L := by
  rw [isPositiveDefiniteKernel_def]
  refine ⟨?_, ?_⟩
  · ext a b
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, ← starRingEnd_apply]
    have hconj : Tendsto (fun i => conj (K i b a)) l (𝓝 (conj (L b a))) :=
      RCLike.continuous_conj.tendsto (L b a) |>.comp (hlim b a)
    have hswap : Tendsto (fun i => conj (K i b a)) l (𝓝 (L a b)) :=
      (hlim a b).congr' <| by
        filter_upwards [hK] with i hi
        exact (isPositiveDefiniteKernel_conj_symm hi b a).symm
    exact tendsto_nhds_unique hconj hswap
  · intro x
    have hquad :
        Tendsto
          (fun i => x.support.sum fun a =>
            x.support.sum fun b => star (x a) * K i a b * x b) l
          (𝓝 (x.support.sum fun a => x.support.sum fun b => star (x a) * L a b * x b)) := by
      refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
      exact ((tendsto_const_nhds.mul (hlim a b)).mul tendsto_const_nhds)
    have hnonneg : 0 ≤ x.support.sum fun a =>
        x.support.sum fun b => star (x a) * L a b * x b := by
      refine ge_of_tendsto hquad ?_
      filter_upwards [hK] with i hi
      simpa [Finsupp.sum] using ((isPositiveDefiniteKernel_def (K i)).mp hi).2 x
    simpa [Finsupp.sum] using hnonneg

namespace IsPositiveDefinite

variable {M : Type*} [AddMonoid M] [StarAddMonoid M]

/-- Positive-definiteness is preserved under pointwise limits along a nontrivial filter. The
hypothesis on positive-definiteness is eventual, so this applies equally to nets that are
eventually positive definite. -/
theorem of_tendsto {ι : Type*} {l : Filter ι} [NeBot l] {F : ι → M → ℂ} {G : M → ℂ}
    (hF : ∀ᶠ i in l, IsPositiveDefinite (F i))
    (hlim : ∀ x : M, Tendsto (fun i => F i x) l (𝓝 (G x))) :
    IsPositiveDefinite G :=
  of_isPositiveDefiniteKernel <|
    isPositiveDefiniteKernel_of_tendsto
      (hF.mono fun _ hi => hi.isPositiveDefiniteKernel)
      (fun a b => hlim (a + star b))

/-- A pointwise limit of a family of positive-definite functions is positive definite. This is the
non-eventual form of `TauCeti.IsPositiveDefinite.of_tendsto`. -/
theorem of_forall_tendsto {ι : Type*} {l : Filter ι} [NeBot l] {F : ι → M → ℂ} {G : M → ℂ}
    (hF : ∀ i, IsPositiveDefinite (F i))
    (hlim : ∀ x : M, Tendsto (fun i => F i x) l (𝓝 (G x))) :
    IsPositiveDefinite G :=
  of_tendsto (Eventually.of_forall hF) hlim

/-- Sequential pointwise limits of eventually positive-definite functions are positive definite. -/
theorem of_seq_tendsto {F : ℕ → M → ℂ} {G : M → ℂ}
    (hF : ∀ᶠ n in atTop, IsPositiveDefinite (F n))
    (hlim : ∀ x : M, Tendsto (fun n => F n x) atTop (𝓝 (G x))) :
    IsPositiveDefinite G :=
  of_tendsto hF hlim

variable [TopologicalSpace M]

/-- A locally uniform limit of eventually positive-definite functions is positive definite.

Unlike continuity, positive-definiteness itself only needs pointwise convergence; local uniform
convergence is converted to pointwise convergence before applying
`TauCeti.IsPositiveDefinite.of_tendsto`. -/
theorem of_tendstoLocallyUniformly {ι : Type*} {l : Filter ι} [NeBot l]
    {F : ι → M → ℂ} {G : M → ℂ}
    (hF : ∀ᶠ i in l, IsPositiveDefinite (F i))
    (hlim : TendstoLocallyUniformly F G l) :
    IsPositiveDefinite G :=
  of_tendsto hF fun x =>
    hlim.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)

end IsPositiveDefinite

/-- A locally uniform limit of eventually continuous, eventually positive-definite functions is
continuous and positive definite. -/
theorem continuous_and_isPositiveDefinite_of_tendstoLocallyUniformly
    {M : Type*} [TopologicalSpace M] [AddMonoid M] [StarAddMonoid M]
    {ι : Type*} {l : Filter ι} [NeBot l] {F : ι → M → ℂ} {G : M → ℂ}
    (hcont : ∀ᶠ i in l, Continuous (F i))
    (hpd : ∀ᶠ i in l, IsPositiveDefinite (F i))
    (hlim : TendstoLocallyUniformly F G l) :
    Continuous G ∧ IsPositiveDefinite G :=
  ⟨hlim.continuous hcont.frequently, IsPositiveDefinite.of_tendstoLocallyUniformly hpd hlim⟩

/-- A locally uniform limit of continuous positive-definite functions is continuous and positive
definite. -/
theorem continuous_and_isPositiveDefinite_of_forall_tendstoLocallyUniformly
    {M : Type*} [TopologicalSpace M] [AddMonoid M] [StarAddMonoid M]
    {ι : Type*} {l : Filter ι} [NeBot l] {F : ι → M → ℂ} {G : M → ℂ}
    (hcont : ∀ i, Continuous (F i))
    (hpd : ∀ i, IsPositiveDefinite (F i))
    (hlim : TendstoLocallyUniformly F G l) :
    Continuous G ∧ IsPositiveDefinite G :=
  continuous_and_isPositiveDefinite_of_tendstoLocallyUniformly
    (Eventually.of_forall hcont) (Eventually.of_forall hpd) hlim

/-- A sequential locally uniform limit of eventually continuous, eventually positive-definite
functions is continuous and positive definite. -/
theorem continuous_and_isPositiveDefinite_of_seq_tendstoLocallyUniformly
    {M : Type*} [TopologicalSpace M] [AddMonoid M] [StarAddMonoid M]
    {F : ℕ → M → ℂ} {G : M → ℂ}
    (hcont : ∀ᶠ n in atTop, Continuous (F n))
    (hpd : ∀ᶠ n in atTop, IsPositiveDefinite (F n))
    (hlim : TendstoLocallyUniformly F G atTop) :
    Continuous G ∧ IsPositiveDefinite G :=
  continuous_and_isPositiveDefinite_of_tendstoLocallyUniformly hcont hpd hlim

end TauCeti
