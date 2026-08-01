/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Basic
public import Mathlib.Data.NNReal.Star
public import Mathlib.Topology.Constructions.SumProd

/-!
# Product constructions for semigroup-group positive-definite functions

This file builds Berg--Christensen--Ressel positive-definite functions on `ℝ≥0 × V`
from separate time and spatial factors. If `f : ℝ≥0 → ℂ` supplies the positive-definite
time kernel `(t, u) ↦ f (t + u)`, and `g : V → ℂ` supplies the positive-definite spatial
subtraction kernel `(v, w) ↦ g (v - w)`, then `(t, v) ↦ f t * g v` is semigroup-group
positive definite. We also provide the convenience form where the spatial kernel comes from
a positive-definite function for the negation involution on `V`.

This is a small prerequisite for the BCR semigroup--Bochner representation milestone in
`TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
("BCR semigroup--Bochner"). The eventual Laplace--Fourier examples have exactly this separated
shape before integration: a time kernel multiplied by a spatial Fourier kernel.

No Mathlib infrastructure is vendored. The proof reuses Tau Ceti's positive-definite
function/kernel correspondence and the Schur product closure for positive-definite kernels.

## Main declarations

* `TauCeti.isSemigroupGroupPD_mul_time_spatial`: the product of a time positive-definite
  function and a spatial positive-definite function is BCR positive definite.
* `TauCeti.isSemigroupGroupPD_mul_time_spatial_of_kernels`: the same construction when the time
  factor and spatial subtraction factor are supplied as positive-definite kernels.
* `TauCeti.continuous_mul_time_spatial`: continuity of separated products.
* `TauCeti.isSemigroupGroupPD_mul_time_spatial_and_continuous`: the packaged positive-definite
  and continuous form used by BCR-facing examples.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open scoped ComplexOrder
open scoped NNReal

namespace TauCeti

variable {V : Type*} [AddCommGroup V]

/-- If the time factor gives a positive-definite kernel `(t, u) ↦ f (t + u)`, and the spatial
factor gives a positive-definite subtraction kernel `(v, w) ↦ g (v - w)`, then their separated
product is semigroup-group positive definite. -/
theorem isSemigroupGroupPD_mul_time_spatial_of_kernels {f : ℝ≥0 → ℂ} {g : V → ℂ}
    (hf : IsPositiveDefiniteKernel fun t u : ℝ≥0 => f (t + u))
    (hg : IsPositiveDefiniteKernel fun v w : V => g (v - w)) :
    IsSemigroupGroupPD fun p : ℝ≥0 × V => f p.1 * g p.2 := by
  refine IsSemigroupGroupPD.of_isPositiveDefiniteKernel ?_
  have htime : IsPositiveDefiniteKernel fun p q : ℝ≥0 × V => f (p.1 + q.1) :=
    isPositiveDefiniteKernel_comp hf Prod.fst
  have hspace : IsPositiveDefiniteKernel fun p q : ℝ≥0 × V => g (p.2 - q.2) :=
    isPositiveDefiniteKernel_comp hg Prod.snd
  simpa using isPositiveDefiniteKernel_mul htime hspace

/-- A separated product of a time positive-definite function and a spatial positive-definite
function is semigroup-group positive definite. The time factor uses Mathlib's trivial involution
on `ℝ≥0`; the spatial factor uses the supplied negation-involution hypothesis. -/
theorem isSemigroupGroupPD_mul_time_spatial [StarAddMonoid V] {f : ℝ≥0 → ℂ} {g : V → ℂ}
    (hf : IsPositiveDefinite f) (hg : IsPositiveDefinite g) (hstar : ∀ v : V, star v = -v) :
    IsSemigroupGroupPD fun p : ℝ≥0 × V => f p.1 * g p.2 := by
  refine isSemigroupGroupPD_mul_time_spatial_of_kernels ?_ (hg.isPositiveDefiniteKernel_sub hstar)
  have hK := hf.isPositiveDefiniteKernel
  simpa [star_trivial] using hK

section Topology

variable [TopologicalSpace V] {f : ℝ≥0 → ℂ} {g : V → ℂ}

omit [AddCommGroup V] in
/-- Separated products are continuous when both factors are continuous. -/
theorem continuous_mul_time_spatial (hf : Continuous f) (hg : Continuous g) :
    Continuous fun p : ℝ≥0 × V => f p.1 * g p.2 :=
  (hf.comp continuous_fst).mul (hg.comp continuous_snd)

/-- Package the separated-product construction with continuity of the resulting BCR function. -/
theorem isSemigroupGroupPD_mul_time_spatial_and_continuous [StarAddMonoid V]
    (hfpd : IsPositiveDefinite f) (hgpd : IsPositiveDefinite g)
    (hstar : ∀ v : V, star v = -v) (hfcont : Continuous f) (hgcont : Continuous g) :
    IsSemigroupGroupPD (fun p : ℝ≥0 × V => f p.1 * g p.2) ∧
      Continuous (fun p : ℝ≥0 × V => f p.1 * g p.2) :=
  ⟨isSemigroupGroupPD_mul_time_spatial hfpd hgpd hstar,
    continuous_mul_time_spatial hfcont hgcont⟩

/-- Kernel-supplied version of the separated-product construction, packaged with continuity. -/
theorem isSemigroupGroupPD_mul_time_spatial_of_kernels_and_continuous
    (hf : IsPositiveDefiniteKernel fun t u : ℝ≥0 => f (t + u))
    (hg : IsPositiveDefiniteKernel fun v w : V => g (v - w))
    (hfcont : Continuous f) (hgcont : Continuous g) :
    IsSemigroupGroupPD (fun p : ℝ≥0 × V => f p.1 * g p.2) ∧
      Continuous (fun p : ℝ≥0 × V => f p.1 * g p.2) :=
  ⟨isSemigroupGroupPD_mul_time_spatial_of_kernels hf hg,
    continuous_mul_time_spatial hfcont hgcont⟩

end Topology

end TauCeti
