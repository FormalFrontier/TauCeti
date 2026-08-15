/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Parseval
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Pi.Basis

/-!
# Parseval and expansions for the multi-index Hermite-function basis

`TauCeti.hermiteFunctionPiBasis` exhibits the multi-index Hermite functions
`Ψ_a(x) = ∏ᵢ ψ_{aᵢ}(xᵢ)` as a Hilbert basis of `L²(ℝ^ι)`. This file states the expansion
identities that basis was built for, phrased in the explicit tensors
`TauCeti.L2piMul fun i => TauCeti.hermiteFunctionLp 𝕜 (a i)` rather than the bundled basis, so
that a consumer never has to unfold `hermiteFunctionPiBasis` to expand a function of several
variables in Hermite functions. It is the `Fintype`-indexed analogue of
`TauCeti.tsum_norm_sq_inner_hermiteFunctionLp` and its neighbours.

At this arity the file additionally gives the coordinate as an integral, proves that its integrand
is integrable, and specializes `TauCeti.piHilbertBasis_repr_L2piMul` to show that the coordinates
of a product are the products of the one-dimensional Hermite coordinates.

## Main statements

* `TauCeti.hermiteFunctionPiBasis_repr_apply` — the `a`-th coordinate of `f` is `⟪Ψ_a, f⟫`.
* `TauCeti.hermiteFunctionPiBasis_repr_eq_integral` — the same coordinate as an integral against
  `∏ᵢ ψ_{aᵢ}(xᵢ)`, whose integrand is integrable by
  `TauCeti.integrable_prod_hermiteFunction_mul`.
* `TauCeti.hermiteFunctionPiBasis_repr_L2piMul` — the coordinates of a product function are the
  products of the one-dimensional coordinates.
* `TauCeti.tsum_inner_mul_inner_L2piMul_hermiteFunctionLp` — Parseval in polarized form.
* `TauCeti.tsum_norm_sq_inner_L2piMul_hermiteFunctionLp` — Parseval in norm-square form,
  `∑' a, ‖⟪Ψ_a, f⟫‖² = ‖f‖²`.
* `TauCeti.hasSum_L2piMul_hermiteFunctionLp_expansion` — the multi-index Hermite expansion
  `∑' a, ⟪Ψ_a, f⟫ • Ψ_a = f`.

Every statement holds for an arbitrary `RCLike` scalar field, so `𝕜 = ℝ` and `𝕜 = ℂ` are the same
theorem.
-/

public section

namespace TauCeti

open MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- The coordinates of `f` in the multi-index Hermite-function basis are its inner products
against the tensors `Ψ_a = ∏ᵢ ψ_{aᵢ}`. -/
@[simp]
theorem hermiteFunctionPiBasis_repr_apply
    (f : Lp 𝕜 2 (Measure.pi fun _ : ι => (volume : Measure ℝ))) (a : ι → ℕ) :
    (hermiteFunctionPiBasis 𝕜 ι).repr f a
      = inner 𝕜 (L2piMul fun i => hermiteFunctionLp 𝕜 (a i)) f := by
  simpa using (hermiteFunctionPiBasis 𝕜 ι).repr_apply_apply f a

/-- The integrand of the coordinate integral below is integrable: it is the pointwise inner product
of two `L²` functions. -/
theorem integrable_prod_hermiteFunction_mul
    (f : Lp 𝕜 2 (Measure.pi fun _ : ι => (volume : Measure ℝ))) (a : ι → ℕ) :
    Integrable (fun x : ι → ℝ => (∏ i, (algebraMap ℝ 𝕜) (hermiteFunction (a i) (x i))) * f x)
      (Measure.pi fun _ : ι => (volume : Measure ℝ)) := by
  refine (integrable_L2piMul_mul (fun i => hermiteFunctionLp 𝕜 (a i)) f).congr ?_
  filter_upwards [coeFn_L2piMul (fun i => hermiteFunctionLp 𝕜 (a i)),
    coeFn_hermiteFunctionPiBasis 𝕜 ι a] with x hprod hexplicit
  rw [← hprod, ← hermiteFunctionPiBasis_apply, hexplicit]

/-- The `a`-th multi-index Hermite coordinate of `f`, as an integral of `f` against the product
`∏ᵢ ψ_{aᵢ}(xᵢ)`. The Hermite functions are real, so no complex conjugate survives. -/
theorem hermiteFunctionPiBasis_repr_eq_integral
    (f : Lp 𝕜 2 (Measure.pi fun _ : ι => (volume : Measure ℝ))) (a : ι → ℕ) :
    (hermiteFunctionPiBasis 𝕜 ι).repr f a
      = ∫ x : ι → ℝ, (∏ i, (algebraMap ℝ 𝕜) (hermiteFunction (a i) (x i))) * f x
          ∂(Measure.pi fun _ : ι => (volume : Measure ℝ)) := by
  rw [(hermiteFunctionPiBasis 𝕜 ι).repr_apply_apply, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_hermiteFunctionPiBasis 𝕜 ι a] with x hx
  rw [hx]
  simp [RCLike.algebraMap_eq_ofReal, map_prod, mul_comm]

/-- **The multi-index coordinates of a product function factor.** If `f(x) = ∏ᵢ Fᵢ(xᵢ)` then its
`a`-th multi-index Hermite coordinate is the product of the `aᵢ`-th one-dimensional Hermite
coordinates of the factors — the statement that makes a multidimensional Hermite expansion of a
product function computable from one-dimensional ones. -/
theorem hermiteFunctionPiBasis_repr_L2piMul
    (F : ι → Lp 𝕜 2 (volume : Measure ℝ)) (a : ι → ℕ) :
    (hermiteFunctionPiBasis 𝕜 ι).repr (L2piMul F) a
      = ∏ i, inner 𝕜 (hermiteFunctionLp 𝕜 (a i)) (F i) := by
  rw [HilbertBasis.repr_apply_apply, hermiteFunctionPiBasis_apply]
  calc
    inner 𝕜 (L2piMul fun i => hermiteFunctionLp 𝕜 (a i)) (L2piMul F)
        = ∏ i, (hermiteHilbertBasis 𝕜).repr (F i) (a i) := by
          simpa only [HilbertBasis.repr_apply_apply, piHilbertBasis_apply,
            coe_hermiteHilbertBasis] using
              piHilbertBasis_repr_L2piMul (fun _ : ι => hermiteHilbertBasis 𝕜) F a
    _ = ∏ i, inner 𝕜 (hermiteFunctionLp 𝕜 (a i)) (F i) :=
      Finset.prod_congr rfl fun i _ => by
        rw [HilbertBasis.repr_apply_apply, coe_hermiteHilbertBasis]

/-- **Parseval's identity for the multi-index Hermite basis** (polarized form): the multi-index
Hermite coordinates of `f` and `g` pair to their inner product. -/
theorem tsum_inner_mul_inner_L2piMul_hermiteFunctionLp
    (f g : Lp 𝕜 2 (Measure.pi fun _ : ι => (volume : Measure ℝ))) :
    ∑' a : ι → ℕ, inner 𝕜 f (L2piMul fun i => hermiteFunctionLp 𝕜 (a i))
        * inner 𝕜 (L2piMul fun i => hermiteFunctionLp 𝕜 (a i)) g = inner 𝕜 f g := by
  simpa using (hermiteFunctionPiBasis 𝕜 ι).tsum_inner_mul_inner f g

/-- **Parseval's identity for the multi-index Hermite basis** (norm-square form): the squared
multi-index Hermite coordinates of `f` sum to `‖f‖²`. -/
theorem tsum_norm_sq_inner_L2piMul_hermiteFunctionLp
    (f : Lp 𝕜 2 (Measure.pi fun _ : ι => (volume : Measure ℝ))) :
    ∑' a : ι → ℕ, ‖inner 𝕜 (L2piMul fun i => hermiteFunctionLp 𝕜 (a i)) f‖ ^ 2 = ‖f‖ ^ 2 := by
  simpa using (hermiteFunctionPiBasis 𝕜 ι).tsum_norm_sq_inner f

/-- The squared multi-index Hermite coordinate family of an `L²(ℝ^ι)` function is summable. -/
theorem summable_norm_sq_inner_L2piMul_hermiteFunctionLp
    (f : Lp 𝕜 2 (Measure.pi fun _ : ι => (volume : Measure ℝ))) :
    Summable fun a : ι → ℕ => ‖inner 𝕜 (L2piMul fun i => hermiteFunctionLp 𝕜 (a i)) f‖ ^ 2 := by
  simpa using (hermiteFunctionPiBasis 𝕜 ι).summable_norm_sq_inner f

/-- **The multi-index Hermite expansion.** Every `f ∈ L²(ℝ^ι)` is the sum of its multi-index
Hermite series, summed over multi-indices `a : ι → ℕ` in the unordered sense. -/
theorem hasSum_L2piMul_hermiteFunctionLp_expansion
    (f : Lp 𝕜 2 (Measure.pi fun _ : ι => (volume : Measure ℝ))) :
    HasSum (fun a : ι → ℕ => inner 𝕜 (L2piMul fun i => hermiteFunctionLp 𝕜 (a i)) f
      • L2piMul fun i => hermiteFunctionLp 𝕜 (a i)) f := by
  simpa using (hermiteFunctionPiBasis 𝕜 ι).hasSum_repr f

end TauCeti
