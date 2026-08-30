/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Extension
public import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# The `Lᵖ` translation estimate on `W^{1,p}_0`

This file transports the **translation estimate** to Sobolev functions: for `1 ≤ p < ∞` and a
vector `h`,

`‖u(· + h) - u‖_p ≤ ‖h‖ ‖∇u‖_p`.

It is the quantitative form of the continuity of translation in `Lᵖ`, with a modulus that is
linear in `‖h‖` and controlled by one Sobolev seminorm.  The ambient space is any
finite-dimensional real inner product space `E` carrying an arbitrary additive Haar measure `mu`,
not just `ℝⁿ` with Lebesgue measure; `ℝⁿ` is used informally below for the whole-space case
`Ω = ⊤`.  Together with the extension of a `W^{1,p}_0(Ω)` function by zero, it supplies the
*uniform smallness of translations* hypothesis of the Fréchet--Kolmogorov compactness criterion,
and so is the analytic input for Rellich--Kondrachov, Lane A.6 of
`TauCetiRoadmap/PDE/README.md`.

## The estimate on `W^{1,p}_0(ℝⁿ)`

`TauCeti.W1p.eLpNorm_value_comp_add_sub_value_le_mul_enorm_gradient` transports the `C¹` estimate
from `TauCeti.MeasureTheory.Function.Lp.Translation` to the Sobolev space by density. The set of
jets satisfying it is closed — the translation increment is a continuous function of the `Lᵖ`
class, being the difference of the identity and the isometry induced by a measure-preserving map
— and it contains every test-function jet, so
`TauCeti.w1p0Submodule_subset_of_isClosed` gives it on all of `W^{1,p}_0(ℝⁿ)`.  Note that the
whole space is where a translation estimate can be stated without further data: translating a
function defined on a proper open `Ω` moves it off `Ω`, so the general case is this statement
composed with an extension of `W^{1,p}_0(Ω)` by zero.

The theorem assumes membership in `W^{1,p}_0(ℝⁿ)`, the closure of the test functions, because
test-function density is the available route to the whole-space estimate. Since `Ω = ⊤` has no
boundary, this is not an additional boundary condition. For a proper `Ω`, however, transferring
the estimate by zero extension does require `W^{1,p}_0(Ω)`: the zero-extension of a general
Sobolev function need not be weakly differentiable across `∂Ω`. A local form on `W^{1,p}(Ω)`
survives on compactly contained subsets for translations smaller than their distance to the
boundary.

## Main declarations

* `TauCeti.W1p.eLpNorm_value_comp_add_sub_value_le_mul_enorm_gradient`: the translation estimate
  on `W^{1,p}_0(ℝⁿ)`.
* `TauCeti.W1p0.eLpNorm_value_extendByZeroL_comp_add_sub_le_mul_enorm_gradient`: the same estimate
  for an arbitrary open `Ω`, stated for the extension by zero.

## References

Lane A.6 of `TauCetiRoadmap/PDE/README.md`; H. Brezis, *Functional Analysis, Sobolev Spaces and
Partial Differential Equations*, Proposition 9.3, for the estimate, and Theorem 4.26 for the
Fréchet--Kolmogorov criterion it feeds; L. C. Evans, *Partial Differential Equations*,
Chapter 5, for the difference-quotient form of the same bound.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace

section Sobolev

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

/-- Translation of an `Lᵖ` class on the whole space, as a linear isometry.  It is used only to
see the translation increment as a *continuous* function of the class, which is what makes the
translation estimate a closed condition. -/
private def translateLp (mu : Measure E) [mu.IsAddHaarMeasure] (p : ENNReal) [Fact (1 ≤ p)]
    (h : E) :
    Lp ℝ p (mu.restrict ((⊤ : Opens E) : Set E)) →ₗᵢ[ℝ]
      Lp ℝ p (mu.restrict ((⊤ : Opens E) : Set E)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (· + h) <| by
    rw [Opens.coe_top, Measure.restrict_univ]
    exact measurePreserving_add_right mu h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The `Lᵖ` seminorm of a translation increment, computed on the ambient measure. -/
private theorem enorm_translateLp_sub (h : E)
    (f : Lp ℝ p (mu.restrict ((⊤ : Opens E) : Set E))) :
    ‖translateLp mu p h f - f‖ₑ = eLpNorm (fun x => f (x + h) - f x) p mu := by
  have htop : mu.restrict ((⊤ : Opens E) : Set E) = mu := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hmp : MeasurePreserving (· + h) (mu.restrict ((⊤ : Opens E) : Set E))
      (mu.restrict ((⊤ : Opens E) : Set E)) := by
    rw [htop]
    exact measurePreserving_add_right mu h
  have htr : ⇑(translateLp mu p h f) =ᵐ[mu.restrict ((⊤ : Opens E) : Set E)]
      ⇑f ∘ (· + h) :=
    Lp.coeFn_compMeasurePreserving f hmp
  have hae : ⇑(translateLp mu p h f - f) =ᵐ[mu.restrict ((⊤ : Opens E) : Set E)]
      fun x => f (x + h) - f x := by
    filter_upwards [Lp.coeFn_sub (translateLp mu p h f) f, htr] with x hx hy
    rw [hx, Pi.sub_apply, hy]
    rfl
  rw [Lp.enorm_def, eLpNorm_congr_ae hae]
  exact congrArg (fun nu : Measure E => eLpNorm (fun x => f (x + h) - f x) p nu) htop

/-- The translation estimate for a single test function, in the shape the jets of `W^{1,p}(ℝⁿ)`
present it. -/
private theorem eLpNorm_testFunctionLp_comp_add_sub_testFunctionLp_le (hp : p ≠ ∞) (h : E)
    (phi : 𝓓((⊤ : Opens E), ℝ)) :
    eLpNorm (fun x => testFunctionLp (mu := mu) p phi (x + h)
        - testFunctionLp (mu := mu) p phi x) p mu
      ≤ ‖h‖ₑ * ‖gradientTestFunctionLp (mu := mu) p phi‖ₑ := by
  have hvalue : ⇑(testFunctionLp (mu := mu) p phi) =ᵐ[mu] (phi : E → ℝ) :=
    (testFunctionLp_apply_ae p phi).filter_mono
      (ae_mono (by rw [Opens.coe_top, Measure.restrict_univ]))
  have htrans := hvalue.comp_tendsto
    (measurePreserving_add_right mu h).quasiMeasurePreserving.tendsto_ae
  have hL : eLpNorm (fun x => testFunctionLp (mu := mu) p phi (x + h)
        - testFunctionLp (mu := mu) p phi x) p mu
      = eLpNorm (fun x => (phi : E → ℝ) (x + h) - phi x) p mu := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [hvalue, htrans] with x h1 h2
    rw [h1]
    exact congrArg (· - phi x) h2
  rw [hL, enorm_gradientTestFunctionLp_eq_eLpNorm_fderiv]
  exact eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv
    (phi.contDiff.of_le (by simp)) Fact.out hp h

/-- **The translation estimate on `W^{1,p}_0(ℝⁿ)`**: for `1 ≤ p < ∞`, every `u` in the closure of
the test functions satisfies

`‖u(· + h) - u‖_p ≤ ‖h‖ ‖∇u‖_p`.

The estimate for a single test function comes from
`TauCeti.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv`; the set of jets obeying it is closed, so
`TauCeti.w1p0Submodule_subset_of_isClosed` passes it to the closure. Composing with a
zero-extension operator turns this into the corresponding estimate on `W^{1,p}_0(Ω)` for an
arbitrary open `Ω`, which is the form the Fréchet--Kolmogorov compactness criterion consumes in
the proof of Rellich--Kondrachov. -/
theorem W1p.eLpNorm_value_comp_add_sub_value_le_mul_enorm_gradient (hp : p ≠ ∞) (h : E)
    {u : W1p mu ⊤ p}
    (hu : u ∈ w1p0Submodule mu ⊤ p) :
    eLpNorm (fun x => W1p.value u (x + h) - W1p.value u x) p mu
      ≤ ‖h‖ₑ * ‖W1p.gradient u‖ₑ := by
  have hrw : ∀ v : W1p mu (⊤ : Opens E) p,
      eLpNorm (fun x => W1p.value v (x + h) - W1p.value v x) p mu
        = ‖translateLp mu p h (W1p.valueL v) - W1p.valueL v‖ₑ := fun v => by
    rw [enorm_translateLp_sub, W1p.valueL_apply]
  have hclosed : IsClosed {v : W1p mu ⊤ p |
      eLpNorm (fun x => W1p.value v (x + h) - W1p.value v x) p mu
        ≤ ‖h‖ₑ * ‖W1p.gradient v‖ₑ} := by
    simp only [hrw, ← W1p.gradientL_apply]
    exact isClosed_le
      ((((translateLp mu p h).toContinuousLinearMap.comp W1p.valueL) -
        W1p.valueL).continuous.enorm)
      ((ENNReal.continuous_const_mul (by finiteness)).comp
        W1p.gradientL.continuous.enorm)
  refine w1p0Submodule_subset_of_isClosed hclosed (fun phi => ?_) hu
  simpa only [Set.mem_ofPred_eq, W1p.value_ofTestFunctionₗ, W1p.gradient_ofTestFunctionₗ] using
    eLpNorm_testFunctionLp_comp_add_sub_testFunctionLp_le hp h phi

/-- **The translation estimate on `W^{1,p}_0(Ω)` for an arbitrary open `Ω`**: for `1 ≤ p < ∞`,
the extension by zero of `u ∈ W^{1,p}_0(Ω)` satisfies

`‖u(· + h) - u‖_p ≤ ‖h‖ ‖∇u‖_p`

on the whole space.  This is the whole-space estimate
`TauCeti.W1p.eLpNorm_value_comp_add_sub_value_le_mul_enorm_gradient` composed with the
zero-extension operator `TauCeti.W1p0.extendByZeroL`.  Extension by zero is an isometry on the
gradient component, so the right-hand side is the gradient seminorm of `u` on `Ω` itself and
nothing is lost in the transfer.  This is the form the Fréchet--Kolmogorov criterion consumes in
the proof of Rellich--Kondrachov. -/
theorem W1p0.eLpNorm_value_extendByZeroL_comp_add_sub_le_mul_enorm_gradient {Omega : Opens E}
    (hp : p ≠ ∞) (h : E) (u : W1p0 mu Omega p) :
    eLpNorm (fun x => W1p.value (W1p0.extendByZeroL le_top u : W1p mu ⊤ p) (x + h) -
        W1p.value (W1p0.extendByZeroL le_top u : W1p mu ⊤ p) x) p mu
      ≤ ‖h‖ₑ * ‖W1p.gradient (u : W1p mu Omega p)‖ₑ := by
  refine (W1p.eLpNorm_value_comp_add_sub_value_le_mul_enorm_gradient hp h
    (W1p0.extendByZeroL le_top u).2).trans_eq ?_
  congr 1
  rw [W1p0.gradient_extendByZeroL]
  exact enorm_eq_iff_norm_eq.2 ((extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤))).norm_map _)

end Sobolev

end TauCeti
