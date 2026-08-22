/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.TestFunctionLp
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# First-order weak Sobolev spaces

This file constructs the first-order, real-valued Sobolev space `W^{1,p}(Ω)` on an open subset
of a finite-dimensional real inner product space.  An element is an `Lᵖ` value-gradient jet
`(u, ∇u)` satisfying the distributional integration-by-parts identity from
`TauCeti.HasWeakFDerivOn`.

The quotient issue is handled at the definition boundary.  Both components of a jet are `Lp`
classes for `μ.restrict Ω`; the weak relation is imposed by the continuous Hölder pairing with
the test jet

`(∂_v φ, φ v)`.

Consequently the admissible jets form an intersection of kernels of continuous linear
functionals.  This makes `TauCeti.W1p` a closed subspace of the ambient Bochner `Lᵖ` space, and
hence complete.  The theorem `TauCeti.mem_w1pSubmodule_iff_hasWeakFDerivOn` identifies this closed
subspace definition with the weak-derivative predicate, so the construction does not replace the
distributional condition by a merely formal closedness assumption.

The pointwise jet uses the Euclidean product norm on `ℝ × E`.  Thus at `p = 2` the inherited norm
is the usual Hilbert norm

`(∥u∥²₂ + ∥∇u∥²₂)¹⁄²`,

which is the space needed by the energy-method lane of the PDE roadmap.  No boundedness or
boundary regularity of `Ω` is used.

## Main declarations

* `TauCeti.Sobolev1Jet`: the value-gradient fibre `ℝ × E` with its Euclidean product norm.
* `TauCeti.w1pSubmodule`: the closed subspace of jets annihilating every weak-derivative test.
* `TauCeti.W1p`: the corresponding complete normed space.
* `TauCeti.mem_w1pSubmodule_iff_hasWeakFDerivOn`: membership is exactly weak
  differentiability of the value component with the recorded gradient.
* `TauCeti.W1p.valueL` and `TauCeti.W1p.gradientL`: the two components as continuous linear
  projections from the Sobolev space.

## References

This is the first-order part of Lane A.1 of `TauCetiRoadmap/PDE/README.md`.  The graph-space
construction and completeness argument follow L. C. Evans, *Partial Differential Equations*,
Chapter 5, §5.2.  The continuous annihilator presentation is the quotient-respecting version of
the standard proof that weak differentiation is a closed operator on `Lᵖ`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 <= p)]

/-- The fibre of a first-order scalar Sobolev jet: a value and its gradient, with the Euclidean
product norm. -/
abbrev Sobolev1Jet (E : Type*) :=
  WithLp 2 (ℝ × E)

/-- The ambient Bochner `Lᵖ` space of value-gradient jets on `Ω`. -/
abbrev Sobolev1JetLp (mu : Measure E) (Omega : Opens E) (p : ENNReal) :=
  Lp (Sobolev1Jet E) p (mu.restrict Omega)

/-- The continuous linear projection from an `Lᵖ` Sobolev jet to its value component. -/
def Sobolev1JetLp.valueL :
    Sobolev1JetLp mu Omega p →L[ℝ] Lp ℝ p (mu.restrict Omega) :=
  (WithLp.fstL 2 ℝ ℝ E).compLpL p (mu.restrict Omega)

/-- The value component of an `Lᵖ` Sobolev jet. -/
def Sobolev1JetLp.value (J : Sobolev1JetLp mu Omega p) : Lp ℝ p (mu.restrict Omega) :=
  Sobolev1JetLp.valueL J

/-- The continuous linear projection from an `Lᵖ` Sobolev jet to its gradient component. -/
def Sobolev1JetLp.gradientL :
    Sobolev1JetLp mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
  (WithLp.sndL 2 ℝ ℝ E).compLpL p (mu.restrict Omega)

/-- The gradient component of an `Lᵖ` Sobolev jet. -/
def Sobolev1JetLp.gradient (J : Sobolev1JetLp mu Omega p) : Lp E p (mu.restrict Omega) :=
  Sobolev1JetLp.gradientL J

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
@[simp]
theorem Sobolev1JetLp.value_apply_ae (J : Sobolev1JetLp mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      Sobolev1JetLp.value J x = WithLp.fst (J x) := by
  -- `coeFn_compLp` is stated for the unbundled `compLp`; expose that implementation of
  -- `valueL` so its pointwise theorem applies.
  change ∀ᵐ x ∂mu.restrict Omega,
    (WithLp.fstL 2 ℝ ℝ E).compLp J x = (WithLp.fstL 2 ℝ ℝ E) (J x)
  exact (WithLp.fstL 2 ℝ ℝ E).coeFn_compLp J

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
@[simp]
theorem Sobolev1JetLp.gradient_apply_ae (J : Sobolev1JetLp mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      Sobolev1JetLp.gradient J x = WithLp.snd (J x) := by
  -- As for `value_apply_ae`, expose the unbundled `compLp` implementation consumed by
  -- Mathlib's pointwise coercion theorem.
  change ∀ᵐ x ∂mu.restrict Omega,
    (WithLp.sndL 2 ℝ ℝ E).compLp J x = (WithLp.sndL 2 ℝ ℝ E) (J x)
  exact (WithLp.sndL 2 ℝ ℝ E).coeFn_compLp J

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- Two Sobolev jets are equal when their value and gradient components are equal. -/
@[ext]
theorem Sobolev1JetLp.ext {J K : Sobolev1JetLp mu Omega p}
    (hvalue : Sobolev1JetLp.value J = Sobolev1JetLp.value K)
    (hgradient : Sobolev1JetLp.gradient J = Sobolev1JetLp.gradient K) : J = K := by
  apply Lp.ext
  have hvalue_ae : Sobolev1JetLp.value J =ᵐ[mu.restrict Omega]
      Sobolev1JetLp.value K := by
    rwa [← Lp.ext_iff]
  have hgradient_ae : Sobolev1JetLp.gradient J =ᵐ[mu.restrict Omega]
      Sobolev1JetLp.gradient K := by
    rwa [← Lp.ext_iff]
  filter_upwards [Sobolev1JetLp.value_apply_ae J, Sobolev1JetLp.value_apply_ae K,
    Sobolev1JetLp.gradient_apply_ae J, Sobolev1JetLp.gradient_apply_ae K,
    hvalue_ae, hgradient_ae] with x hJvalue hKvalue hJgradient hKgradient hvalue hgradient
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).injective
  apply Prod.ext
  · simpa only [WithLp.prodContinuousLinearEquiv_apply, WithLp.fst, hJvalue, hKvalue] using hvalue
  · simpa only [WithLp.prodContinuousLinearEquiv_apply, WithLp.snd, hJgradient, hKgradient]
      using hgradient

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- The norm of the value component is bounded by the norm of the ambient Sobolev jet. -/
private theorem norm_value_le_ambient (J : Sobolev1JetLp mu Omega p) :
    ‖Sobolev1JetLp.value J‖ ≤ ‖J‖ := by
  have hfst : ‖WithLp.fstL 2 ℝ ℝ E‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simpa only [WithLp.fstL_apply, one_mul] using WithLp.norm_fst_le ℝ x
  have hvalueL : ‖Sobolev1JetLp.valueL (mu := mu) (Omega := Omega) (p := p)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le (WithLp.fstL 2 ℝ ℝ E)).trans hfst
  calc
    ‖Sobolev1JetLp.value J‖ ≤
        ‖Sobolev1JetLp.valueL (mu := mu) (Omega := Omega) (p := p)‖ * ‖J‖ :=
      (Sobolev1JetLp.valueL (mu := mu) (Omega := Omega) (p := p)).le_opNorm J
    _ ≤ 1 * ‖J‖ := mul_le_mul_of_nonneg_right hvalueL (norm_nonneg J)
    _ = ‖J‖ := one_mul _

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- The norm of the gradient component is bounded by the norm of the ambient Sobolev jet. -/
private theorem norm_gradient_le_ambient (J : Sobolev1JetLp mu Omega p) :
    ‖Sobolev1JetLp.gradient J‖ ≤ ‖J‖ := by
  have hsnd : ‖WithLp.sndL 2 ℝ ℝ E‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simpa only [WithLp.sndL_apply, one_mul] using WithLp.norm_snd_le ℝ x
  have hgradientL : ‖Sobolev1JetLp.gradientL (mu := mu) (Omega := Omega) (p := p)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le (WithLp.sndL 2 ℝ ℝ E)).trans hsnd
  calc
    ‖Sobolev1JetLp.gradient J‖ ≤
        ‖Sobolev1JetLp.gradientL (mu := mu) (Omega := Omega) (p := p)‖ * ‖J‖ :=
      (Sobolev1JetLp.gradientL (mu := mu) (Omega := Omega) (p := p)).le_opNorm J
    _ ≤ 1 * ‖J‖ := mul_le_mul_of_nonneg_right hgradientL (norm_nonneg J)
    _ = ‖J‖ := one_mul _

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- At exponent two, the Sobolev jet norm is the Hilbert graph norm of its components. -/
private theorem norm_sq_eq_norm_value_sq_add_norm_gradient_sq_ambient
    (J : Sobolev1JetLp mu Omega 2) :
    ‖J‖ ^ 2 = ‖Sobolev1JetLp.value J‖ ^ 2 + ‖Sobolev1JetLp.gradient J‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq J,
    ← real_inner_self_eq_norm_sq (Sobolev1JetLp.value J),
    ← real_inner_self_eq_norm_sq (Sobolev1JetLp.gradient J),
    L2.inner_def, L2.inner_def, L2.inner_def,
    ← integral_add (L2.integrable_inner (Sobolev1JetLp.value J) (Sobolev1JetLp.value J))
      (L2.integrable_inner (Sobolev1JetLp.gradient J) (Sobolev1JetLp.gradient J))]
  apply integral_congr_ae
  filter_upwards [Sobolev1JetLp.value_apply_ae J,
    Sobolev1JetLp.gradient_apply_ae J] with x hvalue hgradient
  rw [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, ← hvalue, ← hgradient]

/-- The candidate weak Fréchet derivative recorded by the gradient component of a Sobolev jet. -/
def Sobolev1JetLp.candidateWeakFDeriv (J : Sobolev1JetLp mu Omega p) : E → E →L[ℝ] ℝ :=
  fun x => innerSL ℝ (Sobolev1JetLp.gradient J x)

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
@[simp]
theorem Sobolev1JetLp.candidateWeakFDeriv_apply (J : Sobolev1JetLp mu Omega p) (x v : E) :
    Sobolev1JetLp.candidateWeakFDeriv J x v = ⟪v, Sobolev1JetLp.gradient J x⟫_ℝ := by
  rw [Sobolev1JetLp.candidateWeakFDeriv, innerSL_apply_apply, real_inner_comm]

private def weakDerivativeTestFunction (phi : 𝓓(Omega, ℝ)) (v : E) (x : E) :
    Sobolev1Jet E :=
  WithLp.toLp 2 (lineDeriv ℝ (phi : E → ℝ) x v, phi x • v)

omit [FiniteDimensional ℝ E] in
private theorem weakDerivativeTestFunction_memLp (q : ENNReal) (phi : 𝓓(Omega, ℝ)) (v : E) :
    MemLp (weakDerivativeTestFunction phi v) q (mu.restrict Omega) := by
  have hdphi : ((TestFunction.lineDerivCLM ℝ v phi : 𝓓(Omega, ℝ)) : E → ℝ) =
      fun x => lineDeriv ℝ (phi : E → ℝ) x v :=
    funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
  have hsmul : MemLp (fun x => (phi : E → ℝ) x • v) q (mu.restrict Omega) :=
    (phi.continuous.smul continuous_const).memLp_of_hasCompactSupport
      (phi.hasCompactSupport.mono fun x hx hzero => hx (by simp [hzero]))
  -- A jet is `Lᵠ` exactly when both of its coordinates are, and both are test-function multiples.
  refine MemLp.of_fst_of_snd_prodLp ⟨?_, ?_⟩ <;>
    simp only [weakDerivativeTestFunction, WithLp.toLp_fst, WithLp.toLp_snd]
  · have hmem := memLp_testFunction (mu := mu) q (TestFunction.lineDerivCLM ℝ v phi)
    rwa [hdphi] at hmem
  · exact hsmul

/-- The compactly supported jet `(∂_v φ, φ v)` used to test whether an `Lᵖ` jet is a weak
derivative.  Its exponent is Hölder-conjugate to `p`, including the endpoints `p = 1, ∞`. -/
private def weakDerivativeTestJet (p : ENNReal) (phi : 𝓓(Omega, ℝ)) (v : E) :
    Lp (Sobolev1Jet E) (ENNReal.conjExponent p) (mu.restrict Omega) :=
  (weakDerivativeTestFunction_memLp (mu := mu) (ENNReal.conjExponent p) phi v).toLp
    (weakDerivativeTestFunction phi v)

omit [FiniteDimensional ℝ E] in
@[simp]
private theorem weakDerivativeTestJet_apply_ae (p : ENNReal) (phi : 𝓓(Omega, ℝ)) (v : E) :
    ∀ᵐ x ∂mu.restrict Omega,
      weakDerivativeTestJet (mu := mu) p phi v x =
        WithLp.toLp 2 (lineDeriv ℝ (phi : E → ℝ) x v, phi x • v) := by
  filter_upwards [MemLp.coeFn_toLp (weakDerivativeTestFunction_memLp (mu := mu)
    (ENNReal.conjExponent p) phi v)] with x hx
  simpa only [weakDerivativeTestJet, weakDerivativeTestFunction] using hx

/-- The continuous functional expressing the weak-derivative identity against `φ` in direction
`v`.  It pairs the candidate jet with `(∂_v φ, φ v)`. -/
private def weakDerivativeTestFunctional (p : ENNReal) [Fact (1 <= p)]
    (phi : 𝓓(Omega, ℝ)) (v : E) : Sobolev1JetLp mu Omega p →L[ℝ] ℝ := by
  let _ : (ENNReal.conjExponent p).HolderConjugate p := ENNReal.HolderConjugate.symm
  let _ : Fact (1 <= ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le _ p⟩
  exact ((innerSL ℝ (E := Sobolev1Jet E)).lpPairing (mu.restrict Omega) p
    (ENNReal.conjExponent p)).flip (weakDerivativeTestJet (mu := mu) p phi v)

omit [FiniteDimensional ℝ E] in
/-- The test functional is the sum of the value and candidate-gradient terms in the weak
integration-by-parts identity. -/
private theorem weakDerivativeTestFunctional_apply (J : Sobolev1JetLp mu Omega p)
    (phi : 𝓓(Omega, ℝ)) (v : E) :
    weakDerivativeTestFunctional (mu := mu) p phi v J =
      ∫ x in Omega, (lineDeriv ℝ (phi : E → ℝ) x v * Sobolev1JetLp.value J x +
        phi x * Sobolev1JetLp.candidateWeakFDeriv J x v) ∂mu := by
  let _ : (ENNReal.conjExponent p).HolderConjugate p := ENNReal.HolderConjugate.symm
  let _ : Fact (1 <= ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le _ p⟩
  -- Unfold the private test functional to the `lpPairing` form required by its integral theorem.
  change (innerSL ℝ (E := Sobolev1Jet E)).lpPairing (mu.restrict Omega) p
      (ENNReal.conjExponent p) J (weakDerivativeTestJet (mu := mu) p phi v) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [weakDerivativeTestJet_apply_ae (mu := mu) p phi v,
    Sobolev1JetLp.value_apply_ae J, Sobolev1JetLp.gradient_apply_ae J] with x htest hvalue hgradient
  rw [htest, innerSL_apply_apply, WithLp.prod_inner_apply,
    Sobolev1JetLp.candidateWeakFDeriv_apply, hvalue, hgradient]
  simp only [WithLp.ofLp_fst, RCLike.inner_apply, conj_trivial, WithLp.ofLp_snd,
    add_right_inj]
  rw [inner_smul_right, real_inner_comm]

/-- The first-order weak Sobolev subspace.  It consists of the `Lᵖ` value-gradient jets that
annihilate every test jet `(∂_v φ, φ v)`. -/
def w1pSubmodule (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] : ClosedSubmodule ℝ (Sobolev1JetLp mu Omega p) :=
  ⨅ phi : 𝓓(Omega, ℝ), ⨅ v : E,
    (⊥ : ClosedSubmodule ℝ ℝ).comap (weakDerivativeTestFunctional (mu := mu) p phi v)

omit [FiniteDimensional ℝ E] in
/-- Membership in `w1pSubmodule` is the family of weak integration-by-parts identities. -/
theorem mem_w1pSubmodule_iff (J : Sobolev1JetLp mu Omega p) :
    J ∈ w1pSubmodule mu Omega p ↔
      ∀ (phi : 𝓓(Omega, ℝ)) (v : E),
        ∫ x in Omega, (lineDeriv ℝ (phi : E → ℝ) x v * Sobolev1JetLp.value J x +
          phi x * Sobolev1JetLp.candidateWeakFDeriv J x v) ∂mu = 0 := by
  -- Pass through the private kernel presentation once, keeping it out of the public statement.
  rw [show J ∈ w1pSubmodule mu Omega p ↔
      ∀ (phi : 𝓓(Omega, ℝ)) (v : E),
        weakDerivativeTestFunctional (mu := mu) p phi v J = 0 by
    simp [w1pSubmodule]]
  simp only [weakDerivativeTestFunctional_apply]

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
private theorem testIntegral_eq_zero_iff
    (f f' : E → ℝ) (hf : LocallyIntegrableOn f Omega mu)
    (hf' : LocallyIntegrableOn f' Omega mu) (phi : 𝓓(Omega, ℝ)) (v : E) :
    (∫ x in Omega,
        lineDeriv ℝ (phi : E → ℝ) x v * f x + phi x * f' x ∂mu) = 0 ↔
      (∫ x, lineDeriv ℝ (phi : E → ℝ) x v • f x ∂mu) =
        -(∫ x, phi x • f' x ∂mu) := by
  have hleft : Integrable (fun x => lineDeriv ℝ (phi : E → ℝ) x v * f x) mu := by
    simpa only [smul_eq_mul] using integrable_lineDeriv_smul_of_locallyIntegrableOn hf phi v
  have hright : Integrable (fun x => phi x * f' x) mu := by
    simpa only [smul_eq_mul] using integrable_smul_of_locallyIntegrableOn hf' phi
  rw [integral_add hleft.integrableOn hright.integrableOn]
  simp only [← smul_eq_mul]
  rw [setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
    setIntegral_smul_eq_integral_smul]
  constructor <;> intro h <;> linarith

/-- A jet belongs to `w1pSubmodule` exactly when its value component has the recorded gradient as
its weak Fréchet derivative. -/
theorem mem_w1pSubmodule_iff_hasWeakFDerivOn (J : Sobolev1JetLp mu Omega p) :
    J ∈ w1pSubmodule mu Omega p ↔
      HasWeakFDerivOn mu Omega (Sobolev1JetLp.value J)
        (Sobolev1JetLp.candidateWeakFDeriv J) := by
  have hvalue : LocallyIntegrableOn (Sobolev1JetLp.value J) Omega mu :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (Sobolev1JetLp.value J)).locallyIntegrable Fact.out)
  have hderiv (v : E) : LocallyIntegrableOn
      (fun x => Sobolev1JetLp.candidateWeakFDeriv J x v) Omega mu := by
    apply locallyIntegrableOn_of_locallyIntegrable_restrict
    have hinner := (Lp.memLp (Sobolev1JetLp.gradient J)).const_inner (𝕜 := ℝ) v
    exact (hinner.locallyIntegrable Fact.out).congr <| by
      filter_upwards with x
      simp only [Sobolev1JetLp.candidateWeakFDeriv_apply]
  rw [mem_w1pSubmodule_iff]
  constructor
  · intro h
    rw [hasWeakFDerivOn_iff]
    intro v
    rw [hasWeakLineDerivOn_iff_testFunction]
    refine ⟨inferInstance, hvalue, hderiv v, fun phi => ?_⟩
    exact (testIntegral_eq_zero_iff _ _ hvalue (hderiv v) phi v).mp (h phi v)
  · intro h
    rw [hasWeakFDerivOn_iff] at h
    intro phi v
    exact (testIntegral_eq_zero_iff _ _ (h v).locallyIntegrableOn
      (h v).locallyIntegrableOn_deriv phi v).mpr
        ((h v).integral_lineDeriv_smul_eq_neg_integral_smul phi)

/-- The first-order, real-valued weak Sobolev space `W^{1,p}(Ω)`, represented by its value and
weak gradient. -/
abbrev W1p (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] := (w1pSubmodule mu Omega p).toSubmodule

/-- The continuous linear projection from `W1p` to its `Lᵖ` value component. -/
def W1p.valueL : W1p mu Omega p →L[ℝ] Lp ℝ p (mu.restrict Omega) :=
  Sobolev1JetLp.valueL.comp (w1pSubmodule mu Omega p).toSubmodule.subtypeL

/-- The `Lᵖ` value component of a Sobolev function. -/
def W1p.value (u : W1p mu Omega p) : Lp ℝ p (mu.restrict Omega) :=
  W1p.valueL u

omit [FiniteDimensional ℝ E] in
@[simp]
theorem W1p.valueL_apply (u : W1p mu Omega p) : W1p.valueL u = W1p.value u := (rfl)

/-- The continuous linear projection from `W1p` to its `Lᵖ` weak-gradient component. -/
def W1p.gradientL : W1p mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
  Sobolev1JetLp.gradientL.comp (w1pSubmodule mu Omega p).toSubmodule.subtypeL

/-- The `Lᵖ` weak-gradient component of a Sobolev function. -/
def W1p.gradient (u : W1p mu Omega p) : Lp E p (mu.restrict Omega) :=
  W1p.gradientL u

omit [FiniteDimensional ℝ E] in
@[simp]
theorem W1p.gradientL_apply (u : W1p mu Omega p) : W1p.gradientL u = W1p.gradient u := (rfl)

omit [FiniteDimensional ℝ E] in
/-- The Sobolev value component agrees almost everywhere with the first component of its
ambient value-gradient jet. -/
theorem W1p.value_apply_ae (u : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      W1p.value u x = WithLp.fst ((u : Sobolev1JetLp mu Omega p) x) := by
  -- `W1p.valueL` is the ambient jet projection precomposed with the inclusion, so the two
  -- value components are the same `Lᵖ` class; name that equation instead of relying on it
  -- silently.
  have hvalue : W1p.value u = Sobolev1JetLp.value (u : Sobolev1JetLp mu Omega p) := (rfl)
  rw [hvalue]
  exact Sobolev1JetLp.value_apply_ae (u : Sobolev1JetLp mu Omega p)

omit [FiniteDimensional ℝ E] in
/-- The Sobolev gradient component agrees almost everywhere with the second component of its
ambient value-gradient jet. -/
theorem W1p.gradient_apply_ae (u : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      W1p.gradient u x = WithLp.snd ((u : Sobolev1JetLp mu Omega p) x) := by
  -- As for `W1p.value_apply_ae`: the Sobolev gradient is the ambient jet gradient of the
  -- underlying jet, so record that equation before appealing to the ambient lemma.
  have hgradient : W1p.gradient u = Sobolev1JetLp.gradient (u : Sobolev1JetLp mu Omega p) :=
    (rfl)
  rw [hgradient]
  exact Sobolev1JetLp.gradient_apply_ae (u : Sobolev1JetLp mu Omega p)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure]
    [Fact (1 <= p)] in
private theorem memLp_assembleSobolev1Jet (u : Lp ℝ p (mu.restrict Omega))
    (g : Lp E p (mu.restrict Omega)) :
    MemLp (fun x => WithLp.toLp 2 (u x, g x)) p (mu.restrict Omega) := by
  apply MemLp.of_fst_of_snd_prodLp
  exact ⟨by simpa only [WithLp.toLp_fst] using Lp.memLp u,
    by simpa only [WithLp.toLp_snd] using Lp.memLp g⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
private def assembleSobolev1JetLp (u : Lp ℝ p (mu.restrict Omega))
    (g : Lp E p (mu.restrict Omega)) : Sobolev1JetLp mu Omega p :=
  (memLp_assembleSobolev1Jet u g).toLp fun x => WithLp.toLp 2 (u x, g x)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure]
    [Fact (1 <= p)] in
private theorem assembleSobolev1JetLp_apply_ae (u : Lp ℝ p (mu.restrict Omega))
    (g : Lp E p (mu.restrict Omega)) :
    ∀ᵐ x ∂mu.restrict Omega,
      assembleSobolev1JetLp u g x = WithLp.toLp 2 (u x, g x) := by
  exact (memLp_assembleSobolev1Jet u g).coeFn_toLp

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
@[simp]
private theorem value_assembleSobolev1JetLp (u : Lp ℝ p (mu.restrict Omega))
    (g : Lp E p (mu.restrict Omega)) :
    Sobolev1JetLp.value (assembleSobolev1JetLp u g) = u := by
  apply Lp.ext
  filter_upwards [Sobolev1JetLp.value_apply_ae (assembleSobolev1JetLp u g),
    assembleSobolev1JetLp_apply_ae u g] with x hvalue hassemble
  simpa only [hassemble, WithLp.toLp_fst] using hvalue

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
@[simp]
private theorem gradient_assembleSobolev1JetLp (u : Lp ℝ p (mu.restrict Omega))
    (g : Lp E p (mu.restrict Omega)) :
    Sobolev1JetLp.gradient (assembleSobolev1JetLp u g) = g := by
  apply Lp.ext
  filter_upwards [Sobolev1JetLp.gradient_apply_ae (assembleSobolev1JetLp u g),
    assembleSobolev1JetLp_apply_ae u g] with x hgradient hassemble
  simpa only [hassemble, WithLp.toLp_snd] using hgradient

/-- Construct a Sobolev function from its `Lᵖ` value and weak-gradient components. -/
def W1p.mk (u : Lp ℝ p (mu.restrict Omega)) (g : Lp E p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (g x))) : W1p mu Omega p :=
  ⟨assembleSobolev1JetLp u g, (mem_w1pSubmodule_iff_hasWeakFDerivOn _).mpr (by
    rw [value_assembleSobolev1JetLp]
    convert h using 1
    funext x
    rw [Sobolev1JetLp.candidateWeakFDeriv, gradient_assembleSobolev1JetLp])⟩

@[simp]
theorem W1p.value_mk (u : Lp ℝ p (mu.restrict Omega)) (g : Lp E p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (g x))) :
    W1p.value (W1p.mk u g h) = u :=
  value_assembleSobolev1JetLp u g

@[simp]
theorem W1p.gradient_mk (u : Lp ℝ p (mu.restrict Omega)) (g : Lp E p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (g x))) :
    W1p.gradient (W1p.mk u g h) = g :=
  gradient_assembleSobolev1JetLp u g

omit [FiniteDimensional ℝ E] in
/-- Two Sobolev functions are equal when their value and weak-gradient components are equal. -/
@[ext]
theorem W1p.ext {u v : W1p mu Omega p}
    (hvalue : W1p.value u = W1p.value v)
    (hgradient : W1p.gradient u = W1p.gradient v) : u = v :=
  Subtype.ext (Sobolev1JetLp.ext hvalue hgradient)

/-- The value-gradient pair represented by an element of `W1p` satisfies the weak derivative
identity. -/
theorem W1p.hasWeakFDerivOn (u : W1p mu Omega p) :
    HasWeakFDerivOn mu Omega (W1p.value u)
      (fun x => innerSL ℝ (W1p.gradient u x)) :=
  (mem_w1pSubmodule_iff_hasWeakFDerivOn u.1).mp u.2

/-- Two Sobolev functions are equal when their `Lᵖ` value components are equal.  Uniqueness of
weak derivatives determines the gradient component. -/
@[ext]
theorem W1p.ext_value {u v : W1p mu Omega p} (hvalue : W1p.value u = W1p.value v) : u = v := by
  apply W1p.ext hvalue
  apply Lp.ext
  have hderiv :
      (fun x => innerSL ℝ (W1p.gradient u x)) =ᵐ[mu.restrict Omega]
        fun x => innerSL ℝ (W1p.gradient v x) := by
    apply (W1p.hasWeakFDerivOn u).ae_eq
    simpa only [hvalue] using W1p.hasWeakFDerivOn v
  filter_upwards [hderiv] with x hx
  exact innerSL_inj.mp hx

omit [FiniteDimensional ℝ E] in
/-- The norm of a Sobolev function controls the norm of its value component. -/
theorem W1p.norm_value_le (u : W1p mu Omega p) : ‖W1p.value u‖ ≤ ‖u‖ :=
  norm_value_le_ambient u.1

omit [FiniteDimensional ℝ E] in
/-- The norm of a Sobolev function controls the norm of its weak gradient. -/
theorem W1p.norm_gradient_le (u : W1p mu Omega p) : ‖W1p.gradient u‖ ≤ ‖u‖ :=
  norm_gradient_le_ambient u.1

omit [FiniteDimensional ℝ E] in
/-- At exponent two, the norm on `W1p` is the Hilbert graph norm. -/
theorem W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq (u : W1p mu Omega 2) :
    ‖u‖ ^ 2 = ‖W1p.value u‖ ^ 2 + ‖W1p.gradient u‖ ^ 2 :=
  norm_sq_eq_norm_value_sq_add_norm_gradient_sq_ambient u.1

/-- The integral of the squared pointwise norm of an `L²` function is its squared `L²` norm.

Kept `private`: the natural home for this generic `Lp` fact is the root `MeasureTheory.Lp`
namespace, which is unreachable from inside `namespace TauCeti`, and its only uses are the two
Sobolev specializations below. -/
private theorem integral_norm_sq_eq_norm_sq {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : Lp F 2 m) :
    ∫ x, ‖f x‖ ^ 2 ∂m = ‖f‖ ^ 2 := by
  refine Eq.symm ?_
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_self_eq_norm_sq (f x))

omit [FiniteDimensional ℝ E] in
/-- The squared pointwise norm of a Sobolev gradient is integrable. -/
theorem W1p.integrable_norm_gradient_sq (u : W1p mu Omega 2) :
    Integrable (fun x => ‖W1p.gradient u x‖ ^ 2) (mu.restrict Omega) :=
  (memLp_two_iff_integrable_sq_norm (Lp.memLp (W1p.gradient u)).aestronglyMeasurable).1
    (Lp.memLp (W1p.gradient u))

omit [FiniteDimensional ℝ E] in
/-- The squared pointwise value of a real Sobolev function is integrable. -/
theorem W1p.integrable_value_sq (u : W1p mu Omega 2) :
    Integrable (fun x => (W1p.value u x) ^ 2) (mu.restrict Omega) :=
  (Lp.memLp (W1p.value u)).integrable_sq

omit [FiniteDimensional ℝ E] in
/-- The integral of the squared Sobolev gradient is its squared `L²` norm. -/
theorem W1p.integral_norm_gradient_sq_eq_norm_gradient_sq (u : W1p mu Omega 2) :
    ∫ x in Omega, ‖W1p.gradient u x‖ ^ 2 ∂mu = ‖W1p.gradient u‖ ^ 2 :=
  integral_norm_sq_eq_norm_sq (W1p.gradient u)

omit [FiniteDimensional ℝ E] in
/-- The integral of the squared Sobolev value is its squared `L²` norm. -/
theorem W1p.integral_value_sq_eq_norm_value_sq (u : W1p mu Omega 2) :
    ∫ x in Omega, (W1p.value u x) ^ 2 ∂mu = ‖W1p.value u‖ ^ 2 := by
  rw [← integral_norm_sq_eq_norm_sq (W1p.value u)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp [Real.norm_eq_abs, sq_abs])

/-- `W^{1,p}(Ω)` is complete in its value-gradient graph norm. -/
instance : CompleteSpace (W1p mu Omega p) :=
  (w1pSubmodule mu Omega p).isClosed.completeSpace_coe

end TauCeti
