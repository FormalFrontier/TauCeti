/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.ProdL2

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
* `TauCeti.weakDerivativeTestJet`: the `Lᶜ` test jet `(∂_v φ, φ v)` dual to an `Lᵖ` jet.
* `TauCeti.w1pSubmodule`: the closed subspace of jets annihilating every weak-derivative test.
* `TauCeti.W1p`: the corresponding complete normed space.
* `TauCeti.mem_w1pSubmodule_iff_hasWeakFDerivOn`: membership is exactly weak
  differentiability of the value component with the recorded gradient.

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

/-- The value component of an `Lᵖ` Sobolev jet. -/
def Sobolev1JetLp.value (J : Sobolev1JetLp mu Omega p) : Lp ℝ p (mu.restrict Omega) :=
  (WithLp.fstL 2 ℝ ℝ E).compLp J

/-- The gradient component of an `Lᵖ` Sobolev jet. -/
def Sobolev1JetLp.gradient (J : Sobolev1JetLp mu Omega p) : Lp E p (mu.restrict Omega) :=
  (WithLp.sndL 2 ℝ ℝ E).compLp J

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] [Fact (1 <= p)] in
@[simp]
theorem Sobolev1JetLp.value_apply_ae (J : Sobolev1JetLp mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      Sobolev1JetLp.value J x = WithLp.fst (J x) := by
  simpa [Sobolev1JetLp.value] using (WithLp.fstL 2 ℝ ℝ E).coeFn_compLp J

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] [Fact (1 <= p)] in
@[simp]
theorem Sobolev1JetLp.gradient_apply_ae (J : Sobolev1JetLp mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      Sobolev1JetLp.gradient J x = WithLp.snd (J x) := by
  simpa [Sobolev1JetLp.gradient] using (WithLp.sndL 2 ℝ ℝ E).coeFn_compLp J

/-- The candidate weak Fréchet derivative recorded by the gradient component of a Sobolev jet. -/
def Sobolev1JetLp.weakFDeriv (J : Sobolev1JetLp mu Omega p) : E → E →L[ℝ] ℝ :=
  fun x => innerSL ℝ (Sobolev1JetLp.gradient J x)

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] [Fact (1 <= p)] in
@[simp]
theorem Sobolev1JetLp.weakFDeriv_apply (J : Sobolev1JetLp mu Omega p) (x v : E) :
    Sobolev1JetLp.weakFDeriv J x v = ⟪v, Sobolev1JetLp.gradient J x⟫_ℝ := by
  rw [Sobolev1JetLp.weakFDeriv, innerSL_apply_apply, real_inner_comm]

private def weakDerivativeTestFunction (phi : 𝓓(Omega, ℝ)) (v : E) (x : E) :
    Sobolev1Jet E :=
  WithLp.toLp 2 (lineDeriv ℝ (phi : E → ℝ) x v, phi x • v)

omit [FiniteDimensional ℝ E] in
private theorem weakDerivativeTestFunction_memLp (q : ENNReal) (phi : 𝓓(Omega, ℝ)) (v : E) :
    MemLp (weakDerivativeTestFunction phi v) q (mu.restrict Omega) := by
  let dphi : 𝓓(Omega, ℝ) := TestFunction.lineDerivCLM ℝ v phi
  have hdphi : (dphi : E → ℝ) = fun x => lineDeriv ℝ (phi : E → ℝ) x v := by
    funext x
    exact TestFunction.lineDerivCLM_apply_of_le le_top
  let f : E → Sobolev1Jet E := fun x => WithLp.toLp 2 (dphi x, phi x • v)
  have hf_cont : Continuous f :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.continuous.comp
      (dphi.continuous.prodMk (phi.continuous.smul continuous_const))
  have hd_support : HasCompactSupport (fun x => WithLp.toLp 2 (dphi x, (0 : E))) :=
    dphi.hasCompactSupport.mono fun x hx hzero => hx (by simp [hzero])
  have hv_support : HasCompactSupport (fun x => WithLp.toLp 2 ((0 : ℝ), phi x • v)) :=
    phi.hasCompactSupport.mono fun x hx hzero => hx (by simp [hzero])
  have hf_support : HasCompactSupport f := by
    have hf_eq : f = (fun x => WithLp.toLp 2 (dphi x, (0 : E))) +
        fun x => WithLp.toLp 2 ((0 : ℝ), phi x • v) := by
      funext x
      change WithLp.toLp 2 (dphi x, phi x • v) =
        WithLp.toLp 2 (dphi x, 0) + WithLp.toLp 2 (0, phi x • v)
      rw [show (dphi x, phi x • v) =
          (dphi x, (0 : E)) + ((0 : ℝ), phi x • v) by ext <;> simp]
      exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.map_add _ _
    rw [hf_eq]
    exact hd_support.add hv_support
  have hfun : weakDerivativeTestFunction phi v = f := by
    funext x
    simp only [weakDerivativeTestFunction, f]
    rw [congrFun hdphi x]
  rw [hfun]
  exact hf_cont.memLp_of_hasCompactSupport (μ := mu.restrict Omega) (p := q) hf_support

/-- The compactly supported jet `(∂_v φ, φ v)` used to test whether an `Lᵖ` jet is a weak
derivative.  Its exponent is Hölder-conjugate to `p`, including the endpoints `p = 1, ∞`. -/
def weakDerivativeTestJet (p : ENNReal) (phi : 𝓓(Omega, ℝ)) (v : E) :
    Lp (Sobolev1Jet E) (ENNReal.conjExponent p) (mu.restrict Omega) :=
  (weakDerivativeTestFunction_memLp (mu := mu) (ENNReal.conjExponent p) phi v).toLp
    (weakDerivativeTestFunction phi v)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem weakDerivativeTestJet_apply_ae (p : ENNReal) (phi : 𝓓(Omega, ℝ)) (v : E) :
    ∀ᵐ x ∂mu.restrict Omega,
      weakDerivativeTestJet (mu := mu) p phi v x =
        WithLp.toLp 2 (lineDeriv ℝ (phi : E → ℝ) x v, phi x • v) := by
  filter_upwards [MemLp.coeFn_toLp (weakDerivativeTestFunction_memLp (mu := mu)
    (ENNReal.conjExponent p) phi v)] with x hx
  simpa only [weakDerivativeTestJet, weakDerivativeTestFunction] using hx

/-- The continuous functional expressing the weak-derivative identity against `φ` in direction
`v`.  It pairs the candidate jet with `(∂_v φ, φ v)`. -/
def weakDerivativeTestFunctional (p : ENNReal) [Fact (1 <= p)]
    (phi : 𝓓(Omega, ℝ)) (v : E) : Sobolev1JetLp mu Omega p →L[ℝ] ℝ := by
  let _ : (ENNReal.conjExponent p).HolderConjugate p := ENNReal.HolderConjugate.symm
  let _ : Fact (1 <= ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le _ p⟩
  exact ((innerSL ℝ (E := Sobolev1Jet E)).lpPairing (mu.restrict Omega) p
    (ENNReal.conjExponent p)).flip (weakDerivativeTestJet (mu := mu) p phi v)

omit [FiniteDimensional ℝ E] in
/-- The test functional is the sum of the value and candidate-gradient terms in the weak
integration-by-parts identity. -/
theorem weakDerivativeTestFunctional_apply (J : Sobolev1JetLp mu Omega p)
    (phi : 𝓓(Omega, ℝ)) (v : E) :
    weakDerivativeTestFunctional (mu := mu) p phi v J =
      ∫ x in Omega, (lineDeriv ℝ (phi : E → ℝ) x v * Sobolev1JetLp.value J x +
        phi x * Sobolev1JetLp.weakFDeriv J x v) ∂mu := by
  let _ : (ENNReal.conjExponent p).HolderConjugate p := ENNReal.HolderConjugate.symm
  let _ : Fact (1 <= ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le _ p⟩
  change (innerSL ℝ (E := Sobolev1Jet E)).lpPairing (mu.restrict Omega) p
      (ENNReal.conjExponent p) J (weakDerivativeTestJet (mu := mu) p phi v) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [weakDerivativeTestJet_apply_ae (mu := mu) p phi v,
    Sobolev1JetLp.value_apply_ae J, Sobolev1JetLp.gradient_apply_ae J] with x htest hvalue hgradient
  rw [htest, innerSL_apply_apply, WithLp.prod_inner_apply,
    Sobolev1JetLp.weakFDeriv_apply, hvalue, hgradient]
  simp only [WithLp.ofLp_fst, RCLike.inner_apply, conj_trivial, WithLp.ofLp_snd,
    add_right_inj]
  rw [inner_smul_right, real_inner_comm]

/-- The first-order weak Sobolev subspace.  It consists of the `Lᵖ` value-gradient jets that
annihilate every test jet `(∂_v φ, φ v)`. -/
def w1pSubmodule (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] : Submodule ℝ (Sobolev1JetLp mu Omega p) :=
  ⨅ phi : 𝓓(Omega, ℝ), ⨅ v : E,
    LinearMap.ker (weakDerivativeTestFunctional (mu := mu) p phi v).toLinearMap

omit [FiniteDimensional ℝ E] in
/-- Membership in `w1pSubmodule` is the family of weak integration-by-parts identities. -/
theorem mem_w1pSubmodule_iff (J : Sobolev1JetLp mu Omega p) :
    J ∈ w1pSubmodule mu Omega p ↔
      ∀ (phi : 𝓓(Omega, ℝ)) (v : E),
        weakDerivativeTestFunctional (mu := mu) p phi v J = 0 := by
  simp [w1pSubmodule]

/-- A jet belongs to `w1pSubmodule` exactly when its value component has the recorded gradient as
its weak Fréchet derivative. -/
theorem mem_w1pSubmodule_iff_hasWeakFDerivOn (J : Sobolev1JetLp mu Omega p) :
    J ∈ w1pSubmodule mu Omega p ↔
      HasWeakFDerivOn mu Omega (Sobolev1JetLp.value J)
        (Sobolev1JetLp.weakFDeriv J) := by
  have hvalue : LocallyIntegrableOn (Sobolev1JetLp.value J) Omega mu :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (Sobolev1JetLp.value J)).locallyIntegrable Fact.out)
  have hderiv (v : E) : LocallyIntegrableOn
      (fun x => Sobolev1JetLp.weakFDeriv J x v) Omega mu := by
    apply locallyIntegrableOn_of_locallyIntegrable_restrict
    have hinner := (Lp.memLp (Sobolev1JetLp.gradient J)).const_inner (𝕜 := ℝ) v
    exact (hinner.locallyIntegrable Fact.out).congr <| by
      filter_upwards with x
      simp only [Sobolev1JetLp.weakFDeriv_apply]
  rw [mem_w1pSubmodule_iff]
  constructor
  · intro h
    rw [hasWeakFDerivOn_iff]
    intro v
    rw [hasWeakLineDerivOn_iff_testFunction]
    refine ⟨inferInstance, hvalue, hderiv v, fun phi => ?_⟩
    have hleft : Integrable
        (fun x => lineDeriv ℝ (phi : E → ℝ) x v * Sobolev1JetLp.value J x) mu := by
      simpa only [smul_eq_mul] using
        integrable_lineDeriv_smul_of_locallyIntegrableOn hvalue phi v
    have hright : Integrable
        (fun x => phi x * Sobolev1JetLp.weakFDeriv J x v) mu := by
      simpa only [smul_eq_mul] using integrable_smul_of_locallyIntegrableOn (hderiv v) phi
    have hsupport : ∀ x, x ∉ (Omega : Set E) →
        lineDeriv ℝ (phi : E → ℝ) x v * Sobolev1JetLp.value J x +
          phi x * Sobolev1JetLp.weakFDeriv J x v = 0 := by
      intro x hx
      have hxt : x ∉ tsupport (phi : E → ℝ) := fun hmem => hx (phi.tsupport_subset hmem)
      rw [lineDeriv_eq_zero_of_notMem_tsupport phi hxt v,
        image_eq_zero_of_notMem_tsupport hxt]
      simp
    have hzero := h phi v
    rw [weakDerivativeTestFunctional_apply,
      setIntegral_eq_integral_of_forall_compl_eq_zero hsupport,
      integral_add hleft hright] at hzero
    simpa only [smul_eq_mul] using (show
      (∫ x, lineDeriv ℝ (phi : E → ℝ) x v * Sobolev1JetLp.value J x ∂mu) =
        -(∫ x, phi x * Sobolev1JetLp.weakFDeriv J x v ∂mu) by linarith)
  · intro h
    rw [hasWeakFDerivOn_iff] at h
    intro phi v
    rw [weakDerivativeTestFunctional_apply]
    have hleft : Integrable
        (fun x => lineDeriv ℝ (phi : E → ℝ) x v * Sobolev1JetLp.value J x) mu := by
      simpa only [smul_eq_mul] using
        integrable_lineDeriv_smul_of_locallyIntegrableOn (h v).locallyIntegrableOn phi v
    have hright : Integrable
        (fun x => phi x * Sobolev1JetLp.weakFDeriv J x v) mu := by
      simpa only [smul_eq_mul] using
        integrable_smul_of_locallyIntegrableOn (h v).locallyIntegrableOn_deriv phi
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hxt : x ∉ tsupport (phi : E → ℝ) := fun hmem => hx (phi.tsupport_subset hmem)
      rw [lineDeriv_eq_zero_of_notMem_tsupport phi hxt v,
        image_eq_zero_of_notMem_tsupport hxt]
      simp), integral_add hleft hright]
    have hid := (h v).integral_lineDeriv_smul_eq_neg_integral_smul phi
    simp only [smul_eq_mul] at hid
    linarith

omit [FiniteDimensional ℝ E] in
/-- The first-order weak Sobolev subspace is closed in its ambient Bochner `Lᵖ` space. -/
theorem isClosed_w1pSubmodule :
    IsClosed (w1pSubmodule mu Omega p : Set (Sobolev1JetLp mu Omega p)) := by
  rw [show (w1pSubmodule mu Omega p : Set (Sobolev1JetLp mu Omega p)) =
      ⋂ phi : 𝓓(Omega, ℝ), ⋂ v : E,
        (LinearMap.ker (weakDerivativeTestFunctional (mu := mu) p phi v).toLinearMap :
          Set (Sobolev1JetLp mu Omega p)) by
    ext J
    simp [w1pSubmodule]]
  exact isClosed_iInter fun phi => isClosed_iInter fun v =>
    ContinuousLinearMap.isClosed_ker (weakDerivativeTestFunctional (mu := mu) p phi v)

/-- The first-order, real-valued weak Sobolev space `W^{1,p}(Ω)`, represented by its value and
weak gradient. -/
abbrev W1p (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] := w1pSubmodule mu Omega p

/-- The value-gradient pair represented by an element of `W1p` satisfies the weak derivative
identity. -/
theorem W1p.hasWeakFDerivOn (u : W1p mu Omega p) :
    HasWeakFDerivOn mu Omega (Sobolev1JetLp.value u.1)
      (Sobolev1JetLp.weakFDeriv u.1) :=
  (mem_w1pSubmodule_iff_hasWeakFDerivOn u.1).mp u.2

/-- `W^{1,p}(Ω)` is complete in its value-gradient graph norm. -/
instance : CompleteSpace (W1p mu Omega p) :=
  isClosed_w1pSubmodule.completeSpace_coe

end TauCeti
