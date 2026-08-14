/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p

/-!
# Second-order weak Sobolev spaces

This file constructs the real-valued Sobolev space `W^{2,p}(Ω)` on an open subset of a
finite-dimensional real inner product space.  It builds directly on `TauCeti.W1p`: an element
records a first-order Sobolev function together with an `Lᵖ` field of continuous linear maps,
and the latter is required to be the weak Fréchet derivative of the weak gradient.

The admissibility condition is again imposed as the common kernel of continuous Hölder
pairings.  Hence `TauCeti.W2p` is a closed subspace of the product of `W^{1,p}(Ω)` and the
`Lᵖ` Hessian field, and is complete.  Its graph norm is

`(∥u∥_{W¹ᵖ}² + ∥D²u∥_p²)¹⁄²`.

The value and weak gradient of a second-order Sobolev function are those of its first-order
component, so they are read off as `TauCeti.W1p.value` and `TauCeti.W1p.gradient` of
`TauCeti.W2p.firstOrder` rather than through a second layer of projections.

No boundedness or boundary regularity of `Ω` is used.  The Hessian is represented basis-free as
an element of `E →L[ℝ] E`.  Its almost-everywhere symmetry is a theorem about iterated weak
derivatives, rather than an extra field of the definition, and is left to the higher-order API.

## Main declarations

* `TauCeti.w2pSubmodule`: the closed subspace of first-order jets and weak Hessians.
* `TauCeti.W2p`: the complete second-order weak Sobolev space.
* `TauCeti.W2p.hasWeakFDerivOn_gradient`: the recorded Hessian is the weak derivative of the
  recorded weak gradient.

## References

This is the second-order case of Lane A.1, target 1, in `TauCetiRoadmap/PDE/README.md`.  The
iterated weak-derivative definition and closed-graph completeness argument follow L. C. Evans,
*Partial Differential Equations*, Chapter 5, §5.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 <= p)]

/-- The ambient graph space for a second-order Sobolev function: a first-order Sobolev function
and an `Lᵖ` candidate Hessian, with their Euclidean product norm.  Its two components are
projected out by `WithLp.fst` and `WithLp.snd`. -/
abbrev Sobolev2JetLp (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] :=
  WithLp 2 (W1p mu Omega p × Lp (E →L[ℝ] E) p (mu.restrict Omega))

/-- The continuous functional expressing that the candidate Hessian is the weak derivative of
the first-order jet's gradient, tested against `phi` in the direction `v`. -/
private def weakHessianTestFunctional (p : ENNReal) [Fact (1 <= p)]
    (phi : 𝓓(Omega, ℝ)) (v : E) : Sobolev2JetLp mu Omega p →L[ℝ] E := by
  let _ : (ENNReal.conjExponent p).HolderConjugate p := ENNReal.HolderConjugate.symm
  let _ : Fact (1 <= ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le _ p⟩
  let dphi : 𝓓(Omega, ℝ) := TestFunction.lineDerivCLM ℝ v phi
  let gradientL : Sobolev2JetLp mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
    W1p.gradientL.comp (WithLp.fstL 2 ℝ _ _)
  let hessianDirectionL :
      Sobolev2JetLp mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
    (ContinuousLinearMap.apply ℝ E v).compLpL p (mu.restrict Omega) |>.comp
      (WithLp.sndL 2 ℝ _ _)
  let smulPairing :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).lpPairing
      (mu.restrict Omega) (ENNReal.conjExponent p) p
  exact (smulPairing (testFunctionLp (mu := mu) (ENNReal.conjExponent p) dphi)).comp
      gradientL +
    (smulPairing (testFunctionLp (mu := mu) (ENNReal.conjExponent p) phi)).comp
      hessianDirectionL

private theorem weakHessianTestFunctional_apply (J : Sobolev2JetLp mu Omega p)
    (phi : 𝓓(Omega, ℝ)) (v : E) :
    weakHessianTestFunctional (mu := mu) p phi v J =
      (∫ x, lineDeriv ℝ (phi : E → ℝ) x v • W1p.gradient (WithLp.fst J) x ∂mu) +
        ∫ x, phi x • WithLp.snd J x v ∂mu := by
  let _ : (ENNReal.conjExponent p).HolderConjugate p := ENNReal.HolderConjugate.symm
  let _ : Fact (1 <= ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le _ p⟩
  let dphi : 𝓓(Omega, ℝ) := TestFunction.lineDerivCLM ℝ v phi
  let gradientL : Sobolev2JetLp mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
    W1p.gradientL.comp (WithLp.fstL 2 ℝ _ _)
  let hessianDirectionL :
      Sobolev2JetLp mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
    (ContinuousLinearMap.apply ℝ E v).compLpL p (mu.restrict Omega) |>.comp
      (WithLp.sndL 2 ℝ _ _)
  let smulPairing :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).lpPairing
      (mu.restrict Omega) (ENNReal.conjExponent p) p
  have hdphi : (dphi : E → ℝ) = fun x => lineDeriv ℝ (phi : E → ℝ) x v := by
    funext x
    exact TestFunction.lineDerivCLM_apply_of_le le_top
  have hgradient : gradientL J = W1p.gradient (WithLp.fst J) := by
    simp only [gradientL, ContinuousLinearMap.comp_apply, WithLp.fstL_apply, W1p.gradientL_apply]
  have hhessian : hessianDirectionL J =
      (ContinuousLinearMap.apply ℝ E v).compLp (WithLp.snd J) := rfl
  -- Expose the private functional as the two `lpPairing`s whose integral theorem applies.
  rw [show weakHessianTestFunctional (mu := mu) p phi v J =
      smulPairing (testFunctionLp (mu := mu) (ENNReal.conjExponent p) dphi) (gradientL J) +
        smulPairing (testFunctionLp (mu := mu) (ENNReal.conjExponent p) phi)
          (hessianDirectionL J) by rfl,
    ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.lpPairing_eq_integral]
  have hfirst :
      (∫ x, testFunctionLp (mu := mu) (ENNReal.conjExponent p) dphi x • gradientL J x
          ∂mu.restrict Omega) =
        ∫ x in Omega, lineDeriv ℝ (phi : E → ℝ) x v • W1p.gradient (WithLp.fst J) x ∂mu := by
    apply integral_congr_ae
    filter_upwards [testFunctionLp_apply_ae (mu := mu) (ENNReal.conjExponent p) dphi]
      with x hx
    rw [hx, hgradient, congrFun hdphi x]
  have hsecond :
      (∫ x, testFunctionLp (mu := mu) (ENNReal.conjExponent p) phi x •
          hessianDirectionL J x ∂mu.restrict Omega) =
        ∫ x in Omega, phi x • WithLp.snd J x v ∂mu := by
    apply integral_congr_ae
    filter_upwards [testFunctionLp_apply_ae (mu := mu) (ENNReal.conjExponent p) phi,
      (ContinuousLinearMap.apply ℝ E v).coeFn_compLp (WithLp.snd J)] with x hphi hx
    rw [hphi, hhessian, hx, ContinuousLinearMap.apply_apply]
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [hfirst, hsecond, setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
    setIntegral_smul_eq_integral_smul]

/-- The second-order weak Sobolev subspace.  Its Hessian component is required to be the weak
Fréchet derivative of the weak gradient in its first-order component. -/
def w2pSubmodule (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] : ClosedSubmodule ℝ (Sobolev2JetLp mu Omega p) :=
  ⨅ phi : 𝓓(Omega, ℝ), ⨅ v : E,
    (⊥ : ClosedSubmodule ℝ E).comap (weakHessianTestFunctional (mu := mu) p phi v)

/-- Membership in `w2pSubmodule` is the family of weak Hessian integration-by-parts identities. -/
theorem mem_w2pSubmodule_iff (J : Sobolev2JetLp mu Omega p) :
    J ∈ w2pSubmodule mu Omega p ↔
      ∀ (phi : 𝓓(Omega, ℝ)) (v : E),
        (∫ x, lineDeriv ℝ (phi : E → ℝ) x v • W1p.gradient (WithLp.fst J) x ∂mu) +
          ∫ x, phi x • WithLp.snd J x v ∂mu = 0 := by
  -- Pass through the private kernel presentation once, keeping it out of the public statement.
  rw [show J ∈ w2pSubmodule mu Omega p ↔
      ∀ (phi : 𝓓(Omega, ℝ)) (v : E),
        weakHessianTestFunctional (mu := mu) p phi v J = 0 by
    simp only [w2pSubmodule, ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_comap,
      ClosedSubmodule.mem_bot]]
  simp only [weakHessianTestFunctional_apply]

/-- A jet belongs to `w2pSubmodule` exactly when its Hessian is the weak Fréchet derivative of
its weak gradient. -/
theorem mem_w2pSubmodule_iff_hasWeakFDerivOn (J : Sobolev2JetLp mu Omega p) :
    J ∈ w2pSubmodule mu Omega p ↔
      HasWeakFDerivOn mu Omega (W1p.gradient (WithLp.fst J))
        (WithLp.snd J : Lp (E →L[ℝ] E) p (mu.restrict Omega)) := by
  have hgradient : LocallyIntegrableOn (W1p.gradient (WithLp.fst J)) Omega mu :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (W1p.gradient (WithLp.fst J))).locallyIntegrable Fact.out)
  have hhessian (v : E) :
      LocallyIntegrableOn (fun x => WithLp.snd J x v) Omega mu := by
    apply locallyIntegrableOn_of_locallyIntegrable_restrict
    exact (((Lp.memLp (WithLp.snd J)).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ E v)).locallyIntegrable Fact.out)
  rw [mem_w2pSubmodule_iff, hasWeakFDerivOn_iff]
  constructor
  · intro h v
    rw [hasWeakLineDerivOn_iff_testFunction]
    exact ⟨inferInstance, hgradient, hhessian v, fun phi =>
      add_eq_zero_iff_eq_neg.mp (h phi v)⟩
  · intro h phi v
    exact add_eq_zero_iff_eq_neg.mpr
      ((h v).integral_lineDeriv_smul_eq_neg_integral_smul phi)

/-- The second-order, real-valued weak Sobolev space `W^{2,p}(Ω)`, represented by its first-order
Sobolev jet and weak Hessian. -/
abbrev W2p (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] := (w2pSubmodule mu Omega p).toSubmodule

/-- The continuous linear projection from `W2p` to its first-order Sobolev component.  Its value
and weak gradient are the value and weak gradient of the second-order function. -/
def W2p.firstOrderL : W2p mu Omega p →L[ℝ] W1p mu Omega p :=
  (WithLp.fstL 2 ℝ _ _).comp (w2pSubmodule mu Omega p).toSubmodule.subtypeL

/-- The first-order Sobolev component of a second-order Sobolev function. -/
def W2p.firstOrder (u : W2p mu Omega p) : W1p mu Omega p :=
  W2p.firstOrderL u

@[simp]
theorem W2p.firstOrderL_apply (u : W2p mu Omega p) :
    W2p.firstOrderL u = W2p.firstOrder u := (rfl)

theorem W2p.firstOrder_coe (u : W2p mu Omega p) :
    W2p.firstOrder u = WithLp.fst (u : Sobolev2JetLp mu Omega p) := (rfl)

/-- The continuous linear projection from `W2p` to its weak Hessian. -/
def W2p.hessianL : W2p mu Omega p →L[ℝ] Lp (E →L[ℝ] E) p (mu.restrict Omega) :=
  (WithLp.sndL 2 ℝ _ _).comp (w2pSubmodule mu Omega p).toSubmodule.subtypeL

/-- The `Lᵖ` weak Hessian of a second-order Sobolev function. -/
def W2p.hessian (u : W2p mu Omega p) : Lp (E →L[ℝ] E) p (mu.restrict Omega) :=
  W2p.hessianL u

@[simp]
theorem W2p.hessianL_apply (u : W2p mu Omega p) :
    W2p.hessianL u = W2p.hessian u := (rfl)

theorem W2p.hessian_coe (u : W2p mu Omega p) :
    W2p.hessian u = WithLp.snd (u : Sobolev2JetLp mu Omega p) := (rfl)

/-- Construct a second-order Sobolev function from a first-order Sobolev function and a weak
Hessian. -/
def W2p.mk (u : W1p mu Omega p) (H : Lp (E →L[ℝ] E) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (W1p.gradient u) H) : W2p mu Omega p :=
  ⟨WithLp.toLp 2 (u, H), (mem_w2pSubmodule_iff_hasWeakFDerivOn _).mpr (by simpa)⟩

@[simp]
theorem W2p.firstOrder_mk (u : W1p mu Omega p)
    (H : Lp (E →L[ℝ] E) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (W1p.gradient u) H) :
    W2p.firstOrder (W2p.mk u H h) = u := by
  rw [W2p.firstOrder_coe]
  simp [W2p.mk]

@[simp]
theorem W2p.hessian_mk (u : W1p mu Omega p)
    (H : Lp (E →L[ℝ] E) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (W1p.gradient u) H) :
    W2p.hessian (W2p.mk u H h) = H := by
  rw [W2p.hessian_coe]
  simp [W2p.mk]

/-- Two second-order Sobolev functions are equal when their first-order components and weak
Hessians are equal. -/
theorem W2p.ext_firstOrder {u v : W2p mu Omega p}
    (hfirstOrder : W2p.firstOrder u = W2p.firstOrder v)
    (hhessian : W2p.hessian u = W2p.hessian v) : u = v := by
  refine Subtype.ext ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective ?_)
  exact Prod.ext hfirstOrder hhessian

/-- The Hessian of a second-order Sobolev function is the weak Fréchet derivative of its weak
gradient. -/
theorem W2p.hasWeakFDerivOn_gradient (u : W2p mu Omega p) :
    HasWeakFDerivOn mu Omega (W1p.gradient (W2p.firstOrder u)) (W2p.hessian u) :=
  (mem_w2pSubmodule_iff_hasWeakFDerivOn u.1).mp u.2

/-- Two second-order Sobolev functions are equal when their `Lᵖ` value components are equal.
Successive uniqueness of weak derivatives determines both the gradient and Hessian components. -/
@[ext]
theorem W2p.ext {u v : W2p mu Omega p}
    (hvalue : W1p.value (W2p.firstOrder u) = W1p.value (W2p.firstOrder v)) : u = v := by
  have hfirstOrder : W2p.firstOrder u = W2p.firstOrder v := W1p.ext_value hvalue
  have hv : HasWeakFDerivOn mu Omega (W1p.gradient (W2p.firstOrder u)) (W2p.hessian v) := by
    rw [hfirstOrder]
    exact W2p.hasWeakFDerivOn_gradient v
  have hhessian : W2p.hessian u = W2p.hessian v :=
    Lp.ext ((W2p.hasWeakFDerivOn_gradient u).ae_eq hv)
  exact W2p.ext_firstOrder hfirstOrder hhessian

/-- The norm of a second-order Sobolev function controls the norm of its first-order component. -/
theorem W2p.norm_firstOrder_le (u : W2p mu Omega p) : ‖W2p.firstOrder u‖ ≤ ‖u‖ := by
  rw [W2p.firstOrder_coe]
  exact WithLp.norm_fst_le (W1p mu Omega p) u.1

/-- The norm of a second-order Sobolev function controls the norm of its value component. -/
theorem W2p.norm_value_le (u : W2p mu Omega p) : ‖W1p.value (W2p.firstOrder u)‖ ≤ ‖u‖ :=
  (W1p.norm_value_le (W2p.firstOrder u)).trans (W2p.norm_firstOrder_le u)

/-- The norm of a second-order Sobolev function controls the norm of its weak gradient. -/
theorem W2p.norm_gradient_le (u : W2p mu Omega p) : ‖W1p.gradient (W2p.firstOrder u)‖ ≤ ‖u‖ :=
  (W1p.norm_gradient_le (W2p.firstOrder u)).trans (W2p.norm_firstOrder_le u)

/-- The norm of a second-order Sobolev function controls the norm of its weak Hessian. -/
theorem W2p.norm_hessian_le (u : W2p mu Omega p) : ‖W2p.hessian u‖ ≤ ‖u‖ := by
  rw [W2p.hessian_coe]
  exact WithLp.norm_snd_le (W1p mu Omega p) u.1

/-- At exponent two, the norm on `W2p` is the graph norm of the first-order Sobolev component and
the weak Hessian. -/
theorem W2p.norm_sq_eq_norm_firstOrder_sq_add_norm_hessian_sq (u : W2p mu Omega 2) :
    ‖u‖ ^ 2 = ‖W2p.firstOrder u‖ ^ 2 + ‖W2p.hessian u‖ ^ 2 :=
  by
    have hnorm := WithLp.prod_norm_eq_add (by norm_num : 0 < (2 : ENNReal).toReal) u.1
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div] at hnorm
    -- `W2p` inherits the subtype norm, while its projections are the two `WithLp` coordinates.
    change ‖u.1‖ ^ 2 = ‖WithLp.fst u.1‖ ^ 2 + ‖WithLp.snd u.1‖ ^ 2
    rw [hnorm]
    exact Real.rpow_inv_natCast_pow (by positivity) (by norm_num)

/-- At exponent two, the norm on `W2p` is the sum-of-squares graph norm of the value, weak
gradient, and weak Hessian. -/
theorem W2p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq_add_norm_hessian_sq
    (u : W2p mu Omega 2) :
    ‖u‖ ^ 2 = ‖W1p.value (W2p.firstOrder u)‖ ^ 2 + ‖W1p.gradient (W2p.firstOrder u)‖ ^ 2 +
      ‖W2p.hessian u‖ ^ 2 := by
  rw [W2p.norm_sq_eq_norm_firstOrder_sq_add_norm_hessian_sq,
    W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]

/-- `W^{2,p}(Ω)` is complete in its iterated weak-derivative graph norm. -/
instance : CompleteSpace (W2p mu Omega p) :=
  (w2pSubmodule mu Omega p).isClosed.completeSpace_coe

end TauCeti
