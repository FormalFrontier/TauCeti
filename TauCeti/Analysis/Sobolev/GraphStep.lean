/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p

/-!
# The closed-graph step for weak Sobolev spaces

This file packages the successor step shared by the iterated weak Sobolev spaces. Given a
complete normed space `X` and a continuous map from `X` to an `Lᵖ` space of `F`-valued fields,
`TauCeti.WeakDerivStep` adjoins an `Lᵖ` weak Fréchet derivative of that field. The admissibility
condition is a closed subspace, so the resulting graph space is complete.

The construction is independent of the order of differentiation. It is instantiated by `W2p`
with the weak gradient and by `W3p` with the weak Hessian, and supplies the reusable successor
needed for the arbitrary-order construction in Lane A.1 of `TauCetiRoadmap/PDE/README.md`.

## Main declarations

* `TauCeti.weakDerivStepSubmodule`: the closed graph of one weak-derivative step.
* `TauCeti.mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn`: its intrinsic characterization.
* `TauCeti.WeakDerivStep`: the resulting complete normed space.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal

variable {E F X : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 <= p)]

/-- The ambient graph space obtained by adjoining an `Lᵖ` candidate weak derivative to `X`. -/
abbrev WeakDerivStepJetLp (mu : Measure E) (Omega : Opens E) (p : ENNReal) (X F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  WithLp 2 (X × Lp (E →L[ℝ] F) p (mu.restrict Omega))

private def weakDerivStepBaseL
    (base : X →L[ℝ] Lp F p (mu.restrict Omega)) :
    WeakDerivStepJetLp mu Omega p X F →L[ℝ] Lp F p (mu.restrict Omega) :=
  base.comp (WithLp.fstL 2 ℝ _ _)

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [CompleteSpace X]
  [mu.IsAddHaarMeasure] in
@[simp]
private theorem weakDerivStepBaseL_apply
    (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (J : WeakDerivStepJetLp mu Omega p X F) :
    weakDerivStepBaseL base J = base (WithLp.fst J) := rfl

private def weakDerivStepDirectionL (v : E) :
    WeakDerivStepJetLp mu Omega p X F →L[ℝ] Lp F p (mu.restrict Omega) :=
  ((ContinuousLinearMap.apply ℝ F v).compLpL p (mu.restrict Omega)).comp
    (WithLp.sndL 2 ℝ _ _)

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [CompleteSpace X]
  [mu.IsAddHaarMeasure] in
@[simp]
private theorem weakDerivStepDirectionL_apply (v : E)
    (J : WeakDerivStepJetLp mu Omega p X F) :
    weakDerivStepDirectionL (mu := mu) (Omega := Omega) (p := p) (X := X) (F := F) v J =
      (ContinuousLinearMap.apply ℝ F v).compLp (WithLp.snd J) := rfl

private def weakDerivStepSmulPairing (p : ENNReal) [Fact (1 <= p)]
    [Fact (1 <= ENNReal.conjExponent p)] :
    Lp ℝ (ENNReal.conjExponent p) (mu.restrict Omega) →L[ℝ]
      Lp F p (mu.restrict Omega) →L[ℝ] F := by
  let _ : (ENNReal.conjExponent p).HolderConjugate p := ENNReal.HolderConjugate.symm
  exact (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).lpPairing
    (mu.restrict Omega) (ENNReal.conjExponent p) p

private def weakDerivStepTestFunctional
    (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (phi : 𝓓(Omega, ℝ)) (v : E) : WeakDerivStepJetLp mu Omega p X F →L[ℝ] F := by
  let _ : Fact (1 <= ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le _ p⟩
  let dphi : 𝓓(Omega, ℝ) := TestFunction.lineDerivCLM ℝ v phi
  exact ((weakDerivStepSmulPairing (mu := mu) (Omega := Omega) (F := F) p)
      (testFunctionLp (mu := mu) (ENNReal.conjExponent p) dphi)).comp
        (weakDerivStepBaseL base) +
    ((weakDerivStepSmulPairing (mu := mu) (Omega := Omega) (F := F) p)
      (testFunctionLp (mu := mu) (ENNReal.conjExponent p) phi)).comp
        (weakDerivStepDirectionL (mu := mu) (Omega := Omega) (p := p) (X := X) (F := F) v)

omit [FiniteDimensional ℝ E] [CompleteSpace X] in
private theorem weakDerivStepTestFunctional_apply
    (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (J : WeakDerivStepJetLp mu Omega p X F) (phi : 𝓓(Omega, ℝ)) (v : E) :
    weakDerivStepTestFunctional base phi v J =
      (∫ x, lineDeriv ℝ (phi : E → ℝ) x v • base (WithLp.fst J) x ∂mu) +
        ∫ x, phi x • WithLp.snd J x v ∂mu := by
  let _ : (ENNReal.conjExponent p).HolderConjugate p := ENNReal.HolderConjugate.symm
  let _ : Fact (1 <= ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le _ p⟩
  let dphi : 𝓓(Omega, ℝ) := TestFunction.lineDerivCLM ℝ v phi
  have hdphi : (dphi : E → ℝ) = fun x => lineDeriv ℝ (phi : E → ℝ) x v := by
    funext x
    exact TestFunction.lineDerivCLM_apply_of_le le_top
  rw [show weakDerivStepTestFunctional base phi v J =
      weakDerivStepSmulPairing (mu := mu) (Omega := Omega) (F := F) p
          (testFunctionLp (mu := mu) (ENNReal.conjExponent p) dphi)
          (weakDerivStepBaseL base J) +
        weakDerivStepSmulPairing (mu := mu) (Omega := Omega) (F := F) p
          (testFunctionLp (mu := mu) (ENNReal.conjExponent p) phi)
          (weakDerivStepDirectionL (mu := mu) (Omega := Omega) (p := p) (X := X) (F := F) v J)
      by rfl, weakDerivStepSmulPairing, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.lpPairing_eq_integral]
  have hfirst :
      (∫ x, testFunctionLp (mu := mu) (ENNReal.conjExponent p) dphi x •
          weakDerivStepBaseL base J x ∂mu.restrict Omega) =
        ∫ x in Omega, lineDeriv ℝ (phi : E → ℝ) x v • base (WithLp.fst J) x ∂mu := by
    apply integral_congr_ae
    filter_upwards [testFunctionLp_apply_ae (mu := mu) (ENNReal.conjExponent p) dphi]
      with x hx
    rw [hx, weakDerivStepBaseL_apply, congrFun hdphi x]
  have hsecond :
      (∫ x, testFunctionLp (mu := mu) (ENNReal.conjExponent p) phi x •
          weakDerivStepDirectionL (mu := mu) (Omega := Omega) (p := p) (X := X) (F := F) v J x
          ∂mu.restrict Omega) =
        ∫ x in Omega, phi x • WithLp.snd J x v ∂mu := by
    apply integral_congr_ae
    filter_upwards [testFunctionLp_apply_ae (mu := mu) (ENNReal.conjExponent p) phi,
      (ContinuousLinearMap.apply ℝ F v).coeFn_compLp (WithLp.snd J)] with x hphi hx
    rw [hphi, weakDerivStepDirectionL_apply, hx, ContinuousLinearMap.apply_apply]
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [hfirst, hsecond, setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
    setIntegral_smul_eq_integral_smul]

/-- The closed subspace in which the adjoined field is the weak derivative of `base x`. -/
def weakDerivStepSubmodule (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E)
    (p : ENNReal) [Fact (1 <= p)] (base : X →L[ℝ] Lp F p (mu.restrict Omega)) :
    ClosedSubmodule ℝ (WeakDerivStepJetLp mu Omega p X F) :=
  ⨅ phi : 𝓓(Omega, ℝ), ⨅ v : E,
    (⊥ : ClosedSubmodule ℝ F).comap (weakDerivStepTestFunctional base phi v)

omit [FiniteDimensional ℝ E] [CompleteSpace X] in
/-- Membership in the weak-derivative step is the family of integration-by-parts identities. -/
theorem mem_weakDerivStepSubmodule_iff
    (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (J : WeakDerivStepJetLp mu Omega p X F) :
    J ∈ weakDerivStepSubmodule mu Omega p base ↔
      ∀ (phi : 𝓓(Omega, ℝ)) (v : E),
        (∫ x, lineDeriv ℝ (phi : E → ℝ) x v • base (WithLp.fst J) x ∂mu) +
          ∫ x, phi x • WithLp.snd J x v ∂mu = 0 := by
  rw [show J ∈ weakDerivStepSubmodule mu Omega p base ↔
      ∀ (phi : 𝓓(Omega, ℝ)) (v : E), weakDerivStepTestFunctional base phi v J = 0 by
    simp only [weakDerivStepSubmodule, ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_comap,
      ClosedSubmodule.mem_bot]]
  simp only [weakDerivStepTestFunctional_apply]

omit [CompleteSpace X] in
/-- A jet is in the closed graph exactly when its last field is the weak derivative of the
field selected by `base`. -/
theorem mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn
    (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (J : WeakDerivStepJetLp mu Omega p X F) :
    J ∈ weakDerivStepSubmodule mu Omega p base ↔
      HasWeakFDerivOn mu Omega (base (WithLp.fst J))
        (WithLp.snd J : Lp (E →L[ℝ] F) p (mu.restrict Omega)) := by
  have hbase : LocallyIntegrableOn (base (WithLp.fst J)) Omega mu :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (base (WithLp.fst J))).locallyIntegrable Fact.out)
  have hderiv (v : E) : LocallyIntegrableOn (fun x => WithLp.snd J x v) Omega mu := by
    apply locallyIntegrableOn_of_locallyIntegrable_restrict
    exact (((Lp.memLp (WithLp.snd J)).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ F v)).locallyIntegrable Fact.out)
  rw [mem_weakDerivStepSubmodule_iff, hasWeakFDerivOn_iff]
  constructor
  · intro h v
    rw [hasWeakLineDerivOn_iff_testFunction]
    exact ⟨inferInstance, hbase, hderiv v, fun phi =>
      add_eq_zero_iff_eq_neg.mp (h phi v)⟩
  · intro h phi v
    exact add_eq_zero_iff_eq_neg.mpr
      ((h v).integral_lineDeriv_smul_eq_neg_integral_smul phi)

/-- One complete weak-derivative graph step over the field selected by `base`. -/
abbrev WeakDerivStep (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] (base : X →L[ℝ] Lp F p (mu.restrict Omega)) :=
  (weakDerivStepSubmodule mu Omega p base).toSubmodule

namespace WeakDerivStep

/-- The continuous projection to the preceding graph space. -/
def prevL (base : X →L[ℝ] Lp F p (mu.restrict Omega)) :
    WeakDerivStep mu Omega p base →L[ℝ] X :=
  (WithLp.fstL 2 ℝ _ _).comp (weakDerivStepSubmodule mu Omega p base).toSubmodule.subtypeL

/-- The preceding graph-space component. -/
def prev (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p base) : X := prevL base u

omit [FiniteDimensional ℝ E] [CompleteSpace X] in
@[simp]
theorem prevL_apply (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p base) : prevL base u = prev base u := by
  rw [prev]

omit [FiniteDimensional ℝ E] [CompleteSpace X] in
theorem prev_coe (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p base) : prev base u = WithLp.fst u.1 := by
  simp [prev, prevL]

/-- The continuous projection to the adjoined weak derivative. -/
def derivL (base : X →L[ℝ] Lp F p (mu.restrict Omega)) :
    WeakDerivStep mu Omega p base →L[ℝ] Lp (E →L[ℝ] F) p (mu.restrict Omega) :=
  (WithLp.sndL 2 ℝ _ _).comp (weakDerivStepSubmodule mu Omega p base).toSubmodule.subtypeL

/-- The adjoined `Lᵖ` weak derivative. -/
def deriv (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p base) : Lp (E →L[ℝ] F) p (mu.restrict Omega) :=
  derivL base u

omit [FiniteDimensional ℝ E] [CompleteSpace X] in
@[simp]
theorem derivL_apply (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p base) : derivL base u = deriv base u := by
  rw [deriv]

omit [FiniteDimensional ℝ E] [CompleteSpace X] in
theorem deriv_coe (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p base) : deriv base u = WithLp.snd u.1 := by
  simp [deriv, derivL]

/-- Construct an element of a weak-derivative graph from its two components. -/
def mk (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (x : X)
    (D : Lp (E →L[ℝ] F) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (base x) D) : WeakDerivStep mu Omega p base :=
  ⟨WithLp.toLp 2 (x, D), (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn base _).mpr (by simpa)⟩

omit [CompleteSpace X] in
@[simp]
theorem prev_mk (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (x : X)
    (D : Lp (E →L[ℝ] F) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (base x) D) : prev base (mk base x D h) = x := by
  rw [prev_coe]
  simp [mk]

omit [CompleteSpace X] in
@[simp]
theorem deriv_mk (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (x : X)
    (D : Lp (E →L[ℝ] F) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (base x) D) : deriv base (mk base x D h) = D := by
  rw [deriv_coe]
  simp [mk]

omit [CompleteSpace X] in
/-- The adjoined field is the weak derivative of the field selected by `base`. -/
theorem hasWeakFDerivOn_prev (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p base) :
    HasWeakFDerivOn mu Omega (base (prev base u)) (deriv base u) :=
  (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn base u.1).mp u.2

omit [FiniteDimensional ℝ E] [CompleteSpace X] in
/-- The graph norm controls the preceding component. -/
theorem norm_prev_le (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p base) : ‖prev base u‖ ≤ ‖u‖ := by
  rw [prev_coe]
  exact WithLp.norm_fst_le X u.1

omit [FiniteDimensional ℝ E] [CompleteSpace X] in
/-- The graph norm controls the adjoined weak derivative. -/
theorem norm_deriv_le (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p base) : ‖deriv base u‖ ≤ ‖u‖ := by
  rw [deriv_coe]
  exact WithLp.norm_snd_le X u.1

omit [FiniteDimensional ℝ E] [CompleteSpace X] in
/-- The squared graph norm is the sum of the squared component norms. -/
theorem norm_sq_eq_norm_prev_sq_add_norm_deriv_sq
    (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (u : WeakDerivStep mu Omega p base) :
    ‖u‖ ^ 2 = ‖prev base u‖ ^ 2 + ‖deriv base u‖ ^ 2 := by
  rw [Submodule.coe_norm, prev_coe, deriv_coe]
  exact WithLp.prod_norm_sq_eq_of_L2 u.1

instance (base : X →L[ℝ] Lp F p (mu.restrict Omega)) :
    CompleteSpace (WeakDerivStep mu Omega p base) :=
  (weakDerivStepSubmodule mu Omega p base).isClosed.completeSpace_coe

end WeakDerivStep

end TauCeti
