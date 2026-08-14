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
and an `Lᵖ` candidate Hessian, with their Euclidean product norm. -/
abbrev Sobolev2JetLp (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] :=
  WithLp 2 (W1p mu Omega p × Lp (E →L[ℝ] E) p (mu.restrict Omega))

/-- The continuous linear projection of a second-order jet to its first-order Sobolev part. -/
def Sobolev2JetLp.firstOrderL : Sobolev2JetLp mu Omega p →L[ℝ] W1p mu Omega p :=
  WithLp.fstL 2 ℝ _ _

/-- The first-order Sobolev part of a second-order jet. -/
def Sobolev2JetLp.firstOrder (J : Sobolev2JetLp mu Omega p) : W1p mu Omega p :=
  Sobolev2JetLp.firstOrderL J

omit [FiniteDimensional ℝ E] in
@[simp]
theorem Sobolev2JetLp.firstOrder_eq_fst (J : Sobolev2JetLp mu Omega p) :
    Sobolev2JetLp.firstOrder J = WithLp.fst J := (rfl)

/-- The continuous linear projection of a second-order jet to its candidate Hessian. -/
def Sobolev2JetLp.hessianL :
    Sobolev2JetLp mu Omega p →L[ℝ] Lp (E →L[ℝ] E) p (mu.restrict Omega) :=
  WithLp.sndL 2 ℝ _ _

/-- The candidate `Lᵖ` Hessian of a second-order jet. -/
def Sobolev2JetLp.hessian (J : Sobolev2JetLp mu Omega p) :
    Lp (E →L[ℝ] E) p (mu.restrict Omega) :=
  Sobolev2JetLp.hessianL J

omit [FiniteDimensional ℝ E] in
@[simp]
theorem Sobolev2JetLp.hessian_eq_snd (J : Sobolev2JetLp mu Omega p) :
    Sobolev2JetLp.hessian J = WithLp.snd J := (rfl)

omit [FiniteDimensional ℝ E] in
/-- Two second-order jets are equal when their first-order parts and Hessians are equal. -/
@[ext]
theorem Sobolev2JetLp.ext {J K : Sobolev2JetLp mu Omega p}
    (hfirstOrder : Sobolev2JetLp.firstOrder J = Sobolev2JetLp.firstOrder K)
    (hhessian : Sobolev2JetLp.hessian J = Sobolev2JetLp.hessian K) : J = K := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  exact Prod.ext hfirstOrder hhessian

private def testFunctionLp (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    Lp ℝ q (mu.restrict Omega) :=
  (phi.continuous.memLp_of_hasCompactSupport (μ := mu.restrict Omega) (p := q)
    phi.hasCompactSupport).toLp phi

omit [FiniteDimensional ℝ E] in
@[simp]
private theorem testFunctionLp_apply_ae (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    ∀ᵐ x ∂mu.restrict Omega, testFunctionLp (mu := mu) q phi x = phi x :=
  (phi.continuous.memLp_of_hasCompactSupport (μ := mu.restrict Omega) (p := q)
    phi.hasCompactSupport).coeFn_toLp

/-- The continuous functional expressing that the candidate Hessian is the weak derivative of
the first-order jet's gradient, tested against `phi` in the direction `v`. -/
private def weakHessianTestFunctional (p : ENNReal) [Fact (1 <= p)]
    (phi : 𝓓(Omega, ℝ)) (v : E) : Sobolev2JetLp mu Omega p →L[ℝ] E := by
  let _ : (ENNReal.conjExponent p).HolderConjugate p := ENNReal.HolderConjugate.symm
  let _ : Fact (1 <= ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le _ p⟩
  let dphi : 𝓓(Omega, ℝ) := TestFunction.lineDerivCLM ℝ v phi
  let gradientL : Sobolev2JetLp mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
    W1p.gradientL.comp Sobolev2JetLp.firstOrderL
  let hessianDirectionL :
      Sobolev2JetLp mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
    (ContinuousLinearMap.apply ℝ E v).compLpL p (mu.restrict Omega) |>.comp
      Sobolev2JetLp.hessianL
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
      (∫ x, lineDeriv ℝ (phi : E → ℝ) x v •
          W1p.gradient (Sobolev2JetLp.firstOrder J) x ∂mu) +
        ∫ x, phi x • Sobolev2JetLp.hessian J x v ∂mu := by
  let _ : (ENNReal.conjExponent p).HolderConjugate p := ENNReal.HolderConjugate.symm
  let _ : Fact (1 <= ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le _ p⟩
  let dphi : 𝓓(Omega, ℝ) := TestFunction.lineDerivCLM ℝ v phi
  let gradientL : Sobolev2JetLp mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
    W1p.gradientL.comp Sobolev2JetLp.firstOrderL
  let hessianDirectionL :
      Sobolev2JetLp mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
    (ContinuousLinearMap.apply ℝ E v).compLpL p (mu.restrict Omega) |>.comp
      Sobolev2JetLp.hessianL
  let smulPairing :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).lpPairing
      (mu.restrict Omega) (ENNReal.conjExponent p) p
  have hdphi : (dphi : E → ℝ) = fun x => lineDeriv ℝ (phi : E → ℝ) x v := by
    funext x
    exact TestFunction.lineDerivCLM_apply_of_le le_top
  have hgradient : gradientL J = W1p.gradient (Sobolev2JetLp.firstOrder J) := by
    simp only [gradientL, Sobolev2JetLp.firstOrder, ContinuousLinearMap.comp_apply,
      W1p.gradientL_apply]
  have hhessian : hessianDirectionL J =
      (ContinuousLinearMap.apply ℝ E v).compLp (Sobolev2JetLp.hessian J) := rfl
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
        ∫ x in Omega, lineDeriv ℝ (phi : E → ℝ) x v •
          W1p.gradient (Sobolev2JetLp.firstOrder J) x ∂mu := by
    apply integral_congr_ae
    filter_upwards [testFunctionLp_apply_ae (mu := mu) (ENNReal.conjExponent p) dphi]
      with x hx
    rw [hx, hgradient, congrFun hdphi x]
  have hsecond :
      (∫ x, testFunctionLp (mu := mu) (ENNReal.conjExponent p) phi x •
          hessianDirectionL J x ∂mu.restrict Omega) =
        ∫ x in Omega, phi x • Sobolev2JetLp.hessian J x v ∂mu := by
    apply integral_congr_ae
    filter_upwards [testFunctionLp_apply_ae (mu := mu) (ENNReal.conjExponent p) phi,
      (ContinuousLinearMap.apply ℝ E v).coeFn_compLp (Sobolev2JetLp.hessian J)] with x hphi hx
    rw [hphi, hhessian, hx, ContinuousLinearMap.apply_apply]
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [hfirst, hsecond]
  congr 1
  · apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [lineDeriv_eq_zero_of_notMem_tsupport phi
      (fun hmem => hx (phi.tsupport_subset hmem)) v]
    simp
  · apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hmem => hx (phi.tsupport_subset hmem))]
    simp

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
        (∫ x, lineDeriv ℝ (phi : E → ℝ) x v •
            W1p.gradient (Sobolev2JetLp.firstOrder J) x ∂mu) +
          ∫ x, phi x • Sobolev2JetLp.hessian J x v ∂mu = 0 := by
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
      HasWeakFDerivOn mu Omega (W1p.gradient (Sobolev2JetLp.firstOrder J))
        (Sobolev2JetLp.hessian J) := by
  have hgradient : LocallyIntegrableOn (W1p.gradient (Sobolev2JetLp.firstOrder J)) Omega mu :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (W1p.gradient (Sobolev2JetLp.firstOrder J))).locallyIntegrable Fact.out)
  have hhessian (v : E) :
      LocallyIntegrableOn (fun x => Sobolev2JetLp.hessian J x v) Omega mu := by
    apply locallyIntegrableOn_of_locallyIntegrable_restrict
    exact (((Lp.memLp (Sobolev2JetLp.hessian J)).continuousLinearMap_comp
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

/-- The continuous linear projection from `W2p` to its first-order Sobolev component. -/
def W2p.firstOrderL : W2p mu Omega p →L[ℝ] W1p mu Omega p :=
  Sobolev2JetLp.firstOrderL.comp (w2pSubmodule mu Omega p).toSubmodule.subtypeL

/-- The first-order Sobolev component of a second-order Sobolev function. -/
def W2p.firstOrder (u : W2p mu Omega p) : W1p mu Omega p :=
  W2p.firstOrderL u

@[simp]
theorem W2p.firstOrderL_apply (u : W2p mu Omega p) :
    W2p.firstOrderL u = W2p.firstOrder u := (rfl)

@[simp]
theorem W2p.firstOrder_coe (u : W2p mu Omega p) :
    W2p.firstOrder u = Sobolev2JetLp.firstOrder u.1 := (rfl)

/-- The continuous linear projection from `W2p` to its `Lᵖ` value component. -/
def W2p.valueL : W2p mu Omega p →L[ℝ] Lp ℝ p (mu.restrict Omega) :=
  W1p.valueL.comp W2p.firstOrderL

/-- The `Lᵖ` value component of a second-order Sobolev function. -/
def W2p.value (u : W2p mu Omega p) : Lp ℝ p (mu.restrict Omega) :=
  W2p.valueL u

@[simp]
theorem W2p.valueL_apply (u : W2p mu Omega p) : W2p.valueL u = W2p.value u := (rfl)

@[simp]
theorem W2p.value_eq_value_firstOrder (u : W2p mu Omega p) :
    W2p.value u = W1p.value (W2p.firstOrder u) := by
  calc
    W2p.value u = W1p.valueL (W2p.firstOrder u) := (rfl)
    _ = W1p.value (W2p.firstOrder u) := W1p.valueL_apply _

/-- The continuous linear projection from `W2p` to its `Lᵖ` weak-gradient component. -/
def W2p.gradientL : W2p mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
  W1p.gradientL.comp W2p.firstOrderL

/-- The `Lᵖ` weak gradient of a second-order Sobolev function. -/
def W2p.gradient (u : W2p mu Omega p) : Lp E p (mu.restrict Omega) :=
  W2p.gradientL u

@[simp]
theorem W2p.gradientL_apply (u : W2p mu Omega p) :
    W2p.gradientL u = W2p.gradient u := (rfl)

@[simp]
theorem W2p.gradient_eq_gradient_firstOrder (u : W2p mu Omega p) :
    W2p.gradient u = W1p.gradient (W2p.firstOrder u) := by
  calc
    W2p.gradient u = W1p.gradientL (W2p.firstOrder u) := (rfl)
    _ = W1p.gradient (W2p.firstOrder u) := W1p.gradientL_apply _

/-- The continuous linear projection from `W2p` to its weak Hessian. -/
def W2p.hessianL : W2p mu Omega p →L[ℝ] Lp (E →L[ℝ] E) p (mu.restrict Omega) :=
  Sobolev2JetLp.hessianL.comp (w2pSubmodule mu Omega p).toSubmodule.subtypeL

/-- The `Lᵖ` weak Hessian of a second-order Sobolev function. -/
def W2p.hessian (u : W2p mu Omega p) : Lp (E →L[ℝ] E) p (mu.restrict Omega) :=
  W2p.hessianL u

@[simp]
theorem W2p.hessianL_apply (u : W2p mu Omega p) :
    W2p.hessianL u = W2p.hessian u := (rfl)

@[simp]
theorem W2p.hessian_coe (u : W2p mu Omega p) :
    W2p.hessian u = Sobolev2JetLp.hessian u.1 := (rfl)

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
  simp [W2p.firstOrder, W2p.firstOrderL, W2p.mk, Sobolev2JetLp.firstOrderL]

@[simp]
theorem W2p.value_mk (u : W1p mu Omega p)
    (H : Lp (E →L[ℝ] E) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (W1p.gradient u) H) :
    W2p.value (W2p.mk u H h) = W1p.value u := by
  rw [W2p.value_eq_value_firstOrder, W2p.firstOrder_mk]

@[simp]
theorem W2p.gradient_mk (u : W1p mu Omega p)
    (H : Lp (E →L[ℝ] E) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (W1p.gradient u) H) :
    W2p.gradient (W2p.mk u H h) = W1p.gradient u := by
  rw [W2p.gradient_eq_gradient_firstOrder, W2p.firstOrder_mk]

@[simp]
theorem W2p.hessian_mk (u : W1p mu Omega p)
    (H : Lp (E →L[ℝ] E) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (W1p.gradient u) H) :
    W2p.hessian (W2p.mk u H h) = H := by
  simp [W2p.hessian, W2p.hessianL, W2p.mk, Sobolev2JetLp.hessianL]

/-- Two second-order Sobolev functions are equal when their first-order components and weak
Hessians are equal. -/
theorem W2p.ext_firstOrder {u v : W2p mu Omega p}
    (hfirstOrder : W2p.firstOrder u = W2p.firstOrder v)
    (hhessian : W2p.hessian u = W2p.hessian v) : u = v :=
  Subtype.ext (Sobolev2JetLp.ext hfirstOrder hhessian)

/-- The value-gradient pair underlying a second-order Sobolev function satisfies the first weak
derivative identity. -/
theorem W2p.hasWeakFDerivOn (u : W2p mu Omega p) :
    HasWeakFDerivOn mu Omega (W2p.value u) (fun x => innerSL ℝ (W2p.gradient u x)) := by
  simpa using W1p.hasWeakFDerivOn (W2p.firstOrder u)

/-- The Hessian of a second-order Sobolev function is the weak Fréchet derivative of its weak
gradient. -/
theorem W2p.hasWeakFDerivOn_gradient (u : W2p mu Omega p) :
    HasWeakFDerivOn mu Omega (W2p.gradient u) (W2p.hessian u) := by
  simpa using (mem_w2pSubmodule_iff_hasWeakFDerivOn u.1).mp u.2

/-- Two second-order Sobolev functions are equal when their `Lᵖ` value components are equal.
Successive uniqueness of weak derivatives determines both the gradient and Hessian components. -/
@[ext]
theorem W2p.ext {u v : W2p mu Omega p} (hvalue : W2p.value u = W2p.value v) : u = v := by
  have hfirstOrder : W2p.firstOrder u = W2p.firstOrder v := by
    apply W1p.ext_value
    simpa using hvalue
  have hgradient : W2p.gradient u = W2p.gradient v := by
    simpa using congrArg W1p.gradient hfirstOrder
  have hv : HasWeakFDerivOn mu Omega (W2p.gradient u) (W2p.hessian v) := by
    simpa only [hgradient] using W2p.hasWeakFDerivOn_gradient v
  have hhessian : W2p.hessian u = W2p.hessian v :=
    Lp.ext ((W2p.hasWeakFDerivOn_gradient u).ae_eq hv)
  exact W2p.ext_firstOrder hfirstOrder hhessian

/-- The norm of a second-order Sobolev function controls the norm of its first-order component. -/
theorem W2p.norm_firstOrder_le (u : W2p mu Omega p) : ‖W2p.firstOrder u‖ ≤ ‖u‖ := by
  rw [W2p.firstOrder_coe, Sobolev2JetLp.firstOrder_eq_fst]
  exact WithLp.norm_fst_le (W1p mu Omega p) u.1

/-- The norm of a second-order Sobolev function controls the norm of its value component. -/
theorem W2p.norm_value_le (u : W2p mu Omega p) : ‖W2p.value u‖ ≤ ‖u‖ :=
  W2p.value_eq_value_firstOrder u ▸
    (W1p.norm_value_le (W2p.firstOrder u)).trans (W2p.norm_firstOrder_le u)

/-- The norm of a second-order Sobolev function controls the norm of its weak gradient. -/
theorem W2p.norm_gradient_le (u : W2p mu Omega p) : ‖W2p.gradient u‖ ≤ ‖u‖ :=
  W2p.gradient_eq_gradient_firstOrder u ▸
    (W1p.norm_gradient_le (W2p.firstOrder u)).trans (W2p.norm_firstOrder_le u)

/-- The norm of a second-order Sobolev function controls the norm of its weak Hessian. -/
theorem W2p.norm_hessian_le (u : W2p mu Omega p) : ‖W2p.hessian u‖ ≤ ‖u‖ := by
  rw [W2p.hessian_coe, Sobolev2JetLp.hessian_eq_snd]
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
    ‖u‖ ^ 2 = ‖W2p.value u‖ ^ 2 + ‖W2p.gradient u‖ ^ 2 + ‖W2p.hessian u‖ ^ 2 := by
  rw [W2p.norm_sq_eq_norm_firstOrder_sq_add_norm_hessian_sq,
    W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  simp only [W2p.value_eq_value_firstOrder, W2p.gradient_eq_gradient_firstOrder]

/-- `W^{2,p}(Ω)` is complete in its iterated weak-derivative graph norm. -/
instance : CompleteSpace (W2p mu Omega p) :=
  (w2pSubmodule mu Omega p).isClosed.completeSpace_coe

end TauCeti
