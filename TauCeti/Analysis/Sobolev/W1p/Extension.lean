/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero

/-!
# Extending a `W^{1,p}_0` function by zero

A function in `W^{1,p}(Ω)` has no reason to stay Sobolev when it is extended by zero across `∂Ω`:
without some condition forcing it to vanish towards the boundary, the extension can fail to be
weakly differentiable on the larger set at all.  For `W^{1,p}_0(Ω)`, the closure of `C_c^∞(Ω)`,
that obstruction disappears, and this file proves it: the zero-extension of a `W^{1,p}_0(Ω)`
function to any larger open set `Ω'` lies in `W^{1,p}_0(Ω')`, and its weak gradient is the
zero-extension of the original weak gradient.

This is the boundary-regularity-free half of Lane A.6 of `TauCetiRoadmap/PDE/README.md`.  Taking
`Ω' = ⊤` gives the extension operator `W^{1,p}_0(Ω) → W^{1,p}(ℝⁿ)` that lane asks for, which is
what lets whole-space statements (Gagliardo--Nirenberg--Sobolev, translation estimates, and
through them Rellich--Kondrachov) be applied to functions given on a domain.  The extension
operator for `W^{1,p}(Ω)` itself is a genuinely harder theorem needing Lipschitz `∂Ω`, and is not
proved here.

## The argument

Everything rests on `TauCeti.w1p0Submodule_subset_of_isClosed`: the zero-extension map is
continuous, and the property "the extension is a test-function limit on `Ω'`" is closed, so it is
enough to check it on test functions.  For a test function it is immediate, because a test
function on `Ω` *is* a test function on `Ω'` — `TestFunction.monoCLM` — and extending it by zero
does not change it at all: it already vanished off `Ω`, as did its gradient.

The zero-extension itself is `TauCeti.extendByZeroLpₗᵢ`, applied once to the value component,
once to the gradient component, and once to the value-gradient jet that carries both.  It is an
isometry of `Lᵖ` spaces, so the extension operator is an isometry of Sobolev spaces:
`TauCeti.W1p0.norm_extendByZeroL`.

## Main declarations

* `TauCeti.Sobolev1JetLp.extendByZeroₗᵢ`: extension by zero of an `Lᵖ` value-gradient jet.
* `TauCeti.Sobolev1JetLp.extendByZeroₗᵢ_mem_w1pSubmodule`: the zero-extension of a `W^{1,p}_0(Ω)`
  function is a Sobolev function on `Ω'`.
* `TauCeti.W1p0.extendByZeroL`: the extension operator `W^{1,p}_0(Ω) →L[ℝ] W^{1,p}_0(Ω')`, with
  `TauCeti.W1p0.norm_extendByZeroL` and its value and gradient components; it is functorial in
  `Ω` by `TauCeti.W1p0.extendByZeroL_self` and
  `TauCeti.W1p0.extendByZeroL_extendByZeroL`.
* `TauCeti.W1p0.value_extendByZeroL_ae_eq_zero_compl`: the whole-space extension vanishes almost
  everywhere off `Ω`.
* `TauCeti.W1p0.hasWeakFDerivOn_indicator`: the analytic content, that the
  zero-extension of `u` is weakly differentiable on `Ω'` with the zero-extension of `∇u` as its
  weak gradient.

## References

Lane A.6 of `TauCetiRoadmap/PDE/README.md`; L. C. Evans, *Partial Differential Equations*,
Section 5.5, and H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Lemma 9.5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace

open scoped Distributions ENNReal Gradient InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega Omega' Omega'' : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Extension by zero of `Lᵖ` jets -/

omit [mu.IsAddHaarMeasure] in
/-- **Extension by zero of an `Lᵖ` value-gradient jet** from `Ω` to a larger open set `Ω'`: both
components are declared zero on `Ω' \ Ω`.  It is an isometry, since the added region contributes
nothing to the `Lᵖ` norm of the jet: both of its components vanish there. -/
def Sobolev1JetLp.extendByZeroₗᵢ (hsub : Omega ≤ Omega') :
    Sobolev1JetLp mu Omega p →ₗᵢ[ℝ] Sobolev1JetLp mu Omega' p :=
  extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- The extension of a jet is the indicator of the original jet. -/
theorem Sobolev1JetLp.coeFn_extendByZeroₗᵢ (hsub : Omega ≤ Omega')
    (J : Sobolev1JetLp mu Omega p) :
    (Sobolev1JetLp.extendByZeroₗᵢ hsub J : E → Sobolev1Jet E) =ᵐ[mu.restrict Omega']
      (Omega : Set E).indicator (J : E → Sobolev1Jet E) :=
  coeFn_extendByZeroLpₗᵢ _ _ _ _

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- The value component of an extended jet is the extension of the value component: taking a
component is a pointwise postcomposition, and `TauCeti.coeFn_extendByZeroLpₗᵢ_comp` says that
those commute with extension by zero. -/
@[simp]
theorem Sobolev1JetLp.value_extendByZeroₗᵢ (hsub : Omega ≤ Omega')
    (J : Sobolev1JetLp mu Omega p) :
    Sobolev1JetLp.value (Sobolev1JetLp.extendByZeroₗᵢ hsub J) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (Sobolev1JetLp.value J) :=
  (Lp.ext ((coeFn_extendByZeroLpₗᵢ_comp ℝ Omega.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr hsub) WithLp.fst rfl (Sobolev1JetLp.value_apply_ae J)).trans
      (Filter.EventuallyEq.symm (Sobolev1JetLp.value_apply_ae _)))).symm

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- The gradient component of an extended jet is the extension of the gradient component; as for
`TauCeti.Sobolev1JetLp.value_extendByZeroₗᵢ`, this is postcomposition commuting with extension. -/
@[simp]
theorem Sobolev1JetLp.gradient_extendByZeroₗᵢ (hsub : Omega ≤ Omega')
    (J : Sobolev1JetLp mu Omega p) :
    Sobolev1JetLp.gradient (Sobolev1JetLp.extendByZeroₗᵢ hsub J) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (Sobolev1JetLp.gradient J) :=
  (Lp.ext ((coeFn_extendByZeroLpₗᵢ_comp ℝ Omega.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr hsub) WithLp.snd rfl (Sobolev1JetLp.gradient_apply_ae J)).trans
      (Filter.EventuallyEq.symm (Sobolev1JetLp.gradient_apply_ae _)))).symm

/-! ### Test functions extend to test functions -/

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- A test function on `Ω`, viewed on the larger open set `Ω'`, is the same function. -/
private theorem coe_monoCLM (hsub : Omega ≤ Omega') (phi : 𝓓(Omega, ℝ)) :
    ((TestFunction.monoCLM ℝ phi : 𝓓(Omega', ℝ)) : E → ℝ) = (phi : E → ℝ) := by
  rw [TestFunction.monoCLM_apply]
  simp [hsub]

omit [FiniteDimensional ℝ E] in
/-- Extending a test function's `Lᵖ` class by zero gives the class of the same test function on
the larger open set: it already vanished outside `Ω`. -/
private theorem extendByZeroLpₗᵢ_testFunctionLp (hsub : Omega ≤ Omega') (phi : 𝓓(Omega, ℝ)) :
    extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (testFunctionLp p phi) =
      testFunctionLp (mu := mu) (Omega := Omega') p (TestFunction.monoCLM ℝ phi) :=
  extendByZeroLpₗᵢ_eq_of_ae_eq ℝ Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
    ((subset_tsupport _).trans phi.tsupport_subset) (testFunctionLp_apply_ae (mu := mu) p phi) <| by
      filter_upwards [testFunctionLp_apply_ae (mu := mu) (Omega := Omega') p
        (TestFunction.monoCLM ℝ phi)] with x hx
      rw [hx, coe_monoCLM hsub phi]

/-- Extending a test function's gradient by zero gives the gradient of the same test function on
the larger open set. -/
private theorem extendByZeroLpₗᵢ_gradientTestFunctionLp (hsub : Omega ≤ Omega')
    (phi : 𝓓(Omega, ℝ)) :
    extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (gradientTestFunctionLp p phi) =
      gradientTestFunctionLp (mu := mu) (Omega := Omega') p (TestFunction.monoCLM ℝ phi) :=
  extendByZeroLpₗᵢ_eq_of_ae_eq ℝ Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
    (support_gradient_testFunction_subset phi)
    (gradientTestFunctionLp_apply_ae (mu := mu) p phi) <| by
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) (Omega := Omega') p
        (TestFunction.monoCLM ℝ phi)] with x hx
      rw [hx, coe_monoCLM hsub phi]

/-- The zero-extension of a test-function jet is the jet of the same test function on the larger
open set. -/
@[simp]
theorem Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ (hsub : Omega ≤ Omega')
    (phi : 𝓓(Omega, ℝ)) :
    Sobolev1JetLp.extendByZeroₗᵢ hsub
        (W1p.ofTestFunctionₗ mu Omega p phi : Sobolev1JetLp mu Omega p) =
      (W1p.ofTestFunctionₗ mu Omega' p (TestFunction.monoCLM ℝ phi) :
        Sobolev1JetLp mu Omega' p) := by
  refine Sobolev1JetLp.ext ?_ ?_
  · rw [Sobolev1JetLp.value_extendByZeroₗᵢ, ← W1p.value_coe, ← W1p.value_coe,
      W1p.value_ofTestFunctionₗ, W1p.value_ofTestFunctionₗ]
    exact extendByZeroLpₗᵢ_testFunctionLp hsub phi
  · rw [Sobolev1JetLp.gradient_extendByZeroₗᵢ, ← W1p.gradient_coe, ← W1p.gradient_coe,
      W1p.gradient_ofTestFunctionₗ, W1p.gradient_ofTestFunctionₗ]
    exact extendByZeroLpₗᵢ_gradientTestFunctionLp hsub phi

/-! ### The extension theorem -/

/-- The zero-extension of a `W^{1,p}_0(Ω)` function belongs to the image of
`W^{1,p}_0(Ω')` in the ambient jet space. -/
private theorem extendByZero_mem_image (hsub : Omega ≤ Omega') {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) :
    Sobolev1JetLp.extendByZeroₗᵢ hsub (u : Sobolev1JetLp mu Omega p) ∈
      Subtype.val '' (w1p0Submodule mu Omega' p : Set (W1p mu Omega' p)) := by
  have hclosed : IsClosed
      (Subtype.val '' (w1p0Submodule mu Omega' p : Set (W1p mu Omega' p))) :=
    ((w1pSubmodule mu Omega' p).isClosed.isClosedEmbedding_subtypeVal).isClosedMap _
      (w1p0Submodule mu Omega' p).isClosed
  have hcont : Continuous fun v : W1p mu Omega p =>
      Sobolev1JetLp.extendByZeroₗᵢ (mu := mu) (p := p) hsub (v : Sobolev1JetLp mu Omega p) :=
    (Sobolev1JetLp.extendByZeroₗᵢ hsub).continuous.comp continuous_subtype_val
  refine w1p0Submodule_subset_of_isClosed (hclosed.preimage hcont) (fun phi => ?_) hu
  exact ⟨W1p.ofTestFunctionₗ mu Omega' p (TestFunction.monoCLM ℝ phi),
    W1p.ofTestFunctionₗ_mem_w1p0Submodule _,
    (Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ hsub phi).symm⟩

/-- Transporting `TauCeti.extendByZero_mem_image` to any Sobolev function on `Ω'` whose ambient
jet is the zero-extension. -/
private theorem mem_w1p0Submodule_of_coe_eq (hsub : Omega ≤ Omega') {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) {v : W1p mu Omega' p}
    (hv : (v : Sobolev1JetLp mu Omega' p) =
      Sobolev1JetLp.extendByZeroₗᵢ hsub (u : Sobolev1JetLp mu Omega p)) :
    v ∈ w1p0Submodule mu Omega' p := by
  obtain ⟨w, hw, hwval⟩ := extendByZero_mem_image hsub hu
  exact Subtype.ext (hwval.trans hv.symm) ▸ hw

/-- **The zero-extension of a `W^{1,p}_0(Ω)` function is a Sobolev function on `Ω'`.**  No
regularity of `∂Ω` is needed, and no boundedness of either open set; the boundary condition
carried by membership in `W^{1,p}_0(Ω)` is what makes the extension weakly differentiable. -/
theorem Sobolev1JetLp.extendByZeroₗᵢ_mem_w1pSubmodule (hsub : Omega ≤ Omega')
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    Sobolev1JetLp.extendByZeroₗᵢ hsub (u : Sobolev1JetLp mu Omega p) ∈
      w1pSubmodule mu Omega' p := by
  obtain ⟨v, -, hv⟩ := extendByZero_mem_image hsub hu
  exact hv ▸ v.2

/-- **Extension by zero as an operator `W^{1,p}_0(Ω) →L[ℝ] W^{1,p}_0(Ω')`.**  The extension of a
limit of test functions on `Ω` is again a limit of test functions, on `Ω'`, so the operator lands
in `W^{1,p}_0(Ω')` and not merely in `W^{1,p}(Ω')`; compose with
`(TauCeti.w1p0Submodule mu Omega' p).toSubmodule.subtypeL` for the `W^{1,p}(Ω')`-valued map.
Taking `Ω' = ⊤`, that is `hsub = le_top`, gives the extension operator to the whole space. -/
def W1p0.extendByZeroL (hsub : Omega ≤ Omega') :
    W1p0 mu Omega p →L[ℝ] W1p0 mu Omega' p :=
  ContinuousLinearMap.codRestrict
    (ContinuousLinearMap.codRestrict
      ((Sobolev1JetLp.extendByZeroₗᵢ (mu := mu) (p := p) hsub).toContinuousLinearMap.comp
        ((w1pSubmodule mu Omega p).toSubmodule.subtypeL.comp
          (w1p0Submodule mu Omega p).toSubmodule.subtypeL))
      (w1pSubmodule mu Omega' p).toSubmodule
      fun u => Sobolev1JetLp.extendByZeroₗᵢ_mem_w1pSubmodule hsub u.2)
    (w1p0Submodule mu Omega' p).toSubmodule
    fun u => mem_w1p0Submodule_of_coe_eq hsub u.2 rfl

/-- The ambient jet of the extension is the extension of the ambient jet. -/
@[simp]
theorem W1p0.coe_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    ((W1p0.extendByZeroL hsub u : W1p mu Omega' p) : Sobolev1JetLp mu Omega' p) =
      Sobolev1JetLp.extendByZeroₗᵢ hsub ((u : W1p mu Omega p) : Sobolev1JetLp mu Omega p) :=
  (rfl)

/-- **Extending by zero from `Ω` to `Ω` does nothing.** -/
@[simp]
theorem W1p0.extendByZeroL_self (u : W1p0 mu Omega p) : W1p0.extendByZeroL le_rfl u = u :=
  Subtype.ext (Subtype.ext (extendByZeroLpₗᵢ_self ℝ _ _))

/-- **Extending by zero twice is extending by zero once.** -/
@[simp]
theorem W1p0.extendByZeroL_extendByZeroL (hsub : Omega ≤ Omega') (hsub' : Omega' ≤ Omega'')
    (u : W1p0 mu Omega p) :
    W1p0.extendByZeroL hsub' (W1p0.extendByZeroL hsub u) =
      W1p0.extendByZeroL (hsub.trans hsub') u :=
  Subtype.ext (Subtype.ext (extendByZeroLpₗᵢ_extendByZeroLpₗᵢ ℝ _ _ _ _ _))

/-- **Extension by zero is an isometry of Sobolev spaces.**  The `W^{1,p}` norm — the `Lᵖ` norm
of the value-gradient jet — is unchanged; the extension adds a region on which both components
vanish. -/
theorem W1p0.norm_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    ‖W1p0.extendByZeroL hsub u‖ = ‖u‖ :=
  (Sobolev1JetLp.extendByZeroₗᵢ hsub).norm_map _

/-- The value component of the extension is the zero-extension of the value component. -/
@[simp]
theorem W1p0.value_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    W1p.value (W1p0.extendByZeroL hsub u : W1p mu Omega' p) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (W1p.value (u : W1p mu Omega p)) := by
  rw [W1p.value_coe, W1p.value_coe, W1p0.coe_extendByZeroL,
    Sobolev1JetLp.value_extendByZeroₗᵢ]

/-- The value component of the whole-space zero extension of `u ∈ W^{1,p}_0(Ω)` vanishes almost
everywhere off `Ω`. Thus its support is contained in `Ω` up to a null set; when `Ω` is bounded,
this is the fixed-bounded-support input for Fréchet--Kolmogorov. -/
theorem W1p0.value_extendByZeroL_ae_eq_zero_compl (u : W1p0 mu Omega p) :
    ∀ᵐ x ∂mu, x ∉ (Omega : Set E) →
      W1p.value (W1p0.extendByZeroL le_top u : W1p mu ⊤ p) x = 0 := by
  rw [W1p0.value_extendByZeroL (Omega' := ⊤) le_top u]
  have hvalue : ⇑(extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet
      (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤))
      (W1p.value (u : W1p mu Omega p))) =ᵐ[mu]
      (Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      coeFn_extendByZeroLpₗᵢ ℝ Omega.isOpen.measurableSet
        (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤)) (W1p.value (u : W1p mu Omega p))
  filter_upwards [hvalue] with x hx hxo
  rw [hx, Set.indicator_of_notMem hxo]

/-- The gradient component of the extension is the zero-extension of the gradient component. -/
@[simp]
theorem W1p0.gradient_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    W1p.gradient (W1p0.extendByZeroL hsub u : W1p mu Omega' p) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (W1p.gradient (u : W1p mu Omega p)) := by
  rw [W1p.gradient_coe, W1p.gradient_coe, W1p0.coe_extendByZeroL,
    Sobolev1JetLp.gradient_extendByZeroₗᵢ]

/-- **The analytic content of the extension theorem.**  The zero-extension of `u ∈ W^{1,p}_0(Ω)`
is weakly differentiable on the larger open set `Ω'`, with weak gradient the zero-extension of the
weak gradient of `u`.  This is the statement that can *fail* for a general `u ∈ W^{1,p}(Ω)`: with
no condition forcing `u` to vanish towards `∂Ω`, its zero-extension need not be weakly
differentiable on `Ω'` at all. -/
theorem W1p0.hasWeakFDerivOn_indicator (hsub : Omega ≤ Omega')
    (u : W1p0 mu Omega p) :
    HasWeakFDerivOn mu Omega'
      ((Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ))
      fun x => innerSL ℝ
        ((Omega : Set E).indicator (W1p.gradient (u : W1p mu Omega p) : E → E) x) := by
  have hbridge :=
    (W1p.value_coe (W1p0.extendByZeroL hsub u : W1p mu Omega' p)).symm
  have hmem := (mem_w1pSubmodule_iff_hasWeakFDerivOn
    ((W1p0.extendByZeroL hsub u : W1p mu Omega' p) : Sobolev1JetLp mu Omega' p)).mp
      (W1p0.extendByZeroL hsub u : W1p mu Omega' p).2
  rw [hbridge] at hmem
  have hvalue : (W1p.value (W1p0.extendByZeroL hsub u : W1p mu Omega' p) : E → ℝ)
      =ᵐ[mu.restrict Omega']
      (Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ) := by
    rw [W1p0.value_extendByZeroL]
    exact coeFn_extendByZeroLpₗᵢ _ _ _ _
  have hgradient : (W1p.gradient (W1p0.extendByZeroL hsub u : W1p mu Omega' p) : E → E)
      =ᵐ[mu.restrict Omega']
      (Omega : Set E).indicator (W1p.gradient (u : W1p mu Omega p) : E → E) := by
    rw [W1p0.gradient_extendByZeroL]
    exact coeFn_extendByZeroLpₗᵢ _ _ _ _
  refine (hmem.congr_ae hvalue).congr_ae_deriv ?_
  filter_upwards [hgradient] with x hx
  refine ContinuousLinearMap.ext fun v => ?_
  rw [Sobolev1JetLp.candidateWeakFDeriv_apply, innerSL_apply_apply, ← W1p.gradient_coe, hx]
  exact real_inner_comm _ _

end TauCeti
