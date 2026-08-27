/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Zero
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The Sobolev embedding `W^{1,p}_0(Ω) ↪ L^{p⋆}(Ω)`

This file proves the **critical Sobolev embedding in the `p < n` regime** on
`W^{1,p}_0(Ω)`: for a domain
`Ω ⊆ E` in a finite-dimensional real inner product space of dimension `n`, an exponent
`1 ≤ p` and the Sobolev conjugate `p⋆` determined by `1/p⋆ + 1/n = 1/p` (so `p < n`),

`‖u‖_{p⋆} ≤ C ‖∇u‖_p` for every `u ∈ W^{1,p}_0(Ω)`,

and it bundles the resulting map `u ↦ u` as a continuous linear map
`W^{1,p}_0(Ω) →L[ℝ] L^{p⋆}(Ω)`. This is the `p < n` half of Lane A.4 of
`TauCetiRoadmap/PDE/README.md`; the Morrey regime `p > n` and the borderline `p = n` are not
proved here.

## Consuming Gagliardo--Nirenberg--Sobolev

The inequality for a *test function* is Mathlib's
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`, with the explicit constant
`MeasureTheory.SNormLESNormFDerivOfEqConst`; nothing is reproved here. What this file adds is
the passage from test functions to their closure `W^{1,p}_0(Ω)`, which is not formal: the two
sides of the estimate live at *different* exponents, so, unlike the Poincaré inequality of
`TauCeti/Analysis/Sobolev/Poincare/W1p0.lean`, the left-hand side is not a continuous function
of the jet.

The fix is that it is still *lower semicontinuous* along `Lᵖ` convergence, which is what
`TauCeti.W1p.isClosed_setOf_eLpNorm_value_le` records: convergence in `W^{1,p}(Ω)` gives convergence
in measure of the values, hence an almost-everywhere convergent subsequence, and Fatou's lemma
in the form `MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm` passes the bound to the limit. With
the set closed, `TauCeti.w1p0Submodule_subset_of_isClosed` finishes.

The estimate is stated for an arbitrary target exponent `q` and constant `C` in
`TauCeti.W1p.eLpNorm_value_le_of_forall_testFunction`, so that any Gagliardo--Nirenberg--Sobolev
variant proved for test functions transfers to `W^{1,p}_0(Ω)` by supplying it as a hypothesis.

## The boundary condition is load-bearing

No embedding of this shape holds on all of `W^{1,p}(Ω)` with `‖∇u‖_p` alone on the right: a
nonzero constant function on a bounded `Ω` has vanishing gradient. Membership in `W^{1,p}_0(Ω)`
is exactly what rules this out, and it is carried as an explicit hypothesis throughout.

## Main declarations

* `TauCeti.W1p.eLpNorm_value_le_of_forall_testFunction`: the transfer principle, from an
  estimate on test functions to the same estimate on `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.eLpNorm_value_le_mul_enorm_gradient`: the Gagliardo--Nirenberg--Sobolev
  inequality on `W^{1,p}_0(Ω)` at the critical exponent `p⋆`.
* `TauCeti.W1p.eLpNorm_value_le_mul_enorm_gradient_of_isBounded`: the same for every `q ≤ p⋆`
  when `Ω` is bounded.
* `TauCeti.W1p.memLp_value_of_mem_w1p0Submodule`: a `W^{1,p}_0(Ω)` function is `L^{p⋆}`.
* `TauCeti.W1p0.sobolevEmbeddingL`: the embedding `W^{1,p}_0(Ω) →L[ℝ] L^{p⋆}(Ω)`, together
  with `TauCeti.W1p0.coeFn_sobolevEmbeddingL` identifying it with the function itself and
  `TauCeti.W1p0.norm_sobolevEmbeddingL_le` bounding it by the gradient alone.

## References

The `p < n` half of Lane A.4 of `TauCetiRoadmap/PDE/README.md`; L. C. Evans, *Partial
Differential Equations*, Section 5.6.1; H. Brezis, *Functional Analysis, Sobolev Spaces and
Partial Differential Equations*, Corollary 9.9.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Module Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Transferring an estimate from test functions to `W^{1,p}_0(Ω)` -/

omit [FiniteDimensional ℝ E] in
/-- The jets whose value has `L^q` norm at most `C` times the `Lᵖ` norm of their gradient form a
**closed** set, for any exponent `q` and constant `C`.

Unlike the equal-exponent case, `u ↦ ‖u‖_q` is not continuous on `W^{1,p}(Ω)` when `q ≠ p`, so
this is not a matter of composing continuous maps. It is instead the lower semicontinuity of
`‖·‖_q`: convergence in `W^{1,p}(Ω)` forces convergence in measure of the values, an
almost-everywhere convergent subsequence, and then Fatou's lemma. -/
theorem W1p.isClosed_setOf_eLpNorm_value_le (q : ENNReal) (C : ℝ≥0) :
    IsClosed {u : W1p mu Omega p |
      eLpNorm (W1p.value u : E → ℝ) q (mu.restrict Omega) ≤ C * ‖W1p.gradient u‖ₑ} := by
  refine IsSeqClosed.isClosed fun v u hv hvu => ?_
  have hvalue : Tendsto (fun k => W1p.value (v k)) atTop (𝓝 (W1p.value u)) := by
    simpa only [W1p.valueL_apply, Function.comp_def] using
      ((map_continuous (W1p.valueL (mu := mu) (Omega := Omega) (p := p))).tendsto u).comp hvu
  have hgradient : Tendsto (fun k => W1p.gradient (v k)) atTop (𝓝 (W1p.gradient u)) := by
    simpa only [W1p.gradientL_apply, Function.comp_def] using
      ((map_continuous (W1p.gradientL (mu := mu) (Omega := Omega) (p := p))).tendsto u).comp hvu
  have hbound : Tendsto (fun k => (C : ℝ≥0∞) * ‖W1p.gradient (v k)‖ₑ) atTop
      (𝓝 ((C : ℝ≥0∞) * ‖W1p.gradient u‖ₑ)) :=
    ENNReal.Tendsto.const_mul ((continuous_enorm.tendsto _).comp hgradient)
      (Or.inr ENNReal.coe_ne_top)
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hvalue).exists_seq_tendsto_ae
  calc eLpNorm (W1p.value u : E → ℝ) q (mu.restrict Omega)
      ≤ atTop.liminf fun i => eLpNorm (W1p.value (v (ns i)) : E → ℝ) q (mu.restrict Omega) :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun _ => Lp.aestronglyMeasurable _) _ hae
    _ ≤ atTop.liminf fun i => (C : ℝ≥0∞) * ‖W1p.gradient (v (ns i))‖ₑ :=
        liminf_le_liminf (.of_forall fun i => hv (ns i))
    _ = (C : ℝ≥0∞) * ‖W1p.gradient u‖ₑ := (hbound.comp hns.tendsto_atTop).liminf_eq

/-- **Transfer of a Sobolev estimate to `W^{1,p}_0(Ω)`.** If every test function on `Ω` satisfies
`‖φ‖_q ≤ C ‖Dφ‖_p`, then so does every `u ∈ W^{1,p}_0(Ω)`.

Only the closedness of the estimate is used, so the hypothesis may be any
Gagliardo--Nirenberg--Sobolev variant available for test functions; the target exponent `q` is
unrelated to `p`. Both norms in the hypothesis are taken with respect to the ambient measure,
which is harmless for a test function because it vanishes outside `Ω`. -/
theorem W1p.eLpNorm_value_le_of_forall_testFunction {q : ENNReal} {C : ℝ≥0}
    (h : ∀ phi : 𝓓(Omega, ℝ),
      eLpNorm (phi : E → ℝ) q mu ≤ C * eLpNorm (fderiv ℝ (phi : E → ℝ)) p mu)
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    eLpNorm (W1p.value u : E → ℝ) q (mu.restrict Omega) ≤ C * ‖W1p.gradient u‖ₑ := by
  refine w1p0Submodule_subset_of_isClosed (W1p.isClosed_setOf_eLpNorm_value_le q C)
    (fun phi => ?_) hu
  have hvalue : eLpNorm (W1p.value (W1p.ofTestFunctionₗ mu Omega p phi) : E → ℝ) q
      (mu.restrict Omega) = eLpNorm (phi : E → ℝ) q mu := by
    rw [W1p.value_ofTestFunctionₗ, eLpNorm_congr_ae (testFunctionLp_apply_ae p phi),
      eLpNorm_restrict_eq_of_support_subset ((subset_tsupport _).trans phi.tsupport_subset)]
  have hgradient : ‖W1p.gradient (W1p.ofTestFunctionₗ mu Omega p phi)‖ₑ =
      eLpNorm (fderiv ℝ (phi : E → ℝ)) p mu := by
    rw [W1p.gradient_ofTestFunctionₗ, enorm_gradientTestFunctionLp_eq_eLpNorm_fderiv]
  simpa only [Set.mem_ofPred_eq, hvalue, hgradient] using h phi

/-! ### The Sobolev embedding at the critical exponent -/

variable {pstar : ENNReal}

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- If `1 ≤ p` and `p⋆⁻¹ + r = p⁻¹` for some `r`, then `1 ≤ p⋆`; nothing about the summand `r`
is used beyond its being an element of `ℝ≥0∞`. Instantiated at `r = (finrank ℝ E : ℝ≥0∞)⁻¹`, it
discharges the `Fact (1 ≤ p⋆)` instance that `L^{p⋆}` needs in order to be a normed space, and so
it occurs in the *type* of `TauCeti.W1p0.sobolevEmbeddingL`. -/
theorem one_le_of_inv_add_eq_inv {r : ENNReal} (hexp : pstar⁻¹ + r = p⁻¹) : 1 ≤ pstar := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  rw [← ENNReal.inv_le_one]
  calc pstar⁻¹ ≤ pstar⁻¹ + r := le_self_add
    _ = p⁻¹ := hexp
    _ ≤ 1 := ENNReal.inv_le_one.2 hp1

/-- **The Gagliardo--Nirenberg--Sobolev inequality on `W^{1,p}_0(Ω)`.** If `1 ≤ p` and the Sobolev
conjugate `p⋆` satisfies `1/p⋆ + 1/n = 1/p`, where `n = dim E`, then every `u ∈ W^{1,p}_0(Ω)`
obeys

`‖u‖_{p⋆} ≤ C ‖∇u‖_p`

with Mathlib's explicit constant `MeasureTheory.SNormLESNormFDerivOfEqConst`, which depends only
on `E`, `mu` and `p`.

The hypothesis `p⋆ ≠ ∞` is the subcritical regime `p < n` in disguise, and the remaining side
conditions come free: `p ≠ ∞`, `p⋆ ≠ 0` and `0 < n` all follow from the exponent identity
together with `1 ≤ p`. No regularity, and no boundedness, of `Ω` is assumed. -/
theorem W1p.eLpNorm_value_le_mul_enorm_gradient (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹)
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    eLpNorm (W1p.value u : E → ℝ) pstar (mu.restrict Omega) ≤
      SNormLESNormFDerivOfEqConst ℝ mu p.toReal * ‖W1p.gradient u‖ₑ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hncast : ((finrank ℝ E : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hn : 0 < finrank ℝ E := by
    rcases Nat.eq_zero_or_pos (finrank ℝ E) with h | h
    · rw [h, Nat.cast_zero, ENNReal.inv_zero, add_top, eq_comm, ENNReal.inv_eq_top] at hexp
      rw [hexp] at hp1
      simp at hp1
    · exact h
  have hpne : p ≠ ∞ := by
    intro h
    rw [h, ENNReal.inv_top, add_eq_zero] at hexp
    exact hncast (ENNReal.inv_eq_zero.1 hexp.2)
  have hpstar0 : pstar ≠ 0 := by
    intro h
    rw [h, ENNReal.inv_zero, top_add, eq_comm, ENNReal.inv_eq_top] at hexp
    rw [hexp] at hp1
    simp at hp1
  have hreal : ((pstar.toNNReal : ℝ))⁻¹ = ((p.toNNReal : ℝ))⁻¹ - ((finrank ℝ E : ℝ))⁻¹ := by
    have htoReal := congrArg ENNReal.toReal hexp
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 hpstar0)
      (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hn.ne'))] at htoReal
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.coe_toNNReal_eq_toReal] at htoReal ⊢
    linarith
  have hp1' : (1 : ℝ≥0) ≤ p.toNNReal := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_one, ENNReal.coe_toNNReal hpne]
    exact hp1
  refine W1p.eLpNorm_value_le_of_forall_testFunction (fun phi => ?_) hu
  have hphi := eLpNorm_le_eLpNorm_fderiv_of_eq (F := ℝ) mu (phi.contDiff.of_le (by simp))
    phi.hasCompactSupport hp1' hn hreal
  rwa [ENNReal.coe_toNNReal hpstar, ENNReal.coe_toNNReal hpne,
    ENNReal.coe_toNNReal_eq_toReal] at hphi

/-! ### Subcritical exponents on a bounded domain -/

/-- **The subcritical Sobolev embedding on a bounded domain.** For `1 ≤ p < n` and any exponent
`q` with `1/p - 1/n ≤ 1/q`, a bounded `Ω` gives

`‖u‖_q ≤ C ‖∇u‖_p` for every `u ∈ W^{1,p}_0(Ω)`,

with the constant `MeasureTheory.eLpNormLESNormFDerivOfLeConst`, which additionally depends on
`Ω` through its measure.  Taking `q = p⋆` recovers
`TauCeti.W1p.eLpNorm_value_le_mul_enorm_gradient` with a worse constant; the point of this form is
the whole range `q ≤ p⋆`, where the estimate is obtained from the critical one by Hölder on a set
of finite measure.

Boundedness of `Ω` is genuinely needed here, unlike at the critical exponent: the interpolation
step needs finite measure, and on the whole space the scaling `u ↦ u(λ ·)` rules the estimate out
for every `q ≠ p⋆`. -/
theorem W1p.eLpNorm_value_le_mul_enorm_gradient_of_isBounded {q : ℝ≥0}
    (hpn : p < (finrank ℝ E : ℝ≥0∞))
    (hpq : (p.toReal)⁻¹ - (finrank ℝ E : ℝ)⁻¹ ≤ (q : ℝ)⁻¹)
    (hOmega : Bornology.IsBounded (Omega : Set E))
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    eLpNorm (W1p.value u : E → ℝ) q (mu.restrict Omega) ≤
      eLpNormLESNormFDerivOfLeConst ℝ mu (Omega : Set E) p.toNNReal q * ‖W1p.gradient u‖ₑ := by
  have hpne : p ≠ ∞ := hpn.ne_top
  have hp1 : (1 : ℝ≥0) ≤ p.toNNReal := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_one, ENNReal.coe_toNNReal hpne]
    exact Fact.out
  have h2p : p.toNNReal < (finrank ℝ E : ℝ≥0) := by
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hpne, ENNReal.coe_natCast]
    exact hpn
  refine W1p.eLpNorm_value_le_of_forall_testFunction (fun phi => ?_) hu
  have hphi := eLpNorm_le_eLpNorm_fderiv_of_le (F := ℝ) (q := q) mu
    (phi.contDiff.of_le (by simp)) ((subset_tsupport _).trans phi.tsupport_subset) hp1 h2p
    (by rwa [NNReal.coe_inv, ENNReal.coe_toNNReal_eq_toReal]) hOmega
  rwa [ENNReal.coe_toNNReal hpne] at hphi

/-! ### The embedding as a continuous linear map -/

/-- A function in `W^{1,p}_0(Ω)` is `p⋆`-integrable: this is what makes the Sobolev embedding a
map into `L^{p⋆}(Ω)` rather than merely an estimate. -/
theorem W1p.memLp_value_of_mem_w1p0Submodule (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹)
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    MemLp (W1p.value u : E → ℝ) pstar (mu.restrict Omega) :=
  ⟨Lp.aestronglyMeasurable _,
    lt_of_le_of_lt (W1p.eLpNorm_value_le_mul_enorm_gradient hpstar hexp hu) (by finiteness)⟩

/-- The `p⋆`-integrability of an element of `W^{1,p}_0(Ω)`, packaged for the subtype. -/
theorem W1p0.memLp_value (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (u : W1p0 mu Omega p) :
    MemLp (W1p.value (u : W1p mu Omega p) : E → ℝ) pstar (mu.restrict Omega) :=
  W1p.memLp_value_of_mem_w1p0Submodule hpstar hexp
    ((ClosedSubmodule.mem_toSubmodule_iff _ _).1 u.2)

/-- The **Sobolev embedding** `W^{1,p}_0(Ω) → L^{p⋆}(Ω)` as a linear map, before recording its
boundedness.  It sends a Sobolev function to its own `L^{p⋆}` class, so the underlying function is
unchanged; see `TauCeti.W1p0.coeFn_sobolevEmbeddingL`. -/
private def W1p0.sobolevEmbeddingₗ (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    W1p0 mu Omega p →ₗ[ℝ] Lp ℝ pstar (mu.restrict Omega) where
  toFun u := (W1p0.memLp_value hpstar hexp u).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    have hvalue : W1p.value ((u : W1p mu Omega p) + (v : W1p mu Omega p)) =
        W1p.value (u : W1p mu Omega p) + W1p.value (v : W1p mu Omega p) := by
      simp only [← W1p.valueL_apply, map_add]
    simp only [Submodule.coe_add, hvalue]
    exact Lp.coeFn_add _ _
  map_smul' c u := by
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    have hvalue : W1p.value (c • (u : W1p mu Omega p)) = c • W1p.value (u : W1p mu Omega p) := by
      simp only [← W1p.valueL_apply, map_smul]
    simp only [RingHom.id_apply, Submodule.coe_smul, hvalue]
    exact Lp.coeFn_smul _ _

private theorem W1p0.coeFn_sobolevEmbeddingₗ (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (u : W1p0 mu Omega p) :
    W1p0.sobolevEmbeddingₗ hpstar hexp u =ᵐ[mu.restrict Omega]
      (W1p.value (u : W1p mu Omega p) : E → ℝ) :=
  (W1p0.memLp_value hpstar hexp u).coeFn_toLp

/-- The `L^{p⋆}` norm of the image is controlled by the `Lᵖ` norm of the *gradient* alone, which
is sharper than the bound by the full graph norm that makes the embedding continuous. -/
private theorem W1p0.norm_sobolevEmbeddingₗ_le (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (u : W1p0 mu Omega p) :
    ‖W1p0.sobolevEmbeddingₗ hpstar hexp u‖ ≤
      SNormLESNormFDerivOfEqConst ℝ mu p.toReal * ‖W1p.gradient (u : W1p mu Omega p)‖ := by
  rw [W1p0.sobolevEmbeddingₗ, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (W1p.eLpNorm_value_le_mul_enorm_gradient hpstar hexp
    ((ClosedSubmodule.mem_toSubmodule_iff _ _).1 u.2)).trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, ofReal_norm]

/-- **The Sobolev embedding `W^{1,p}_0(Ω) ↪ L^{p⋆}(Ω)`.** For `1 ≤ p` and `1/p⋆ + 1/n = 1/p`,
inclusion is a continuous linear map, bounded by Mathlib's Gagliardo--Nirenberg--Sobolev constant
times the graph norm.  The sharper bound by the gradient alone is
`TauCeti.W1p0.norm_sobolevEmbeddingL_le`.

This is an embedding in the honest sense: `TauCeti.W1p0.coeFn_sobolevEmbeddingL` says the image of
`u` is the function `u` itself, so nothing is being reinterpreted. -/
def W1p0.sobolevEmbeddingL (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    W1p0 mu Omega p →L[ℝ] Lp ℝ pstar (mu.restrict Omega) := by
  letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  exact (W1p0.sobolevEmbeddingₗ hpstar hexp).mkContinuous
    (SNormLESNormFDerivOfEqConst ℝ mu p.toReal) fun u =>
    (W1p0.norm_sobolevEmbeddingₗ_le hpstar hexp u).trans
      (mul_le_mul_of_nonneg_left (W1p.norm_gradient_le _) (NNReal.coe_nonneg _))

/-- The Sobolev embedding does not change the function: the image of `u` in `L^{p⋆}(Ω)` is `u`
itself. -/
theorem W1p0.coeFn_sobolevEmbeddingL (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (u : W1p0 mu Omega p) :
    W1p0.sobolevEmbeddingL hpstar hexp u =ᵐ[mu.restrict Omega]
      (W1p.value (u : W1p mu Omega p) : E → ℝ) :=
  by
    let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    rw [W1p0.sobolevEmbeddingL, LinearMap.mkContinuous_apply]
    exact W1p0.coeFn_sobolevEmbeddingₗ hpstar hexp u

/-- The Sobolev embedding is injective. -/
theorem W1p0.sobolevEmbeddingL_injective (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    Function.Injective
      (W1p0.sobolevEmbeddingL (mu := mu) (Omega := Omega) (p := p) hpstar hexp) := by
  intro u v huv
  apply Subtype.ext
  apply W1p.ext_value
  apply Lp.ext
  filter_upwards [W1p0.coeFn_sobolevEmbeddingL hpstar hexp u,
    W1p0.coeFn_sobolevEmbeddingL hpstar hexp v] with x hu hv
  rw [← hu, ← hv, huv]

/-- The image of `u` under the Sobolev embedding is bounded in `L^{p⋆}` by the `Lᵖ` norm of the
gradient of `u` alone.  This is the quantitative content of the embedding, sharper than the bound
by the graph norm that `TauCeti.W1p0.sobolevEmbeddingL` records as its operator bound. -/
theorem W1p0.norm_sobolevEmbeddingL_le (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (u : W1p0 mu Omega p) :
    ‖W1p0.sobolevEmbeddingL hpstar hexp u‖ ≤
      SNormLESNormFDerivOfEqConst ℝ mu p.toReal * ‖W1p.gradient (u : W1p mu Omega p)‖ := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  rw [W1p0.sobolevEmbeddingL, LinearMap.mkContinuous_apply]
  exact W1p0.norm_sobolevEmbeddingₗ_le hpstar hexp u

end TauCeti
