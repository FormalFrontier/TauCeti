/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Leibniz
public import TauCeti.Analysis.Sobolev.W1p.Zero

/-!
# Multiplication by a smooth cutoff on `W^{1,p}(Ω)`

The Leibniz rule of `TauCeti/Analysis/Sobolev/Leibniz.lean` says that `ψ u` is weakly
differentiable whenever `u` is and `ψ` is smooth.  This file upgrades that from a statement about
weak derivatives to a statement about the Sobolev space itself: if `ψ` and `∇ψ` are bounded by a
constant `M`, then

`u ↦ ψ u`

is a continuous linear operator on `W^{1,p}(Ω)` of norm at most `2 M`, with value component `ψ u`
and gradient component `ψ ∇u + u ∇ψ`.

Boundedness of `ψ` *and* of `∇ψ` on `Ω` is what the statement needs, and neither is automatic: for
`ψ x = exp ‖x‖²` on `Ω = ℝⁿ`, multiplication by `ψ` need not preserve `Lᵖ`.  Both bounds are
therefore carried explicitly, through a single constant `M`, so that the operator norm is visible
rather than hidden behind an unquantified `∃ C`; that is the convention the PDE roadmap asks for.
A cutoff built from `ContDiffBump` satisfies them, which is the intended use.

## The operator and the milestone

Multiplication by a cutoff is the localization device of Lane A of
`TauCetiRoadmap/PDE/README.md`: it is the first step of the Meyers--Serrin `H = W` density theorem
and of the extension operator (Lane A.2 and A.6), and it is what converts an interior estimate
into an estimate on a compactly contained subdomain.  Having it as a *bounded operator*, rather
than as a pointwise membership statement, is what lets those arguments range over a family of
cutoffs while keeping uniform control of the resulting Sobolev norms.

The factor `2` in `‖ψ u‖ ≤ 2 M ‖u‖` is explicit, and it is the only shape the downstream
localization arguments need.

## Main declarations

* `TauCeti.W1p.contDiffSMul`: the product `ψ u`, as an element of `W^{1,p}(Ω)`.
* `TauCeti.W1p.value_contDiffSMul_ae` and `TauCeti.W1p.gradient_contDiffSMul_ae`: its two
  components, `ψ u` and `ψ ∇u + u ∇ψ`.
* `TauCeti.W1p.norm_contDiffSMul_le`: the bound `‖ψ u‖ ≤ 2 M ‖u‖`.
* `TauCeti.W1p.contDiffSMulL`: the same map, bundled as a continuous linear operator.
* `TauCeti.W1p.contDiffSMul_mem_w1p0Submodule`: it preserves `W^{1,p}_0(Ω)`, the closure of
  `C_c^∞(Ω)`.

## References

L. C. Evans, *Partial Differential Equations*, §5.2.3, Theorem 1(iv) and §5.3.3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {psi : E → ℝ} {M : ℝ}

/-! ### The two `Lᵖ` components -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- The gradient of a smooth function is the Riesz representative of its Fréchet derivative, hence
continuous.  This is what makes the product below measurable. -/
theorem ContDiff.continuous_gradient (hpsi : ContDiff ℝ ∞ psi) : Continuous (∇ psi) := by
  have heq : ∇ psi = fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ psi x) := by
    funext x
    exact (hasFDerivAt_iff_hasGradientAt.1
      ((hpsi.differentiable (by simp)) x).hasFDerivAt).gradient
  rw [heq]
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hpsi.continuous_fderiv (by simp))

omit [FiniteDimensional ℝ E] in
/-- The value component `ψ u` of the product is `Lᵖ`, because `ψ` is bounded. -/
theorem W1p.memLp_smul_value (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (u : W1p mu Omega p) :
    MemLp (fun x => psi x • W1p.value u x) p (mu.restrict Omega) := by
  refine MemLp.of_le ((Lp.memLp (W1p.value u)).const_mul M) ?_ ?_
  · exact hpsi.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)
  · filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
    rw [smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (hpsiM x hx) (abs_nonneg _)

/-- The gradient component `ψ ∇u + u ∇ψ` of the product is `Lᵖ`, because `ψ` and `∇ψ` are
bounded. -/
theorem W1p.memLp_smul_gradient (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (u : W1p mu Omega p) :
    MemLp (fun x => psi x • W1p.gradient u x + W1p.value u x • ∇ psi x) p (mu.restrict Omega) := by
  refine MemLp.add ?_ ?_
  · refine MemLp.of_le ((Lp.memLp (W1p.gradient u)).const_smul M) ?_ ?_
    · exact hpsi.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)
    · filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
      rw [norm_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hM]
      exact mul_le_mul_of_nonneg_right (hpsiM x hx) (norm_nonneg _)
  · refine MemLp.of_le ((Lp.memLp (W1p.value u)).const_mul M) ?_ ?_
    · exact (Lp.aestronglyMeasurable _).smul
        (ContDiff.continuous_gradient hpsi).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
      rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hM, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hgradM x hx) (abs_nonneg _)

/-! ### The product -/

/-- **Multiplication by a smooth cutoff.**  If `ψ` is smooth with `|ψ| ≤ M` and `‖∇ψ‖ ≤ M` on
`Ω`, the product `ψ u` of `ψ` with a Sobolev function `u ∈ W^{1,p}(Ω)` is again in `W^{1,p}(Ω)`;
its weak gradient is `ψ ∇u + u ∇ψ` by the Leibniz rule. -/
def W1p.contDiffSMul (psi : E → ℝ) (hpsi : ContDiff ℝ ∞ psi) {M : ℝ}
    (hM : 0 ≤ M) (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M)
    (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M) (u : W1p mu Omega p) :
    W1p mu Omega p :=
  W1p.mk ((W1p.memLp_smul_value hpsi hM hpsiM u).toLp _)
    ((W1p.memLp_smul_gradient hpsi hM hpsiM hgradM u).toLp _)
    (by
      have hv := (W1p.memLp_smul_value (mu := mu) (Omega := Omega) (p := p)
        hpsi hM hpsiM u).coeFn_toLp
      have hg := (W1p.memLp_smul_gradient (mu := mu) (Omega := Omega) (p := p)
        hpsi hM hpsiM hgradM u).coeFn_toLp
      refine (((W1p.hasWeakFDerivOn u).contDiff_smul_gradient hpsi).congr_ae
        hv.symm).congr_ae_deriv (hg.mono fun x hx => ?_)
      simp only [hx])

/-- The value component of `ψ u` is `ψ u`. -/
theorem W1p.value_contDiffSMul_ae (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (u : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      W1p.value (W1p.contDiffSMul psi hpsi hM hpsiM hgradM u) x
        = psi x • W1p.value u x := by
  rw [W1p.contDiffSMul, W1p.value_mk]
  exact MemLp.coeFn_toLp _

/-- **The Leibniz rule in `W^{1,p}(Ω)`**: the weak gradient of `ψ u` is `ψ ∇u + u ∇ψ`. -/
theorem W1p.gradient_contDiffSMul_ae (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (u : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      W1p.gradient (W1p.contDiffSMul psi hpsi hM hpsiM hgradM u) x
        = psi x • W1p.gradient u x + W1p.value u x • ∇ psi x := by
  rw [W1p.contDiffSMul, W1p.gradient_mk]
  exact MemLp.coeFn_toLp _

/-! ### Linearity and boundedness -/

/-- Multiplication by `ψ` is additive. -/
theorem W1p.contDiffSMul_add (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (u v : W1p mu Omega p) :
    W1p.contDiffSMul psi hpsi hM hpsiM hgradM (u + v)
      = W1p.contDiffSMul psi hpsi hM hpsiM hgradM u
        + W1p.contDiffSMul psi hpsi hM hpsiM hgradM v := by
  have hvalue : ∀ w z : W1p mu Omega p, W1p.value (w + z) = W1p.value w + W1p.value z := by
    intro w z
    rw [← W1p.valueL_apply, map_add, W1p.valueL_apply, W1p.valueL_apply]
  refine W1p.ext_value (Lp.ext ?_)
  rw [hvalue]
  filter_upwards [W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM (u + v),
    W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM u,
    W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM v,
    Lp.coeFn_add (W1p.value (W1p.contDiffSMul psi hpsi hM hpsiM hgradM u))
      (W1p.value (W1p.contDiffSMul psi hpsi hM hpsiM hgradM v)),
    Lp.coeFn_add (W1p.value u) (W1p.value v)] with x h h₁ h₂ hadd hadd'
  simp only [h, h₁, h₂, hadd, hadd', hvalue u v, Pi.add_apply, smul_eq_mul]
  ring

/-- Multiplication by `ψ` commutes with scalars. -/
theorem W1p.contDiffSMul_smul (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (c : ℝ) (u : W1p mu Omega p) :
    W1p.contDiffSMul psi hpsi hM hpsiM hgradM (c • u)
      = c • W1p.contDiffSMul psi hpsi hM hpsiM hgradM u := by
  have hvalue : ∀ (a : ℝ) (w : W1p mu Omega p), W1p.value (a • w) = a • W1p.value w := by
    intro a w
    rw [← W1p.valueL_apply, map_smul, W1p.valueL_apply]
  refine W1p.ext_value (Lp.ext ?_)
  rw [hvalue]
  filter_upwards [W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM (c • u),
    W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM u,
    Lp.coeFn_smul c (W1p.value (W1p.contDiffSMul psi hpsi hM hpsiM hgradM u)),
    Lp.coeFn_smul c (W1p.value u)] with x h h₁ hsmul hsmul'
  simp only [h, h₁, hsmul, hsmul', hvalue c u, Pi.smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
/-- The squared Euclidean jet norm splits into the value and gradient contributions. -/
private theorem norm_sq_coe_ae (w : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      ‖(w : Sobolev1JetLp mu Omega p) x‖ ^ 2
        = ‖W1p.value w x‖ ^ 2 + ‖W1p.gradient w x‖ ^ 2 := by
  filter_upwards [W1p.value_apply_ae w, W1p.gradient_apply_ae w] with x hv hg
  rw [hv, hg]
  exact WithLp.prod_norm_sq_eq_of_L2 _

/-- **The operator bound.**  Multiplication by `ψ` increases the `W^{1,p}` norm by a factor of at
most `2 M`, where `M` bounds both `|ψ|` and `‖∇ψ‖`.  The two bounds enter separately: `M` scales
the value and the `ψ ∇u` half of the gradient, while the second `M` pays for the Leibniz error
`u ∇ψ`, which is why a bound on `ψ` alone cannot suffice. -/
theorem W1p.norm_contDiffSMul_le (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (u : W1p mu Omega p) :
    ‖W1p.contDiffSMul psi hpsi hM hpsiM hgradM u‖ ≤ 2 * M * ‖u‖ := by
  have hle : ‖(W1p.contDiffSMul psi hpsi hM hpsiM hgradM u : Sobolev1JetLp mu Omega p)‖
      ≤ ‖(2 * M) • (u : Sobolev1JetLp mu Omega p)‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [norm_sq_coe_ae (W1p.contDiffSMul psi hpsi hM hpsiM hgradM u),
      norm_sq_coe_ae u, W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM u,
      W1p.gradient_contDiffSMul_ae hpsi hM hpsiM hgradM u,
      Lp.coeFn_smul (2 * M) (u : Sobolev1JetLp mu Omega p),
      ae_restrict_mem Omega.isOpen.measurableSet] with x hsq hsq' hv hg hsmul hx
    have ha : (0 : ℝ) ≤ ‖W1p.value u x‖ := norm_nonneg _
    have hb : (0 : ℝ) ≤ ‖W1p.gradient u x‖ := norm_nonneg _
    have h₁ : ‖psi x • W1p.value u x‖ ≤ M * ‖W1p.value u x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hpsiM x hx) ha
    have h₂ : ‖psi x • W1p.gradient u x + W1p.value u x • ∇ psi x‖
        ≤ M * ‖W1p.gradient u x‖ + ‖W1p.value u x‖ * M := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hpsiM x hx) hb
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hgradM x hx) (norm_nonneg _)
    have hsqle : ‖(W1p.contDiffSMul psi hpsi hM hpsiM hgradM u : Sobolev1JetLp mu Omega p) x‖ ^ 2
        ≤ (2 * M * ‖(u : Sobolev1JetLp mu Omega p) x‖) ^ 2 := by
      rw [hsq, hv, hg, mul_pow, hsq']
      have hs₁ := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
      have hs₂ := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
      nlinarith [sq_nonneg (‖W1p.value u x‖ - ‖W1p.gradient u x‖), sq_nonneg M,
        mul_nonneg ha hb, mul_nonneg (mul_nonneg hM hM) (mul_nonneg ha hb)]
    have hBnn : (0 : ℝ) ≤ 2 * M * ‖(u : Sobolev1JetLp mu Omega p) x‖ := by positivity
    have hfinal := Real.sqrt_le_sqrt hsqle
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hBnn] at hfinal
    rw [hsmul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hfinal
  calc ‖W1p.contDiffSMul psi hpsi hM hpsiM hgradM u‖
      ≤ ‖(2 * M) • (u : Sobolev1JetLp mu Omega p)‖ := hle
    _ = 2 * M * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * M)]
        rfl

/-- **Multiplication by a smooth cutoff, as a continuous linear operator** on `W^{1,p}(Ω)`, of
norm at most `2 M`. -/
def W1p.contDiffSMulL (psi : E → ℝ) (hpsi : ContDiff ℝ ∞ psi) {M : ℝ}
    (hM : 0 ≤ M) (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M)
    (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M) :
    W1p mu Omega p →L[ℝ] W1p mu Omega p :=
  LinearMap.mkContinuous
    { toFun := W1p.contDiffSMul psi hpsi hM hpsiM hgradM
      map_add' := W1p.contDiffSMul_add hpsi hM hpsiM hgradM
      map_smul' := W1p.contDiffSMul_smul hpsi hM hpsiM hgradM }
    (2 * M) (W1p.norm_contDiffSMul_le hpsi hM hpsiM hgradM)

@[simp]
theorem W1p.contDiffSMulL_apply (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (u : W1p mu Omega p) :
    W1p.contDiffSMulL psi hpsi hM hpsiM hgradM u
      = W1p.contDiffSMul psi hpsi hM hpsiM hgradM u :=
  (rfl)

/-! ### The zero-boundary subspace is preserved -/

/-- Multiplying a test function by a smooth `ψ` gives the test function `ψ φ`, whichever of the
two orders — multiply then embed, or embed then multiply — is used. -/
theorem W1p.contDiffSMul_ofTestFunctionₗ (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (phi Phi : 𝓓(Omega, ℝ))
    (hPhi : (Phi : E → ℝ) = psi * (phi : E → ℝ)) :
    W1p.contDiffSMul psi hpsi hM hpsiM hgradM (W1p.ofTestFunctionₗ mu Omega p phi)
      = W1p.ofTestFunctionₗ mu Omega p Phi := by
  refine W1p.ext_value (Lp.ext ?_)
  rw [W1p.value_ofTestFunctionₗ]
  filter_upwards [W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM
      (W1p.ofTestFunctionₗ mu Omega p phi),
    testFunctionLp_apply_ae (mu := mu) p phi, testFunctionLp_apply_ae (mu := mu) p Phi]
    with x h h₁ h₂
  rw [h, W1p.value_ofTestFunctionₗ, h₁, h₂, hPhi, Pi.mul_apply, smul_eq_mul]

/-- **`W^{1,p}_0(Ω)` is stable under multiplication by a smooth cutoff.**  Since `ψ φ` is again a
test function supported in `Ω`, the operator maps the generating test-function jets back into
`W^{1,p}_0(Ω)`, and continuity extends that to their closure.  This is the form the localization
arguments of Lane A use, because a cutoff must not create a boundary trace. -/
theorem W1p.contDiffSMul_mem_w1p0Submodule (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    W1p.contDiffSMul psi hpsi hM hpsiM hgradM u ∈ w1p0Submodule mu Omega p := by
  have hclosed : IsClosed (W1p.contDiffSMulL psi hpsi hM hpsiM hgradM ⁻¹'
      (w1p0Submodule mu Omega p : Set (W1p mu Omega p))) :=
    (w1p0Submodule mu Omega p).isClosed.preimage
      (W1p.contDiffSMulL psi hpsi hM hpsiM hgradM).continuous
  have htest : ∀ phi : 𝓓(Omega, ℝ), W1p.ofTestFunctionₗ mu Omega p phi ∈
      W1p.contDiffSMulL psi hpsi hM hpsiM hgradM ⁻¹'
        (w1p0Submodule mu Omega p : Set (W1p mu Omega p)) := by
    intro phi
    obtain ⟨Phi, hPhi⟩ : ∃ Phi : 𝓓(Omega, ℝ), (Phi : E → ℝ) = psi * (phi : E → ℝ) :=
      ⟨⟨psi * (phi : E → ℝ), hpsi.mul phi.contDiff, phi.hasCompactSupport.mul_left,
        tsupport_mul_subset_right.trans phi.tsupport_subset⟩, rfl⟩
    simp only [Set.mem_preimage, SetLike.mem_coe, W1p.contDiffSMulL_apply,
      W1p.contDiffSMul_ofTestFunctionₗ hpsi hM hpsiM hgradM phi Phi hPhi]
    exact W1p.ofTestFunctionₗ_mem_w1p0Submodule Phi
  have := w1p0Submodule_subset_of_isClosed hclosed htest hu
  simpa using this

/-- The operator norm of multiplication by `ψ` is at most `2 M`. -/
theorem W1p.norm_contDiffSMulL_le (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M)
    (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M) :
    ‖W1p.contDiffSMulL (mu := mu) (Omega := Omega) (p := p)
      psi hpsi hM hpsiM hgradM‖ ≤ 2 * M :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end TauCeti
