/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Analysis.Normed.Operator.ClosedRange

/-!
# A map with Fredholm derivative is proper near the point

A continuous map between infinite-dimensional Banach spaces need not be proper: a Fredholm linear
map with nonzero kernel has a noncompact fibre over zero. A map whose derivative at a point `a` is
closed-range with finite-dimensional complemented kernel — in particular, a **Fredholm**
operator — is nonetheless proper on a neighbourhood of `a`:

`∃ N ∈ 𝓝 a, ∀ L compact, N ∩ f ⁻¹' L is compact`.

This is Smale's local properness lemma, the geometric half of the input to the Sard--Smale theorem
(Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. 87 (1965), 861–866;
McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A). Its consequence
recorded here is that the preimage `f ⁻¹' L` of a compact set — in particular a level set
`f ⁻¹' {c}`, the shape every moduli space of the analytic Heegaard Floer roadmap takes — is a
**locally compact** space, even though the Banach space it sits inside is not.

The proof is quantitative rather than chart-theoretic. The a priori estimate
`ContinuousLinearMap.exists_projection_norm_le_mul_norm_add_norm` supplies a continuous projection
`P` of `E` onto `ker f'` and a constant `C > 0` with `‖x‖ ≤ C * ‖f' x‖ + ‖P x‖`; that is exactly
the statement that the linear map `f'.prod P` is anti-Lipschitz. On a small enough closed ball `N`
around `a`, strict differentiability makes `x ↦ (f x, P x)` a small Lipschitz perturbation of
`f'.prod P`, hence anti-Lipschitz there as well. Its second component takes values in the
finite-dimensional space `ker f'`, where bounded sets have compact closure, so `x ↦ (f x, P x)`
sends `N ∩ f ⁻¹' L` into a compact box; being anti-Lipschitz, it reflects total boundedness, and
`N ∩ f ⁻¹' L` is totally bounded and closed, hence compact.

## Main declarations

* `HasStrictFDerivAt.exists_mem_nhds_forall_isCompact_inter_preimage` and
  `HasStrictFDerivAt.exists_mem_nhds_forall_isCompact_inter_preimage_of_isFredholm`: local
  properness, from the unbundled hypotheses and from `ContinuousLinearMap.IsFredholm`.
* `TauCeti.locallyCompactSpace_preimage_of_isClosed_range_of_finite_ker` and
  `TauCeti.locallyCompactSpace_preimage_of_isFredholm`: the preimage of a compact set along which
  the derivative is Fredholm is locally compact.
* `TauCeti.locallyCompactSpace_preimage_singleton_of_isFredholm`: the same for a level set.

Lane F0 of the analytic Heegaard Floer roadmap asks for the package "a moduli space is the zero
set of a Fredholm section, and at a regular point a manifold of dimension the index", of which
`TauCeti.Analysis.Fredholm.LevelSet` supplies the charts; local properness is the complementary
topological half, and it is what will make the critical values of a Fredholm map locally closed
in the Sard--Smale argument.
-/

public section

namespace TauCeti

open Filter Metric Set Submodule Topology
open scoped NNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
variable {f : E → F} {f' : E →L[𝕜] F} {a : E}

/-- **Local properness of a map with upper semi-Fredholm derivative.** If `f` is strictly
differentiable at `a` and its derivative there has closed range and finite-dimensional
complemented kernel, then `f` is proper on a neighbourhood `N` of `a`: the part of the preimage of
any compact set lying in `N` is compact.

Compare `ContinuousLinearMap.exists_projection_norm_le_mul_norm_add_norm`, the linear estimate this
is read off from: the kernel direction, in which `f'` loses all control, is finite-dimensional, so
the loss of compactness it causes is harmless. -/
theorem _root_.HasStrictFDerivAt.exists_mem_nhds_forall_isCompact_inter_preimage
    (hf : HasStrictFDerivAt f f' a) (hclosed : IsClosed (f'.range : Set F))
    (hfinite : FiniteDimensional 𝕜 f'.ker) (hcompl : f'.ker.ClosedComplemented) :
    ∃ N ∈ 𝓝 a, ∀ L : Set F, IsCompact L → IsCompact (N ∩ f ⁻¹' L) := by
  obtain ⟨P, C, hC, _hPidemp, hPrange, hest⟩ :=
    f'.exists_projection_norm_le_mul_norm_add_norm hclosed hcompl
  -- the estimate says precisely that the linear map `f'.prod P` is bounded below
  set K : ℝ≥0 := ⟨C + 1, by positivity⟩ with hKdef
  have hKcoe : (K : ℝ) = C + 1 := rfl
  have hQ : AntilipschitzWith K (f'.prod P) := by
    refine (f'.prod P).antilipschitz_of_bound fun x => ?_
    have hfst : ‖f' x‖ ≤ ‖(f'.prod P) x‖ := by
      rw [ContinuousLinearMap.prod_apply, Prod.norm_def]; exact le_max_left _ _
    have hsnd : ‖P x‖ ≤ ‖(f'.prod P) x‖ := by
      rw [ContinuousLinearMap.prod_apply, Prod.norm_def]; exact le_max_right _ _
    have hx := hest x
    rw [hKcoe]
    nlinarith [norm_nonneg ((f'.prod P) x)]
  -- a perturbation smaller than `K⁻¹` keeps that bound, by
  -- `AntilipschitzWith.add_sub_lipschitzWith`
  set ε : ℝ≥0 := ⟨(2 * (C + 1))⁻¹, by positivity⟩ with hεdef
  have hεcoe : (ε : ℝ) = (2 * (C + 1))⁻¹ := rfl
  have hεpos : 0 < ε := by rw [← NNReal.coe_pos, hεcoe]; positivity
  have hεlt : ε < K⁻¹ := by
    rw [← NNReal.coe_lt_coe, hεcoe, NNReal.coe_inv, hKcoe, inv_lt_inv₀ (by positivity) (by
      positivity)]
    linarith
  obtain ⟨s, hs, happ⟩ := hf.approximates_deriv_on_nhds (Or.inr hεpos)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hs
  set N : Set E := Metric.closedBall a (δ / 2) with hNdef
  have hNs : N ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have happN : ApproximatesLinearOn f f' N ε := happ.mono_set hNs
  have hcontOn : ContinuousOn f N := happN.continuousOn
  refine ⟨N, Metric.closedBall_mem_nhds a (by linarith), fun L hL => ?_⟩
  -- the compact box the projection lands in
  have hPmem : ∀ x, P x ∈ f'.ker := by
    intro x
    rw [← hPrange]
    exact LinearMap.mem_range_self _ x
  let _ : FiniteDimensional 𝕜 f'.ker := hfinite
  have : ProperSpace f'.ker := FiniteDimensional.proper 𝕜 f'.ker
  set Kp : Set E := f'.ker.subtypeL '' Metric.closedBall (0 : f'.ker) (‖P‖ * (‖a‖ + δ / 2))
  have hKpc : IsCompact Kp :=
    (isCompact_closedBall _ _).image f'.ker.subtypeL.continuous
  have hPN : ∀ x ∈ N, P x ∈ Kp := by
    intro x hx
    refine ⟨⟨P x, hPmem x⟩, ?_, rfl⟩
    have hxa : ‖x - a‖ ≤ δ / 2 := by
      rw [hNdef, Metric.mem_closedBall, dist_eq_norm] at hx
      exact hx
    have hnx : ‖x‖ ≤ ‖a‖ + δ / 2 := by
      calc ‖x‖ = ‖a + (x - a)‖ := by rw [add_sub_cancel]
        _ ≤ ‖a‖ + ‖x - a‖ := norm_add_le _ _
        _ ≤ ‖a‖ + δ / 2 := by linarith
    simp only [Metric.mem_closedBall, dist_zero_right, Submodule.coe_norm]
    calc ‖P x‖ ≤ ‖P‖ * ‖x‖ := P.le_opNorm x
      _ ≤ ‖P‖ * (‖a‖ + δ / 2) := by gcongr
  -- the anti-Lipschitz coordinate on `N`: a small perturbation of `f'.prod P`
  set Θ : N → F × E := fun x => (f (x : E), P (x : E)) with hΘdef
  have hsub : Θ - N.domRestrict (f'.prod P) = fun x : N => (f (x : E) - f' (x : E), (0 : E)) := by
    funext x
    simp [hΘdef]
  have hlip : LipschitzWith ε (Θ - N.domRestrict (f'.prod P)) := by
    rw [hsub]
    simpa using happN.lipschitz_sub.prodMk (LipschitzWith.const (α := N) (0 : E))
  have hanti : AntilipschitzWith (K⁻¹ - ε)⁻¹ Θ :=
    (hQ.domRestrict N).add_sub_lipschitzWith hlip hεlt
  have hΘlip : LipschitzWith (‖f'‖₊ + ε + ‖P‖₊) Θ := by
    have h1 : LipschitzWith (‖f'‖₊ + ε) fun x : N => f (x : E) := happN.lipschitz
    have h2 : LipschitzWith ‖P‖₊ fun x : N => P (x : E) := P.lipschitz.restrict N
    exact (h1.prodMk h2).weaken (by simp)
  have hind : IsUniformInducing Θ := hanti.isUniformInducing hΘlip.uniformContinuous
  -- total boundedness, then compactness
  have htb : TotallyBounded
      ((Subtype.val : N → E) '' (Subtype.val : N → E) ⁻¹' (f ⁻¹' L)) := by
    refine TotallyBounded.image ?_ uniformContinuous_subtype_val
    refine (totallyBounded_preimage hind (hL.prod hKpc).totallyBounded).subset ?_
    exact fun x hx => ⟨hx, hPN (x : E) x.2⟩
  rw [Subtype.image_preimage_coe] at htb
  exact htb.isCompact_of_isClosed
    (hcontOn.preimage_isClosed_of_isClosed Metric.isClosed_closedBall hL.isClosed)

/-- **Local properness of a map with Fredholm derivative** (Smale). This is
`HasStrictFDerivAt.exists_mem_nhds_forall_isCompact_inter_preimage` phrased against
`ContinuousLinearMap.IsFredholm`, as `TauCeti.Analysis.Fredholm.Basic` prescribes; the finite
dimensionality of the cokernel plays no role. -/
theorem _root_.HasStrictFDerivAt.exists_mem_nhds_forall_isCompact_inter_preimage_of_isFredholm
    (hf : HasStrictFDerivAt f f' a) (hFred : f'.IsFredholm) :
    ∃ N ∈ 𝓝 a, ∀ L : Set F, IsCompact L → IsCompact (N ∩ f ⁻¹' L) :=
  hf.exists_mem_nhds_forall_isCompact_inter_preimage hFred.isClosed_range hFred.finite_ker
    hFred.closedComplemented_ker

/-- **The preimage of a compact set under a map with upper semi-Fredholm derivative is locally
compact.** If `f` is strictly differentiable at each point of `f ⁻¹' L`, its derivative there has
closed range and finite-dimensional complemented kernel, and `L` is compact, then `f ⁻¹' L`, with
the topology induced from `E`, is a locally compact space.

No compactness is assumed of the ambient Banach space, and none is available: the point is that
the hypotheses confine the failure of local compactness to the finite-dimensional kernel
direction, which is itself locally compact and is controlled by the kernel projection. -/
theorem locallyCompactSpace_preimage_of_isClosed_range_of_finite_ker {D : E → E →L[𝕜] F}
    {L : Set F} (hL : IsCompact L)
    (hf : ∀ x ∈ f ⁻¹' L, HasStrictFDerivAt f (D x) x)
    (hclosed : ∀ x ∈ f ⁻¹' L, IsClosed ((D x).range : Set F))
    (hfinite : ∀ x ∈ f ⁻¹' L, FiniteDimensional 𝕜 (D x).ker)
    (hcompl : ∀ x ∈ f ⁻¹' L, (D x).ker.ClosedComplemented) :
    LocallyCompactSpace (f ⁻¹' L) := by
  have : WeaklyLocallyCompactSpace (f ⁻¹' L) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨N, hN, hprop⟩ :=
      (hf x x.2).exists_mem_nhds_forall_isCompact_inter_preimage
        (hclosed x x.2) (hfinite x x.2) (hcompl x x.2)
    refine ⟨(Subtype.val : (f ⁻¹' L) → E) ⁻¹' N, ?_, ?_⟩
    · rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, Subtype.image_preimage_coe,
        Set.inter_comm]
      exact hprop L hL
    · exact continuous_subtype_val.continuousAt.preimage_mem_nhds hN
  infer_instance

/-- **The preimage of a compact set along which the derivative is Fredholm is locally compact**:
`TauCeti.locallyCompactSpace_preimage_of_isClosed_range_of_finite_ker` phrased against
`ContinuousLinearMap.IsFredholm`. -/
theorem locallyCompactSpace_preimage_of_isFredholm {D : E → E →L[𝕜] F} {L : Set F}
    (hL : IsCompact L) (hf : ∀ x ∈ f ⁻¹' L, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ f ⁻¹' L, (D x).IsFredholm) :
    LocallyCompactSpace (f ⁻¹' L) :=
  locallyCompactSpace_preimage_of_isClosed_range_of_finite_ker hL hf
    (fun x hx => (hFred x hx).isClosed_range) (fun x hx => (hFred x hx).finite_ker)
    fun x hx => (hFred x hx).closedComplemented_ker

/-- **A level set of a map with Fredholm derivative is locally compact**: the case `L = {c}` of
`TauCeti.locallyCompactSpace_preimage_of_isFredholm`, and the shape every moduli space of a
Fredholm problem takes. -/
theorem locallyCompactSpace_preimage_singleton_of_isFredholm {D : E → E →L[𝕜] F} {c : F}
    (hf : ∀ x ∈ f ⁻¹' {c}, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ f ⁻¹' {c}, (D x).IsFredholm) :
    LocallyCompactSpace (f ⁻¹' {c}) :=
  locallyCompactSpace_preimage_of_isFredholm isCompact_singleton hf hFred

end TauCeti
