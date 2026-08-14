/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Fredholm.Estimate

/-!
# A map with Fredholm derivative is proper near the point

A continuous map between infinite-dimensional Banach spaces is essentially never proper: closed
balls are not compact, so even a linear isomorphism has noncompact fibres of compact sets. A map
whose derivative at a point `a` is **Fredholm** is nonetheless proper on a neighbourhood of `a`:

`∃ N ∈ 𝓝 a, ∀ L compact, N ∩ f ⁻¹' L is compact`.

This is Smale's local properness lemma, the geometric half of the input to the Sard--Smale theorem
(Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. 87 (1965), 861–866;
McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A). Its consequence
recorded here is that the preimage `f ⁻¹' L` of a compact set — in particular a level set
`f ⁻¹' {c}`, the shape every moduli space of the analytic Heegaard Floer roadmap takes — is a
**locally compact** space, even though the Banach space it sits inside is not.

The proof is quantitative rather than chart-theoretic. The a priori estimate
`ContinuousLinearMap.IsFredholm.exists_projection_norm_le` supplies a continuous projection `P`
of `E` onto `ker f'` and a constant `C > 0` with `‖x‖ ≤ C * ‖f' x‖ + ‖P x‖`. On a small enough
closed ball `N` around `a`, strict differentiability turns this into the two-sided bound

`‖x - y‖ ≤ 2 * (C * ‖f x - f y‖) + 2 * ‖P x - P y‖`  for `x, y ∈ N`,

so the map `x ↦ (f x, P x)` is anti-Lipschitz on `N`. Its second component takes values in the
finite-dimensional space `ker f'`, where bounded sets have compact closure, so `x ↦ (f x, P x)`
sends `N ∩ f ⁻¹' L` into a compact box; being anti-Lipschitz, it reflects total boundedness, and
`N ∩ f ⁻¹' L` is totally bounded and closed, hence compact.

## Main declarations

* `HasStrictFDerivAt.exists_mem_nhds_forall_isCompact_inter_preimage`: local properness.
* `HasStrictFDerivAt.exists_mem_nhds_isCompact_inter_preimage_singleton`: the fibre through
  a point is compact near that point.
* `TauCeti.locallyCompactSpace_preimage` and `TauCeti.locallyCompactSpace_preimage_singleton`: the
  preimage of a compact set, and in particular a level set, along which the derivative is Fredholm
  is locally compact.

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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
variable {f : E → F} {f' : E →L[𝕜] F} {a : E}

/-- **Local properness of a map with Fredholm derivative.** If `f` is strictly differentiable at
`a` and its derivative there is a Fredholm operator, then `f` is proper on a neighbourhood `N` of
`a`: the part of the preimage of any compact set lying in `N` is compact.

Compare `ContinuousLinearMap.IsFredholm.exists_projection_norm_le`, the linear estimate this is
read off from: the kernel direction, in which `f'` loses all control, is finite-dimensional, so
the loss of compactness it causes is harmless. -/
theorem _root_.HasStrictFDerivAt.exists_mem_nhds_forall_isCompact_inter_preimage
    (hf : HasStrictFDerivAt f f' a) (hf' : f'.IsFredholm) :
    ∃ N ∈ 𝓝 a, ∀ L : Set F, IsCompact L → IsCompact (N ∩ f ⁻¹' L) := by
  obtain ⟨P, C, hC, hPrange, hest⟩ := hf'.exists_projection_norm_le
  have hCpos : (0 : ℝ) < 2 * C := by linarith
  set ε : ℝ≥0 := ⟨(2 * C)⁻¹, inv_nonneg.2 hCpos.le⟩
  have hεcoe : (ε : ℝ) = (2 * C)⁻¹ := rfl
  have hεpos : 0 < ε := by
    rw [← NNReal.coe_pos, hεcoe]
    exact inv_pos.2 hCpos
  obtain ⟨s, hs, happ⟩ := hf.approximates_deriv_on_nhds (Or.inr hεpos)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hs
  set N : Set E := Metric.closedBall a (δ / 2) with hNdef
  have hNs : N ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have happN : ApproximatesLinearOn f f' N ε := happ.mono_set hNs
  have hcontOn : ContinuousOn f N := happN.continuousOn
  -- the two-sided bound on `N`
  have key : ∀ x ∈ N, ∀ y ∈ N,
      ‖x - y‖ ≤ 2 * (C * ‖f x - f y‖) + 2 * ‖P x - P y‖ := by
    intro x hx y hy
    have h1 := hest (x - y)
    have h2 := happN x hx y hy
    have h3 : ‖f' (x - y)‖ ≤ ‖f x - f y‖ + (ε : ℝ) * ‖x - y‖ := by
      have hrw : f' (x - y) = f x - f y - (f x - f y - f' (x - y)) := by abel
      rw [hrw]
      exact (norm_sub_le _ _).trans (by linarith)
    have h4 : C * ‖f' (x - y)‖ ≤ C * (‖f x - f y‖ + (ε : ℝ) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left h3 hC.le
    have h5 : C * (‖f x - f y‖ + (ε : ℝ) * ‖x - y‖)
        = C * ‖f x - f y‖ + 1 / 2 * ‖x - y‖ := by
      rw [mul_add, ← mul_assoc, hεcoe]
      field_simp
    rw [map_sub P x y] at h1
    linarith
  refine ⟨N, Metric.closedBall_mem_nhds a (by linarith), fun L hL => ?_⟩
  -- the compact box the projection lands in
  have hPmem : ∀ x, P x ∈ f'.ker := by
    intro x
    rw [← hPrange]
    exact ⟨x, rfl⟩
  have : FiniteDimensional 𝕜 f'.ker := hf'.finite_ker
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
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc ‖(⟨P x, hPmem x⟩ : f'.ker)‖ = ‖P x‖ := rfl
      _ ≤ ‖P‖ * ‖x‖ := P.le_opNorm x
      _ ≤ ‖P‖ * (‖a‖ + δ / 2) := by gcongr
  -- the anti-Lipschitz coordinate on `N`
  set Θ : N → F × E := fun x => (f (x : E), P (x : E))
  have hanti : AntilipschitzWith ⟨2 * C + 2, by positivity⟩ Θ := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have hd1 : ‖f (x : E) - f (y : E)‖ ≤ dist (Θ x) (Θ y) := by
      rw [Prod.dist_eq, ← dist_eq_norm]
      exact le_max_left _ _
    have hd2 : ‖P (x : E) - P (y : E)‖ ≤ dist (Θ x) (Θ y) := by
      rw [Prod.dist_eq, ← dist_eq_norm]
      exact le_max_right _ _
    have hk := key (x : E) x.2 (y : E) y.2
    have hCd : C * ‖f (x : E) - f (y : E)‖ ≤ C * dist (Θ x) (Θ y) :=
      mul_le_mul_of_nonneg_left hd1 hC.le
    rw [Subtype.dist_eq, dist_eq_norm]
    change ‖(x : E) - (y : E)‖ ≤ (2 * C + 2) * dist (Θ x) (Θ y)
    nlinarith [dist_nonneg (x := Θ x) (y := Θ y)]
  have hΘlip : LipschitzWith (‖f'‖₊ + ε + ‖P‖₊) Θ := by
    have h1 : LipschitzWith (‖f'‖₊ + ε) fun x : N => f (x : E) := happN.lipschitz
    have h2 : LipschitzWith ‖P‖₊ fun x : N => P (x : E) := P.lipschitz.restrict N
    exact (h1.prodMk h2).weaken (by simp)
  have hind : IsUniformInducing Θ := hanti.isUniformInducing hΘlip.uniformContinuous
  -- total boundedness, then compactness
  have htb : TotallyBounded ((Subtype.val : N → E) '' {x : N | f (x : E) ∈ L}) := by
    refine TotallyBounded.image ?_ uniformContinuous_subtype_val
    refine (totallyBounded_preimage hind (hL.prod hKpc).totallyBounded).subset ?_
    exact fun x hx => ⟨hx, hPN (x : E) x.2⟩
  have himg : (Subtype.val : N → E) '' {x : N | f (x : E) ∈ L} = N ∩ f ⁻¹' L := by
    rw [show {x : N | f (x : E) ∈ L} = (Subtype.val : N → E) ⁻¹' (f ⁻¹' L) from rfl,
      Subtype.image_preimage_coe, Set.inter_comm]
  rw [himg] at htb
  exact htb.isCompact_of_isClosed
    (hcontOn.preimage_isClosed_of_isClosed Metric.isClosed_closedBall hL.isClosed)

/-- The fibre of `f` through a point at which the derivative is Fredholm is compact near that
point. This is the case `L = {f a}` of local properness, and it is the local finiteness statement
that a moduli space of a Fredholm problem inherits before any global energy bound is imposed. -/
theorem _root_.HasStrictFDerivAt.exists_mem_nhds_isCompact_inter_preimage_singleton
    (hf : HasStrictFDerivAt f f' a) (hf' : f'.IsFredholm) (c : F) :
    ∃ N ∈ 𝓝 a, IsCompact (N ∩ f ⁻¹' {c}) := by
  obtain ⟨N, hN, hprop⟩ := hf.exists_mem_nhds_forall_isCompact_inter_preimage hf'
  exact ⟨N, hN, hprop {c} isCompact_singleton⟩

/-- **The preimage of a compact set under a map with Fredholm derivative is locally compact.** If
`f` is strictly differentiable at each point of `f ⁻¹' L` with Fredholm derivative there, and `L`
is compact, then `f ⁻¹' L`, with the topology induced from `E`, is a locally compact space.

No compactness is assumed of the ambient Banach space, and none is available: the point is that
the Fredholm condition confines the failure of local compactness to the finite-dimensional kernel
direction, which the preimage does not see. -/
theorem locallyCompactSpace_preimage {D : E → E →L[𝕜] F} {L : Set F} (hL : IsCompact L)
    (hf : ∀ x ∈ f ⁻¹' L, HasStrictFDerivAt f (D x) x)
    (hD : ∀ x ∈ f ⁻¹' L, (D x).IsFredholm) :
    LocallyCompactSpace (f ⁻¹' L) := by
  have : WeaklyLocallyCompactSpace (f ⁻¹' L) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨N, hN, hprop⟩ :=
      (hf x x.2).exists_mem_nhds_forall_isCompact_inter_preimage (hD x x.2)
    refine ⟨(Subtype.val : (f ⁻¹' L) → E) ⁻¹' N, ?_, ?_⟩
    · rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, Subtype.image_preimage_coe,
        Set.inter_comm]
      exact hprop L hL
    · exact continuous_subtype_val.continuousAt.preimage_mem_nhds hN
  infer_instance

/-- **A level set of a map with Fredholm derivative is locally compact**: the case `L = {c}` of
`TauCeti.locallyCompactSpace_preimage`, and the shape every moduli space of a Fredholm problem
takes. -/
theorem locallyCompactSpace_preimage_singleton {D : E → E →L[𝕜] F} {c : F}
    (hf : ∀ x ∈ f ⁻¹' {c}, HasStrictFDerivAt f (D x) x)
    (hD : ∀ x ∈ f ⁻¹' {c}, (D x).IsFredholm) :
    LocallyCompactSpace (f ⁻¹' {c}) :=
  locallyCompactSpace_preimage isCompact_singleton hf hD

end TauCeti
