/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Archon Horizon (claude+codex), Axel Delaval,
  Chunlei Liu, Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.EDistComparison
public import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# The total variation of a curve is bounded by its Riemannian path length

The total variation `eVariationOn γ (Set.Icc a b)` of a curve in a Riemannian manifold is the
supremum of the sums of the ambient distances along finite monotone partitions of `[a, b]`. For a
`C¹` curve it is at most `Manifold.pathELength I γ a b`, the integral of the norm of the velocity,
and the same bound holds for a piecewise-`C¹` curve.

The proof tests the total variation on an arbitrary finite monotone partition: the ambient
distance between consecutive partition points is at most the path length over that subinterval,
and `TauCeti.Manifold.sum_pathELength_eq` telescopes the resulting sum. Combined with Mathlib's
lower semicontinuity of `eVariationOn`, the bound passes to pointwise — hence to uniform — limits
of curves and gives a lower bound for the `liminf` of their Riemannian lengths. The transfer lemma
carrying that last step is stated in `TauCeti.Topology.EMetricSpace.BoundedVariation`, since its
proof uses no manifold structure.

This is one direction of the identification of Riemannian path length with total variation. The
opposite inequality is the remaining ingredient needed to turn the `liminf` bounds proved here
into lower semicontinuity of `Manifold.pathELength` itself.

Like the corner-smoothing comparison of
`TauCeti/Geometry/Manifold/Riemannian/EDistComparison.lean`, the piecewise-`C¹` statement here
only compares the piecewise formulation with Mathlib's `C¹` `Manifold.pathELength`: no piecewise
notion of length or variation is introduced. The limit results concern arbitrary pointwise or
uniform limits of families that are eventually `C¹`.

## Main results

* `TauCeti.eVariationOn_le_liminf_of_eventually_le`: an eventual bound on the total variations of
  a family of maps bounds the total variation of a pointwise limit by the `liminf` of the bounds.
* `TauCeti.Manifold.eVariationOn_le_pathELength`: the total variation of a `C¹` curve on `[a, b]`
  is at most its Riemannian path length there.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.eVariationOn_le_pathELength`: the same bound for a
  piecewise-`C¹` curve.
* `TauCeti.Manifold.eVariationOn_le_liminf_pathELength`: the total variation of a pointwise limit
  of eventually `C¹` curves is at most the `liminf` of their Riemannian path lengths.
* `TauCeti.Manifold.eVariationOn_le_liminf_pathELength_of_tendstoUniformlyOn`: the same bound for
  a uniform limit, which is the convergence mode of the Hopf--Rinow roadmap; it supplies the
  total-variation half of that roadmap's lower-semicontinuity target.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 7, Section 2.
* D. Burago, Y. Burago, and S. Ivanov, *A Course in Metric Geometry*, Section 2.7.1.
* The finite-partition proof of `TauCeti.Manifold.eVariationOn_le_pathELength` is adapted from
  `edist_le_pathELength_of_cmdiff` and `eVariationOn_le_pathELength` in the Apache-2.0 file
  `formalized-sources/DoCarmo/DoCarmoLib/Riemannian/Geodesic/HopfRinow/EVariationLePathELength.lean`
  of [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture),
  revision `24f32e4d600878bfaac6bc2f2f9324175571c321`. That file carries no per-file authorship,
  so the authors above are the contributors credited for the same revision in
  `TauCeti/Geometry/Manifold/Riemannian/EDistComparison.lean`.
* [The Hopf--Rinow roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 0, "Regular reparametrization and limits".
-/

public section

open Bundle Filter Set
open scoped Bundle ContDiff ENNReal Manifold

noncomputable section

namespace TauCeti

namespace Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {γ : ℝ → M} {a b : ℝ}

omit [IsRiemannianManifold I M] in
/-- The finite-partition argument underlying the comparison with Riemannian path length. It is
separated from the regularity assumptions so that both `C¹` and piecewise-`C¹` curves use the
same telescoping proof. -/
private theorem eVariationOn_le_pathELength_of_edist_le
    (hedist : ∀ {s t : ℝ}, a ≤ s → s ≤ t → t ≤ b →
      edist (γ s) (γ t) ≤ Manifold.pathELength I γ s t) :
    eVariationOn γ (Icc a b) ≤ Manifold.pathELength I γ a b := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  have hedist' (i : ℕ) :
      edist (γ (u (i + 1))) (γ (u i)) ≤ Manifold.pathELength I γ (u i) (u (i + 1)) := by
    rw [edist_comm]
    exact hedist (hus i).1 (hu i.le_succ) (hus (i + 1)).2
  calc
    ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))
        ≤ ∑ i ∈ Finset.range n, Manifold.pathELength I γ (u i) (u (i + 1)) :=
      Finset.sum_le_sum fun i _ ↦ hedist' i
    _ = Manifold.pathELength I γ (u 0) (u n) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun i ↦ Manifold.pathELength I γ (u i) (u (i + 1))) n]
      exact sum_pathELength_eq (fun i : Fin (n + 1) ↦ u i) fun i ↦ hu (Nat.le_succ i)
    _ ≤ Manifold.pathELength I γ a b := Manifold.pathELength_mono (hus 0).1 (hus n).2

/-- **The total variation of a `C¹` curve is bounded by its Riemannian path length.** If `γ` is
`C¹` on `[a, b]`, then `eVariationOn γ (Icc a b) ≤ Manifold.pathELength I γ a b`. -/
theorem eVariationOn_le_pathELength (hγ : CMDiff[Icc a b] 1 γ) :
    eVariationOn γ (Icc a b) ≤ Manifold.pathELength I γ a b :=
  eVariationOn_le_pathELength_of_edist_le fun has hst htb ↦
    IsRiemannianManifold.edist_le_pathELength (hγ.mono (Icc_subset_Icc has htb)) hst

/-- The total variation of a piecewise-`C¹` curve on `[a, b]` is at most its Riemannian path
length there. -/
theorem IsPiecewiseContMDiffOn.eVariationOn_le_pathELength
    (hγ : IsPiecewiseContMDiffOn I 1 γ a b) :
    eVariationOn γ (Icc a b) ≤ Manifold.pathELength I γ a b :=
  eVariationOn_le_pathELength_of_edist_le fun has hst htb ↦
    hγ.edist_le_pathELength_of_subset has hst htb

/-- The total variation of a pointwise limit of eventually `C¹` curves is at most the `liminf` of
their Riemannian path lengths.

The stronger-looking conclusion with `Manifold.pathELength I γ a b` on the left requires the
converse comparison between Riemannian path length and total variation. -/
theorem eVariationOn_le_liminf_pathELength {ι : Type*} {l : Filter ι} {γi : ι → ℝ → M}
    (hγi : ∀ᶠ i in l, CMDiff[Icc a b] 1 (γi i))
    (hγ : ∀ t ∈ Icc a b, Tendsto (fun i ↦ γi i t) l (nhds (γ t))) :
    eVariationOn γ (Icc a b) ≤
      liminf (fun i ↦ Manifold.pathELength I (γi i) a b) l :=
  eVariationOn_le_liminf_of_eventually_le
    (hγi.mono fun _ hi ↦ eVariationOn_le_pathELength hi) hγ

/-- The total variation of a uniform limit on `[a, b]` of eventually `C¹` curves is at most the
`liminf` of their Riemannian path lengths. Uniform convergence is the mode in which the
Hopf--Rinow roadmap states lower semicontinuity of length. -/
theorem eVariationOn_le_liminf_pathELength_of_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι} {γi : ι → ℝ → M}
    (hγi : ∀ᶠ i in l, CMDiff[Icc a b] 1 (γi i))
    (hγ : TendstoUniformlyOn γi γ l (Icc a b)) :
    eVariationOn γ (Icc a b) ≤
      liminf (fun i ↦ Manifold.pathELength I (γi i) a b) l :=
  eVariationOn_le_liminf_pathELength hγi fun _ ht ↦ hγ.tendsto_at ht

end Manifold

end TauCeti
