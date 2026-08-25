/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.EDistComparison

/-!
# Metric variation is bounded by Riemannian path length

The metric variation of a `C¹` curve is at most the integral of the norm of its velocity. More
precisely, when the ambient extended distance is the Riemannian distance,
`eVariationOn γ (Set.Icc a b) ≤ Manifold.pathELength I γ a b`. The same result holds for a
piecewise-`C¹` curve.

The proof tests metric variation on an arbitrary finite monotone partition. The Riemannian
distance between consecutive partition points is at most the path length on that subinterval,
and additivity of `Manifold.pathELength` telescopes the resulting sum. This also combines with
Mathlib's lower semicontinuity of `eVariationOn` to give a lower bound on the `liminf` of the
Riemannian lengths of pointwise, hence uniformly, convergent curves.

This is one direction of the identification of Riemannian path length with metric variation. The
opposite inequality is the remaining ingredient needed to turn the final two lower bounds in this
file into lower semicontinuity of `Manifold.pathELength` itself.

## Main results

* `TauCeti.Manifold.eVariationOn_le_pathELength`: metric variation is bounded by the Riemannian
  path length of a `C¹` curve.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.eVariationOn_le_pathELength`: the piecewise-`C¹`
  version.
* `TauCeti.Manifold.eVariationOn_le_liminf_pathELength`: the variation of a pointwise limit is
  bounded by the `liminf` of the approximating Riemannian lengths.
* `TauCeti.Manifold.eVariationOn_le_liminf_pathELength_of_tendstoUniformlyOn`: the uniform-limit
  specialization used by the Hopf--Rinow roadmap.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 7, Section 2.
* D. Burago, Y. Burago, and S. Ivanov, *A Course in Metric Geometry*, Section 2.7.1.
* The proof is adapted from the Apache-2.0 file
  `DoCarmoLib/Riemannian/Geodesic/HopfRinow/EVariationLePathELength.lean` in
  [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture), revision
  `24f32e4d600878bfaac6bc2f2f9324175571c321`.
* [The Hopf--Rinow roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 0, "Regular reparametrization and limits".
-/

public section

open Bundle Filter Set
open scoped Bundle ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

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
private theorem eVariationOn_le_pathELength_of_segment_bound
    (hsegment : ∀ {s t : ℝ}, a ≤ s → s ≤ t → t ≤ b →
      edist (γ s) (γ t) ≤ Manifold.pathELength I γ s t) :
    eVariationOn γ (Icc a b) ≤ Manifold.pathELength I γ a b := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  have hsegment' (i : ℕ) :
      edist (γ (u (i + 1))) (γ (u i)) ≤ Manifold.pathELength I γ (u i) (u (i + 1)) := by
    rw [edist_comm]
    exact hsegment (hus i).1 (hu i.le_succ) (hus (i + 1)).2
  have htelescope (m : ℕ) :
      ∑ i ∈ Finset.range m, Manifold.pathELength I γ (u i) (u (i + 1)) =
        Manifold.pathELength I γ (u 0) (u m) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih,
        Manifold.pathELength_add (hu (Nat.zero_le m)) (hu m.le_succ)]
  calc
    ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))
        ≤ ∑ i ∈ Finset.range n, Manifold.pathELength I γ (u i) (u (i + 1)) :=
      Finset.sum_le_sum fun i _ ↦ hsegment' i
    _ = Manifold.pathELength I γ (u 0) (u n) := htelescope n
    _ ≤ Manifold.pathELength I γ a b := Manifold.pathELength_mono (hus 0).1 (hus n).2

/-- **Metric variation is bounded by Riemannian path length.** If `γ` is `C¹` on `[a, b]`,
then every finite sum of successive ambient distances along `γ` is at most the integral of the
norm of its velocity. -/
theorem eVariationOn_le_pathELength (hγ : CMDiff[Icc a b] 1 γ) :
    eVariationOn γ (Icc a b) ≤ Manifold.pathELength I γ a b := by
  apply eVariationOn_le_pathELength_of_segment_bound
  intro s t has hst htb
  rw [IsRiemannianManifold.out (I := I)]
  exact Manifold.riemannianEDist_le_pathELength
    (hγ.mono (Icc_subset_Icc has htb)) rfl rfl hst

/-- Metric variation is bounded by Riemannian path length for a piecewise-`C¹` curve. The
corners do not contribute to either length, and the already-established piecewise distance bound
applies on every subinterval selected by a metric partition. -/
theorem IsPiecewiseContMDiffOn.eVariationOn_le_pathELength
    (hγ : IsPiecewiseContMDiffOn I 1 γ a b) :
    eVariationOn γ (Icc a b) ≤ Manifold.pathELength I γ a b := by
  apply eVariationOn_le_pathELength_of_segment_bound
  intro s t has hst htb
  rw [IsRiemannianManifold.out (I := I)]
  exact hγ.riemannianEDist_le_pathELength_of_subset has hst htb

/-- The metric variation of a pointwise limit is bounded by the `liminf` of the Riemannian path
lengths of eventually `C¹` approximating curves. Pointwise convergence is enough because metric
variation is the supremum of finite sums, each of which reads only finitely many parameter values.

The stronger-looking conclusion with `pathELength I γ a b` on the left requires the converse
comparison between Riemannian path length and metric variation. -/
theorem eVariationOn_le_liminf_pathELength {γn : ℕ → ℝ → M}
    (hγn : ∀ᶠ n in atTop, CMDiff[Icc a b] 1 (γn n))
    (hγ : ∀ t ∈ Icc a b, Tendsto (fun n ↦ γn n t) atTop (nhds (γ t))) :
    eVariationOn γ (Icc a b) ≤
      liminf (fun n ↦ Manifold.pathELength I (γn n) a b) atTop := by
  rw [le_liminf_iff]
  intro v hv
  filter_upwards [eVariationOn.lowerSemicontinuous_aux hγ hv, hγn] with n hn hγn
  exact hn.trans_le (eVariationOn_le_pathELength hγn)

/-- Uniform convergence on `[a, b]` gives the metric-variation lower bound on the `liminf` of
Riemannian path lengths of eventually `C¹` curves. This is the convergence mode in the Hopf--Rinow
roadmap; the proof passes through the stronger pointwise result above. -/
theorem eVariationOn_le_liminf_pathELength_of_tendstoUniformlyOn {γn : ℕ → ℝ → M}
    (hγn : ∀ᶠ n in atTop, CMDiff[Icc a b] 1 (γn n))
    (hγ : TendstoUniformlyOn γn γ atTop (Icc a b)) :
    eVariationOn γ (Icc a b) ≤
      liminf (fun n ↦ Manifold.pathELength I (γn n) a b) atTop :=
  eVariationOn_le_liminf_pathELength hγn fun _ ht ↦ hγ.tendsto_at ht

end TauCeti.Manifold
