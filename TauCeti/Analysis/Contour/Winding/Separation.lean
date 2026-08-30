/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Segment.Jump
public import TauCeti.Analysis.Normed.Module.FilledHull
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Contour.Curve.Approximation
import TauCeti.Analysis.Contour.Winding.LocallyConstant

/-!
# A segment crossing a set once has its ends on different sides

A closed set `K ⊆ ℂ` with `K \ {p}` preconnected, crossed once by a straight segment at `p` with
`K` adherent from both sides, separates the two ends into different connected components of `Kᶜ`.
The proof uses winding numbers and needs no Jordan curve theorem.

This is the planar-separation input for layer L5 of the `ConformalMapping` roadmap.

## Main results

* `TauCeti.Contour.notMem_connectedComponentIn_compl_of_isPreconnected_sdiff_singleton` — **the
  two ends of the segment lie in different components of `Kᶜ`.**
* `TauCeti.Contour.mem_filledHull_or_mem_filledHull_of_isPreconnected_sdiff_singleton` — **for
  bounded `K`, one end lies in the filled hull.**

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4, §2.1.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Section 2.2.
-/

public section

open Bornology Complex Filter Metric Set

open scoped Topology

namespace TauCeti.Contour

variable {K : Set ℂ} {v z₀ : ℂ} {a b s : ℝ}

/-- **A segment crossing a set once has its ends in different components of the complement.**
Let `K` be closed with `K \ {p}` preconnected, crossed by a straight segment at an interior point
`p = v · s + z₀` with `K` adherent from both sides of the segment. Then the two endpoints
`v · a + z₀` and `v · b + z₀` lie in different connected components of `Kᶜ`. -/
theorem notMem_connectedComponentIn_compl_of_isPreconnected_sdiff_singleton (hK : IsClosed K)
    (hv : v ≠ 0) (hs : s ∈ Ioo a b)
    (hseg : ∀ t ∈ Icc a b, v * t + z₀ ∈ K → t = s)
    (hKp : IsPreconnected (K \ {v * s + z₀}))
    (hleft : v * s + z₀ ∈ closure (K ∩ {q | 0 < ((q - (v * s + z₀)) / v).im}))
    (hright : v * s + z₀ ∈ closure (K ∩ {q | ((q - (v * s + z₀)) / v).im < 0})) :
    v * b + z₀ ∉ connectedComponentIn Kᶜ (v * a + z₀) := by
  intro hmem
  set p : ℂ := v * s + z₀ with hp_def
  have hp : p ∈ K := hK.closure_subset (closure_mono inter_subset_left hleft)
  have hab : a < b := hs.1.trans hs.2
  have hx : v * a + z₀ ∈ Kᶜ := fun h => hs.1.ne (hseg a ⟨le_rfl, hab.le⟩ h)
  have hy : v * b + z₀ ∈ Kᶜ := fun h => hs.2.ne' (hseg b ⟨hab.le, le_rfl⟩ h)
  -- Stage 1: smooth the return path through `Kᶜ`
  have hCopen : IsOpen (connectedComponentIn Kᶜ (v * a + z₀)) :=
    hK.isOpen_compl.connectedComponentIn
  have hCpath : IsPathConnected (connectedComponentIn Kᶜ (v * a + z₀)) :=
    hCopen.isConnected_iff_isPathConnected.mp (isConnected_connectedComponentIn_iff.mpr hx)
  obtain ⟨π₀, hπ₀⟩ := hCpath.joinedIn _ hmem _ (mem_connectedComponentIn hx)
  have hrangeK : range π₀ ⊆ Kᶜ := by
    rintro _ ⟨t, rfl⟩
    exact connectedComponentIn_subset _ _ (hπ₀ t)
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_range π₀.continuous).exists_thickening_subset_open hK.isOpen_compl hrangeK
  obtain ⟨g, hg, hg0, hg1, hgδ⟩ := exists_contDiff_eq_endpoints_dist_lt π₀.toContinuousMap hδ
  replace hg0 : g 0 = v * b + z₀ := hg0.trans π₀.source
  replace hg1 : g 1 = v * a + z₀ := hg1.trans π₀.target
  have hgK : ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ Kᶜ := by
    intro t ht
    apply hthick
    rw [mem_thickening_iff]
    exact ⟨π₀ ⟨t, ht⟩, ⟨_, rfl⟩, by simpa using hgδ ⟨t, ht⟩⟩
  -- Stage 2: construct the closed curve Γ = segment ∪ smooth return
  set Γ : ℝ → ℂ := fun t => if t ≤ b then v * t + z₀ else g (t - b) with hΓ_def
  have hΓseg : EqOn Γ (fun t : ℝ => v * (t : ℂ) + z₀) (Icc a b) := fun t ht => ite_eq_left ht.2
  have hΓg : ∀ t ∈ Icc b (b + 1), Γ t = g (t - b) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      simp [Γ, hg0]
    · exact ite_eq_right (not_le.mpr h)
  have hΓclosed : Γ a = Γ (b + 1) := by
    have h1 : Γ a = v * a + z₀ := ite_eq_left hab.le
    have h2 : Γ (b + 1) = g 1 := by
      rw [hΓg (b + 1) ⟨by linarith, le_rfl⟩]
      ring_nf
    rw [h1, h2, hg1]
  have hΓcont : Continuous Γ := by
    refine Continuous.if_le (by fun_prop)
      (hg.continuous.comp (continuous_id.sub continuous_const)) continuous_id continuous_const ?_
    intro t ht
    simp [ht, hg0]
  have hΓpw : IsPiecewiseC1On Γ a (b + 1) := by
    refine IsPiecewiseC1On.of_breakpoints hΓcont.continuousOn {b} ?_ fun c d hcd hdisj => ?_
    · rw [min_eq_left (by linarith : a ≤ b + 1), max_eq_right (by linarith : a ≤ b + 1),
        Finset.coe_singleton, singleton_subset_iff]
      exact ⟨hab, by linarith⟩
    · have hside : d ≤ b ∨ b ≤ c := by
        by_contra hcon
        push Not at hcon
        exact Set.disjoint_left.mp hdisj (by simp) (mem_Ioo.mpr ⟨hcon.2, hcon.1⟩)
      rw [uIcc_of_le (by linarith : a ≤ b + 1)] at hcd
      rcases hside with hd | hc
      · have hseg1 : ContDiff ℝ 1 fun t : ℝ => v * (t : ℂ) + z₀ :=
          ContDiff.add (ContDiff.mul contDiff_const Complex.ofRealCLM.contDiff) contDiff_const
        exact hseg1.contDiffOn.congr fun t ht => hΓseg ⟨(hcd ht).1, ht.2.trans hd⟩
      · have hg1' : ContDiff ℝ 1 fun t : ℝ => g (t - b) :=
          ContDiff.comp (ContDiff.of_le hg le_top) (ContDiff.sub contDiff_id contDiff_const)
        exact hg1'.contDiffOn.congr fun t ht => hΓg t ⟨hc.trans ht.1, (hcd ht).2⟩
  -- Stage 3: the smooth part avoids p, so the jump formula applies
  have hpg : p ∉ Γ '' Icc b (b + 1) := by
    rintro ⟨t, ht, hpt⟩
    rw [hΓg t ht] at hpt
    exact hgK (t - b) ⟨by linarith [ht.1], by linarith [ht.2]⟩ (by rw [hpt]; exact hp)
  obtain ⟨r, hr, hjump⟩ := exists_forall_windingNumber_eq_add_one_of_eqOn_segment hΓpw hΓclosed
    (by linarith : b ≤ b + 1) hΓseg hv hs hpg
  -- Stage 4: winding number is constant on K \ {p} yet jumps — contradiction
  obtain ⟨q₁, ⟨hq₁K, hq₁im⟩, hq₁r⟩ := Metric.mem_closure_iff.mp hleft r hr
  obtain ⟨q₂, ⟨hq₂K, hq₂im⟩, hq₂r⟩ := Metric.mem_closure_iff.mp hright r hr
  simp only [mem_ofPred_eq] at hq₁im hq₂im
  have hq₁p : q₁ ≠ p := by
    rintro rfl
    simp only [sub_self, zero_div, zero_im, lt_irrefl] at hq₁im
  have hq₂p : q₂ ≠ p := by
    rintro rfl
    simp only [sub_self, zero_div, zero_im, lt_irrefl] at hq₂im
  have hKΓ : K \ {p} ⊆ (Γ '' uIcc a (b + 1))ᶜ := by
    rintro q ⟨hqK, hqp⟩ ⟨t, ht, hqt⟩
    rw [uIcc_of_le (by linarith : a ≤ b + 1)] at ht
    rcases le_or_gt t b with htb | htb
    · have hΓt : Γ t = v * t + z₀ := hΓseg ⟨ht.1, htb⟩
      have hts : t = s := hseg t ⟨ht.1, htb⟩ (by rw [← hΓt, hqt]; exact hqK)
      apply hqp
      rw [mem_singleton_iff, ← hqt, hΓt, hts]
    · rw [hΓg t ⟨htb.le, ht.2⟩] at hqt
      exact hgK (t - b) ⟨by linarith, by linarith [ht.2]⟩ (by rw [hqt]; exact hqK)
  have hW : windingNumber Γ a (b + 1) q₁ = windingNumber Γ a (b + 1) q₂ :=
    hΓpw.windingNumber_eq_of_mem_connectedComponentIn hΓclosed
      (hKp.subset_connectedComponentIn ⟨hq₂K, hq₂p⟩ hKΓ ⟨hq₁K, hq₁p⟩)
  have hJ := hjump q₁ (by rw [mem_ball, dist_comm]; exact hq₁r) q₂
    (by rw [mem_ball, dist_comm]; exact hq₂r) hq₁im hq₂im
  rw [hW] at hJ
  have h0 := sub_eq_zero.mpr hJ
  have h1 : windingNumber Γ a (b + 1) q₂ -
      (windingNumber Γ a (b + 1) q₂ + 1) = -1 := by ring
  rw [h1] at h0
  exact absurd (neg_eq_zero.mp h0) one_ne_zero

/-- **One end of a segment crossing a bounded set once lies in its filled hull.**
Under the same hypotheses as
`notMem_connectedComponentIn_compl_of_isPreconnected_sdiff_singleton`, plus boundedness of `K`,
at least one of `v · a + z₀` and `v · b + z₀` lies in `filledHull K`. -/
theorem mem_filledHull_or_mem_filledHull_of_isPreconnected_sdiff_singleton (hK : IsClosed K)
    (hKb : IsBounded K) (hv : v ≠ 0) (hs : s ∈ Ioo a b)
    (hseg : ∀ t ∈ Icc a b, v * t + z₀ ∈ K → t = s)
    (hKp : IsPreconnected (K \ {v * s + z₀}))
    (hleft : v * s + z₀ ∈ closure (K ∩ {q | 0 < ((q - (v * s + z₀)) / v).im}))
    (hright : v * s + z₀ ∈ closure (K ∩ {q | ((q - (v * s + z₀)) / v).im < 0})) :
    v * a + z₀ ∈ filledHull K ∨ v * b + z₀ ∈ filledHull K := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  exact mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn hrank hKb
    (notMem_connectedComponentIn_compl_of_isPreconnected_sdiff_singleton hK hv hs hseg
      hKp hleft hright)

end TauCeti.Contour
