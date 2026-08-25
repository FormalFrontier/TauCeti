/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Arzelà--Ascoli in `ε`-net form

The Arzelà--Ascoli theorem says that a uniformly equicontinuous family of functions whose values
lie in a fixed compact set is relatively compact for uniform convergence on a compact set. This
file records the finite-net form of that conclusion, for a family `g : ι → X → Y` indexed by an
arbitrary type: for each `η > 0` there is a *finite set of indices* `t` such that every member of
the family is uniformly `η`-close on `K` to a member indexed by `t`.

Mathlib states Arzelà--Ascoli (`BoundedContinuousFunction.arzela_ascoli`) as compactness of the
closure of a set of bounded continuous functions on a compact space with a Hausdorff target. The
form proved here is the one an approximation argument wants, and is not a specialization of that
statement: it keeps the indexing, so that the approximating subfamily is a finite subset of the
*original* index set; it needs neither a bundled function space nor a compact ambient space; and,
since a finite net is a statement about approximation rather than about limits, its hypotheses are
total boundedness of `K` and of the sets of values, plus equicontinuity on `K` only — no
compactness, no completeness and no separation axiom. It is the second half of the
Fréchet--Kolmogorov compactness criterion in `Lᵖ`
(`TauCeti/MeasureTheory/Function/Lp/FrechetKolmogorov.lean`), where `ι` indexes an `Lᵖ`-bounded
family of ball averages and `K` is a large closed ball.

## Main declarations

* `TauCeti.exists_finite_approx_of_uniformEquicontinuousOn`: the finite-net form of
  Arzelà--Ascoli.

## Implementation notes

The proof is the classical three-`ε` argument, run through a discretization rather than through a
subsequence: cover `K` by finitely many `δ`-balls centred at points of `K`, with `δ` an
equicontinuity modulus for `η / 4`, cover the values taken at each of those finitely many sample
points by finitely many balls of radius `η / 4`, and record for each index which of the value
balls each sample point lands in. The record takes finitely many values, so it has a right inverse
defined on its range; the finite set of indices produced by that right inverse is the required net.
-/

public section

namespace TauCeti

open Metric Set

variable {ι X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- **Arzelà--Ascoli, in `ε`-net form.** Let `g : ι → X → Y` be a family that is uniformly
equicontinuous on a totally bounded set `K` and whose values at each point of `K` form a totally
bounded set. Then for every `η > 0` there is a finite set of indices `t` such that every member of
the family is uniformly `η`-close on `K` to a member indexed by `t`. -/
theorem exists_finite_approx_of_uniformEquicontinuousOn {K : Set X} (hK : TotallyBounded K)
    {g : ι → X → Y} (hgtb : ∀ x ∈ K, TotallyBounded (Set.range fun i => g i x))
    (hg : UniformEquicontinuousOn g K) {η : ℝ} (hη : 0 < η) :
    ∃ t : Set ι, t.Finite ∧ ∀ i, ∃ j ∈ t, ∀ x ∈ K, dist (g i x) (g j x) ≤ η := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, Set.finite_empty, fun i => (hι.false i).elim⟩
  -- An equicontinuity modulus `δ` for `η / 4`, in `ε`-`δ` form on `K`.
  obtain ⟨δ, hδ, hδg⟩ : ∃ δ > 0, ∀ x ∈ K, ∀ z ∈ K, dist x z < δ →
      ∀ i, dist (g i x) (g i z) < η / 4 := by
    have h := hg _ (dist_mem_uniformity (show (0 : ℝ) < η / 4 by linarith))
    rw [Filter.eventually_iff, Filter.mem_inf_principal] at h
    obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_uniformity_dist.mp h
    exact ⟨δ, hδ, fun x hx z hz hxz i => hδ' hxz ⟨hx, hz⟩ i⟩
  -- A finite `δ`-net of `K` made of points of `K`, ...
  obtain ⟨u, huK, hufin, hucov⟩ := hK.exists_subset (dist_mem_uniformity hδ)
  -- ... and, at each of its points, a finite `η / 4`-net of the values of the family there.
  have hL : ∀ x : u, ∃ L : Set Y, L.Finite ∧ ∀ i, ∃ w ∈ L, dist (g i x) w < η / 4 := by
    intro x
    obtain ⟨L, hLfin, hLcov⟩ :=
      Metric.totallyBounded_iff.mp (hgtb x (huK x.2)) (η / 4) (by linarith)
    refine ⟨L, hLfin, fun i => ?_⟩
    simpa only [mem_iUnion, mem_ball, exists_prop] using hLcov (Set.mem_range_self i)
  choose L hLfin hLmem using hL
  have : Finite u := hufin.to_subtype
  have : ∀ x : u, Finite (L x) := fun x => (hLfin x).to_subtype
  -- Record, for each index, which value ball the value at each sample point falls into.
  have hval : ∀ (i : ι) (x : u), ∃ w : L x, dist (g i x) (w : Y) < η / 4 := fun i x =>
    let ⟨w, hw, hdw⟩ := hLmem x i; ⟨⟨w, hw⟩, hdw⟩
  choose w hw using hval
  -- The record takes finitely many values, so its range has a right inverse.
  refine ⟨Set.range (Function.invFun w), Set.finite_range _, fun i => ?_⟩
  refine ⟨Function.invFun w (w i), Set.mem_range_self _, fun x hx => ?_⟩
  set j := Function.invFun w (w i) with hj
  have hji : w j = w i := Function.invFun_eq ⟨i, rfl⟩
  obtain ⟨x₀, hx₀u, hx₀⟩ : ∃ x₀ ∈ u, dist x x₀ < δ := by
    simpa only [mem_iUnion, mem_ofPred_eq, exists_prop] using hucov hx
  have hsample : dist (g i x₀) (g j x₀) < η / 4 + η / 4 := by
    have hw₁ := hw i ⟨x₀, hx₀u⟩
    have hw₂ := hw j ⟨x₀, hx₀u⟩
    rw [hji] at hw₂
    calc dist (g i x₀) (g j x₀) ≤ dist (g i x₀) (w i ⟨x₀, hx₀u⟩ : Y) +
          dist (w i ⟨x₀, hx₀u⟩ : Y) (g j x₀) := dist_triangle _ _ _
      _ < η / 4 + η / 4 := by
          exact add_lt_add hw₁ (by rw [dist_comm]; exact hw₂)
  refine le_of_lt ?_
  calc dist (g i x) (g j x) ≤ dist (g i x) (g i x₀) + dist (g i x₀) (g j x) :=
        dist_triangle _ _ _
    _ ≤ dist (g i x) (g i x₀) + (dist (g i x₀) (g j x₀) + dist (g j x₀) (g j x)) := by
        gcongr; exact dist_triangle _ _ _
    _ < η / 4 + (η / 4 + η / 4 + η / 4) := by
        refine add_lt_add (hδg x hx x₀ (huK hx₀u) hx₀ i) ?_
        refine add_lt_add hsample ?_
        rw [dist_comm]
        exact hδg x hx x₀ (huK hx₀u) hx₀ j
    _ = η := by ring

end TauCeti
