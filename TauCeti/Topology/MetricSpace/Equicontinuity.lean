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

Mathlib states Arzelà--Ascoli
(`BoundedContinuousFunction.arzela_ascoli`) as compactness of the closure of a set of bounded
continuous functions on a compact space. The form proved here is the one an approximation
argument wants: it keeps the indexing, so that the approximating subfamily is a finite subset of
the *original* index set, and it needs neither a bundled function space nor a compact ambient
space. It is the second half of the Fréchet--Kolmogorov compactness criterion in `Lᵖ`
(`TauCeti/MeasureTheory/Function/Lp/FrechetKolmogorov.lean`), where `ι` indexes an `Lᵖ`-bounded
family of ball averages and `K` is a large closed ball.

## Main declarations

* `TauCeti.exists_finite_approx_of_uniformEquicontinuous`: the finite-net form of
  Arzelà--Ascoli.

## Implementation notes

The proof is the classical three-`ε` argument, run through a discretization rather than through a
subsequence: cover `K` by finitely many balls of radius `δ`, with `δ` an equicontinuity modulus
for `η / 4`, cover the compact set of values by finitely many balls of radius `η / 4`, and record
for each index which of the value balls each of the finitely many sample points lands in. The
record takes finitely many values, so it has a right inverse defined on its range; the finite set
of indices produced by that right inverse is the required net.
-/

public section

namespace TauCeti

open Metric Set

variable {ι X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- **Arzelà--Ascoli, in `ε`-net form.** Let `g : ι → X → Y` be a uniformly equicontinuous family
whose members take, on a compact set `K`, their values in a fixed compact set `V`. Then for every
`η > 0` there is a finite set of indices `t` such that every member of the family is uniformly
`η`-close on `K` to a member indexed by `t`. -/
theorem exists_finite_approx_of_uniformEquicontinuous {K : Set X} (hK : IsCompact K) {V : Set Y}
    (hV : IsCompact V) {g : ι → X → Y} (hgV : ∀ i, ∀ x ∈ K, g i x ∈ V)
    (hg : UniformEquicontinuous g) {η : ℝ} (hη : 0 < η) :
    ∃ t : Set ι, t.Finite ∧ ∀ i, ∃ j ∈ t, ∀ x ∈ K, dist (g i x) (g j x) ≤ η := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, Set.finite_empty, fun i => (hι.false i).elim⟩
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformEquicontinuous_iff.mp hg (η / 4) (by linarith)
  obtain ⟨u, huK, hufin, hucov⟩ := finite_cover_balls_of_compact hK hδ
  obtain ⟨L, hLV, hLfin, hLcov⟩ :=
    finite_approx_of_totallyBounded hV.totallyBounded (η / 4) (by linarith)
  have : Fintype u := hufin.fintype
  have : Fintype L := hLfin.fintype
  -- Record, for each index and each sample point, a value-ball the value falls into.
  have hval : ∀ (i : ι) (x : u), ∃ y : L, dist (g i x) (y : Y) < η / 4 := by
    intro i x
    have hx := hLcov (hgV i x (huK x.2))
    simp only [mem_iUnion, mem_ball, exists_prop] at hx
    obtain ⟨y, hy, hdist⟩ := hx
    exact ⟨⟨y, hy⟩, hdist⟩
  choose y hy using hval
  -- The record takes finitely many values, so its range has a right inverse.
  refine ⟨Set.range (Function.invFun y), Set.finite_range _, fun i => ?_⟩
  refine ⟨Function.invFun y (y i), Set.mem_range_self _, fun x hx => ?_⟩
  set j := Function.invFun y (y i) with hj
  have hji : y j = y i := Function.invFun_eq ⟨i, rfl⟩
  obtain ⟨x₀, hx₀u, hx₀⟩ : ∃ x₀ ∈ u, x ∈ ball x₀ δ := by
    have := hucov hx
    simpa only [mem_iUnion, exists_prop] using this
  have hdx : dist x x₀ < δ := by rwa [mem_ball] at hx₀
  have hsample : dist (g i x₀) (g j x₀) < η / 4 + η / 4 := by
    have hy₁ := hy i ⟨x₀, hx₀u⟩
    have hy₂ := hy j ⟨x₀, hx₀u⟩
    rw [hji] at hy₂
    calc dist (g i x₀) (g j x₀) ≤ dist (g i x₀) (y i ⟨x₀, hx₀u⟩ : Y) +
          dist (y i ⟨x₀, hx₀u⟩ : Y) (g j x₀) := dist_triangle _ _ _
      _ < η / 4 + η / 4 := by
          exact add_lt_add hy₁ (by rw [dist_comm]; exact hy₂)
  refine le_of_lt ?_
  calc dist (g i x) (g j x) ≤ dist (g i x) (g i x₀) + dist (g i x₀) (g j x) :=
        dist_triangle _ _ _
    _ ≤ dist (g i x) (g i x₀) + (dist (g i x₀) (g j x₀) + dist (g j x₀) (g j x)) := by
        gcongr; exact dist_triangle _ _ _
    _ < η / 4 + (η / 4 + η / 4 + η / 4) := by
        refine add_lt_add (hδg x x₀ hdx i) ?_
        refine add_lt_add hsample ?_
        rw [dist_comm]
        exact hδg x x₀ hdx j
    _ = η := by ring

end TauCeti
