/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.L2
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Average
public import TauCeti.MeasureTheory.Integral.Finpartition
import TauCeti.MeasureTheory.MeasurableSpace.Finpartition

/-!
# The graphon partition energy

The Frieze--Kannan weak regularity argument is a potential argument: refine a measurable finite
partition as long as the block-average step graphon fails to approximate the graphon in cut norm,
and bound the number of refinements by the growth of an `L²` potential that is trapped in `[0, 1]`.
This file builds that potential.

`graphonPartitionEnergy μ P hP W` is the `L²(μ ⊗ μ)` norm squared of the block-average step graphon
`stepGraphonAvg`, that is of `E[W | P ⊗ P]`.  Its two structural properties are proved here:

* **projection moment.** Pairing `W` with its block-average step graphon gives the self-pairing of
  that block average (`l2inner_graphon_stepGraphonAvg`); hence the exact defect identity
  `l2sq_sub_stepGraphonAvg`.
* **Pythagoras.** Refining the partition increases the energy by exactly the `L²` norm squared of
  the change in the block-average step graphon (`graphonPartitionEnergy_increment`), so the energy
  is monotone under refinement.

Both rest on the same block computation: the energy is a finite sum of block contributions
(`graphonPartitionEnergy_eq_sum`), and a block average over a *refinement* still reproduces the
coarse block integrals (`stepGraphonAvg_rectIntegral_of_le_of_le`).  That last identity needs no
hypothesis excluding null parts: a null part of the finer partition cuts out a null rectangle,
which contributes zero to both sides whatever value the step graphon takes there.  The null-cell
convention of `stepGraphonAvg` is what makes it a well-defined strict `[0, 1]`-valued
representative at all — it is load-bearing for `stepGraphonAvg_idem` — but it is not what makes
this identity true.

This is `‖E[W | P ⊗ P]‖₂²` written entirely in terms of finite block averages; the identification
with `MeasureTheory.condExp` belongs to the later a.e. layer, and nothing here needs it.  It is also
distinct from Mathlib's `Finpartition.energy`, which is the finite edge-density energy of a finite
graph.

## Main definitions

* `TauCeti.DenseGraphLimits.graphonPartitionEnergy` is the graphon partition energy.

## Main results

* `TauCeti.DenseGraphLimits.stepGraphonAvg_rectIntegral_of_le_of_le`: block averaging over a
  refinement preserves rectangle integrals whose sides come from possibly different coarser
  partitions;
* `TauCeti.DenseGraphLimits.l2inner_stepGraphonAvg_eq_sum`: the block computation everything else
  is read off from — pairing any kernel against a block-average step graphon;
* `TauCeti.DenseGraphLimits.graphonPartitionEnergy_eq_sum`: the energy as a finite block sum;
* `TauCeti.DenseGraphLimits.l2inner_graphon_stepGraphonAvg`: the projection moment identity, and
  `TauCeti.DenseGraphLimits.l2inner_stepGraphonAvg_of_le` is its refinement form;
* `TauCeti.DenseGraphLimits.graphonPartitionEnergy_le_l2sq`: the corresponding Bessel-type bound;
* `TauCeti.DenseGraphLimits.l2sq_sub_stepGraphonAvg`: the defect identity `‖W - E[W|P⊗P]‖₂² =
  ‖W‖₂² - E(P)`;
* `TauCeti.DenseGraphLimits.graphonPartitionEnergy_increment`: the `L²`-Pythagoras increment;
* `TauCeti.DenseGraphLimits.graphonPartitionEnergy_stepGraphonAvg`: averaging twice at the same
  partition changes nothing;
* `TauCeti.DenseGraphLimits.graphonPartitionEnergy_mono`,
  `TauCeti.DenseGraphLimits.graphonPartitionEnergy_nonneg` and
  `TauCeti.DenseGraphLimits.graphonPartitionEnergy_le_one`: the bounded monotone potential.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
* A. Frieze and R. Kannan, *Quick approximation to matrices and applications*, Combinatorica 19
  (1999), 175--220.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 2 — the analytic energy stack
  (`graphonPartitionEnergy`, `graphonPartitionEnergy_eq`, the `L²`-Pythagoras increment and its
  `_mono` / `_nonneg` / `_le_one` corollaries).  The signatures of `graphonPartitionEnergy` and of
  its `_eq` / `_increment` / `_mono` / `_nonneg` / `_le_one` companions, together with the
  `_mono` and `_nonneg` proofs, follow `TauCetiRoadmap/DenseGraphLimits/Suggested.lean` (Layer 2);
  the block computation, the projection moment identity and the defect identity are developed here.
* The roadmap lists the null-cell `Finpartition` convention — including unchanged weighted energy,
  the scope of `stepGraphonAvg_rectIntegral_of_le_of_le` and of the increment — under its
  migration-backed routes, with an independent development in `Graphon/RegularityFinpartition.lean`
  in `cameronfreer/graphon` (Apache 2.0) at commit
  `dfd7ecc9b197d8211842935204bcec6051d57863`.  No material is adapted from that source; the proofs
  here are the `L²` route through `l2inner_stepGraphonAvg_eq_sum`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

section Decomposition

/-- Two kernels with the same integral over every rectangle of a partition `Q` have the same
integral over a rectangle whose sides are parts of two partitions coarser than `Q`. -/
private theorem rectIntegral_eq_of_le_left_right {P R Q : Finpartition (Set.univ : Set Ω)}
    (p : P.parts) (r : R.parts) (hQ : ∀ q ∈ Q.parts, MeasurableSet q)
    (hQP : Q ≤ P) (hQR : Q ≤ R)
    {K L : SymmKernel Ω μ}
    (h : ∀ r s : Q.parts, K.rectIntegral μ (r : Set Ω) (s : Set Ω)
      = L.rectIntegral μ (r : Set Ω) (s : Set Ω)) :
    K.rectIntegral μ (p : Set Ω) (r : Set Ω) = L.rectIntegral μ (p : Set Ω) (r : Set Ω) := by
  have hp : MeasurableSet (p : Set Ω) :=
    Finpartition.measurableSet_of_mem_of_le hQ hQP p.property
  have hr : MeasurableSet (r : Set Ω) :=
    Finpartition.measurableSet_of_mem_of_le hQ hQR r.property
  rw [SymmKernel.rectIntegral_def, SymmKernel.rectIntegral_def,
    Finpartition.setIntegral_prod_eq_sum_parts μ Q hQ hp hr
      (SymmKernel.integrable_uncurry μ K).integrableOn,
    Finpartition.setIntegral_prod_eq_sum_parts μ Q hQ hp hr
      (SymmKernel.integrable_uncurry μ L).integrableOn]
  refine Finset.sum_congr rfl fun rs _ => ?_
  rcases Finpartition.inter_part_eq_self_or_eq_empty_of_le hQP rs.1.property p.property with
    h1 | h1
  · rcases Finpartition.inter_part_eq_self_or_eq_empty_of_le hQR rs.2.property r.property with
      h2 | h2
    · rw [h1, h2]
      simpa only [SymmKernel.rectIntegral_def] using h rs.1 rs.2
    · rw [h2]
      simp
  · rw [h1]
    simp

end Decomposition

/-- Block averaging over `Q` reproduces the integral over any rectangle whose two sides are parts
of (possibly different) measurable partitions coarser than `Q`. -/
@[simp]
theorem stepGraphonAvg_rectIntegral_of_le_of_le {P R Q : Finpartition (Set.univ : Set Ω)}
    (p : P.parts) (r : R.parts) (hQ : ∀ q ∈ Q.parts, MeasurableSet q)
    (hQP : Q ≤ P) (hQR : Q ≤ R)
    (W : Graphon Ω μ) :
    (stepGraphonAvg (μ := μ) Q hQ W).toSymmKernel.rectIntegral μ (p : Set Ω) (r : Set Ω)
      = W.toSymmKernel.rectIntegral μ (p : Set Ω) (r : Set Ω) :=
  rectIntegral_eq_of_le_left_right μ p r hQ hQP hQR
    (fun q q' => stepGraphonAvg_rectIntegral Q hQ W q q')

variable (P Q : Finpartition (Set.univ : Set Ω))

/-- On a single block, pairing any kernel against the block-average step graphon multiplies the
block integral of the kernel by the block average of `W`. -/
private theorem setIntegral_mul_stepGraphonAvg (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (W : Graphon Ω μ) (K : SymmKernel Ω μ) (p q : P.parts) :
    ∫ z in (p : Set Ω) ×ˢ (q : Set Ω), K z.1 z.2 * stepGraphonAvg (μ := μ) P hP W z.1 z.2
        ∂(μ.prod μ)
      = K.rectIntegral μ (p : Set Ω) (q : Set Ω)
        * ⨍ z in (p : Set Ω) ×ˢ (q : Set Ω), W z.1 z.2 ∂(μ.prod μ) := by
  rw [SymmKernel.rectIntegral_def, ← integral_mul_const]
  refine setIntegral_congr_fun ((hP _ p.property).prod (hP _ q.property)) fun z hz => ?_
  rw [stepGraphonAvg_apply P hP W hz.1 hz.2]

/-- The `L²` pairing of any kernel with a block-average step graphon is the finite sum of its block
integrals weighted by the block averages of `W`. -/
theorem l2inner_stepGraphonAvg_eq_sum (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ)
    (K : SymmKernel Ω μ) :
    l2inner μ K (stepGraphonAvg (μ := μ) P hP W).toSymmKernel
      = ∑ pq : P.parts × P.parts, K.rectIntegral μ (pq.1 : Set Ω) (pq.2 : Set Ω)
        * ⨍ z in (pq.1 : Set Ω) ×ˢ (pq.2 : Set Ω), W z.1 z.2 ∂(μ.prod μ) := by
  rw [l2inner_def, Finpartition.integral_eq_sum_parts μ P hP
    (SymmKernel.integrable_mul μ K (stepGraphonAvg (μ := μ) P hP W).toSymmKernel)]
  simp only [Graphon.coe_toSymmKernel]
  exact Finset.sum_congr rfl fun pq _ => setIntegral_mul_stepGraphonAvg μ P hP W K pq.1 pq.2

/-- The **graphon partition energy** of `W` over a measurable finite partition `P`: the
`L²(μ ⊗ μ)` norm squared of the block-average step graphon `E[W | P ⊗ P]`.

This is the analytic potential of the Frieze--Kannan weak regularity argument.  It is not Mathlib's
`Finpartition.energy`, which is the finite edge-density energy of a finite graph. -/
def graphonPartitionEnergy (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) : ℝ :=
  l2sq μ (stepGraphonAvg (μ := μ) P hP W).toSymmKernel

/-- The partition energy is the `L²` norm squared of the block-average step graphon.  The
definition's body is not exposed across module boundaries, so this is the unfolding lemma
downstream modules should use. -/
theorem graphonPartitionEnergy_eq (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) :
    graphonPartitionEnergy μ P hP W = l2sq μ (stepGraphonAvg (μ := μ) P hP W).toSymmKernel :=
  (rfl)

/-- The partition energy as a finite sum of block contributions: each block contributes the
integral of `W` over it times the average of `W` on it. -/
theorem graphonPartitionEnergy_eq_sum (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) :
    graphonPartitionEnergy μ P hP W
      = ∑ pq : P.parts × P.parts, W.toSymmKernel.rectIntegral μ (pq.1 : Set Ω) (pq.2 : Set Ω)
        * ⨍ z in (pq.1 : Set Ω) ×ˢ (pq.2 : Set Ω), W z.1 z.2 ∂(μ.prod μ) := by
  rw [graphonPartitionEnergy_eq, l2sq_eq_l2inner_self, l2inner_stepGraphonAvg_eq_sum]
  exact Finset.sum_congr rfl fun pq _ => by
    rw [stepGraphonAvg_rectIntegral P hP W pq.1 pq.2]

/-- The projection moment identity: pairing `W` against its block average equals the self-pairing
of that block average, namely the partition energy. -/
theorem l2inner_graphon_stepGraphonAvg (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) :
    l2inner μ W.toSymmKernel (stepGraphonAvg (μ := μ) P hP W).toSymmKernel
      = graphonPartitionEnergy μ P hP W := by
  rw [l2inner_stepGraphonAvg_eq_sum, graphonPartitionEnergy_eq_sum]

/-- The defect identity: the `L²` distance from `W` to its block average is the remaining gap
between the graphon's `L²` norm squared and the current partition energy. -/
theorem l2sq_sub_stepGraphonAvg (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) :
    l2sq μ (W.toSymmKernel - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel)
      = l2sq μ W.toSymmKernel - graphonPartitionEnergy μ P hP W := by
  rw [l2sq_sub, l2inner_graphon_stepGraphonAvg, graphonPartitionEnergy_eq]
  ring

/-- The partition energy never exceeds the `L²` norm squared of the graphon — the Bessel-type
bound following from the projection moment identity. -/
theorem graphonPartitionEnergy_le_l2sq (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) :
    graphonPartitionEnergy μ P hP W ≤ l2sq μ W.toSymmKernel := by
  have h := l2sq_nonneg μ (W.toSymmKernel - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel)
  rw [l2sq_sub_stepGraphonAvg] at h
  linarith

/-- Under refinement, the finer block-average step graphon pairs with the coarser one to give
exactly the coarser energy: the coarse block average is unchanged by the finer averaging. -/
theorem l2inner_stepGraphonAvg_of_le (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (hQ : ∀ r ∈ Q.parts, MeasurableSet r) (href : Q ≤ P) (W : Graphon Ω μ) :
    l2inner μ (stepGraphonAvg (μ := μ) Q hQ W).toSymmKernel
        (stepGraphonAvg (μ := μ) P hP W).toSymmKernel
      = graphonPartitionEnergy μ P hP W := by
  rw [l2inner_stepGraphonAvg_eq_sum, graphonPartitionEnergy_eq_sum]
  exact Finset.sum_congr rfl fun pq _ => by
    rw [stepGraphonAvg_rectIntegral_of_le_of_le μ pq.1 pq.2 hQ href href W]

/-- **The `L²`-Pythagoras energy increment.**  Refining a partition raises the energy by exactly the
`L²` norm squared of the change in the block-average step graphon.  This is the quantitative driver
of the Frieze--Kannan iteration.

Mathlib's refinement order has `P ≤ Q` mean that `P` refines `Q`, so `Q ≤ P` is the hypothesis that
`Q` is the finer partition. -/
theorem graphonPartitionEnergy_increment (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (hQ : ∀ r ∈ Q.parts, MeasurableSet r) (href : Q ≤ P) (W : Graphon Ω μ) :
    graphonPartitionEnergy μ Q hQ W
      = graphonPartitionEnergy μ P hP W
        + l2sq μ ((stepGraphonAvg (μ := μ) Q hQ W).toSymmKernel
          - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel) := by
  simp only [l2sq_sub, l2inner_stepGraphonAvg_of_le μ P Q hP hQ href W,
    graphonPartitionEnergy_eq]
  ring

/-- The partition energy is monotone under refinement — the `≥ 0` corollary of the Pythagoras
increment. -/
theorem graphonPartitionEnergy_mono (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (hQ : ∀ r ∈ Q.parts, MeasurableSet r) (href : Q ≤ P) (W : Graphon Ω μ) :
    graphonPartitionEnergy μ P hP W ≤ graphonPartitionEnergy μ Q hQ W := by
  rw [graphonPartitionEnergy_increment μ P Q hP hQ href W]
  linarith [l2sq_nonneg μ ((stepGraphonAvg (μ := μ) Q hQ W).toSymmKernel
    - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel)]

/-- The partition energy is nonnegative. -/
theorem graphonPartitionEnergy_nonneg (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) :
    0 ≤ graphonPartitionEnergy μ P hP W := by
  rw [graphonPartitionEnergy_eq]
  exact l2sq_nonneg μ _

/-- Block averaging does not change the partition energy at the same partition: the block-average
step graphon is already constant on the rectangles of `P`, so averaging it again changes nothing.
This is the idempotence identity `E(P, E[W|P⊗P]) = E(P, W)`. -/
@[simp]
theorem graphonPartitionEnergy_stepGraphonAvg (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (W : Graphon Ω μ) :
    graphonPartitionEnergy μ P hP (stepGraphonAvg (μ := μ) P hP W)
      = graphonPartitionEnergy μ P hP W := by
  rw [graphonPartitionEnergy_eq, graphonPartitionEnergy_eq, stepGraphonAvg_idem]

/-- The partition energy is at most `1`, because a graphon is `[0, 1]`-valued.  With
`graphonPartitionEnergy_mono` and `graphonPartitionEnergy_nonneg` this is the bounded monotone
potential the Frieze--Kannan iteration runs on. -/
theorem graphonPartitionEnergy_le_one (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) :
    graphonPartitionEnergy μ P hP W ≤ 1 := by
  rw [graphonPartitionEnergy_eq]
  refine l2sq_le_one_of_abs_le_one μ _ fun x y => ?_
  rw [Graphon.coe_toSymmKernel, abs_of_nonneg ((stepGraphonAvg (μ := μ) P hP W).nonneg x y)]
  exact (stepGraphonAvg (μ := μ) P hP W).le_one x y

end DenseGraphLimits

end TauCeti
