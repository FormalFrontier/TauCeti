/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.L2
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Average

/-!
# The graphon partition energy

The Frieze--Kannan weak regularity argument is a potential argument: refine a measurable finite
partition as long as the block-average step graphon fails to approximate the graphon in cut norm,
and bound the number of refinements by the growth of an `L²` potential that is trapped in `[0, 1]`.
This file builds that potential.

`graphonPartitionEnergy μ P hP W` is the `L²(μ ⊗ μ)` norm squared of the block-average step graphon
`stepGraphonAvg`, that is of `E[W | P ⊗ P]`.  Its two structural properties are proved here:

* **projection.** The block-average step graphon is the `L²` orthogonal projection of `W` onto the
  functions constant on the rectangles of `P`, in the concrete form
  `l2inner_graphon_stepGraphonAvg`; hence the exact defect identity `l2sq_sub_stepGraphonAvg`.
* **Pythagoras.** Refining the partition increases the energy by exactly the `L²` norm squared of
  the change in the block-average step graphon (`graphonPartitionEnergy_increment`), so the energy
  is monotone under refinement.

Both rest on the same block computation: the energy is a finite sum of block contributions
(`graphonPartitionEnergy_eq_sum`), and a block average over a *refinement* still reproduces the
coarse block integrals (`stepGraphonAvg_rectIntegral_of_le`).  That last point is where the
null-cell convention of `stepGraphonAvg` is tested: a part of the finer partition may be null, and
the convention assigning it the value zero is exactly what keeps its contribution to the coarse
block integral correct.

This is `‖E[W | P ⊗ P]‖₂²` written entirely in terms of finite block averages; the identification
with `MeasureTheory.condExp` belongs to the later a.e. layer, and nothing here needs it.  It is also
distinct from Mathlib's `Finpartition.energy`, which is the finite edge-density energy of a finite
graph.

## Main definitions

* `TauCeti.DenseGraphLimits.graphonPartitionEnergy` is the graphon partition energy.

## Main results

* `TauCeti.DenseGraphLimits.stepGraphonAvg_rectIntegral_of_le`: block averaging over a refinement
  preserves the coarse block integrals;
* `TauCeti.DenseGraphLimits.graphonPartitionEnergy_eq_sum`: the energy as a finite block sum;
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
  `_mono` / `_nonneg` / `_le_one` corollaries).
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*}

section Parts

/-- The parts of a finite partition of the carrier cover it. -/
private theorem iUnion_parts (R : Finpartition (Set.univ : Set Ω)) :
    ⋃ r : R.parts, (r : Set Ω) = Set.univ := by
  refine eq_univ_of_forall fun x => ?_
  have hx : x ∈ ⋃₀ (R.parts : Set (Set Ω)) := by
    rw [← Finset.sup_id_set_eq_sUnion, R.sup_parts]
    exact mem_univ x
  obtain ⟨r, hr, hxr⟩ := mem_sUnion.mp hx
  exact mem_iUnion.2 ⟨⟨r, hr⟩, hxr⟩

/-- Under refinement, a part of the finer partition is either contained in a given part of the
coarser one or disjoint from it. -/
private theorem inter_eq_self_or_empty {P Q : Finpartition (Set.univ : Set Ω)} (href : Q ≤ P)
    {r : Set Ω} (hr : r ∈ Q.parts) {p : Set Ω} (hp : p ∈ P.parts) :
    r ∩ p = r ∨ r ∩ p = ∅ := by
  obtain ⟨p', hp', hrp'⟩ := href hr
  by_cases h : p' = p
  · exact Or.inl (inter_eq_self_of_subset_left (h ▸ hrp'))
  · refine Or.inr (eq_empty_of_subset_empty fun x hx => ?_)
    exact absurd hx.2 (disjoint_left.mp (P.disjoint hp' hp h) (hrp' hx.1))

end Parts

variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

section Decomposition

omit [IsProbabilityMeasure μ] in
/-- A finite measurable partition of the carrier cuts a rectangle into finitely many disjoint
subrectangles, splitting any integral over it into a finite sum. -/
private theorem setIntegral_prod_eq_sum_parts (R : Finpartition (Set.univ : Set Ω))
    (hR : ∀ r ∈ R.parts, MeasurableSet r) {S T : Set Ω} (hS : MeasurableSet S)
    (hT : MeasurableSet T) {f : Ω × Ω → ℝ} (hf : Integrable f (μ.prod μ)) :
    ∫ z in S ×ˢ T, f z ∂(μ.prod μ)
      = ∑ rs : R.parts × R.parts,
          ∫ z in ((rs.1 : Set Ω) ∩ S) ×ˢ ((rs.2 : Set Ω) ∩ T), f z ∂(μ.prod μ) := by
  have hmeas : ∀ rs : R.parts × R.parts,
      MeasurableSet (((rs.1 : Set Ω) ∩ S) ×ˢ ((rs.2 : Set Ω) ∩ T)) := fun rs =>
    ((hR _ rs.1.property).inter hS).prod ((hR _ rs.2.property).inter hT)
  have hdisj : Pairwise (Function.onFun Disjoint fun rs : R.parts × R.parts =>
      ((rs.1 : Set Ω) ∩ S) ×ˢ ((rs.2 : Set Ω) ∩ T)) := by
    intro rs rs' hne
    have key : ∀ {u v : R.parts} {A : Set Ω}, u ≠ v →
        ((u : Set Ω) ∩ A) ∩ ((v : Set Ω) ∩ A) = ∅ := by
      intro u v A huv
      refine disjoint_iff_inter_eq_empty.mp ?_
      exact (R.disjoint u.property v.property fun h => huv (Subtype.ext h)).mono
        inter_subset_left inter_subset_left
    simp only [Function.onFun, disjoint_iff_inter_eq_empty, prod_inter_prod, prod_eq_empty_iff]
    by_cases h1 : rs.1 = rs'.1
    · refine Or.inr (key ?_)
      intro h2
      exact hne (Prod.ext h1 h2)
    · exact Or.inl (key h1)
  have hunion : (⋃ rs : R.parts × R.parts, ((rs.1 : Set Ω) ∩ S) ×ˢ ((rs.2 : Set Ω) ∩ T))
      = S ×ˢ T := by
    rw [iUnion_prod (fun r : R.parts => (r : Set Ω) ∩ S) fun r : R.parts => (r : Set Ω) ∩ T,
      ← iUnion_inter, ← iUnion_inter, iUnion_parts R, univ_inter, univ_inter]
  rw [← hunion, integral_iUnion_fintype hmeas hdisj fun _ => hf.integrableOn]

omit [IsProbabilityMeasure μ] in
/-- A finite measurable partition of the carrier splits an integral over the whole product carrier
into a finite sum over its rectangles. -/
private theorem integral_eq_sum_parts (R : Finpartition (Set.univ : Set Ω))
    (hR : ∀ r ∈ R.parts, MeasurableSet r) {f : Ω × Ω → ℝ} (hf : Integrable f (μ.prod μ)) :
    ∫ z, f z ∂(μ.prod μ)
      = ∑ rs : R.parts × R.parts, ∫ z in (rs.1 : Set Ω) ×ˢ (rs.2 : Set Ω), f z ∂(μ.prod μ) := by
  rw [← setIntegral_univ (μ := μ.prod μ), ← univ_prod_univ,
    setIntegral_prod_eq_sum_parts μ R hR MeasurableSet.univ MeasurableSet.univ hf]
  simp

/-- Two kernels with the same integral over every rectangle of a partition `Q` have the same
integral over every rectangle of any coarser partition `P`. -/
private theorem rectIntegral_eq_of_le {P Q : Finpartition (Set.univ : Set Ω)}
    (hP : ∀ p ∈ P.parts, MeasurableSet p) (hQ : ∀ r ∈ Q.parts, MeasurableSet r) (href : Q ≤ P)
    {K L : SymmKernel Ω μ}
    (h : ∀ r s : Q.parts, K.rectIntegral μ (r : Set Ω) (s : Set Ω)
      = L.rectIntegral μ (r : Set Ω) (s : Set Ω)) (p q : P.parts) :
    K.rectIntegral μ (p : Set Ω) (q : Set Ω) = L.rectIntegral μ (p : Set Ω) (q : Set Ω) := by
  rw [SymmKernel.rectIntegral_def, SymmKernel.rectIntegral_def,
    setIntegral_prod_eq_sum_parts μ Q hQ (hP _ p.property) (hP _ q.property)
      (SymmKernel.integrable_uncurry μ K),
    setIntegral_prod_eq_sum_parts μ Q hQ (hP _ p.property) (hP _ q.property)
      (SymmKernel.integrable_uncurry μ L)]
  refine Finset.sum_congr rfl fun rs _ => ?_
  rcases inter_eq_self_or_empty href rs.1.property p.property with h1 | h1
  · rcases inter_eq_self_or_empty href rs.2.property q.property with h2 | h2
    · rw [h1, h2]
      simpa only [SymmKernel.rectIntegral_def] using h rs.1 rs.2
    · rw [h2]
      simp
  · rw [h1]
    simp

end Decomposition

variable (P Q : Finpartition (Set.univ : Set Ω))

/-- Block averaging over a refinement still reproduces the block integrals of the coarser
partition.  This is where the null-cell convention of `stepGraphonAvg` is exercised: a null part of
the finer partition is given the value zero, and contributes zero to the coarse block integral,
which is exactly what this identity requires. -/
theorem stepGraphonAvg_rectIntegral_of_le (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (hQ : ∀ r ∈ Q.parts, MeasurableSet r) (href : Q ≤ P) (W : Graphon Ω μ) (p q : P.parts) :
    (stepGraphonAvg (μ := μ) Q hQ W).toSymmKernel.rectIntegral μ (p : Set Ω) (q : Set Ω)
      = W.toSymmKernel.rectIntegral μ (p : Set Ω) (q : Set Ω) :=
  rectIntegral_eq_of_le μ hP hQ href (fun r s => stepGraphonAvg_rectIntegral Q hQ W r s) p q

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
  rw [l2inner_def, integral_eq_sum_parts μ P hP
    (SymmKernel.integrable_mul μ K (stepGraphonAvg (μ := μ) P hP W).toSymmKernel)]
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

/-- The block-average step graphon is the `L²` orthogonal projection of `W`: pairing `W` against it
already returns the partition energy. -/
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

/-- The partition energy never exceeds the `L²` norm squared of the graphon — Bessel's inequality
for the block-average projection. -/
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
    rw [stepGraphonAvg_rectIntegral_of_le μ P Q hP hQ href W pq.1 pq.2]

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
  rw [l2sq_sub, l2inner_stepGraphonAvg_of_le μ P Q hP hQ href W, graphonPartitionEnergy_eq μ Q,
    graphonPartitionEnergy_eq μ P]
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
This is the projection identity `E(P, E[W|P⊗P]) = E(P, W)`. -/
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
