/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Analysis.Calculus.RescaledDerivative
public import TauCeti.Geometry.Lie.Exponential.Derivative.Log
public import TauCeti.Geometry.Lie.Interior

/-!
# The Trotter product formula

This file proves a tangent-to-identity power limit for finite-dimensional real Lie groups and
applies it to the product of two exponential curves. The resulting Trotter formula supplies the
addition-closure input for the subgroup Lie algebra in Deliverable A, Layer 2 of the Lie-groups
roadmap.

## Main results

* `tendsto_pow_div_of_hasDerivAt_mulInvariantLog`: a curve whose local logarithm has initial
  derivative `X` has rescaled powers converging to `exp (t X)`.
* `tendsto_mulInvariantExp_smul_mul_mulInvariantExp_smul_pow`: the Trotter product formula in the
  tangent model.
* `tendsto_lieExp_smul_mul_lieExp_smul_pow`: the Trotter product formula for left-invariant
  derivations.

## References

* [H. Liu, *Notes for Lie Groups & Representations*](https://member.ipmu.jp/henry.liu/notes/f16-lie-groups.pdf),
  notes from Andrei Okounkov's Fall 2016 course, Proposition 2.4.3.
* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 2, "The Lie subalgebra of a subgroup".
-/

public section

open Filter Function Manifold
open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsManifold I 1 G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- A tangent-to-identity curve has the expected exponential power limit. The derivative is
stated in local logarithmic coordinates so the result can be reused independently of a chosen
manifold expression for the curve. -/
theorem tendsto_pow_div_of_hasDerivAt_mulInvariantLog [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] {f : ℝ → G} (X : GroupLieAlgebra I G) (hf0 : f 0 = 1) :
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    ContinuousAt f 0 →
      HasDerivAt (fun s =>
        (show E from mulInvariantLog (I := I) (G := G) (f s)))
        (show E from X) 0 →
      ∀ t : ℝ, Tendsto (fun n : ℕ => (f (t / n)) ^ n) atTop
        (nhds (mulInvariantExp (I := I) (G := G) (t • X))) := by
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  intro hf hlog t
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hlog0 : (show E from mulInvariantLog (I := I) (G := G) (f 0)) = 0 := by
    rw [hf0]
    exact mulInvariantLog_one (I := I) (G := G)
  have hseq := tendsto_nsmul_apply_div_of_hasDerivAt hlog hlog0 t
  have hexp :=
    (contMDiff_mulInvariantExp (I := I) (G := G)).continuous.continuousAt.tendsto.comp hseq
  have hs : Tendsto (fun n : ℕ => t / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat t
  have hfseq : Tendsto (fun n : ℕ => f (t / (n : ℝ))) atTop (nhds (1 : G)) := by
    have hf' := hf.tendsto
    rw [hf0] at hf'
    -- Expose the sequence as a composition so `ContinuousAt.tendsto` can consume `hs`.
    change Tendsto (f ∘ fun n : ℕ => t / (n : ℝ)) atTop (nhds (1 : G))
    exact hf'.comp hs
  have hevent := hfseq.eventually
    (eventually_mulInvariantExp_log (I := I) (G := G))
  apply hexp.congr'
  filter_upwards [hevent] with n hnlog
  -- Unwrap the tangent-space power formula before rewriting by the local exp-log inverse.
  change mulInvariantExp (I := I) (G := G)
      (n • (mulInvariantLog (I := I) (G := G) (f (t / (n : ℝ))) :
        GroupLieAlgebra I G)) = f (t / (n : ℝ)) ^ n
  rw [mulInvariantExp_nsmul, hnlog]

/-- The Trotter product formula for the tangent-space exponential. -/
theorem tendsto_mulInvariantExp_smul_mul_mulInvariantExp_smul_pow [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] :
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    ∀ (X Y : GroupLieAlgebra I G) (t : ℝ),
      Tendsto (fun n : ℕ =>
        (mulInvariantExp (I := I) (G := G) ((t / n) • X) *
          mulInvariantExp (I := I) (G := G) ((t / n) • Y)) ^ n) atTop
        (nhds (mulInvariantExp (I := I) (G := G) (t • (X + Y)))) := by
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  intro X Y t
  let f : ℝ → G := fun s =>
    mulInvariantExp (I := I) (G := G) (s • X) *
      mulInvariantExp (I := I) (G := G) (s • Y)
  have hf0 : f 0 = 1 := by simp [f]
  have hf : ContinuousAt f 0 := by
    exact ((contMDiff_mulInvariantExp_smul (I := I) (G := G) X).mul
      (contMDiff_mulInvariantExp_smul (I := I) (G := G) Y)).continuous.continuousAt
  have hlog := hasDerivAt_mulInvariantLog_mulInvariantExp_smul_mul_mulInvariantExp_smul
    (I := I) (G := G) X Y
  simpa only [f] using
    tendsto_pow_div_of_hasDerivAt_mulInvariantLog (I := I) (G := G)
      (X + Y) hf0 hf hlog t

/-- The Trotter product formula for the exponential of left-invariant derivations. -/
theorem tendsto_lieExp_smul_mul_lieExp_smul_pow [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] :
    let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    ∀ (X Y : LeftInvariantDerivation I G) (t : ℝ),
      Tendsto (fun n : ℕ => (lieExp ((t / n) • X) * lieExp ((t / n) • Y)) ^ n) atTop
        (nhds (lieExp (t • (X + Y)))) := by
  let _ : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  intro X Y t
  let L := leftInvariantDerivationEquivGroupLieAlgebra
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint
  simpa only [lieExp_eq_mulInvariantExp, map_smul, map_add] using
    tendsto_mulInvariantExp_smul_mul_mulInvariantExp_smul_pow
      (I := I) (G := G) (L X) (L Y) t
