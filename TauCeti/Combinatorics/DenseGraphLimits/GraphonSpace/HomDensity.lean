/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.Separation.Forward

/-!
# Homomorphism densities on graphon space

Homomorphism density is invariant under zero cut distance, so it descends from strict graphon
representatives to `GraphonSpace`.  The descended observable retains the quantitative counting
bound: for a finite graph `F`, it is Lipschitz with constant equal to the number of edges of `F`.
In particular every homomorphism density is continuous on graphon space.

These quotient-stable observables are the coordinates used by graphon separation, compactness, and
the equivalence between cut-distance convergence and convergence of all homomorphism densities.

## Main definitions

* `TauCeti.DenseGraphLimits.homDensityOnSpace` is homomorphism density on the cut-distance
  quotient.

## Main results

* `TauCeti.DenseGraphLimits.lipschitzWith_homDensity` is the edge-count Lipschitz bound on strict
  graphons, which makes the descent well defined;
* `TauCeti.DenseGraphLimits.homDensityOnSpace_mk` computes it on a representative;
* `TauCeti.DenseGraphLimits.homDensityOnSpace_nonneg` and
  `TauCeti.DenseGraphLimits.homDensityOnSpace_le_one` bound it in `[0, 1]`;
* `TauCeti.DenseGraphLimits.lipschitzWith_homDensityOnSpace` gives the edge-count Lipschitz bound;
* `TauCeti.DenseGraphLimits.continuous_homDensityOnSpace` gives continuity on every fixed-carrier
  graphon space.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Lemma 10.23.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 7.2.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {V Ω : Type*} [Fintype V] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Homomorphism density is Lipschitz for the cut-distance pseudometric on strict graphons, with
constant the number of edges of the finite graph. -/
theorem lipschitzWith_homDensity (F : SimpleGraph V) [DecidableRel F.Adj] :
    LipschitzWith (F.edgeFinset.card : NNReal) (homDensity F : Graphon Ω μ → ℝ) := by
  refine LipschitzWith.of_dist_le_mul fun U W => ?_
  rw [Real.dist_eq, NNReal.coe_natCast, Graphon.dist_eq_cutDist]
  exact abs_homDensity_sub_le_cutDist F U W

/-- The homomorphism density of a finite graph, as a function on graphon space.

It is well defined because homomorphism density is continuous for the cut-distance pseudometric,
hence constant on inseparable graphons. -/
def homDensityOnSpace (F : SimpleGraph V) [DecidableRel F.Adj] :
    GraphonSpace Ω μ → ℝ :=
  SeparationQuotient.lift (homDensity F) fun _ _ h =>
    (h.map (lipschitzWith_homDensity F).continuous).eq

/-- Homomorphism density on graphon space computes as the original density on representatives. -/
@[simp]
theorem homDensityOnSpace_mk (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) :
    homDensityOnSpace (μ := μ) F (SeparationQuotient.mk W) = homDensity F W :=
  SeparationQuotient.lift_mk
    (fun _ _ h => (h.map (lipschitzWith_homDensity F).continuous).eq) W

/-- Homomorphism density on graphon space is nonnegative. -/
theorem homDensityOnSpace_nonneg (F : SimpleGraph V) [DecidableRel F.Adj] (W : GraphonSpace Ω μ) :
    0 ≤ homDensityOnSpace F W := by
  refine (SeparationQuotient.surjective_mk.forall
    (p := fun W => 0 ≤ homDensityOnSpace (μ := μ) F W)).2 (fun U => ?_) W
  rw [homDensityOnSpace_mk]
  exact homDensity_nonneg F U

/-- Homomorphism density on graphon space is at most `1`. -/
theorem homDensityOnSpace_le_one (F : SimpleGraph V) [DecidableRel F.Adj] (W : GraphonSpace Ω μ) :
    homDensityOnSpace F W ≤ 1 := by
  refine (SeparationQuotient.surjective_mk.forall
    (p := fun W => homDensityOnSpace (μ := μ) F W ≤ 1)).2 (fun U => ?_) W
  rw [homDensityOnSpace_mk]
  exact homDensity_le_one F U

/-- Homomorphism density on graphon space is Lipschitz with constant the number of edges of the
finite graph. -/
theorem lipschitzWith_homDensityOnSpace (F : SimpleGraph V) [DecidableRel F.Adj] :
    LipschitzWith (F.edgeFinset.card : NNReal) (homDensityOnSpace (μ := μ) F) := by
  refine LipschitzWith.of_dist_le_mul (SeparationQuotient.surjective_mk.forall₂.2 fun U W => ?_)
  rw [homDensityOnSpace_mk, homDensityOnSpace_mk, SeparationQuotient.dist_mk]
  exact (lipschitzWith_homDensity F).dist_le_mul U W

/-- Every finite-graph homomorphism density is continuous on graphon space. -/
theorem continuous_homDensityOnSpace (F : SimpleGraph V) [DecidableRel F.Adj] :
    Continuous (homDensityOnSpace (μ := μ) F) :=
  (lipschitzWith_homDensityOnSpace (μ := μ) F).continuous

end DenseGraphLimits

end TauCeti
