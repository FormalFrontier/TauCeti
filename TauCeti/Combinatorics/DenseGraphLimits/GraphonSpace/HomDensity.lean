/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
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

* `TauCeti.DenseGraphLimits.homDensityOnSpace_mk` computes it on a representative;
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

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The homomorphism density of a finite graph, as a function on graphon space. -/
def homDensityOnSpace (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    GraphonSpace Ω μ → ℝ :=
  GraphonSpace.lift (homDensity F) fun U W h =>
    forall_homDensity_eq_of_cutDist_eq_zero U W h n F

/-- Homomorphism density on graphon space computes as the original density on representatives. -/
@[simp]
theorem homDensityOnSpace_mk (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) :
    homDensityOnSpace (μ := μ) n F (GraphonSpace.mk W) = homDensity F W :=
  GraphonSpace.lift_mk (homDensity F)
    (fun U W h => forall_homDensity_eq_of_cutDist_eq_zero U W h n F) W

/-- Homomorphism density on graphon space is Lipschitz with constant the number of edges of the
finite graph. -/
theorem lipschitzWith_homDensityOnSpace (n : ℕ) (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] :
    LipschitzWith (F.edgeFinset.card : NNReal) (homDensityOnSpace (μ := μ) n F) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro U W
  induction U using GraphonSpace.inductionOn with
  | mk U =>
    induction W using GraphonSpace.inductionOn with
    | mk W =>
      rw [Real.dist_eq, homDensityOnSpace_mk, homDensityOnSpace_mk,
        dist_graphonSpace_mk_mk, NNReal.coe_natCast]
      exact abs_homDensity_sub_le_cutDist F U W

/-- Every finite-graph homomorphism density is continuous on graphon space. -/
theorem continuous_homDensityOnSpace (n : ℕ) (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] :
    Continuous (homDensityOnSpace (μ := μ) n F) :=
  (lipschitzWith_homDensityOnSpace (μ := μ) n F).continuous

end DenseGraphLimits

end TauCeti
