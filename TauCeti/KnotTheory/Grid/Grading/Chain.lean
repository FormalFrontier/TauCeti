/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.KnotTheory.Grid.Complex
public import TauCeti.KnotTheory.Grid.Grading.Parity
public import TauCeti.KnotTheory.Grid.StateCardinality

/-!
# The bigraded grid chain module

This file turns the integer `O`-Maslov and Alexander gradings of a grid diagram with odd component
count into a direct-sum decomposition of the grid chain module. The summand in bidegree `(m, a)` is
the direct sum of one copy of the coefficient ring for each state with `O`-Maslov grading `m` and
Alexander grading `a`.

The decomposition groups the standard basis through Mathlib's linear direct-sum reindexing and
sigma-currying equivalences; no second direct-sum or graded-module framework is introduced.

## Main definitions

* `TauCeti.OddComponentGridDiagram.BigradedChainPiece`: the homogeneous grid-chain module in one
  bidegree.
* `TauCeti.OddComponentGridDiagram.bigradedChainEquiv`: the grid chain module as the direct sum of
  its homogeneous pieces.

## Main results

* `TauCeti.OddComponentGridDiagram.bigradedChainEquiv_single`: a state generator lies in its own
  bidegree.
* `TauCeti.OddComponentGridDiagram.finrank_bigradedChainPiece`: the rank of a homogeneous piece is
  the number of states in that bidegree.
* `TauCeti.OddComponentGridDiagram.sum_finrank_bigradedChainPiece`: the ranks of the occupied pieces
  add to `n!`.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, by giving the grid
chain module its missing bigraded decomposition. It is also the algebraic input for Lane G.4,
where the Alexander-graded Euler characteristic is compared with the grid determinant. The
grading conventions follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 4.
-/

public section

open scoped DirectSum

namespace TauCeti

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

/-- The homogeneous grid-chain module in bidegree `g`: one copy of `R` for each state of that
bidegree. -/
abbrev BigradedChainPiece (R : Type*) [Semiring R] (g : ℤ × ℤ) :=
  ⨁ _ : {x : GridState n // G.bidegree x = g}, R

/-- Regroup a direct sum indexed by `ι` into the fibres of a degree function `f`.

This is the composite of Mathlib's linear reindexing and sigma-currying equivalences. -/
private noncomputable def sigmaFiberLinearEquiv {R : Type*} [Semiring R]
    {ι κ : Type*} [DecidableEq κ] (f : ι → κ) :
    (⨁ _ : ι, R) ≃ₗ[R] ⨁ k : κ, (⨁ _ : {i : ι // f i = k}, R) :=
  (DirectSum.lequivCongrLeft R (Equiv.sigmaFiberEquiv f).symm).trans
    (DirectSum.sigmaLcurryEquiv R (δ := fun _ (_ : {i // f i = _}) => R))

/-- The linear sigma-fibre equivalence has the same underlying function as Mathlib's additive
sigma-fibre equivalence. -/
private theorem sigmaFiberLinearEquiv_apply {R : Type*} [Semiring R]
    {ι κ : Type u} [DecidableEq κ] (f : ι → κ) (x : ⨁ _ : ι, R) :
    sigmaFiberLinearEquiv f x =
      DirectSum.sigmaFiberAddEquiv (β := fun _ : ι => R) f x := by
  ext k i
  rw [sigmaFiberLinearEquiv, LinearEquiv.trans_apply]
  -- `sigmaLcurryEquiv` has no application lemma, so expose its forward linear map.
  change DirectSum.sigmaLcurry R (α := fun k : κ => {i : ι // f i = k})
      (δ := fun _ _ => R)
      (DirectSum.lequivCongrLeft R (Equiv.sigmaFiberEquiv f).symm x) k i = _
  rw [DirectSum.sigmaLcurry_apply, DirectSum.lequivCongrLeft_apply,
    DirectSum.sigmaFiberAddEquiv_apply_apply, Equiv.symm_symm, Equiv.sigmaFiberEquiv_apply]

/-- The grid chain module decomposed as the direct sum of its (`O`-Maslov, Alexander)-homogeneous
pieces. -/
noncomputable def bigradedChainEquiv (R : Type*) [Semiring R] :
    GridChain R n ≃ₗ[R] ⨁ g : ℤ × ℤ, G.BigradedChainPiece R g :=
  (finsuppLEquivDirectSum R R (GridState n)).trans
    (sigmaFiberLinearEquiv G.bidegree)

/-- In the bigraded decomposition, the coefficient at a state in degree `g` is its original grid
chain coefficient. -/
@[simp]
theorem bigradedChainEquiv_apply_apply (R : Type*) [Semiring R]
    (c : GridChain R n) (g : ℤ × ℤ) (x : {x : GridState n // G.bidegree x = g}) :
    G.bigradedChainEquiv R c g x = c x := by
  rw [bigradedChainEquiv, LinearEquiv.trans_apply, sigmaFiberLinearEquiv_apply,
    DirectSum.sigmaFiberAddEquiv_apply_apply, finsuppLEquivDirectSum_apply]

/-- Reading a chain back off its homogeneous components: the coefficient at a state is the
component of the state's own bidegree, at that state. -/
@[simp]
theorem bigradedChainEquiv_symm_apply_apply (R : Type*) [Semiring R]
    (d : ⨁ g : ℤ × ℤ, G.BigradedChainPiece R g) (x : GridState n) :
    (G.bigradedChainEquiv R).symm d x = d (G.bidegree x) ⟨x, rfl⟩ := by
  conv_rhs => rw [← (G.bigradedChainEquiv R).apply_symm_apply d]
  exact (G.bigradedChainEquiv_apply_apply R _ (G.bidegree x) ⟨x, rfl⟩).symm

/-- A grid-state generator maps to the copy of the coefficient ring indexed by that state inside
its own bidegree. -/
@[simp]
theorem bigradedChainEquiv_single (R : Type*) [Semiring R] (x : GridState n) (r : R) :
    G.bigradedChainEquiv R (Finsupp.single x r) =
      DirectSum.lof R (ℤ × ℤ) (fun g => G.BigradedChainPiece R g) (G.bidegree x)
        (DirectSum.lof R {y : GridState n // G.bidegree y = G.bidegree x}
          (fun _ => R) ⟨x, rfl⟩ r) := by
  rw [bigradedChainEquiv, LinearEquiv.trans_apply, finsuppLEquivDirectSum_single,
    sigmaFiberLinearEquiv_apply]
  simpa only [DirectSum.lof_eq_of] using
    (DirectSum.sigmaFiberAddEquiv_of (β := fun _ : GridState n => R) G.bidegree x r)

/-- The rank of a homogeneous grid-chain piece is the number of states in its bidegree. -/
theorem finrank_bigradedChainPiece (R : Type*) [Semiring R] [StrongRankCondition R]
    (g : ℤ × ℤ) : Module.finrank R (G.BigradedChainPiece R g) =
      (Finset.univ.filter fun x : GridState n => G.bidegree x = g).card := by
  rw [Module.finrank_directSum]
  simp [Fintype.card_subtype]

/-- A homogeneous grid-chain piece has positive rank exactly when its bidegree is occupied by a
grid state. -/
theorem finrank_bigradedChainPiece_pos_iff (R : Type*) [Semiring R] [StrongRankCondition R]
    (g : ℤ × ℤ) :
    0 < Module.finrank R (G.BigradedChainPiece R g) ↔ g ∈ G.bidegreeSupport := by
  rw [G.finrank_bigradedChainPiece R g, Finset.card_pos, G.mem_bidegreeSupport_iff g]
  simp [Finset.filter_nonempty_iff]

/-- The ranks of all occupied homogeneous pieces add to `n!`, the number of grid states. -/
theorem sum_finrank_bigradedChainPiece (R : Type*) [Semiring R] [StrongRankCondition R] :
    ∑ g ∈ G.bidegreeSupport, Module.finrank R (G.BigradedChainPiece R g) = n.factorial := by
  simp_rw [G.finrank_bigradedChainPiece R]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp

end OddComponentGridDiagram

end TauCeti
