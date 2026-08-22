/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.KnotTheory.Grid.ChainCardinality
public import TauCeti.KnotTheory.Grid.Grading.Parity

/-!
# The bigraded grid chain module

For a knot grid diagram, both the Maslov and Alexander gradings of a grid state are integers.
This file turns those two functions on the state basis into an actual direct-sum decomposition of
the grid chain module. The summand in bidegree `(m, a)` is the direct sum of one copy of the
coefficient ring for each state with Maslov grading `m` and Alexander grading `a`.

The integer Alexander grading `GridDiagram.alexanderℤ` is the half of the already-defined integer
numerator `alexanderTwoℤ`. Its agreement with the rational grading uses the parity theorem for knot
grids. The decomposition itself groups the standard basis through Mathlib's
`DirectSum.sigmaFiberAddEquiv`; no second direct-sum or graded-module framework is introduced.

## Main definitions

* `TauCeti.GridDiagram.alexanderℤ`: the integer Alexander grading of a state in a knot grid.
* `TauCeti.GridDiagram.bidegree`: the `(Maslov, Alexander)` degree of a state in a knot grid.
* `TauCeti.GridDiagram.BigradedChainPiece`: the homogeneous grid-chain module in one bidegree.
* `TauCeti.GridDiagram.bigradedChainEquiv`: the grid chain module as the direct sum of its
  homogeneous pieces.

## Main results

* `TauCeti.GridDiagram.alexander_eq_intCast`: the integer Alexander grading agrees with the
  original rational grading.
* `TauCeti.GridDiagram.bigradedChainEquiv_single`: a state generator lies in its own bidegree.
* `TauCeti.GridDiagram.finrank_bigradedChainPiece`: the rank of a homogeneous piece is the number
  of states in that bidegree.
* `TauCeti.GridDiagram.sum_finrank_bigradedChainPiece`: the ranks of the occupied pieces add to
  `n!`.

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

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The integer Alexander grading of a state in a knot grid diagram.

The numerator `alexanderTwoℤ` is even for knot grids, so integer division by two is exact. The
knot hypothesis is part of the interface because the Alexander grading is a strict half-integer
on every state of a diagram with an even number of link components. -/
def alexanderℤ (_hG : G.IsKnot) (x : GridState n) : ℤ :=
  G.alexanderTwoℤ x / 2

/-- The integer Alexander grading is half of its integer numerator. -/
theorem two_mul_alexanderℤ (hG : G.IsKnot) (x : GridState n) :
    2 * G.alexanderℤ hG x = G.alexanderTwoℤ x := by
  obtain ⟨a, ha⟩ := G.even_alexanderTwoℤ_of_isKnot hG x
  rw [alexanderℤ, ha]
  omega

/-- The integer Alexander grading of a knot grid agrees with the original rational-valued
Alexander grading. -/
theorem alexander_eq_intCast (hG : G.IsKnot) (x : GridState n) :
    G.alexander x = (G.alexanderℤ hG x : ℚ) := by
  have h := G.two_mul_alexander_eq_intCast x
  rw [← G.two_mul_alexanderℤ hG x] at h
  push_cast at h
  linarith

/-- The `(Maslov, Alexander)` bidegree of a state in a knot grid diagram. -/
def bidegree (hG : G.IsKnot) (x : GridState n) : ℤ × ℤ :=
  (G.maslovOℤ x, G.alexanderℤ hG x)

/-- The first component of the grid bidegree is the integer `O`-Maslov grading. -/
@[simp]
theorem bidegree_fst (hG : G.IsKnot) (x : GridState n) :
    (G.bidegree hG x).1 = G.maslovOℤ x :=
  (rfl)

/-- The second component of the grid bidegree is the integer Alexander grading. -/
@[simp]
theorem bidegree_snd (hG : G.IsKnot) (x : GridState n) :
    (G.bidegree hG x).2 = G.alexanderℤ hG x :=
  (rfl)

/-- The finite set of bidegrees occupied by grid states. -/
noncomputable def bidegreeSupport (hG : G.IsKnot) : Finset (ℤ × ℤ) :=
  Finset.univ.image (G.bidegree hG)

/-- A bidegree is occupied exactly when some grid state has that bidegree. -/
@[simp]
theorem mem_bidegreeSupport_iff (hG : G.IsKnot) (g : ℤ × ℤ) :
    g ∈ G.bidegreeSupport hG ↔ ∃ x : GridState n, G.bidegree hG x = g := by
  simp [bidegreeSupport]

/-- The homogeneous grid-chain module in bidegree `g`: one copy of `R` for each state of that
bidegree. -/
abbrev BigradedChainPiece (R : Type*) [Semiring R] (hG : G.IsKnot) (g : ℤ × ℤ) :=
  ⨁ _ : {x : GridState n // G.bidegree hG x = g}, R

/-- Regroup a direct sum indexed by `ι` into the fibres of a degree function `f`.

Mathlib provides the additive equivalence; scalar multiplication is pointwise on both direct
sums, so it upgrades directly to a linear equivalence. -/
private noncomputable def sigmaFiberLinearEquiv {R : Type*} [Semiring R]
    {ι κ : Type} [DecidableEq κ] (f : ι → κ) :
    (⨁ _ : ι, R) ≃ₗ[R] ⨁ k : κ, (⨁ _ : {i : ι // f i = k}, R) := by
  let e : (⨁ _ : ι, R) ≃+ ⨁ k : κ, (⨁ _ : {i : ι // f i = k}, R) :=
    DirectSum.sigmaFiberAddEquiv (β := fun _ : ι => R) f
  exact
  { e with
    map_smul' := by
      intro r x
      -- Fix the additive equivalence in the goal so its fibre indices elaborate uniformly.
      change e (r • x) = r • e x
      ext k i
      rfl }

/-- The grid chain module decomposed as the direct sum of its `(Maslov, Alexander)`-homogeneous
pieces. -/
noncomputable def bigradedChainEquiv (R : Type*) [Semiring R] (hG : G.IsKnot) :
    GridChain R n ≃ₗ[R] ⨁ g : ℤ × ℤ, G.BigradedChainPiece R hG g :=
  (finsuppLEquivDirectSum R R (GridState n)).trans
    (sigmaFiberLinearEquiv (G.bidegree hG))

/-- In the bigraded decomposition, the coefficient at a state in degree `g` is its original grid
chain coefficient. -/
@[simp]
theorem bigradedChainEquiv_apply_apply (R : Type*) [Semiring R] (hG : G.IsKnot)
    (c : GridChain R n) (g : ℤ × ℤ) (x : {x : GridState n // G.bidegree hG x = g}) :
    G.bigradedChainEquiv R hG c g x = c x := by
  rw [bigradedChainEquiv, LinearEquiv.trans_apply, sigmaFiberLinearEquiv]
  -- Expose the upgraded additive equivalence so Mathlib's pointwise fibre formula applies.
  change ((DirectSum.sigmaFiberAddEquiv (β := fun _ : GridState n => R) (G.bidegree hG))
      ((finsuppLEquivDirectSum R R (GridState n)) c)) g x = c x
  rw [DirectSum.sigmaFiberAddEquiv_apply_apply, finsuppLEquivDirectSum_apply]

/-- A grid-state generator maps to the copy of the coefficient ring indexed by that state inside
its own bidegree. -/
@[simp]
theorem bigradedChainEquiv_single (R : Type*) [Semiring R] (hG : G.IsKnot)
    (x : GridState n) (r : R) :
    G.bigradedChainEquiv R hG (Finsupp.single x r) =
      DirectSum.lof R (ℤ × ℤ) (fun g => G.BigradedChainPiece R hG g) (G.bidegree hG x)
        (DirectSum.lof R {y : GridState n // G.bidegree hG y = G.bidegree hG x}
          (fun _ => R) ⟨x, rfl⟩ r) := by
  rw [bigradedChainEquiv, LinearEquiv.trans_apply, sigmaFiberLinearEquiv,
    finsuppLEquivDirectSum_single]
  exact DirectSum.sigmaFiberAddEquiv_of (β := fun _ : GridState n => R)
    (G.bidegree hG) x r

/-- Over a division ring, the rank of a homogeneous grid-chain piece is the number of states in
its bidegree. -/
theorem finrank_bigradedChainPiece (R : Type*) [DivisionRing R] (hG : G.IsKnot) (g : ℤ × ℤ) :
    Module.finrank R (G.BigradedChainPiece R hG g) =
      (Finset.univ.filter fun x : GridState n => G.bidegree hG x = g).card := by
  rw [Module.finrank_directSum]
  simp [Fintype.card_subtype]

/-- A homogeneous grid-chain piece has positive rank exactly when its bidegree is occupied by a
grid state. -/
theorem finrank_bigradedChainPiece_pos_iff (R : Type*) [DivisionRing R] (hG : G.IsKnot)
    (g : ℤ × ℤ) :
    0 < Module.finrank R (G.BigradedChainPiece R hG g) ↔ g ∈ G.bidegreeSupport hG := by
  rw [G.finrank_bigradedChainPiece R hG g, Finset.card_pos,
    G.mem_bidegreeSupport_iff hG g]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩

/-- The ranks of all occupied homogeneous pieces add to `n!`, the number of grid states. -/
theorem sum_finrank_bigradedChainPiece (R : Type*) [DivisionRing R] (hG : G.IsKnot) :
    ∑ g ∈ G.bidegreeSupport hG, Module.finrank R (G.BigradedChainPiece R hG g) =
      n.factorial := by
  simp_rw [G.finrank_bigradedChainPiece R hG]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp

end GridDiagram

end TauCeti
