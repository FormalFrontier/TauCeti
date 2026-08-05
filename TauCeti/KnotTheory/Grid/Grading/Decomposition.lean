/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import TauCeti.KnotTheory.Grid.Complex
public import TauCeti.KnotTheory.Grid.Grading.Integer

/-!
# The bigraded grid chain module

This file decomposes the free grid chain module into its homogeneous summands. A grid state has
bidegree `(M_O, 2A)`, using the integer Maslov grading and the integer numerator of twice the
Alexander grading. Doubling the second coordinate keeps the construction valid for link grids,
whose Alexander grading can be half-integral, while retaining the usual integer Alexander degree
on knot grids once its parity theorem is available.

For a bidegree `d`, `GridDiagram.bigradedPiece R d` consists of the chains supported on states of
degree `d`. The main result `GridDiagram.bigradedPieceDecomposition` packages these submodules as
Mathlib's canonical internal direct-sum decomposition. Consequently downstream constructions can
use `DirectSum.decompose` and the standard graded-module API instead of unfolding finite supports.

## Main definitions

* `TauCeti.GridDiagram.bidegree`: the `(M_O, 2A)` degree of a grid state.
* `TauCeti.GridDiagram.bigradedPiece`: chains homogeneous of a fixed bidegree.
* `TauCeti.GridDiagram.bigradedPieceDecomposition`: the direct-sum decomposition by bidegree.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3--G.4: the grid
complex needs a bigrading decomposition before its homology can be graded and its graded Euler
characteristic compared with the Alexander polynomial. The grading conventions follow
Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Chapter 4.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The integral bidegree `(M_O, 2A)` of a grid state.

The second coordinate is twice the Alexander grading so that link grids with half-integral
Alexander degree are included without a parity hypothesis. -/
def bidegree (x : GridState n) : ℤ × ℤ :=
  (G.maslovOℤ x, G.alexanderTwoℤ x)

/-- The Maslov coordinate of a grid state's bidegree. -/
@[simp]
theorem bidegree_fst (x : GridState n) : (G.bidegree x).1 = G.maslovOℤ x :=
  (rfl)

/-- The doubled Alexander coordinate of a grid state's bidegree. -/
@[simp]
theorem bidegree_snd (x : GridState n) : (G.bidegree x).2 = G.alexanderTwoℤ x :=
  (rfl)

/-- Diagonal reflection preserves the bidegree of a grid state. -/
@[simp]
theorem bidegree_transpose (x : GridState n) :
    G.transpose.bidegree x.transpose = G.bidegree x := by
  apply Prod.ext
  · simpa only [bidegree_fst] using G.maslovOℤ_transpose x
  · simpa only [bidegree_snd] using G.alexanderTwoℤ_transpose x

/-- Half-turn rotation preserves the bidegree of a grid state. -/
@[simp]
theorem bidegree_rotate (x : GridState n) :
    G.rotate.bidegree x.rotate = G.bidegree x := by
  apply Prod.ext
  · simpa only [bidegree_fst] using G.maslovOℤ_rotate x
  · simpa only [bidegree_snd] using G.alexanderTwoℤ_rotate x

/-- The submodule of grid chains supported on states of bidegree `d`. -/
def bigradedPiece (R : Type*) [Semiring R] (d : ℤ × ℤ) :
    Submodule R (GridChain R n) :=
  Finsupp.supported R R {x | G.bidegree x = d}

variable {G}

/-- A chain belongs to a homogeneous piece exactly when every state outside that bidegree has
zero coefficient. -/
theorem mem_bigradedPiece_iff {R : Type*} [Semiring R] {d : ℤ × ℤ}
    (c : GridChain R n) :
    c ∈ G.bigradedPiece R d ↔ ∀ x, G.bidegree x ≠ d → c x = 0 := by
  rw [bigradedPiece, Finsupp.mem_supported']
  rfl

/-- A scalar multiple of one grid-state generator belongs to the piece indexed by that state. -/
theorem single_mem_bigradedPiece {R : Type*} [Semiring R] (x : GridState n) (a : R) :
    Finsupp.single x a ∈ G.bigradedPiece R (G.bidegree x) := by
  exact Finsupp.single_mem_supported R a rfl

/-- A nonzero standard generator belongs to precisely its own bidegree piece. -/
@[simp]
theorem single_one_mem_bigradedPiece_iff {R : Type*} [Semiring R] [Nontrivial R]
    (x : GridState n) (d : ℤ × ℤ) :
    Finsupp.single x 1 ∈ G.bigradedPiece R d ↔ G.bidegree x = d := by
  rw [bigradedPiece, Finsupp.mem_supported]
  simp

section Decomposition

variable (G) (R : Type*) [CommSemiring R]

/-- Split a grid chain into its homogeneous bidegree pieces. -/
noncomputable def bigradingDecomposition :
    GridChain R n →ₗ[R] DirectSum (ℤ × ℤ) fun d ↦ G.bigradedPiece R d :=
  Finsupp.lsum R fun x : GridState n ↦
    (DirectSum.lof R (ℤ × ℤ) (G.bigradedPiece R ·) (G.bidegree x)).comp
      (LinearMap.codRestrict _ (Finsupp.lsingle x) fun a ↦ G.single_mem_bigradedPiece x a)

/-- Splitting a single generator puts it in the summand indexed by its bidegree. -/
@[simp]
theorem bigradingDecomposition_single (x : GridState n) (a : R) :
    G.bigradingDecomposition R (Finsupp.single x a) =
      DirectSum.lof R (ℤ × ℤ) (G.bigradedPiece R ·) (G.bidegree x)
        ⟨Finsupp.single x a, G.single_mem_bigradedPiece x a⟩ := by
  classical
  simp [bigradingDecomposition]
  congr

/-- Grid chains are the internal direct sum of the submodules at each `(M_O, 2A)` bidegree. -/
noncomputable instance bigradedPieceDecomposition :
    DirectSum.Decomposition (G.bigradedPiece R) where
  decompose' := G.bigradingDecomposition R
  left_inv := by
    have h : DirectSum.coeLinearMap (G.bigradedPiece R) ∘ₗ G.bigradingDecomposition R =
        LinearMap.id := by
      apply Finsupp.lhom_ext
      intro x a
      simp
    exact DFunLike.congr_fun h
  right_inv := by
    have decompose_of_mem : ∀ {d : ℤ × ℤ} (c : GridChain R n)
        (hc : c ∈ G.bigradedPiece R d),
        G.bigradingDecomposition R c =
          DirectSum.lof R (ℤ × ℤ) (G.bigradedPiece R ·) d ⟨c, hc⟩ := by
      intro d c
      classical
      induction c using Finsupp.induction with
      | zero =>
          intro hc
          have hzero : (⟨0, hc⟩ : G.bigradedPiece R d) = 0 := rfl
          rw [hzero]
          exact (map_zero (DirectSum.lof R (ℤ × ℤ) (G.bigradedPiece R ·) d)).symm
      | single_add x a c hx ha ih =>
          intro hc
          have hdegree : G.bidegree x = d := by
            by_contra hne
            have hzero := (G.mem_bigradedPiece_iff (Finsupp.single x a + c)).mp hc x hne
            have hcx : c x = 0 := Finsupp.notMem_support_iff.mp hx
            simp [hcx, ha] at hzero
          have hc' : c ∈ G.bigradedPiece R d := by
            rw [G.mem_bigradedPiece_iff]
            intro y hy
            have hzero := (G.mem_bigradedPiece_iff (Finsupp.single x a + c)).mp hc y hy
            by_cases hyx : y = x
            · subst y
              exact Finsupp.notMem_support_iff.mp hx
            · simpa [hyx] using hzero
          subst d
          rw [map_add, G.bigradingDecomposition_single, ih hc', ← map_add]
          congr
    have h : G.bigradingDecomposition R ∘ₗ DirectSum.coeLinearMap (G.bigradedPiece R) =
        LinearMap.id := by
      apply DirectSum.linearMap_ext
      intro d
      apply LinearMap.ext
      intro c
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
      exact decompose_of_mem c c.property
    exact DFunLike.congr_fun h

/-- The canonical direct-sum decomposition sends a grid-state generator to the summand indexed by
its bidegree. -/
@[simp]
theorem decompose_bigradedPiece_single (x : GridState n) (a : R) :
    DirectSum.decompose (G.bigradedPiece R) (Finsupp.single x a) =
      DirectSum.lof R (ℤ × ℤ) (G.bigradedPiece R ·) (G.bidegree x)
        ⟨Finsupp.single x a, G.single_mem_bigradedPiece x a⟩ := by
  exact G.bigradingDecomposition_single R x a

end Decomposition

end GridDiagram

end TauCeti
