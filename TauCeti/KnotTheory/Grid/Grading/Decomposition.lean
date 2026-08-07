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
# An auxiliary doubled-Alexander decomposition of the grid chain module

This file gives an auxiliary decomposition of the free grid chain module using the rescaled degree
`(M_O, 2A)`, where both coordinates are integral for arbitrary link grids. This is not the
conventional `(M_O, A)` bigrading: in particular, it doubles Alexander grading shifts. The
conventional decomposition for knot grids requires the still-missing theorem that their Alexander
gradings are integers.

For a rescaled degree `d`, `GridDiagram.doubledAlexanderPiece R d` consists of the chains supported
on states of degree `d`. The main result `GridDiagram.doubledAlexanderPieceDecomposition` packages
these submodules as an internal direct-sum decomposition. It is auxiliary bookkeeping that can be
used without a knot hypothesis; downstream constructions requiring the roadmap's conventional
Alexander degree must wait for its integrality theorem.

## Main definitions

* `TauCeti.GridDiagram.doubledAlexanderBidegree`: the auxiliary `(M_O, 2A)` degree of a grid state.
* `TauCeti.GridDiagram.doubledAlexanderPiece`: chains homogeneous for this rescaled degree.
* `TauCeti.GridDiagram.doubledAlexanderPieceDecomposition`: its direct-sum decomposition.

## References

This supplies preliminary bookkeeping for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane G.2--G.4. The roadmap's actual `(M_O, A)` decomposition will specialize to knot grids after
the parity theorem establishing integer-valuedness of `A`. The grading conventions follow
Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Chapter 4.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The auxiliary integral bidegree `(M_O, 2A)` of a grid state.

The second coordinate is twice the Alexander grading so that link grids with half-integral
Alexander degree are included without a parity hypothesis. It is rescaled and is not the
conventional `(M_O, A)` bidegree. -/
def doubledAlexanderBidegree (x : GridState n) : ℤ × ℤ :=
  (G.maslovOℤ x, G.alexanderTwoℤ x)

/-- The Maslov coordinate of a grid state's auxiliary doubled-Alexander bidegree. -/
@[simp]
theorem doubledAlexanderBidegree_fst (x : GridState n) :
    (G.doubledAlexanderBidegree x).1 = G.maslovOℤ x :=
  (rfl)

/-- The doubled Alexander coordinate of a grid state's auxiliary bidegree. -/
@[simp]
theorem doubledAlexanderBidegree_snd (x : GridState n) :
    (G.doubledAlexanderBidegree x).2 = G.alexanderTwoℤ x :=
  (rfl)

/-- Diagonal reflection preserves the auxiliary doubled-Alexander bidegree of a grid state. -/
@[simp]
theorem doubledAlexanderBidegree_transpose (x : GridState n) :
    G.transpose.doubledAlexanderBidegree x.transpose = G.doubledAlexanderBidegree x := by
  apply Prod.ext
  · simpa only [doubledAlexanderBidegree_fst] using G.maslovOℤ_transpose x
  · simpa only [doubledAlexanderBidegree_snd] using G.alexanderTwoℤ_transpose x

/-- Half-turn rotation preserves the auxiliary doubled-Alexander bidegree of a grid state. -/
@[simp]
theorem doubledAlexanderBidegree_rotate (x : GridState n) :
    G.rotate.doubledAlexanderBidegree x.rotate = G.doubledAlexanderBidegree x := by
  apply Prod.ext
  · simpa only [doubledAlexanderBidegree_fst] using G.maslovOℤ_rotate x
  · simpa only [doubledAlexanderBidegree_snd] using G.alexanderTwoℤ_rotate x

/-- The submodule of grid chains supported on states of auxiliary degree `(M_O, 2A) = d`. -/
def doubledAlexanderPiece (R : Type*) [Semiring R] (d : ℤ × ℤ) :
    Submodule R (GridChain R n) :=
  Finsupp.supported R R {x | G.doubledAlexanderBidegree x = d}

variable {G}

/-- A chain belongs to a homogeneous piece exactly when every state outside that bidegree has
zero coefficient. -/
theorem mem_doubledAlexanderPiece_iff {R : Type*} [Semiring R] {d : ℤ × ℤ}
    (c : GridChain R n) :
    c ∈ G.doubledAlexanderPiece R d ↔
      ∀ x, G.doubledAlexanderBidegree x ≠ d → c x = 0 := by
  rw [doubledAlexanderPiece, Finsupp.mem_supported']
  rfl

/-- A scalar multiple of one grid-state generator belongs to its doubled-Alexander piece. -/
theorem single_mem_doubledAlexanderPiece {R : Type*} [Semiring R]
    (x : GridState n) (a : R) :
    Finsupp.single x a ∈
      G.doubledAlexanderPiece R (G.doubledAlexanderBidegree x) := by
  exact Finsupp.single_mem_supported R a rfl

/-- A nonzero standard generator belongs to precisely its own doubled-Alexander piece. -/
@[simp]
theorem single_one_mem_doubledAlexanderPiece_iff {R : Type*} [Semiring R] [Nontrivial R]
    (x : GridState n) (d : ℤ × ℤ) :
    Finsupp.single x 1 ∈ G.doubledAlexanderPiece R d ↔
      G.doubledAlexanderBidegree x = d := by
  rw [doubledAlexanderPiece, Finsupp.mem_supported]
  simp

section Decomposition

variable (G) (R : Type*) [Semiring R]

/-- Split a grid chain into its homogeneous auxiliary `(M_O, 2A)` pieces.

Implementation-only linear map underlying `doubledAlexanderPieceDecomposition`. External users
should access the decomposition through `DirectSum.decompose`. -/
noncomputable def doubledAlexanderDecomposition :
    GridChain R n →ₗ[R] DirectSum (ℤ × ℤ) fun d ↦ G.doubledAlexanderPiece R d :=
  Finsupp.lsum ℕ fun x : GridState n ↦
    (DirectSum.lof R (ℤ × ℤ) (G.doubledAlexanderPiece R ·)
      (G.doubledAlexanderBidegree x)).comp
      (LinearMap.codRestrict _ (Finsupp.lsingle x) fun a ↦
        G.single_mem_doubledAlexanderPiece x a)

theorem doubledAlexanderDecomposition_single (x : GridState n) (a : R) :
    doubledAlexanderDecomposition G R (Finsupp.single x a) =
      DirectSum.lof R (ℤ × ℤ) (G.doubledAlexanderPiece R ·)
        (G.doubledAlexanderBidegree x)
        ⟨Finsupp.single x a, G.single_mem_doubledAlexanderPiece x a⟩ := by
  classical
  simp [doubledAlexanderDecomposition]
  congr

/-- The implementation map takes a homogeneous chain to its own summand. This is the reusable
characterization used to prove the direct-sum right-inverse law. -/
theorem doubledAlexanderDecomposition_of_mem {d : ℤ × ℤ} (c : GridChain R n)
    (hc : c ∈ G.doubledAlexanderPiece R d) :
    doubledAlexanderDecomposition G R c =
      DirectSum.lof R (ℤ × ℤ) (G.doubledAlexanderPiece R ·) d ⟨c, hc⟩ := by
  classical
  induction c using Finsupp.induction with
  | zero =>
      have hzero : (⟨0, hc⟩ : G.doubledAlexanderPiece R d) = 0 := rfl
      rw [hzero]
      exact (map_zero (DirectSum.lof R (ℤ × ℤ) (G.doubledAlexanderPiece R ·) d)).symm
  | single_add x a c hx ha ih =>
      have hdegree : G.doubledAlexanderBidegree x = d := by
        by_contra hne
        have hzero := (G.mem_doubledAlexanderPiece_iff (Finsupp.single x a + c)).mp hc x hne
        have hcx : c x = 0 := Finsupp.notMem_support_iff.mp hx
        simp [hcx, ha] at hzero
      have hc' : c ∈ G.doubledAlexanderPiece R d := by
        rw [G.mem_doubledAlexanderPiece_iff]
        intro y hy
        have hzero := (G.mem_doubledAlexanderPiece_iff (Finsupp.single x a + c)).mp hc y hy
        by_cases hyx : y = x
        · subst y
          exact Finsupp.notMem_support_iff.mp hx
        · simpa [hyx] using hzero
      subst d
      rw [map_add, doubledAlexanderDecomposition_single G R x a, ih hc', ← map_add]
      congr

/-- Grid chains are the internal direct sum of the submodules at each auxiliary `(M_O, 2A)`
bidegree. -/
noncomputable instance doubledAlexanderPieceDecomposition :
    DirectSum.Decomposition (G.doubledAlexanderPiece R) where
  decompose' := doubledAlexanderDecomposition G R
  left_inv := by
    have h : DirectSum.coeLinearMap (G.doubledAlexanderPiece R) ∘ₗ
        doubledAlexanderDecomposition G R = LinearMap.id := by
      apply Finsupp.lhom_ext
      intro x a
      simp [doubledAlexanderDecomposition]
      rfl
    exact DFunLike.congr_fun h
  right_inv := by
    have h : doubledAlexanderDecomposition G R ∘ₗ
        DirectSum.coeLinearMap (G.doubledAlexanderPiece R) = LinearMap.id := by
      apply DirectSum.linearMap_ext
      intro d
      apply LinearMap.ext
      intro c
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
      exact doubledAlexanderDecomposition_of_mem G R c c.property
    exact DFunLike.congr_fun h

/-- The doubled-Alexander direct-sum decomposition sends a grid-state generator to its summand. -/
@[simp]
theorem decompose_doubledAlexanderPiece_single (x : GridState n) (a : R) :
    DirectSum.decompose (G.doubledAlexanderPiece R) (Finsupp.single x a) =
      DirectSum.lof R (ℤ × ℤ) (G.doubledAlexanderPiece R ·)
        (G.doubledAlexanderBidegree x)
        ⟨Finsupp.single x a, G.single_mem_doubledAlexanderPiece x a⟩ :=
  doubledAlexanderDecomposition_single G R x a

end Decomposition

end GridDiagram

end TauCeti
