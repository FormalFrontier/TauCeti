/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Direct sums of internally graded modules

This file equips an external direct sum of internally graded modules with its canonical internal
grading.  Its degree-`p` piece is the direct sum of the componentwise degree-`p` pieces, included
in the ambient direct sum, so membership is characterized componentwise.

This is the direct-sum compatibility target in Layer 0 of the `DGAInfinity` roadmap.

## Main definitions

* `TauCeti.InternalGrading.directSumPieceInclusion`: the inclusion of homogeneous summands of one
  fixed degree into the ambient direct sum.
* `TauCeti.InternalGrading.directSumPiece`: the corresponding homogeneous submodule.
* `TauCeti.InternalGrading.directSum`: the canonical internal grading on an external direct sum.

## References

* Mathlib's `DirectSum` API.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

open scoped DirectSum

namespace TauCeti

universe u v w

namespace InternalGrading

variable {R : Type u} {ι : Type v} {M : ι → Type w}
variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The canonical inclusion of the direct sum of degree-`p` pieces into the direct sum of the
underlying modules. -/
def directSumPieceInclusion (G : ∀ i, InternalGrading R (M i)) (p : ℤ) :
    (⨁ i, (G i).piece p) →ₗ[R] ⨁ i, M i :=
  TauCeti.DirectSum.piInclusion fun i ↦ (G i).piece p

/-- The componentwise formula for the graded direct-sum inclusion. -/
@[simp]
theorem directSumPieceInclusion_apply (G : ∀ i, InternalGrading R (M i)) (p : ℤ)
    (x : ⨁ i, (G i).piece p) (i : ι) :
    directSumPieceInclusion G p x i = (x i : M i) := by
  simpa only [directSumPieceInclusion] using
    (TauCeti.DirectSum.piInclusion_apply (fun i ↦ (G i).piece p) x i)

/-- The degree-`p` piece in the direct sum of a family of internally graded modules. -/
def directSumPiece (G : ∀ i, InternalGrading R (M i)) (p : ℤ) : Submodule R (⨁ i, M i) :=
  TauCeti.DirectSum.piSubmodule fun i ↦ (G i).piece p

/-- On a homogeneous summand, `directSumPieceInclusion` is the usual external direct-sum
inclusion. -/
@[simp]
theorem directSumPieceInclusion_lof (G : ∀ i, InternalGrading R (M i)) (p : ℤ) (i : ι)
    (x : (G i).piece p) [DecidableEq ι] :
    directSumPieceInclusion G p (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x) =
      DirectSum.lof R ι M i x := by
  exact TauCeti.DirectSum.piInclusion_lof (fun i ↦ (G i).piece p) i x

/-- The linear equivalence from the external direct sum of degree-`p` pieces to its range in the
ambient direct sum. -/
noncomputable def directSumPieceEquiv (G : ∀ i, InternalGrading R (M i)) (p : ℤ) :
    (⨁ i, (G i).piece p) ≃ₗ[R] directSumPiece G p :=
  TauCeti.DirectSum.piSubmoduleEquiv fun i ↦ (G i).piece p

/-- The underlying element of `directSumPieceEquiv` is the canonical inclusion. -/
@[simp]
theorem directSumPieceEquiv_apply (G : ∀ i, InternalGrading R (M i)) (p : ℤ)
    (x : ⨁ i, (G i).piece p) :
    ((directSumPieceEquiv G p x : directSumPiece G p) : ⨁ i, M i) =
      directSumPieceInclusion G p x := by
  exact TauCeti.DirectSum.piSubmoduleEquiv_apply (fun i ↦ (G i).piece p) x

/-- The componentwise formula for the inverse of `directSumPieceEquiv`. -/
@[simp]
theorem directSumPieceEquiv_symm_apply (G : ∀ i, InternalGrading R (M i)) (p : ℤ)
    (y : directSumPiece G p) (i : ι) :
    ((directSumPieceEquiv G p).symm y i : M i) = (y : ⨁ i, M i) i := by
  exact TauCeti.DirectSum.piSubmoduleEquiv_symm_apply (fun i ↦ (G i).piece p) y i

private def sigmaSwap (ι : Type v) : (Σ _ : ℤ, ι) ≃ (Σ _ : ι, ℤ) where
  toFun := fun ⟨p, i⟩ ↦ ⟨i, p⟩
  invFun := fun ⟨i, p⟩ ↦ ⟨p, i⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

private def sigmaSwapPieceEquiv (G : ∀ i, InternalGrading R (M i)) (z : Σ _ : ι, ℤ) :
    (G ((sigmaSwap ι).symm z).2).piece ((sigmaSwap ι).symm z).1 ≃ₗ[R] (G z.1).piece z.2 := by
  obtain ⟨i, p⟩ := z
  exact LinearEquiv.refl R _

-- Evaluating the reindexing equivalence on a generator identifies this map with the identity
-- on the corresponding degree-and-summand component.  An API-level rewrite
-- (`DirectSum.coe_congrLinearEquiv` followed by `DirectSum.lmap_lof`) does not typecheck here:
-- the domain family of `sigmaSwapPieceEquiv G z` is
-- `fun z ↦ (G ((sigmaSwap ι).symm z).2).piece ((sigmaSwap ι).symm z).1`, which agrees with the
-- `lof` family `fun z ↦ (G z.1).piece z.2` only up to the semireducible reindexing
-- `(sigmaSwap ι).symm`, and rewrite-step unification does not unfold it.  The `change` below
-- confines that definitional reduction to this private, single-purpose helper.
private theorem sigmaSwapPieceEquiv_lof (G : ∀ i, InternalGrading R (M i)) (p : ℤ) (i : ι)
    (x : (G i).piece p) [DecidableEq ι] :
    DirectSum.congrLinearEquiv (fun z ↦ sigmaSwapPieceEquiv G z)
        (DirectSum.lof R (Σ _ : ι, ℤ)
          (fun z ↦ (G ((sigmaSwap ι).symm z).2).piece ((sigmaSwap ι).symm z).1) ⟨i, p⟩ x) =
      DirectSum.lof R (Σ _ : ι, ℤ) (fun z ↦ (G z.1).piece z.2) ⟨i, p⟩ x := by
  change DirectSum.lmap
      (fun z : Σ _ : ι, ℤ ↦ (LinearEquiv.refl R ((G z.1).piece z.2)).toLinearMap)
      (DirectSum.lof R (Σ _ : ι, ℤ) (fun z ↦ (G z.1).piece z.2) ⟨i, p⟩ x) = _
  rw [DirectSum.lmap_lof]
  rfl

-- Mathlib defines `DirectSum.sigmaLcurryEquiv` as `DFinsupp.sigmaCurryLEquiv` and states no
-- application lemma for it, so its action cannot be rewritten through public API.  It is
-- nevertheless definitionally the additive currying map `DirectSum.sigmaCurry`, whose generator
-- behaviour Mathlib does expose (`DirectSum.sigmaCurry_apply`, `DirectSum.sigmaCurry_of`).
-- This private helper isolates that definitional identification, and a Mathlib refactor of
-- either definition will surface exactly here.
private theorem sigmaLcurryEquiv_apply {ι κ : Type*} {δ : ι → κ → Type*}
    [DecidableEq ι] [∀ i j, AddCommMonoid (δ i j)]
    [∀ i j, Module R (δ i j)] (x : ⨁ z : Σ _ : ι, κ, δ z.1 z.2) :
    DirectSum.sigmaLcurryEquiv R (δ := δ) x = DirectSum.sigmaCurry x := by
  rfl

private theorem sigmaLcurryEquiv_lof_lof {ι κ : Type*} {δ : ι → κ → Type*}
    [DecidableEq ι] [DecidableEq κ] [∀ i j, AddCommMonoid (δ i j)]
    [∀ i j, Module R (δ i j)] (i : ι) (j : κ) (x : δ i j) :
    DirectSum.sigmaLcurryEquiv R (δ := δ)
        (DirectSum.lof R (Σ _ : ι, κ) (fun z ↦ δ z.1 z.2) ⟨i, j⟩ x) =
      DirectSum.lof R ι (fun i ↦ ⨁ j, δ i j) i
        (DirectSum.lof R κ (fun j ↦ δ i j) j x) := by
  rw [sigmaLcurryEquiv_apply]
  rw [DirectSum.lof_eq_of R (Σ _ : ι, κ), DirectSum.lof_eq_of R ι,
    DirectSum.lof_eq_of R κ]
  exact DirectSum.sigmaCurry_of (δ := δ) ⟨i, j⟩ x

private theorem sigmaLcurryEquiv_symm_lof_lof {ι κ : Type*} {δ : ι → κ → Type*}
    [DecidableEq ι] [DecidableEq κ] [∀ i j, AddCommMonoid (δ i j)]
    [∀ i j, Module R (δ i j)] (i : ι) (j : κ) (x : δ i j) :
    (DirectSum.sigmaLcurryEquiv R (δ := δ)).symm
        (DirectSum.lof R ι (fun i ↦ ⨁ j, δ i j) i
          (DirectSum.lof R κ (fun j ↦ δ i j) j x)) =
      DirectSum.lof R (Σ _ : ι, κ) (fun z ↦ δ z.1 z.2) ⟨i, j⟩ x := by
  apply (DirectSum.sigmaLcurryEquiv R (δ := δ)).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (sigmaLcurryEquiv_lof_lof i j x).symm

private noncomputable def directSumRecomposeEquiv (G : ∀ i, InternalGrading R (M i))
    [DecidableEq ι] : (⨁ p, directSumPiece G p) ≃ₗ[R] ⨁ i, M i :=
  (DirectSum.congrLinearEquiv fun p ↦ (directSumPieceEquiv G p).symm).trans <|
    (DirectSum.sigmaLcurryEquiv R (δ := fun p i ↦ (G i).piece p)).symm.trans <|
      (DirectSum.lequivCongrLeft R (sigmaSwap ι)).trans <|
        (DirectSum.congrLinearEquiv fun z ↦ sigmaSwapPieceEquiv G z).trans <|
          (DirectSum.sigmaLcurryEquiv R (δ := fun i p ↦ (G i).piece p)).trans <|
            DirectSum.congrLinearEquiv fun i ↦
              (DirectSum.decomposeLinearEquiv (G i).piece).symm

private theorem directSumRecomposeEquiv_lof_lof (G : ∀ i, InternalGrading R (M i))
    (p : ℤ) (i : ι) (x : (G i).piece p) [DecidableEq ι] :
    directSumRecomposeEquiv G
        (DirectSum.lof R ℤ (fun p ↦ directSumPiece G p) p
          (directSumPieceEquiv G p
            (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x))) =
      DirectSum.lof R ι M i x := by
  rw [directSumRecomposeEquiv]
  simp only [LinearEquiv.trans_apply]
  have hpieces :
      (DirectSum.congrLinearEquiv fun p ↦ (directSumPieceEquiv G p).symm)
          (DirectSum.lof R ℤ (fun p ↦ directSumPiece G p) p
            (directSumPieceEquiv G p
              (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x))) =
        DirectSum.lof R ℤ (fun p ↦ ⨁ i, (G i).piece p) p
          (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x) := by
    rw [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
    congr 1
    exact (directSumPieceEquiv G p).symm_apply_apply _
  rw [hpieces]
  rw [sigmaLcurryEquiv_symm_lof_lof]
  rw [DirectSum.lequivCongrLeft_lof
    (M := fun z : Σ _ : ℤ, ι ↦ (G z.2).piece z.1) R (e := sigmaSwap ι)
    (i := Sigma.mk p i) (k := Sigma.mk i p) rfl x x rfl]
  -- After swapping the indices, apply the second curry generator formula.
  rw [sigmaSwapPieceEquiv_lof]
  rw [sigmaLcurryEquiv_lof_lof]
  -- The last congruence map acts componentwise on the single summand.
  rw [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
  congr 1
  exact DirectSum.decomposeLinearEquiv_symm_lof (G i).piece p x

private theorem directSumRecomposeEquiv_lof (G : ∀ i, InternalGrading R (M i))
    (p : ℤ) (x : directSumPiece G p) [DecidableEq ι] :
    directSumRecomposeEquiv G
        (DirectSum.lof R ℤ (fun p ↦ directSumPiece G p) p x) =
      (x : ⨁ i, M i) := by
  obtain ⟨y, rfl⟩ := (directSumPieceEquiv G p).surjective x
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i y =>
    rw [← DirectSum.lof_eq_of R ι (fun i ↦ (G i).piece p), directSumPieceEquiv_apply,
      directSumPieceInclusion_lof]
    exact directSumRecomposeEquiv_lof_lof G p i y
  | add x y hx hy =>
    simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy

/-- The canonical degreewise ranges in an external direct sum form an internal direct sum. -/
theorem isInternal_directSumPiece (G : ∀ i, InternalGrading R (M i)) :
    DirectSum.IsInternal (directSumPiece G) := by
  let _ : DecidableEq ι := Classical.decEq _
  refine TauCeti.DirectSum.isInternal_of_lof
    (e := fun p ↦ LinearEquiv.refl R (directSumPiece G p))
    (E := directSumRecomposeEquiv G) ?_
  intro p x
  simpa only [LinearEquiv.refl_apply] using directSumRecomposeEquiv_lof G p x

/-- The external direct sum of internally graded modules, with degree-`p` piece the image of the
direct sum of the degree-`p` pieces. -/
def directSum (G : ∀ i, InternalGrading R (M i)) :
    InternalGrading R (⨁ i, M i) where
  piece := directSumPiece G
  isInternal := isInternal_directSumPiece G

/-- Membership in the direct sum of degree-`p` pieces is componentwise. -/
@[simp]
theorem mem_directSumPiece_iff (G : ∀ i, InternalGrading R (M i)) (p : ℤ)
    (x : ⨁ i, M i) :
    x ∈ directSumPiece G p ↔ ∀ i, x i ∈ (G i).piece p := by
  exact TauCeti.DirectSum.mem_piSubmodule_iff (fun i ↦ (G i).piece p) x

/-- The homogeneous pieces of `directSum` are the ranges of the canonical degreewise inclusions. -/
@[simp]
theorem directSum_piece (G : ∀ i, InternalGrading R (M i)) (p : ℤ) :
    (directSum G).piece p = directSumPiece G p :=
  by rw [directSum]

/-- The inclusion of a degree-`p` element from one summand belongs to the degree-`p` piece of the
direct-sum grading. -/
theorem lof_mem_directSumPiece (G : ∀ i, InternalGrading R (M i)) (p : ℤ) (i : ι)
    (x : (G i).piece p) [DecidableEq ι] :
    DirectSum.lof R ι M i x ∈ directSumPiece G p := by
  exact TauCeti.DirectSum.lof_mem_piSubmodule (fun i ↦ (G i).piece p) i x

end InternalGrading

end TauCeti
