/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Direct sums of internally graded modules

This file equips an external direct sum of internally graded modules with its canonical internal
grading.  Its degree-`p` piece is the range of the map that includes the direct sum of the
degree-`p` pieces into the ambient direct sum.  Thus the internal and external presentations of a
grading remain compatible when taking arbitrary direct sums.

This is the direct-sum compatibility target in Layer 0 of the `DGAInfinity` roadmap.

## Main definitions

* `TauCeti.InternalGrading.directSumPieceInclusion`: the inclusion of homogeneous summands of one
  fixed degree into the ambient direct sum.
* `TauCeti.InternalGrading.directSumPiece`: the corresponding homogeneous submodule.
* `TauCeti.InternalGrading.directSum`: the canonical internal grading on an external direct sum.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
* Mathlib's `DirectSum` API.
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
  DirectSum.lmap fun i ↦ ((G i).piece p).subtype

/-- The degree-`p` piece in the direct sum of a family of internally graded modules. -/
def directSumPiece (G : ∀ i, InternalGrading R (M i)) (p : ℤ) : Submodule R (⨁ i, M i) :=
  LinearMap.range (directSumPieceInclusion G p)

/-- On a homogeneous summand, `directSumPieceInclusion` is the usual external direct-sum
inclusion. -/
@[simp]
theorem directSumPieceInclusion_lof (G : ∀ i, InternalGrading R (M i)) (p : ℤ) (i : ι)
    (x : (G i).piece p) [DecidableEq ι] :
    directSumPieceInclusion G p (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x) =
      DirectSum.lof R ι M i x := by
  simp [directSumPieceInclusion]

private theorem directSumPieceInclusion_injective (G : ∀ i, InternalGrading R (M i)) (p : ℤ) :
    Function.Injective (directSumPieceInclusion G p) := by
  rw [directSumPieceInclusion]
  refine (DirectSum.lmap_injective fun i ↦ ((G i).piece p).subtype).mpr fun i ↦ ?_
  exact ((G i).piece p).injective_subtype

/-- The linear equivalence from the external direct sum of degree-`p` pieces to its range in the
ambient direct sum. -/
noncomputable def directSumPieceEquiv (G : ∀ i, InternalGrading R (M i)) (p : ℤ) :
    (⨁ i, (G i).piece p) ≃ₗ[R] directSumPiece G p :=
  LinearEquiv.ofInjective (directSumPieceInclusion G p)
    (directSumPieceInclusion_injective G p)

/-- The underlying element of `directSumPieceEquiv` is the canonical inclusion. -/
@[simp]
theorem directSumPieceEquiv_apply (G : ∀ i, InternalGrading R (M i)) (p : ℤ)
    (x : ⨁ i, (G i).piece p) :
    ((directSumPieceEquiv G p x : directSumPiece G p) : ⨁ i, M i) =
      directSumPieceInclusion G p x := by
  rw [directSumPieceEquiv]
  exact LinearEquiv.ofInjective_apply _ x

private def sigmaSwap (ι : Type v) : (Σ _ : ℤ, ι) ≃ (Σ _ : ι, ℤ) where
  toFun := fun ⟨p, i⟩ ↦ ⟨i, p⟩
  invFun := fun ⟨i, p⟩ ↦ ⟨p, i⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

private def sigmaSwapPieceEquiv (G : ∀ i, InternalGrading R (M i)) (z : Σ _ : ι, ℤ) :
    (G ((sigmaSwap ι).symm z).2).piece ((sigmaSwap ι).symm z).1 ≃ₗ[R] (G z.1).piece z.2 := by
  obtain ⟨i, p⟩ := z
  exact LinearEquiv.refl R _

private theorem sigmaLcurryEquiv_symm_lof_lof (G : ∀ i, InternalGrading R (M i))
    (p : ℤ) (i : ι) (x : (G i).piece p) [DecidableEq ι] :
    (DirectSum.sigmaLcurryEquiv R (δ := fun p i ↦ (G i).piece p)).symm
        (DirectSum.lof R ℤ (fun p ↦ ⨁ i, (G i).piece p) p
          (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x)) =
      DirectSum.lof R (Σ _ : ℤ, ι) (fun z ↦ (G z.2).piece z.1) ⟨p, i⟩ x := by
  apply (DirectSum.sigmaLcurryEquiv R (δ := fun p i ↦ (G i).piece p)).injective
  simp only [LinearEquiv.apply_symm_apply]
  -- Expose the curry equivalence on a generator so `sigmaCurry_of` applies.
  change DirectSum.lof R ℤ (fun p ↦ ⨁ i, (G i).piece p) p
      (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x) =
    DirectSum.sigmaCurry
      (DirectSum.lof R (Σ _ : ℤ, ι) (fun z ↦ (G z.2).piece z.1) ⟨p, i⟩ x)
  rw [DirectSum.lof_eq_of R ℤ, DirectSum.lof_eq_of R ι,
    DirectSum.lof_eq_of R (Σ _ : ℤ, ι)]
  exact (DirectSum.sigmaCurry_of (δ := fun p i ↦ (G i).piece p) ⟨p, i⟩ x).symm

private theorem sigmaLcurryEquiv_lof_lof (G : ∀ i, InternalGrading R (M i))
    (i : ι) (p : ℤ) (x : (G i).piece p) [DecidableEq ι] :
    DirectSum.sigmaLcurryEquiv R (δ := fun i p ↦ (G i).piece p)
        (DirectSum.lof R (Σ _ : ι, ℤ) (fun z ↦ (G z.1).piece z.2) ⟨i, p⟩ x) =
      DirectSum.lof R ι (fun i ↦ ⨁ p, (G i).piece p) i
        (DirectSum.lof R ℤ (fun p ↦ (G i).piece p) p x) := by
  -- The equivalence is definitionally the direct-sum curry map.
  change DirectSum.sigmaCurry
      (DirectSum.lof R (Σ _ : ι, ℤ) (fun z ↦ (G z.1).piece z.2) ⟨i, p⟩ x) =
    DirectSum.lof R ι (fun i ↦ ⨁ p, (G i).piece p) i
      (DirectSum.lof R ℤ (fun p ↦ (G i).piece p) p x)
  rw [DirectSum.lof_eq_of R (Σ _ : ι, ℤ), DirectSum.lof_eq_of R ι,
    DirectSum.lof_eq_of R ℤ]
  exact DirectSum.sigmaCurry_of (δ := fun i p ↦ (G i).piece p) ⟨i, p⟩ x

private noncomputable def directSumRecomposeEquiv (G : ∀ i, InternalGrading R (M i))
    [DecidableEq ι] : (⨁ p, directSumPiece G p) ≃ₗ[R] ⨁ i, M i :=
  (DirectSum.congrLinearEquiv fun p ↦ (directSumPieceEquiv G p).symm).trans <|
    (DirectSum.sigmaLcurryEquiv R (δ := fun p i ↦ (G i).piece p)).symm.trans <|
      (DirectSum.lequivCongrLeft R (sigmaSwap ι)).trans <|
        (DirectSum.congrLinearEquiv fun z ↦ sigmaSwapPieceEquiv G z).trans <|
          (DirectSum.sigmaLcurryEquiv R (δ := fun i p ↦ (G i).piece p)).trans <|
            DirectSum.congrLinearEquiv fun i ↦
              (DirectSum.decomposeLinearEquiv (G i).piece).symm

private theorem directSumPieceEquivs_lof (G : ∀ i, InternalGrading R (M i))
    (p : ℤ) (i : ι) (x : (G i).piece p) [DecidableEq ι] :
    (DirectSum.congrLinearEquiv fun p ↦ (directSumPieceEquiv G p).symm)
        (DirectSum.lof R ℤ (fun p ↦ directSumPiece G p) p
          (directSumPieceEquiv G p
            (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x))) =
      DirectSum.lof R ℤ (fun p ↦ ⨁ i, (G i).piece p) p
        (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x) := by
  -- Expose the bundled map so the direct-sum generator lemma can be rewritten.
  change (DirectSum.congrLinearEquiv fun p ↦ (directSumPieceEquiv G p).symm).toLinearMap
      (DirectSum.lof R ℤ (fun p ↦ directSumPiece G p) p
        (directSumPieceEquiv G p
          (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x))) = _
  rw [DirectSum.congrLinearEquiv_toLinearMap, DirectSum.lmap_lof]
  congr 1
  exact (directSumPieceEquiv G p).symm_apply_apply _

private theorem directSumRecomposeEquiv_lof (G : ∀ i, InternalGrading R (M i))
    (p : ℤ) (i : ι) (x : (G i).piece p) [DecidableEq ι] :
    directSumRecomposeEquiv G
        (DirectSum.lof R ℤ (fun p ↦ directSumPiece G p) p
          (directSumPieceEquiv G p
            (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x))) =
      DirectSum.lof R ι M i x := by
  rw [directSumRecomposeEquiv]
  simp only [LinearEquiv.trans_apply]
  -- Expand the composite on a degree-and-summand generator.
  change (DirectSum.congrLinearEquiv fun i ↦
      (DirectSum.decomposeLinearEquiv (G i).piece).symm)
      (DirectSum.sigmaLcurryEquiv R (δ := fun i p ↦ (G i).piece p)
        ((DirectSum.congrLinearEquiv fun z ↦ sigmaSwapPieceEquiv G z)
          (DirectSum.lequivCongrLeft R (sigmaSwap ι)
            ((DirectSum.sigmaLcurryEquiv R (δ := fun p i ↦ (G i).piece p)).symm
              ((DirectSum.congrLinearEquiv fun p ↦ (directSumPieceEquiv G p).symm)
                (DirectSum.lof R ℤ (fun p ↦ directSumPiece G p) p
                  (directSumPieceEquiv G p
                    (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x)))))))) = _
  rw [directSumPieceEquivs_lof]
  rw [sigmaLcurryEquiv_symm_lof_lof]
  rw [DirectSum.lequivCongrLeft_lof
    (M := fun z : Σ _ : ℤ, ι ↦ (G z.2).piece z.1) R (e := sigmaSwap ι)
    (i := Sigma.mk p i) (k := Sigma.mk i p) rfl x x rfl]
  -- After swapping the indices, apply the second curry generator formula.
  change (DirectSum.congrLinearEquiv fun i ↦
      (DirectSum.decomposeLinearEquiv (G i).piece).symm)
      (DirectSum.sigmaLcurryEquiv R (δ := fun i p ↦ (G i).piece p)
        (DirectSum.lof R (Σ _ : ι, ℤ) (fun z ↦ (G z.1).piece z.2) ⟨i, p⟩ x)) = _
  rw [sigmaLcurryEquiv_lof_lof]
  -- The last congruence map acts componentwise on the single summand.
  change (DirectSum.congrLinearEquiv fun i ↦
      (DirectSum.decomposeLinearEquiv (G i).piece).symm).toLinearMap
      (DirectSum.lof R ι (fun i ↦ ⨁ p, (G i).piece p) i
        (DirectSum.lof R ℤ (fun p ↦ (G i).piece p) p x)) = _
  rw [DirectSum.congrLinearEquiv_toLinearMap, DirectSum.lmap_lof]
  congr 1
  exact DirectSum.decomposeLinearEquiv_symm_lof (G i).piece p x

private theorem coeLinearMap_directSumPiece_eq (G : ∀ i, InternalGrading R (M i))
    [DecidableEq ι] :
    DirectSum.coeLinearMap (directSumPiece G) = (directSumRecomposeEquiv G).toLinearMap := by
  classical
  apply DirectSum.linearMap_ext R
  intro p
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (directSumPieceEquiv G p).surjective x
  induction y using DirectSum.induction_on with
  | zero => simp [directSumRecomposeEquiv]
  | of i y =>
    simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
    rw [← DirectSum.lof_eq_of R ι (fun i ↦ (G i).piece p)]
    rw [directSumPieceEquiv_apply, directSumPieceInclusion_lof]
    exact (directSumRecomposeEquiv_lof G p i y).symm
  | add x y hx hy =>
    simpa only [map_add, LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy

/-- The canonical degreewise ranges in an external direct sum form an internal direct sum. -/
theorem isInternal_directSumPiece (G : ∀ i, InternalGrading R (M i)) :
    DirectSum.IsInternal (directSumPiece G) := by
  classical
  let _ : DecidableEq ι := Classical.decEq _
  change Function.Bijective (DirectSum.coeLinearMap (directSumPiece G))
  rw [coeLinearMap_directSumPiece_eq]
  exact (directSumRecomposeEquiv G).bijective

/-- The external direct sum of internally graded modules, with degree-`p` piece the image of the
direct sum of the degree-`p` pieces. -/
noncomputable def directSum (G : ∀ i, InternalGrading R (M i)) :
    InternalGrading R (⨁ i, M i) where
  piece := directSumPiece G
  isInternal := isInternal_directSumPiece G

/-- Membership in the direct sum of degree-`p` pieces is componentwise. -/
@[simp]
theorem mem_directSumPiece_iff (G : ∀ i, InternalGrading R (M i)) (p : ℤ)
    (x : ⨁ i, M i) :
    x ∈ directSumPiece G p ↔ ∀ i, x i ∈ (G i).piece p := by
  rw [directSumPiece, directSumPieceInclusion, DirectSum.range_lmap]
  simp only [Submodule.mem_comap, DirectSum.coeFnLinearMap_apply, Submodule.mem_pi,
    Set.mem_univ, LinearMap.mem_range]
  constructor
  · intro hx i
    obtain ⟨y, hy⟩ := hx i trivial
    rw [← hy]
    exact y.property
  · intro hx i _
    exact ⟨⟨x i, hx i⟩, rfl⟩

/-- The homogeneous pieces of `directSum` are the ranges of the canonical degreewise inclusions. -/
@[simp]
theorem directSum_piece (G : ∀ i, InternalGrading R (M i)) (p : ℤ) :
    (directSum G).piece p = directSumPiece G p :=
  by rw [directSum]

/-- The inclusion of a degree-`p` element from one summand belongs to the degree-`p` piece of the
direct-sum grading. -/
theorem directSum_lof_mem_piece (G : ∀ i, InternalGrading R (M i)) (p : ℤ) (i : ι)
    (x : (G i).piece p) [DecidableEq ι] :
    DirectSum.lof R ι M i x ∈ (directSum G).piece p := by
  refine ⟨DirectSum.lof R ι (fun i ↦ (G i).piece p) i x, ?_⟩
  simpa only [directSum_piece] using directSumPieceInclusion_lof G p i x

end InternalGrading

end TauCeti
