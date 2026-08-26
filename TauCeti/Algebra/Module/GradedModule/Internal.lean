/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Internally graded modules

This file packages a `ℤ`-graded module as a total module together with an internal direct-sum
decomposition. The total-module presentation is convenient for DG and `A∞` operations, while
`DirectSum.IsInternal` ensures that every element is a finite, uniquely determined sum of
homogeneous elements.

Mathlib already provides the direct-sum equivalence and its induction principle through
`DirectSum.Decomposition`.  An `InternalGrading` retains the family of homogeneous submodules and
the proof that it is internal; the instance below makes Mathlib's decomposition API available
without duplicating it.

## Main definitions

* `InternalGrading`: an internal `ℤ`-grading of a module.

## Main results

* `TauCeti.InternalGrading.ext`: internal gradings are determined by their homogeneous pieces.

This is the first graded-module target in Layer 0 of the `DGAInfinity` roadmap.  Later files use
Mathlib's decomposition API to define maps of nonzero degree, shifts, tensor-product gradings, and
signed multilinear operations.
-/

public section

open scoped DirectSum

namespace TauCeti

universe u v

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/-- An internal integer grading of an `R`-module `M`.

The `isInternal` field says that the canonical map from the external direct sum of the `piece p`
to `M` is bijective.  Thus elements of `M` have unique finite homogeneous decompositions. -/
structure InternalGrading where
  /-- The submodule of elements of degree `p`. -/
  piece : ℤ → Submodule R M
  /-- The homogeneous pieces form an internal direct sum. -/
  isInternal : DirectSum.IsInternal piece

namespace InternalGrading

variable {R M}

/-- Two internal gradings of the same module are equal as soon as their homogeneous pieces
agree. -/
@[ext]
theorem ext : ∀ {G H : InternalGrading R M}, (∀ p, G.piece p = H.piece p) → G = H
  | ⟨_, _⟩, ⟨_, _⟩, h => by
    obtain rfl := funext h
    rfl

/-- The decomposition attached to an internal grading. -/
noncomputable instance (G : InternalGrading R M) : DirectSum.Decomposition G.piece :=
  G.isInternal.chooseDecomposition

end InternalGrading

section ParityTwist

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- The parity operator of twist `q`: on the homogeneous piece of degree `e` it acts as the scalar
`(-1)^(q * e)`.

Downstream modules express their Koszul signs through this operator: the sign acquired by moving
an operation of degree `q` past homogeneous inputs of total degree `D` is the scalar by which
`parityTwist G q` scales those inputs. -/
noncomputable def InternalGrading.parityTwist (G : InternalGrading R M) (q : ℤ) : M →ₗ[R] M :=
  DirectSum.coeLinearMap (fun e => G.piece e) ∘ₗ
    DirectSum.toModule R ℤ (⨁ e : ℤ, G.piece e)
      (fun e => (((q * e).negOnePow : ℤ) : R) •
        DirectSum.lof R ℤ (fun e => G.piece e) e) ∘ₗ
    (DirectSum.decomposeLinearEquiv (ℳ := G.piece)).toLinearMap


end ParityTwist

section ParityTwistLemmas

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- On a homogeneous element of degree `e`, the parity operator of twist `q` acts as the scalar
`(-1)^(q * e)`. -/
theorem InternalGrading.parityTwist_apply_of_mem (G : InternalGrading R M) {x : M} {e : ℤ}
    (hx : x ∈ G.piece e) (q : ℤ) :
    parityTwist G q x = (((q * e).negOnePow : ℤ) : R) • x := by
  rw [parityTwist]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    DirectSum.decomposeLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem (ℳ := G.piece) hx,
    ← DirectSum.lof_eq_of R ℤ (fun i : ℤ => G.piece i)]
  simp [DirectSum.toModule_lof]

/-- The parity operator preserves each homogeneous piece. -/
theorem InternalGrading.parityTwist_mem_piece (G : InternalGrading R M) {x : M} {e : ℤ}
    (hx : x ∈ G.piece e) (q : ℤ) :
    parityTwist G q x ∈ G.piece e := by
  rw [InternalGrading.parityTwist_apply_of_mem G hx q]
  exact Submodule.smul_mem _ _ hx

/-- The parity operator of twist zero is the identity. -/
@[simp]
theorem InternalGrading.parityTwist_zero (G : InternalGrading R M) :
    parityTwist G 0 = LinearMap.id := by
  refine DirectSum.decompose_lhom_ext (ℳ := G.piece) fun e => ?_
  ext x
  simp only [LinearMap.comp_apply]
  have h := InternalGrading.parityTwist_apply_of_mem G (Submodule.coe_mem x) 0
  simpa using h

end ParityTwistLemmas

end TauCeti
