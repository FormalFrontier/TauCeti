/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.ExteriorPower

import Mathlib.LinearAlgebra.Matrix.Kronecker

public section

/-!
# Block-diagonal actions of general linear Lie algebras

The block-diagonal map sends a matrix `A : Matrix ι ι R` to the matrix with one copy of `A` for
each element of an auxiliary finite type `κ`. Restricting the standard `gl (ι × κ)` action along
this map gives a `gl ι` action on every exterior power of `ι × κ → R`.

## Main definitions

* `TauCeti.glBlockDiagonal`: the block-diagonal map from `gl ι` to `gl (ι × κ)`.
* `TauCeti.glBlockDiagonalLieRingModule` and `TauCeti.glBlockDiagonalLieModule`: the induced
  action on exterior powers of the standard module.
-/

namespace TauCeti

open Matrix Module exteriorPower

open scoped Kronecker

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]
variable (ι : Type*) [DecidableEq ι] [Fintype ι]
variable (κ : Type*) [DecidableEq κ] [Fintype κ]

/-- The **block-diagonal map** from `gl ι` to `gl (ι × κ)`, sending a matrix `A` to the block
diagonal matrix with `κ` copies of `A` down the diagonal. On the standard module `ι × κ → R` this
is the action of `gl ι` on the first coordinate alone. -/
def glBlockDiagonal : Matrix ι ι R →ₗ⁅R⁆ Matrix (ι × κ) (ι × κ) R :=
  (AlgHom.mk'
    ((blockDiagonalRingHom ι κ R).comp (Pi.constRingHom κ (Matrix ι ι R)))
    (by
      intro c A
      exact blockDiagonal_smul c (fun _ : κ => A))).toLieHom

@[simp]
theorem glBlockDiagonal_apply (A : Matrix ι ι R) :
    glBlockDiagonal R ι κ A = blockDiagonal fun _ : κ => A :=
  (rfl)

variable {R ι κ}

/-- The block-diagonal map takes a matrix unit of `gl ι` to the sum, over the auxiliary coordinate,
of the matrix units of `gl (ι × κ)` that move a cell from row `t` to row `s` and leave its column
alone. -/
theorem glBlockDiagonal_single (s t : ι) :
    glBlockDiagonal R ι κ (single s t 1) = ∑ c : κ, single (s, c) (t, c) (1 : R) := by
  rw [glBlockDiagonal_apply]
  calc (blockDiagonal fun _ : κ => single s t (1 : R))
      = single s t (1 : R) ⊗ₖ (1 : Matrix κ κ R) := (kronecker_one _).symm
    _ = single s t (1 : R) ⊗ₖ ∑ c : κ, single c c (1 : R) := by rw [sum_single_one]
    _ = ∑ c : κ, single s t (1 : R) ⊗ₖ single c c (1 : R) :=
        map_sum (kroneckerBilinear (R := R) (single s t (1 : R))) _ _
    _ = ∑ c : κ, single (s, c) (t, c) (1 : R) := by
        simp [single_kronecker_single]

variable (R ι κ) in
/-- The bracket of `gl ι` on an exterior power of `ι × κ → R`, pulled back along the block-diagonal
map from the standard `gl (ι × κ)`-action. -/
noncomputable scoped instance glBlockDiagonalLieRingModule (N : ℕ) :
    LieRingModule (Matrix ι ι R) (⋀[R]^N (ι × κ → R)) :=
  LieRingModule.compLieHom _ (glBlockDiagonal R ι κ)

variable (R ι κ) in
/-- The compatibility of that bracket with the `R`-module structures, making an exterior power of
`ι × κ → R` a `gl ι`-module over `R`. -/
noncomputable scoped instance glBlockDiagonalLieModule (N : ℕ) :
    LieModule R (Matrix ι ι R) (⋀[R]^N (ι × κ → R)) :=
  LieModule.compLieHom _ (glBlockDiagonal R ι κ)

/-- The `gl ι`-action on an exterior power of `ι × κ → R` is the `gl (ι × κ)`-action of the
block-diagonal image. -/
theorem gl_lie_blockDiagonal_def {N : ℕ} (A : Matrix ι ι R) (x : ⋀[R]^N (ι × κ → R)) :
    ⁅A, x⁆ = ⁅glBlockDiagonal R ι κ A, x⁆ :=
  LieRingModule.compLieHom_apply _ _ _ _

/-- A matrix unit of `gl ι` acts on an exterior power of `ι × κ → R` as the sum, over the auxiliary
coordinate, of the matrix units of `gl (ι × κ)` it is built from. -/
theorem gl_lie_single {N : ℕ} (s t : ι) (x : ⋀[R]^N (ι × κ → R)) :
    ⁅(single s t 1 : Matrix ι ι R), x⁆
      = ∑ c : κ, ⁅(single (s, c) (t, c) 1 : Matrix (ι × κ) (ι × κ) R), x⁆ := by
  rw [gl_lie_blockDiagonal_def, glBlockDiagonal_single, sum_lie]

end TauCeti
