/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# A `2 × 2` matrix scales the standard symplectic form by its determinant

For `J = !![0, 1; -1, 0]` the standard alternating form on a rank-two module, every `2 × 2` matrix
`φ` satisfies

`φᵀ * J * φ = φ.det • J`,

and consequently a `φ` whose symplectic adjoint composes with it to a scalar has that scalar as its
determinant.

Mathlib's `Matrix.J` is not the right vehicle for this. It is defined on `l ⊕ l` for arbitrary `l`
and characterises the symplectic *group* (`Matrix.mem_iff' : A ∈ symplecticGroup l R ↔ Aᵀ * J * A =
J`), whereas the identity here holds for an **arbitrary** matrix with `det φ` on the right — a
statement about the top exterior power, hence specific to rank two. It is false for larger `l`.

## Main results

* `TauCeti.Matrix.transpose_mul_symplectic_mul_eq_det_smul`: `φᵀ * J * φ = φ.det • J`.
* `TauCeti.Matrix.det_eq_of_symplectic_adjoint_of_mul_eq_smul_one`: if `φᵀ * J = J * ψ` and
  `ψ * φ = d • 1`, then `φ.det = d`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/WeilPairing/PairingDet.lean`, declarations `symJ`, `transpose_mul_symJ_mul` and
`det_eq_of_symplectic_adjoint`. The source's `symJ` definition is not ported — the matrix is
written literally, so no new name competes with Mathlib's `Matrix.J`.

In the pinned Hasse development these are the linear-algebra core of Silverman III.8.6
(`det φ_ℓ = deg φ`): on `E[ℓ] ≅ 𝔽_ℓ²` the Weil pairing is the standard symplectic form, its adjoint
property reads `φᵀ J = J φ̂`, and the dual relation is `φ̂ φ = (deg φ) • 1`. **No elliptic-curve
content appears here** — this file is matrices over a commutative ring.
-/

public section

open Matrix

namespace TauCeti.Matrix

variable {R : Type*} [CommRing R]

/-- A `2 × 2` matrix scales the standard symplectic form `!![0, 1; -1, 0]` by its determinant. -/
@[simp]
theorem transpose_mul_symplectic_mul_eq_det_smul (φ : Matrix (Fin 2) (Fin 2) R) :
    φᵀ * !![0, 1; -1, 0] * φ = φ.det • !![0, 1; -1, 0] := by
  -- This is the rank-two case of the determinant transformation law
  -- (`TauCeti.Matrix.detRowAlternating_mulVec`): both entries are the determinant form evaluated
  -- on the `i`-th and `j`-th columns of `φ`. Deriving it from that lemma is not shorter, because
  -- `detRowAlternating` is an `alternatization` that `simp` does not put into coordinates, so the
  -- four entries have to be computed either way.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, det_fin_two, transpose_apply] <;> ring

/-- If `ψ` is the symplectic adjoint of `φ`, in the sense `φᵀ * J = J * ψ`, and `ψ * φ` is the
scalar `d`, then `d` is the determinant of `φ`.

This is the matrix form of the argument that a pairing-adjoint together with a dual relation pins
the determinant: `φᵀ J φ = J ψ φ = d • J`, and comparing with
`transpose_mul_symplectic_mul_eq_det_smul` gives `det φ = d` by reading off one entry. -/
theorem det_eq_of_symplectic_adjoint_of_mul_eq_smul_one {φ ψ : Matrix (Fin 2) (Fin 2) R} {d : R}
    (hadj : φᵀ * !![0, 1; -1, 0] = !![0, 1; -1, 0] * ψ)
    (hdual : ψ * φ = d • (1 : Matrix (Fin 2) (Fin 2) R)) : φ.det = d := by
  have hkey : φ.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R)
      = d • !![0, 1; -1, 0] := by
    rw [← transpose_mul_symplectic_mul_eq_det_smul φ, hadj, Matrix.mul_assoc, hdual]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  have := congrArg (fun M => M 0 1) hkey
  simpa using this

end TauCeti.Matrix
