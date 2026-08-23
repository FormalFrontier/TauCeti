/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

public section

/-!
# The homogeneous characteristic form of a `2 × 2` matrix

Mathlib's `Matrix.charpoly_fin_two` records the characteristic polynomial of a `2 × 2` matrix as
`X ^ 2 - C M.trace * X + C M.det`. This file records the *homogeneous* two-variable form of the
same fact, evaluated directly as a determinant rather than through `Polynomial`:

`(r • M - s • 1).det = M.det * r ^ 2 - M.trace * (r * s) + s ^ 2`.

The two are close. Applying `charpoly_fin_two` to `r • M`, evaluating at `s` with
`Matrix.eval_charpoly`, and simplifying the resulting `Matrix.trace_smul` and `Matrix.det_smul`
does prove the identity below — in about twice the lines, and only over a `[Nontrivial R]`, which
`charpoly_fin_two` requires and the statement here does not. What this file adds is therefore the
*name* and the `Polynomial`-free form: an equation between two ring elements over any `CommRing`,
which is the shape a caller with matrix data in hand wants to rewrite with.

Read as a binary quadratic form in `(r, s)`, the right-hand side has leading coefficient `M.det`,
middle coefficient `-M.trace` and constant coefficient `1`, so its discriminant is
`M.trace ^ 2 - 4 * M.det` — which is Mathlib's `Matrix.discr` by `Matrix.discr_fin_two`.

## Main results

* `TauCeti.Matrix.det_smul_sub_smul_one_fin_two`: the identity displayed above.
* `TauCeti.Matrix.det_smul_sub_smul_one_of_card_eq_two`: the same for a square matrix on any
  index type of cardinality two, matching the relationship Mathlib's
  `Matrix.charpoly_of_card_eq_two` bears to `Matrix.charpoly_fin_two`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/WeilPairing/MatrixDet.lean`, declaration `det_smul_sub_smul_one_fin_two`.

The file's two other declarations are deliberately not ported: `det_smul_sub_smul_one_fin_two_of`
rewrites the identity under hypotheses `M.det = q` and `M.trace = t`, and `det_one_sub_fin_two` is
the `r = s = -1` instance. Both are one-line consequences better written at their call sites than
carried as API.
-/

open Matrix

namespace TauCeti.Matrix

/-- The determinant of the pencil `r • M - s • 1` of a `2 × 2` matrix, as a binary quadratic form
in `(r, s)` whose coefficients are the determinant and the trace of `M`.

This is the homogeneous form of `Matrix.charpoly_fin_two`, from which it can also be derived by
applying that lemma to the matrix `r • M` and evaluating the resulting polynomial at the scalar
`s`; stated directly it needs no `[Nontrivial R]` hypothesis and no `Polynomial`. -/
theorem det_smul_sub_smul_one_fin_two {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (r s : R) :
    (r • M - s • (1 : Matrix (Fin 2) (Fin 2) R)).det
      = M.det * r ^ 2 - M.trace * (r * s) + s ^ 2 := by
  have hlit : r • M - s • (1 : Matrix (Fin 2) (Fin 2) R)
      = !![r * M 0 0 - s, r * M 0 1; r * M 1 0, r * M 1 1 - s] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hlit, det_fin_two_of, det_fin_two M, trace_fin_two M]
  ring

/-- The pencil determinant of a square matrix on any index type of cardinality two, as a binary
quadratic form in `(r, s)` with coefficients the determinant and trace of `M`.

This is `det_smul_sub_smul_one_fin_two` transported along an equivalence `n ≃ Fin 2`, in the same
relationship that Mathlib's `Matrix.charpoly_of_card_eq_two` bears to `Matrix.charpoly_fin_two`. -/
theorem det_smul_sub_smul_one_of_card_eq_two {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] (M : Matrix n n R) (hn : Fintype.card n = 2) (r s : R) :
    (r • M - s • (1 : Matrix n n R)).det = M.det * r ^ 2 - M.trace * (r * s) + s ^ 2 := by
  let e : n ≃ Fin 2 := Fintype.equivFinOfCardEq hn
  have hsub : (r • M - s • (1 : Matrix n n R)).submatrix e.symm e.symm
      = r • M.submatrix e.symm e.symm - s • (1 : Matrix (Fin 2) (Fin 2) R) := by
    simp [Matrix.submatrix_sub, Matrix.submatrix_smul]
  -- `trace` is transported by hand: Mathlib has `det_submatrix_equiv_self` but no trace analogue.
  have htr : (M.submatrix e.symm e.symm).trace = M.trace :=
    Equiv.sum_comp e.symm fun j => M j j
  rw [← det_submatrix_equiv_self e.symm, hsub, det_smul_sub_smul_one_fin_two,
    det_submatrix_equiv_self e.symm, htr]

end TauCeti.Matrix
