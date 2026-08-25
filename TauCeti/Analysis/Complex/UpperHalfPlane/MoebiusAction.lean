/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The Möbius-action conjugation at a positive determinant

Mathlib's `UpperHalfPlane.σ` sends a matrix `g : GL(2, ℝ)` to the automorphism of `ℂ` which is
the identity when `det g` is positive and complex conjugation otherwise. It is the twist that
makes the Möbius action of a negative-determinant matrix antiholomorphic, and it is carried
through the weight-`k` slash action of a general real matrix.

Positive determinant is the case everything in this project works in — congruence subgroups,
the semigroups `Δ₀(N)` of the Hecke theory, and the scaling matrices `diag(d, 1)` all consist
of matrices of positive determinant — so the conjugation is invariably trivial and every
computation begins by discharging it. This file names that branch, so `σ` need never be
unfolded by hand.

## Main results

* `UpperHalfPlane.σ_eq_refl_of_det_pos`: `σ g = ContinuousAlgEquiv.refl ℝ ℂ` for `0 < det g`.

## Provenance

The statement and its role follow AINTLIB's `sigma_eq_id_of_pos_det` in the `LeanModularForms`
project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), where it
discharges the `σ` branch for the Hecke slash action. The proof is written against the current
pin — `if_pos` is deprecated here in favour of `ite_eq_left`.
-/

public section

namespace UpperHalfPlane

/-- The Möbius-action conjugation `σ` is the identity on matrices of positive determinant:
that is the branch its definition picks. On the other branch `σ` is complex conjugation, which
is where the antiholomorphic behaviour of a negative-determinant Möbius transformation comes
from.

The hypothesis is stated with `Matrix.det` of the underlying matrix rather than with the
`ℝˣ`-valued `GeneralLinearGroup.det`: the two agree by
`Matrix.GeneralLinearGroup.val_det_apply`, which is `simp`, so only this form is in simp-normal
form and only this form makes the lemma usable as a conditional `simp` rule. -/
@[simp]
lemma σ_eq_refl_of_det_pos {g : GL (Fin 2) ℝ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) : σ g = ContinuousAlgEquiv.refl ℝ ℂ :=
  ite_eq_left (by rwa [Matrix.GeneralLinearGroup.val_det_apply])

end UpperHalfPlane
