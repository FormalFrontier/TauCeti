/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# The auxiliary term of the second complement of a normalised EDS

Mathlib defines the second complement of a normalised EDS as a difference,

`complEDS₂ b c d k =
  (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2)
    - preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2)
    * (if Even k then 1 else b)`,

with the two summands written out inline. This file names the subtracted one,

`complEDS₂Aux b c d m =
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * (if Even m then 1 else b)`,

so that the decomposition `complEDS₂ = (first term) - complEDS₂Aux` can be used as an identity
rather than re-expanded at each use. That decomposition is what expresses the second complement
through the invariant of an elliptic net, which is the route the Lutz–Nagell development takes to
the division polynomials.

## Main definitions

* `complEDS₂Aux`: the subtracted summand of Mathlib's `complEDS₂`.

## Main results

* `complEDS₂Aux_mul_b`: one factor of `b` turns the auxiliary term into
  `normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2`. What it redistributes is the parity
  bookkeeping; the `b ^ 4` rescaling is untouched, being the same inside `complEDS₂Aux` as inside
  `normEDS`. This is the companion of Mathlib's `complEDS₂_mul_b`, and it is why the definition is
  stated with `preNormEDS` rather than `normEDS`.
* `complEDS₂Aux_two`: the auxiliary term vanishes at `2`, since `preNormEDS _ _ _ 0`
  does.
* `map_complEDS₂Aux`: it is natural in the coefficient ring.

## Implementation notes

The parity factor `if Even m then 1 else b` and the `b ^ 4` inside `preNormEDS` are the same
bookkeeping Mathlib uses for `normEDS` and `complEDS₂`; keeping them here, rather than defining the
auxiliary term through `normEDS`, is what makes `complEDS₂Aux_mul_b` a single `split_ifs <;> ring`
and keeps the definition literally a summand of Mathlib's.

The `b ^ 4` never goes away. `normEDS b c d n` is by definition
`preNormEDS (b ^ 4) c d n * (if Even n then b else 1)`, so the rescaling on the right of
`complEDS₂Aux_mul_b` is the identical one written out explicitly on the left. Only the parity
factors move.

## Provenance

Ported from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declarations `compl₂EDSAux`, `compl₂EDSAux_two`, `compl₂EDSAux_mul_b` and `map_compl₂EDSAux`. That
file's header reads `Authors: David Kurniadi Angdinata`; following this repository's convention for
adapted material the upstream authorship is credited here rather than in the copyright header. J.
Xu is acknowledged for the surrounding LutzNagell development — he authors `Universal.lean` and
co-authors `DivisionPolynomialOmega.lean` at the same revision — as context for this port, not as
an author of the declarations above.

The same declarations sit in **Mathlib PR #13057** (open, last updated 2024-07-31), the upstreaming
of that AINTLIB file, so they are portable under this project's rule and deduplicate when it lands.
They are spelt `complEDS₂Aux` here rather than `compl₂EDSAux`, following Mathlib's subsequent
rename of this API (`compl₂EDS → complEDS₂`, and likewise `addMulSub → IsEllipticNet.atom`,
`net → IsEllipticNet.rel`, `rel₄ → IsEllipticNet.atomRel`,
`IsEllSequence → IsEllipticSequence`), which #13057 predates. They live in the **root** namespace,
where Mathlib keeps `complEDS₂`, `normEDS` and `preNormEDS` — the `IsEllipticNet` namespace upstream
holds the elliptic-net material (`atom`, `atomRel`, `rel`) and closes well before these.
-/

public section

variable {R S : Type*} [CommRing R] [CommRing S] (b c d : R) (m : ℤ)

/-- The subtracted summand of Mathlib's `complEDS₂`, named so that the decomposition of the second
complement into its two terms is available as an identity. -/
def complEDS₂Aux : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b

/-- The defining formula for `complEDS₂Aux`. The definition body is not exposed, so this equation
lemma is how a consumer computes with it. It is deliberately **not** `@[simp]`: tagging it would
have `simp` unfold `complEDS₂Aux` everywhere and defeat the point of naming the term. Rewrite with
`complEDS₂_eq_sub_complEDS₂Aux` instead when the decomposition is what is wanted. -/
theorem complEDS₂Aux_def : complEDS₂Aux b c d m =
    preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 *
      if Even m then 1 else b := (rfl)

/-- The auxiliary term vanishes at `2`: its first factor is `preNormEDS _ _ _ 0`. -/
@[simp]
theorem complEDS₂Aux_two : complEDS₂Aux b c d 2 = 0 := by simp [complEDS₂Aux_def]

/-- **The decomposition `complEDS₂` was named for.** Mathlib writes the second complement as a
difference with both summands inline; this states it with the subtracted one abstracted, so that
consumers can rewrite rather than re-expand. -/
theorem complEDS₂_eq_sub_complEDS₂Aux :
    complEDS₂ b c d m =
      preNormEDS (b ^ 4) c d (m - 1) ^ 2 * preNormEDS (b ^ 4) c d (m + 2) *
        (if Even m then 1 else b) - complEDS₂Aux b c d m := by
  simp only [complEDS₂, complEDS₂Aux_def]
  ring

/-- **Multiplying the auxiliary term by `b` returns it to the normalised sequence.** The single `b`
converts the auxiliary term's own parity factor into the two that `normEDS` carries at `m - 2` and
`m + 1`: each side contributes `b` for even `m` and `b ^ 2` for odd `m`. The `b ^ 4` rescaling of
`preNormEDS` is not affected, since `normEDS` is defined with the identical one. Companion of
Mathlib's `complEDS₂_mul_b`. -/
theorem complEDS₂Aux_mul_b :
    complEDS₂Aux b c d m * b = normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2 := by
  simp_rw [complEDS₂Aux, normEDS, Int.even_add, Int.even_sub, Int.not_even_one, even_two,
    iff_false, iff_true]
  split_ifs <;> ring

variable {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)

/-- The auxiliary term is natural in the coefficient ring. -/
@[simp]
theorem map_complEDS₂Aux :
    f (complEDS₂Aux b c d m) = complEDS₂Aux (f b) (f c) (f d) m := by
  simp [complEDS₂Aux_def, apply_ite f, map_preNormEDS]

