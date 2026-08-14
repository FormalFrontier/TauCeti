/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EllipticDivisibilitySequence.ComplAux
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Invariant

/-!
# The reduced invariant of a normalised EDS

For a normalised EDS `normEDS b c d`, the invariant of `IsEllipticNet` at `s = 1` carries a factor
that is constant in the index: `IsEllipticNet.invarNum` is divisible by `b = W 2`. This file names
the quotient `reducedInvarNum` and **proves** that cancellation.

The reduced numerator is a sum rather than a quotient: `reducedInvarNum` is defined outright as

`reducedInvarNum b c d m = complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * complEDS₂Aux b c d m`,

and `invarNum_normEDS_one_eq_reducedInvarNum_mul` is what identifies it as the cancellation,
`invarNum` being `reducedInvarNum * b`. Read the other way,
`complEDS₂_eq_reducedInvarNum_sub` expresses the second complement through the invariant — the step
by which the elliptic-net identities reach the division polynomials in the Lutz–Nagell development.

## Main definitions

* `reducedInvarNum`: the invariant numerator of a normalised EDS with one factor of `b` cancelled.

## Main results

* `IsEllipticNet.invarNum_normEDS_one_eq_reducedInvarNum_mul`: `invarNum (normEDS b c d) 1 m` is
  `reducedInvarNum b c d m * b` — the cancellation the reduced numerator is named for.
* `complEDS₂_eq_reducedInvarNum_sub`: the second complement read off the reduced numerator.
* `map_reducedInvarNum`: it is natural in the coefficient ring, so a specialisation or base change
  may be pushed through it rather than around the unexposed body.

## What is deliberately not here

The **denominator** side of the reduction is absent, by measurement rather than oversight. The
source's `redInvarDenom` — a piecewise expression for `W (m + 1) * W m * W (m - 1)` with the
constant factor `W 3 * W 2` cancelled — is worth having only together with the results identifying
it as that quotient, `redInvar_normEDS` and `invarDenom_eq_redInvarDenom_mul` (the source's names).
Both route through the fact that `normEDS` is an elliptic sequence, along

`redInvar_normEDS ← invar₂_normEDS ← invar_normEDS ← net_normEDS ← IsEllipticSequence.normEDS`

for the first, and `invarDenom_eq_redInvarDenom_mul ← normEDS_mul_complEDS_div ←
normEDS_mul_complEDS ← normEDS_mul_complEDS_of_mem ← IsEllipticSequence.normEDS` for the second.
That fact is `isEllipticSequence_normEDS` in `NormEDS.lean`, proved here through the descent of
`Descent.lean`; the pinned Mathlib still records it as an open TODO
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`: "prove that `normEDS` satisfies
`IsEllipticDvdSequence`"). What the denominator side still lacks is the rest of each chain above:
`redInvar_normEDS ← invar₂_normEDS ← invar_normEDS ← net_normEDS` for the first, and
`normEDS_mul_complEDS_div ← normEDS_mul_complEDS ← normEDS_mul_complEDS_of_mem` for the second.
Carrying the bare definition across before them would add a formula that no consumer can state
anything about, so it waits for the layer that gives it meaning. Everything below is independent
of that fact: nothing carries an ellipticity hypothesis, and the source discharges the
ellipticity variables over exactly this block.

## Provenance

Ported from J. Xu's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declarations `invarNum_normEDS`, `redInvarNum`,
`compl₂EDS_eq_redInvarNum_sub` and `invarNum_eq_redInvarNum_mul` — the source's own names, which
this file respells with `reduced` written out. That file's header reads `Authors: Junyan Xu`;
following this repository's convention for adapted material the upstream authorship is credited
here rather than in the copyright header.

The same declarations sit in **Mathlib PR #13057**, the upstreaming of that AINTLIB file, so they
are portable under this project's rule and deduplicate if and when it lands.
They are spelt with Mathlib's later names (`compl₂EDS → complEDS₂`, `IsEllSequence →
IsEllipticSequence`), which #13057 predates, and follow `ComplAux.lean` in keeping the
`normEDS`-family declarations in the **root** namespace where Mathlib keeps `normEDS`, `complEDS`
and `complEDS₂`. Placement follows each left-hand side, so `reducedInvarNum`,
`reducedInvarNum_def`, `complEDS₂_eq_reducedInvarNum_sub` and `map_reducedInvarNum` all sit at
root, and only `invarNum_normEDS_one_eq_reducedInvarNum_mul`, whose left-hand side is an
`IsEllipticNet` term, sits in that namespace.

One adaptation is forced rather than chosen: the source proves `invarNum_normEDS` by
`simp [invarNum]`, unfolding the definition. That does not port, because `Invariant.lean` exports
`invarNum`'s body unexposed — from an importing module `simp [invarNum]` is rejected outright — so
the proof goes through the `@[simp]` equation lemma `IsEllipticNet.invarNum_def` instead.
-/

public section

variable {R S : Type*} [CommRing R] [CommRing S] (b c d : R) (m : ℤ)

/-- The invariant numerator of a normalised EDS with one factor of `b` cancelled. Stated as the sum
it reduces to rather than as a quotient;
`IsEllipticNet.invarNum_normEDS_one_eq_reducedInvarNum_mul` is what
identifies it as the cancellation. -/
def reducedInvarNum : R :=
  complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * complEDS₂Aux b c d m

/-- The defining formula for `reducedInvarNum`. The definition body is not exposed, so this equation
lemma is how a consumer computes with it. It is deliberately **not** `@[simp]`, for the reason
`complEDS₂Aux_def` is not: tagging it would have `simp` unfold `reducedInvarNum` everywhere and
defeat the point of naming the term. -/
theorem reducedInvarNum_def : reducedInvarNum b c d m =
    complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * complEDS₂Aux b c d m := (rfl)

/-- **The second complement read off the reduced numerator.** This is the direction the Lutz–Nagell
development uses: it expresses `complEDS₂` through the invariant of the elliptic net, rather than
through its own defining difference. -/
theorem complEDS₂_eq_reducedInvarNum_sub :
    complEDS₂ b c d m =
      reducedInvarNum b c d m - normEDS b c d m ^ 3 * b - 2 * complEDS₂Aux b c d m := by
  rw [reducedInvarNum_def]; ring

namespace IsEllipticNet

/-- **The cancellation `reducedInvarNum` is named for**: the invariant numerator of a normalised EDS
at `s = 1` is `reducedInvarNum` times `b`. The factor of `b` is constant in `m`, which is what makes
the reduced form the one the division-polynomial identities are stated over.

The **priority is load-bearing**, not decoration. `invarNum_def` is itself `@[simp]`, and at equal
priority it wins on this term: with a plain `@[simp]` here, `simp` still rewrites
`invarNum (normEDS b c d) 1 m` to the fully expanded formula and this lemma never fires. At `high`
it fires first, and because `reducedInvarNum_def` is deliberately *not* `@[simp]` the result then
stays folded at `reducedInvarNum b c d m * b`, which is the normal form this file exists to name. -/
@[simp high]
theorem invarNum_normEDS_one_eq_reducedInvarNum_mul :
    invarNum (normEDS b c d) 1 m = reducedInvarNum b c d m * b := by
  simp_rw [reducedInvarNum_def, right_distrib, complEDS₂_mul_b, mul_assoc 2 _ b,
    complEDS₂Aux_mul_b]
  simp [invarNum_def]
  ring

end IsEllipticNet

variable {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)

/-- The reduced numerator is natural in the coefficient ring. -/
@[simp]
theorem map_reducedInvarNum :
    f (reducedInvarNum b c d m) = reducedInvarNum (f b) (f c) (f d) m := by
  simp [reducedInvarNum_def, map_ofNat]
