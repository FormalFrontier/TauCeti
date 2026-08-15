/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The universal normalised elliptic divisibility sequence

A normalised EDS over a commutative ring `R` is determined by three parameters `b, c, d : R`.
Taking those parameters to be three indeterminates gives the **universal** `normEDS` family

`universalNormEDS : ℤ → MvPolynomial NormEDSParam ℤ`,

of which every sequence **of the form** `normEDS b c d` is a specialization: it is
`universalNormEDS` followed by the evaluation sending the indeterminates to `b, c, d`
(`normEDS_eq_aeval`), and likewise for
`preNormEDS` and for the two complement sequences (`preNormEDS_eq_aeval`, `complEDS₂_eq_aeval`,
`complEDS_eq_aeval`).

Note the claim is about the *constructed function* `normEDS`, not about elliptic divisibility
sequences in the abstract: the pinned Mathlib does not know that `normEDS b c d` satisfies
`IsEllipticDvdSequence` — it records proving so as a TODO — so nothing here says every EDS arises
this way, only that every `normEDS b c d` does.

The point is that an identity between the terms of a sequence of the form `normEDS b c d` need
only be proved once, over `MvPolynomial NormEDSParam ℤ`, and then specialises to every ring and
every choice of parameters. Working universally also buys an integral domain to work in, which the
parameters' ring need not be.

## Main definitions

* `NormEDSParam`: a three-element index type for the parameters `b`, `c`, `d` of `normEDS`.
* `universalNormEDS`: `normEDS` over `ℤ[B, C, D]`, at the three indeterminates.

## Main results

* `normEDS_eq_aeval`: every sequence of the form `normEDS b c d` is `universalNormEDS` specialised
  along `NormEDSParam.rec b c d`.
* `preNormEDS_eq_aeval`, `complEDS₂_eq_aeval`, `complEDS_eq_aeval`: the same for the three companion
  sequences, each specialising **its own** construction over `ℤ[B, C, D]` — `preNormEDS`,
  `complEDS₂` and `complEDS` at the three indeterminates — not `universalNormEDS`, which is only
  the `normEDS` one.

## Implementation notes

The constructors of `NormEDSParam` are uppercase because they name indeterminates rather than
elements, matching `WeierstrassCurve.Coeff` in
`TauCeti/AlgebraicGeometry/EllipticCurve/Universal.lean`, which plays the same role for the
universal Weierstrass curve.

Only `normEDS` gets a named universal object. The three companion sequences are stated against
`preNormEDS (X B) (X C) (X D)` and its analogues written out, since naming each one would add three
definitions whose only use is to be unfolded — the sequences are already determined by the
parameters, and it is the specialization statement that consumers need, not a new name for its
left-hand side. Those three carry an explicit `X (R := ℤ)`: with the coefficient ring appearing
only under `aeval`, elaboration has nothing to pin it to and reports a stuck `CommSemiring`
instance otherwise.

## Provenance

Ported from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declarations `Param`, `universalNormEDS`, `normEDS_eq_aeval`, `compl₂EDS_eq_aeval` and
`complEDS_eq_aeval`. **`Param` is spelt `NormEDSParam` here** — a root-level `Param` says nothing
about elliptic divisibility sequences and makes its namespace equally generic; that rename is an
adaptation made in this repository, not upstream's name. That file's header reads `Authors: David
Kurniadi Angdinata`; following this repository's convention for adapted material the upstream
authorship is credited here rather than in the copyright header. J. Xu is acknowledged for the
surrounding LutzNagell development — he authors `Universal.lean` and co-authors
`DivisionPolynomialOmega.lean` at the same revision — as context for this port, not as an author of
the declarations above.

The same declarations sit in **Mathlib PR #13057** (open, last updated 2024-07-31), the
upstreaming of that AINTLIB file, so they are portable under this project's rule and deduplicate
when it lands. `compl₂EDS` is spelt `complEDS₂` here, following Mathlib's subsequent rename of the
elliptic-net API (`addMulSub → IsEllipticNet.atom`, `net → IsEllipticNet.rel`,
`rel₄ → IsEllipticNet.atomRel`, `IsEllSequence → IsEllipticSequence`, `compl₂EDS → complEDS₂`),
which #13057 predates.

`preNormEDS_eq_aeval` is new: the source states the principle for `normEDS` and the two
complements but not for `preNormEDS`, although Mathlib's `map_preNormEDS` makes it the same
one-line proof and consumers reaching for the pre-normalised sequence would otherwise have to
redo it.

Deliberately **not** ported here: `universalNormEDS_ne_zero` and
`universalNormEDS_mem_nonZeroDivisors`. They rest on `normEDS 2 3 2 = id`, the source's
`normEDS_two_three_two`, which needs two things: `normEDS` known to be an elliptic sequence,
which is now `isEllipticSequence_normEDS` in `NormEDS.lean`, and an extensionality principle for
elliptic sequences — the source's `IsEllSequence.ext`, that two elliptic sequences agreeing at
the indices which determine them are equal — which this repository does not have. They belong
with whichever slice ports that principle.
-/

public section

open MvPolynomial

/-- A three-element index type for the parameters `b`, `c`, `d` of a normalised elliptic
divisibility sequence. It indexes the variables of `MvPolynomial NormEDSParam ℤ = ℤ[B, C, D]`,
the ring the universal normalised EDS is defined over; the constructors are uppercase as names
of indeterminates. -/
inductive NormEDSParam : Type | B : NormEDSParam | C : NormEDSParam | D : NormEDSParam

namespace NormEDSParam

open NormEDSParam

variable {R : Type*} [CommRing R] (b c d : R)

/-- **The universal `normEDS`**: `normEDS` over `ℤ[B, C, D]`, at the three indeterminates. Every
sequence of the form `normEDS b c d` is one of its specializations (`normEDS_eq_aeval`), so an
identity between such terms can be proved here once and read off for every ring and every choice of
parameters. -/
noncomputable def universalNormEDS : ℤ → MvPolynomial NormEDSParam ℤ := normEDS (X B) (X C) (X D)

/-- The `simp` expansion of `universalNormEDS`: `normEDS` at the three indeterminates. It is the
stable name for that expansion, so downstream proofs rewrite with a lemma rather than unfolding a
definition; it does not hide the representation, and its right-hand side is that representation. -/
@[simp]
theorem universalNormEDS_apply (n : ℤ) :
    universalNormEDS n = normEDS (X NormEDSParam.B) (X NormEDSParam.C) (X NormEDSParam.D) n := (rfl)

/-- **Every sequence of the form `normEDS b c d` is a specialization of the universal one.** -/
theorem normEDS_eq_aeval :
    normEDS b c d = fun n ↦ aeval (NormEDSParam.rec b c d) (universalNormEDS n) := by
  simp_rw [universalNormEDS, map_normEDS, aeval_X]

/-- The pre-normalised sequence of a normalised EDS is likewise a specialization. -/
theorem preNormEDS_eq_aeval :
    preNormEDS b c d =
      fun n ↦ aeval (NormEDSParam.rec b c d) (preNormEDS (X (R := ℤ) B) (X C) (X D) n) := by
  simp_rw [map_preNormEDS, aeval_X]

/-- The second complement sequence of a normalised EDS is likewise a specialization. -/
theorem complEDS₂_eq_aeval :
    complEDS₂ b c d =
      fun n ↦ aeval (NormEDSParam.rec b c d) (complEDS₂ (X (R := ℤ) B) (X C) (X D) n) := by
  simp_rw [map_complEDS₂, aeval_X]

/-- The complement sequence of a normalised EDS is likewise a specialization, in both arguments. -/
theorem complEDS_eq_aeval :
    complEDS b c d =
      fun k n ↦ aeval (NormEDSParam.rec b c d) (complEDS (X (R := ℤ) B) (X C) (X D) k n) := by
  simp_rw [map_complEDS, aeval_X]

end NormEDSParam
