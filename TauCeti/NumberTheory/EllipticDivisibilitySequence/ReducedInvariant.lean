/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.EllipticDivisibilitySequence.ComplAux
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Complement
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Invariant.NormEDS
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Six

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
* `reducedInvarDenom`: the invariant denominator with the factor `b * c` cancelled — a six-way
  split on `m % 6`, since which of `W (m+1)`, `W m`, `W (m-1)` gives up `b = W 2` and `c = W 3`
  depends on the residue.

## Main results

* `IsEllipticNet.invarNum_normEDS_one_eq_reducedInvarNum_mul`: `invarNum (normEDS b c d) 1 m` is
  `reducedInvarNum b c d m * b` — the cancellation the reduced numerator is named for.
* `complEDS₂_eq_reducedInvarNum_sub`: the second complement read off the reduced numerator.
* `map_reducedInvarNum` and `map_reducedInvarDenom`: both are natural in the coefficient ring, so
  a specialisation or base change may be pushed through them rather than around the unexposed
  bodies.
* `IsEllipticNet.invarDenom_normEDS_one_eq_reducedInvarDenom_mul`: `invarDenom (normEDS b c d) 1 m`
  is `reducedInvarDenom b c d m * (b * c)` — the cancellation the reduced denominator is named
  for, with no hypotheses.
* `reducedInvarDenom_of_emod_six_eq_zero` and its five siblings: the per-residue elimination
  principle, one lemma per branch, so a consumer holding `m % 6 = r` reaches its branch without
  discharging the preceding `if` conditions.
* `reducedInvarDenom_zero`, `reducedInvarDenom_one`, `reducedInvarDenom_two`: its values at the
  small indices; the last is what fixes the normalisation.
* `reducedInvarNum_eq_reducedInvarDenom_mul`: the reduced invariant identity,
  `reducedInvarNum b c d m = reducedInvarDenom b c d m * (d + b ^ 4)`, with no hypothesis on
  `b`, `c`, `d`.

## Both cancellations, and why neither needs a hypothesis

Each reduced quantity comes with the cancellation it is named for:
`invarNum_normEDS_one_eq_reducedInvarNum_mul` for the numerator, and
`invarDenom_normEDS_one_eq_reducedInvarDenom_mul` for the denominator. Both hold over an arbitrary
commutative ring.

The denominator side reads `invarDenom (normEDS b c d) 1 m = W (m + 1) * W m * W (m - 1)`, and
which of the three factors gives up `b = W 2` and `c = W 3` depends on `m` modulo `6` — hence the
six-way split. Each branch reindexes one or two complements by `normEDS_mul_complEDS_div`
(`Complement.lean`), `W k * complEDS b c d k (n / k) = W n`, which this development adds beside the
identity it is derived from — `normEDS_mul_complEDS`, stated at `W (n * k)` — and which absorbs the
`Int.ediv_mul_cancel` step on the divisibility that `m % 6 = r` supplies. The residues `0`, `1` and
`5` go through the `6`-complement once each and rewrite `W 6` as `(W 5 - d ^ 2) * b * c`
(`WeierstrassCurve.normEDS_six`, `Six.lean`); the residues `2`, `3` and `4` each split the work
between a `2`-complement and a `3`-complement.

Note that `b, c ≠ 0` over a domain would **not** by itself make `normEDS b c d 6` a
nonzerodivisor — that needs `normEDS b c d 5 - d ^ 2 ≠ 0` as well — which is why the
unconditional `normEDS_mul_complEDS` rather than a nonvanishing side condition is what makes this
statement hypothesis-free.

The numerator needs none of this because its cancellation is an identity between polynomial
expressions, proved by `ring` from the complement recurrences rather than through a division.

The other half of the reduced-invariant theory — `redInvar_normEDS ← invar₂_normEDS ←
invar_normEDS ← net_normEDS`, written in the source's names — is complete: `net_normEDS` is
`isEllipticNet_normEDS` (`NormEDS.lean`), `invar_normEDS` is `invarNum_mul_invarDenom`
(`Invariant/Basic.lean`), `invar₂_normEDS` is `invarNum_normEDS_one_mul_eq_invarDenom_mul`
(`Invariant/NormEDS.lean`), and `redInvar_normEDS` is
`reducedInvarNum_eq_reducedInvarDenom_mul` below.

Everything below **except the final identity** is independent of all of that: no other
declaration carries an ellipticity hypothesis, and the source discharges the ellipticity
variables over exactly this block. `reducedInvarNum_eq_reducedInvarDenom_mul` is the exception —
its proof consumes the two cancellations of this file together with
`invarNum_normEDS_one_mul_eq_invarDenom_mul` from the chain above.

## Provenance

Ported from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in the AINTLIB
**NagellLutz** project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), at the revision
`TauCetiRoadmap` pins for that project, `dev/modular-curves @ 9fec8eba7652`. The reduced
invariant identity was ported later, read at `main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`:
`reducedInvarNum_eq_reducedInvarDenom_mul` adapts that file's `redInvar_normEDS` (`:1514`) and
its private `_of_mem` form adapts `redInvar_normEDS_of_mem_nonZeroDivisors` (`:1506`), respelt
`reducedInvar*` like the rest of this file; both are byte-identical at the two revisions, and
the earlier pin is kept for the block below so each declaration cites the revision it was read
at. Declarations
`invarNum_normEDS`, `redInvarNum`, `compl₂EDS_eq_redInvarNum_sub`,
`invarNum_eq_redInvarNum_mul` and `map_redInvarNum` for the numerator, and `redInvarDenom`,
`redInvarDenom_zero`, `redInvarDenom_one`, `redInvarDenom_two`, `map_redInvarDenom` and
`invarDenom_eq_redInvarDenom_mul` for the denominator — the source's own names, which this file
respells with `reduced` written out.

Those names also occur in AINTLIB's **HasseWeil** project, pinned separately at
`dev/hasse-weil @ 513e83879e2f`, so the credit above picks between two candidates rather than
recording the only match a search returns. Two details fix it on NagellLutz. That project spells
the cancellation `invarDenom_eq_redInvarDenom_mul`, where HasseWeil spells it
`invarDenom_normEDS_eq_redInvarDenom_mul`; and its `map_redInvarDenom` is oriented
`f (redInvarDenom …) = redInvarDenom (f b) …`, where HasseWeil states the converse. This file
carries the NagellLutz spelling and the NagellLutz orientation in both places.

Six declarations here are **not** from that file: the `reducedInvarDenom_of_emod_six_eq_*` branch
lemmas have no counterpart in the source, which eliminates the split inline. The cancellation
proof below reaches each branch through the divisor-form identity `normEDS_mul_complEDS_div`
(`Complement.lean`) directly.

The source's `invarDenom_eq_redInvarDenom_mul`, which identifies the denominator formula as the
cancelled quotient, is ported here as
`IsEllipticNet.invarDenom_normEDS_one_eq_reducedInvarDenom_mul`. Both links the source's proof
uses are available in this repository: `normEDS_mul_complEDS_div` is ported by this development
into `Complement.lean`, derived there from the unconditional `normEDS_mul_complEDS` together with
`Int.ediv_mul_cancel` rather than proved afresh, and `normEDS_six_eq_mul` is
`WeierstrassCurve.normEDS_six` (`Six.lean`).

That file's header reads `Authors: David Kurniadi Angdinata`; following this
repository's convention for adapted material the upstream authorship is credited here rather than
in the copyright header. J. Xu is acknowledged for the surrounding LutzNagell development — he
authors `Universal.lean` and co-authors `DivisionPolynomialOmega.lean` at the same revision — as
context for this port, not as an author of the declarations above.

The **numerator** declarations sit in **Mathlib PR #13057**, the upstreaming of that AINTLIB
file, so they are portable under this project's rule and deduplicate if and when it lands. That
PR does not carry the denominator side, so nothing added here for the denominator is covered by
it — the deduplication claim scopes to the numerator alone.
They are spelt with Mathlib's later names (`compl₂EDS → complEDS₂`, `IsEllSequence →
IsEllipticSequence`), which #13057 predates, and follow `ComplAux.lean` in keeping the
`normEDS`-family declarations in the **root** namespace where Mathlib keeps `normEDS`, `complEDS`
and `complEDS₂`. Placement follows each left-hand side, so `reducedInvarNum`,
`reducedInvarNum_def`, `complEDS₂_eq_reducedInvarNum_sub` and `map_reducedInvarNum` all sit at
root, and only `invarNum_normEDS_one_eq_reducedInvarNum_mul`, whose left-hand side is an
`IsEllipticNet` term, sits in that namespace.

One adaptation is forced rather than chosen: the source proves `invarNum_normEDS` by
`simp [invarNum]`, unfolding the definition. That does not port, because `Invariant/Basic.lean`
exports
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

/-- The reduced invariant denominator, the counterpart of `reducedInvarNum`.

`IsEllipticNet.invarDenom_normEDS_one_eq_reducedInvarDenom_mul` is what identifies this with
`invarDenom (normEDS b c d) 1 m` divided by `b * c`, unconditionally over any commutative ring.
The paragraph below motivates the shape of the split.

`invarDenom (normEDS b c d) 1 m` is `W (m + 1) * W m * W (m - 1)`, and the divisibility
`W k ∣ W (n * k)` witnessed by Mathlib's `complEDS` lets `b = W 2` and `c = W 3` be taken out of
that product. Which factors give them up — and whether one factor supplies both or two factors
supply one each — depends on `m` modulo `6`, so the definition is a six-way split on `m % 6` rather
than a single formula. At residues `0`, `1` and `5` a single factor supplies both: the residue-`0`
case has `6 ∣ m`, so the middle factor `W m` gives up `b * c` at once through
`complEDS b c d 6 (m / 6)`, and the outer two survive whole. At residues `2`, `3` and `4` the work
is split between two factors, one giving up `b` through a `2`-complement and another giving up `c`
through a `3`-complement.

The factor `normEDS b c d 5 - d ^ 2` appearing in the residues `0`, `1` and `5` is `normEDS b c d
6` with `b * c` removed: `WeierstrassCurve.normEDS_six` reads `W 6 = (W 5 - d ^ 2) * b * c`, so a
residue that takes `b * c` out through the single `6`-complement is left carrying the remaining
factor. It is not claimed to be a unit: over an arbitrary commutative ring nothing here proves it
invertible. -/
def reducedInvarDenom : R :=
  let C := complEDS b c d
  let W := normEDS b c d
  let r₆ := W 5 - d ^ 2
  if m % 6 = 0 then r₆ * C 6 (m / 6) * W (m + 1) * W (m - 1)
  else if m % 6 = 1 then r₆ * C 6 ((m - 1) / 6) * W (m + 1) * W m
  else if m % 6 = 5 then r₆ * C 6 ((m + 1) / 6) * W m * W (m - 1)
  else if m % 6 = 2 then C 3 ((m + 1) / 3) * C 2 (m / 2) * W (m - 1)
  else if m % 6 = 4 then C 3 ((m - 1) / 3) * C 2 (m / 2) * W (m + 1)
  else C 3 (m / 3) * C 2 ((m - 1) / 2) * W (m + 1)

/-- The defining formula for `reducedInvarDenom`. The definition body is not exposed, so this
equation lemma is how a consumer computes with it.

Not `@[simp]`, but **not** for `reducedInvarNum_def`'s reason. There the point is that `simp`
should never unfold the term at all. Here it should: the whole content of `reducedInvarDenom` is
the residue split, so the six `reducedInvarDenom_of_emod_six_eq_*` lemmas below *are* `@[simp]`
and do unfold it — each into a single product, once the residue is known.

What is wrong is unfolding it into the six-way `if` chain, which is what tagging this lemma would
do: every goal mentioning `reducedInvarDenom` would acquire five undischarged conditions, and the
branch lemmas would then have nothing left to fire on. So the simp normal form of
`reducedInvarDenom b c d m` is "the selected branch, when `m % 6` is known, and the folded term
otherwise" — which is exactly this lemma off simp and those six on. -/
theorem reducedInvarDenom_def : reducedInvarDenom b c d m =
    if m % 6 = 0 then
      (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 (m / 6) *
        normEDS b c d (m + 1) * normEDS b c d (m - 1)
    else if m % 6 = 1 then
      (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 ((m - 1) / 6) *
        normEDS b c d (m + 1) * normEDS b c d m
    else if m % 6 = 5 then
      (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 ((m + 1) / 6) *
        normEDS b c d m * normEDS b c d (m - 1)
    else if m % 6 = 2 then
      complEDS b c d 3 ((m + 1) / 3) * complEDS b c d 2 (m / 2) * normEDS b c d (m - 1)
    else if m % 6 = 4 then
      complEDS b c d 3 ((m - 1) / 3) * complEDS b c d 2 (m / 2) * normEDS b c d (m + 1)
    else
      complEDS b c d 3 (m / 3) * complEDS b c d 2 ((m - 1) / 2) * normEDS b c d (m + 1) := (rfl)

/-- The residue-`0` branch, selected. The six `reducedInvarDenom_of_emod_six_eq_*` lemmas are the
elimination principle for `reducedInvarDenom`: the whole content of the definition is the split, so
a consumer that knows `m % 6` should reach its branch directly rather than rewriting by
`reducedInvarDenom_def` and discharging the preceding `if` conditions by hand. -/
@[simp]
theorem reducedInvarDenom_of_emod_six_eq_zero (h : m % 6 = 0) :
    reducedInvarDenom b c d m = (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 (m / 6) *
      normEDS b c d (m + 1) * normEDS b c d (m - 1) := by
  simp [reducedInvarDenom_def, h]

/-- The residue-`1` branch, selected. -/
@[simp]
theorem reducedInvarDenom_of_emod_six_eq_one (h : m % 6 = 1) :
    reducedInvarDenom b c d m = (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 ((m - 1) / 6) *
      normEDS b c d (m + 1) * normEDS b c d m := by
  simp [reducedInvarDenom_def, h]

/-- The residue-`5` branch, selected. -/
@[simp]
theorem reducedInvarDenom_of_emod_six_eq_five (h : m % 6 = 5) :
    reducedInvarDenom b c d m = (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 ((m + 1) / 6) *
      normEDS b c d m * normEDS b c d (m - 1) := by
  simp [reducedInvarDenom_def, h]

/-- The residue-`2` branch, selected. -/
@[simp]
theorem reducedInvarDenom_of_emod_six_eq_two (h : m % 6 = 2) :
    reducedInvarDenom b c d m =
      complEDS b c d 3 ((m + 1) / 3) * complEDS b c d 2 (m / 2) * normEDS b c d (m - 1) := by
  simp [reducedInvarDenom_def, h]

/-- The residue-`4` branch, selected. -/
@[simp]
theorem reducedInvarDenom_of_emod_six_eq_four (h : m % 6 = 4) :
    reducedInvarDenom b c d m =
      complEDS b c d 3 ((m - 1) / 3) * complEDS b c d 2 (m / 2) * normEDS b c d (m + 1) := by
  simp [reducedInvarDenom_def, h]

/-- The residue-`3` branch, selected — the final `else`, so no positive condition remains. -/
@[simp]
theorem reducedInvarDenom_of_emod_six_eq_three (h : m % 6 = 3) :
    reducedInvarDenom b c d m =
      complEDS b c d 3 (m / 3) * complEDS b c d 2 ((m - 1) / 2) * normEDS b c d (m + 1) := by
  simp [reducedInvarDenom_def, h]

/-- The formula vanishes at `0`. The factor responsible is the *complement*, not a `normEDS`: at
`m = 0` the residue-`0` branch is `(W 5 - d ^ 2) * complEDS b c d 6 0 * normEDS b c d 1 *
normEDS b c d (-1)`, whose `normEDS` factors are `1` and `-1`, and `complEDS_zero` kills it. -/
-- Not `@[simp]`: with the per-residue lemmas tagged, `simp` derives this from
-- `reducedInvarDenom_of_emod_six_eq_zero`, and `simpNF` rejects the redundant annotation.
theorem reducedInvarDenom_zero : reducedInvarDenom b c d 0 = 0 := by
  simp

/-- It vanishes at `1` as well, by the same mechanism: at `m = 1` the residue-`1` branch is
`(W 5 - d ^ 2) * complEDS b c d 6 ((1 - 1) / 6) * normEDS b c d 2 * normEDS b c d 1`, and
`(1 - 1) / 6 = 0`, so `complEDS_zero` applies again. No `normEDS b c d 0` occurs in either
branch. -/
@[simp]
theorem reducedInvarDenom_one : reducedInvarDenom b c d 1 = 0 := by
  simp

/-- The formula takes the value `1` at `2`, the residue-`2` branch collapsing to
`complEDS b c d 3 1 * complEDS b c d 2 1 * normEDS b c d 1`. This is the value that fixes the
formula's normalisation. -/
@[simp]
theorem reducedInvarDenom_two : reducedInvarDenom b c d 2 = 1 := by
  simp

/-- **The second complement read off the reduced numerator.** This is the direction the Lutz–Nagell
development uses: it expresses `complEDS₂` through the invariant of the elliptic net, rather than
through its own defining difference. -/
theorem complEDS₂_eq_reducedInvarNum_sub :
    complEDS₂ b c d m =
      reducedInvarNum b c d m - normEDS b c d m ^ 3 * b - 2 * complEDS₂Aux b c d m := by
  rw [reducedInvarNum_def]; ring

namespace IsEllipticNet

/-- **The cancellation `reducedInvarDenom` is named for**: the invariant denominator of a
normalised EDS at `s = 1` is `reducedInvarDenom` times `b * c`. This is what identifies the
six-way formula as the denominator with its constant factor removed, and so what gives the
definition its meaning. Unconditional over any commutative ring.

The **priority is load-bearing**, exactly as for the numerator counterpart. `invarDenom_def` is
itself `@[simp]`, and at equal priority it wins on this term: with a plain `@[simp]` the left-hand
side would expand to `W (m + 1) * W m * W (m - 1)` and this lemma would never fire. At `high` it
fires first, and because `reducedInvarDenom_def` is deliberately not `@[simp]` the result stays
folded at `reducedInvarDenom b c d m * (b * c)`. -/
@[simp high]
theorem invarDenom_normEDS_one_eq_reducedInvarDenom_mul :
    invarDenom (normEDS b c d) 1 m = reducedInvarDenom b c d m * (b * c) := by
  -- Split on `m % 6`; each branch reindexes one or two complements through
  -- `normEDS_mul_complEDS_div`, on the divisibility that `m % 6 = r` supplies.
  have hcase : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by omega
  rw [invarDenom_def]
  rcases hcase with h | h | h | h | h | h
  · rw [reducedInvarDenom_of_emod_six_eq_zero b c d m h,
      ← normEDS_mul_complEDS_div 6 m (by omega), WeierstrassCurve.normEDS_six]
    ring
  · rw [reducedInvarDenom_of_emod_six_eq_one b c d m h,
      ← normEDS_mul_complEDS_div 6 (m - 1) (by omega), WeierstrassCurve.normEDS_six]
    ring
  · rw [reducedInvarDenom_of_emod_six_eq_two b c d m h,
      ← normEDS_mul_complEDS_div 3 (m + 1) (by omega),
      ← normEDS_mul_complEDS_div 2 m (by omega), normEDS_two, normEDS_three]
    ring
  · rw [reducedInvarDenom_of_emod_six_eq_three b c d m h,
      ← normEDS_mul_complEDS_div 3 m (by omega),
      ← normEDS_mul_complEDS_div 2 (m - 1) (by omega), normEDS_two, normEDS_three]
    ring
  · rw [reducedInvarDenom_of_emod_six_eq_four b c d m h,
      ← normEDS_mul_complEDS_div 3 (m - 1) (by omega),
      ← normEDS_mul_complEDS_div 2 m (by omega), normEDS_two, normEDS_three]
    ring
  · rw [reducedInvarDenom_of_emod_six_eq_five b c d m h,
      ← normEDS_mul_complEDS_div 6 (m + 1) (by omega), WeierstrassCurve.normEDS_six]
    ring

/-- **The cancellation `reducedInvarNum` is named for**: the invariant numerator of a normalised EDS
at `s = 1` is `reducedInvarNum` times `b`. The factor of `b` is constant in `m`, which is what makes
the reduced form the one the division-polynomial identities are stated over.

The **priority is load-bearing**, not decoration. `invarNum_def` is itself `@[simp]`, and at equal
priority it wins on this term: with a plain `@[simp]` here, `simp` still rewrites
`invarNum (normEDS b c d) 1 m` to the fully expanded formula and this lemma never fires. At `high`
it fires first, and because `reducedInvarNum_def` is deliberately *not* `@[simp]` the result never
unfolds; `reducedInvarNum_eq_reducedInvarDenom_mul` carries it one step further, so the simp
normal form is `reducedInvarDenom b c d m * (d + b ^ 4) * b`. -/
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
-- Not `@[simp]`: with `reducedInvarNum_eq_reducedInvarDenom_mul` in the set, `simp` derives this
-- from `map_reducedInvarDenom`, and `simpNF` rejects the redundant annotation.
theorem map_reducedInvarNum :
    f (reducedInvarNum b c d m) = reducedInvarNum (f b) (f c) (f d) m := by
  simp [reducedInvarNum_def, map_ofNat]

/-- The reduced denominator is natural in the coefficient ring, so a specialisation or base change
may be pushed through it rather than around the unexposed body. The six-way split on `m % 6` does
not depend on the ring, so a ring map passes it unchanged. -/
@[simp]
theorem map_reducedInvarDenom :
    f (reducedInvarDenom b c d m) = reducedInvarDenom (f b) (f c) (f d) m := by
  simp [reducedInvarDenom_def, apply_ite f]

section ReducedInvariantIdentity

open MvPolynomial NormEDSParam
open scoped nonZeroDivisors

/-- `reducedInvarNum_eq_reducedInvarDenom_mul` under nonzerodivisor hypotheses on `b` and `c`. -/
private theorem reducedInvarNum_eq_reducedInvarDenom_mul_of_mem (hb : b ∈ R⁰) (hc : c ∈ R⁰) :
    reducedInvarNum b c d m = reducedInvarDenom b c d m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, ← mul_cancel_right_mem_nonZeroDivisors hc,
    ← IsEllipticNet.invarNum_normEDS_one_eq_reducedInvarNum_mul,
    IsEllipticNet.invarNum_normEDS_one_mul_eq_invarDenom_mul,
    IsEllipticNet.invarDenom_normEDS_one_eq_reducedInvarDenom_mul]
  ring

/-- **The reduced invariant identity**: for a normalised EDS the reduced numerator is the
reduced denominator times `d + b ^ 4`, for every `m` and with no hypothesis on `b`, `c`, `d` —
the source's `redInvar_normEDS`. `@[simp]` as the canonical elimination rule for
`reducedInvarNum`: the rewrite removes the `reducedInvarNum` head, chaining after
`invarNum_normEDS_one_eq_reducedInvarNum_mul` rather than racing it, and
`reducedInvarNum_def` is deliberately outside the simp set. -/
@[simp]
theorem reducedInvarNum_eq_reducedInvarDenom_mul :
    reducedInvarNum b c d m = reducedInvarDenom b c d m * (d + b ^ 4) := by
  -- Prove it where `b` and `c` are nonzerodivisors — the universal parameters — and specialise.
  have huniv := reducedInvarNum_eq_reducedInvarDenom_mul_of_mem
    (b := (X B : MvPolynomial NormEDSParam ℤ)) (c := X C) (d := X D) (m := m)
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero (R := ℤ) B))
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero (R := ℤ) C))
  simpa only [map_reducedInvarNum, map_reducedInvarDenom, map_mul, map_add, map_pow, aeval_X]
    using congr(aeval (NormEDSParam.rec b c d) $huniv)

end ReducedInvariantIdentity
