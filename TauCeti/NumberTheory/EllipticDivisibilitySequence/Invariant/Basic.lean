/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# The invariant of an elliptic net

For an elliptic net `W : ℤ → R` and each `s`, the two quantities

* `IsEllipticNet.invarNum W s n
    = (W (n + 2s) * W (n - s)² + W (n + s)² * W (n - 2s)) * W s² + W n³ * W (2s)²`, and
* `IsEllipticNet.invarDenom W s n = W (n + s) * W n * W (n - s)`

cross-multiply symmetrically in the two indices:

`invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m`,

which is `IsEllipticNet.invarNum_mul_invarDenom`. That identity, and not a statement about a
ratio, is what this file proves: `R` is only a commutative ring, where a denominator may vanish or
be a zero divisor and `invarNum / invarDenom` need not exist at all.

Over a field it does become a statement about a ratio. On any set of indices where
`invarDenom W s ·` is nonvanishing, cancelling the identity at a pair `m, n` — which needs both
`invarDenom W s m` and `invarDenom W s n` nonzero, not just one of them — says exactly that
`n ↦ invarNum/invarDenom` is constant there. When `W` is the division-polynomial sequence of a
Weierstrass curve, that constant is a coordinate of the point being multiplied, which is what makes
the invariant the bridge between the elliptic-net identities and the curve.

## Main definitions

* `IsEllipticNet.invarNum` and `IsEllipticNet.invarDenom` are defined for an **arbitrary**
  sequence `W : ℤ → R` — no hypothesis on `W`, and nothing about Weierstrass curves. It is the
  *theorem* that asks `W` to be an elliptic net; the file proves that direction only, and states
  no converse.
* `IsEllipticNet.invarNum_def`, `IsEllipticNet.invarDenom_def`: the defining formulas, as public
  equation lemmas. The section is a plain `public section`, so the bodies are exported unexposed
  and an importing module cannot unfold them: these equations are how a consumer computes.

## Main results

* `IsEllipticNet.invarNum_mul_invarDenom`: the invariance identity for an elliptic net —
  `invarNum` and `invarDenom` cross-multiply symmetrically in the two indices.
* `IsEllipticNet.map_invarNum`, `IsEllipticNet.map_invarDenom`: both are natural in `R`. These are
  deliberately not `@[simp]` — the `_def` equations are, and `simp` derives naturality from them —
  but they are named, because the `simp only` sets of the specialization arguments downstream need
  naturality *without* unfolding the invariant, exactly as Mathlib names `map_atom`, `map_rel` and
  `map_normEDS` alongside the same objects' defining equations.

## Implementation notes

The numerator is *not* symmetric in the two terms it pairs, and the `W s ^ 2` and `W (2 * s) ^ 2`
weights are not decoration: they are what makes the identity hold over a ring with zero divisors,
where one cannot divide through.

## Provenance

Ported from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declarations `invarNum`, `invarDenom` and `invar_of_net`. That file's header reads `Authors: David
Kurniadi Angdinata`; following this repository's convention for adapted material the upstream
authorship is credited here rather than in the copyright header. J. Xu is acknowledged for the
surrounding LutzNagell development — he authors `Universal.lean` and co-authors
`DivisionPolynomialOmega.lean` at the same revision — as context for this port, not as an author of
the declarations above.

The same three declarations sit in **Mathlib PR #13057** (open, last updated 2024-07-31), which is
the upstreaming of that AINTLIB file; this port uses that PR's naming
(`invarNum_mul_invarDenom`, from its sibling PR #13155) rather than the source's `invar_of_net`,
so that deduplication when it lands is a deletion rather than a rename. It could not be copied
from #13057 unchanged: that PR predates Mathlib's rename of the elliptic-net API, and is written
against `net`/`addMulSub`/`rel₄`, which are now `IsEllipticNet.rel`, `IsEllipticNet.atom` and
`IsEllipticNet.atomRel`. The definitions are otherwise character-for-character identical, so the
restatement here is purely the rename.
-/

public section

namespace IsEllipticNet

variable {R S : Type*} [Semiring R] [Semiring S] (W : ℤ → R)

/-! The definitions and their equation and naturality lemmas are pure products and sums, in a fixed
order, so they ask only for a semiring — neither commutativity nor subtraction. Both enter with the
elliptic relator, and the invariance theorems live in the `CommRing` section below. -/

/-- The candidate numerator of the invariant, for an arbitrary sequence `W` — no hypothesis is
imposed here. When `W` is an elliptic net, `invarNum W s n` and `invarDenom W s n` cross-multiply
symmetrically in `n`; that is `invarNum_mul_invarDenom`, which is the ratio
`invarNum W s n / invarDenom W s n` being independent of `n` only over a field where the
denominators involved are nonzero. -/
def invarNum (s n : ℤ) : R :=
  (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
    + W n ^ 3 * W (2 * s) ^ 2

/-- The defining formula for `invarNum`. The body is exported unexposed, so an importing
module cannot unfold it and this equation lemma is how a consumer computes with it. -/
@[simp]
theorem invarNum_def (s n : ℤ) : invarNum W s n =
    (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
      + W n ^ 3 * W (2 * s) ^ 2 := (rfl)

/-- The denominator of the invariant of an elliptic net, `W (n + s) * W n * W (n - s)`. -/
def invarDenom (s n : ℤ) : R := W (n + s) * W n * W (n - s)

/-- The defining formula for `invarDenom`. The body is exported unexposed, so an importing
module cannot unfold it and this equation lemma is how a consumer computes with it. -/
@[simp]
theorem invarDenom_def (s n : ℤ) : invarDenom W s n = W (n + s) * W n * W (n - s) := (rfl)

section CommRing

variable {R : Type*} [CommRing R] {W : ℤ → R}

/-- `invarNum` and `invarDenom` cross-multiply symmetrically in `m` and `n` as soon as the elliptic
relator vanishes at these four arguments. -/
private theorem invarNum_mul_invarDenom_of_rel {s m n : ℤ}
    (h₀ : rel W m n s 0 = 0) (h₁ : rel W m n s s = 0)
    (h₂ : rel W (m - s) (n - s) s s = 0) (h₃ : rel W (n + s) n (n - s) (m - n) = 0) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m := by
  simp_rw [invarNum, invarDenom]
  linear_combination (norm := (simp_rw [rel]; ring_nf))
    h₀ * W m * W n * W (2 * s) ^ 2
      - (h₁ * W (m - s) * W (n - s)
        + h₂ * W (m + s) * W (n + s)
        - h₃ * W (m - n) * W (2 * s)) * W s ^ 2

/-- **The invariance identity for an elliptic net**: `invarNum` and `invarDenom` cross-multiply
symmetrically in the two indices.

That is weaker than "the invariant does not depend on `n`". Over a field, at a pair `m, n` where
both `invarDenom W s m` and `invarDenom W s n` are nonzero, it cancels to equality of the two
ratios; over a general commutative ring a denominator may vanish or be a zero divisor, and then
there is no ratio to compare. -/
theorem invarNum_mul_invarDenom (h : IsEllipticNet W) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m :=
  invarNum_mul_invarDenom_of_rel (h ..) (h ..) (h ..) (h ..)

end CommRing

variable {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)

/-- The numerator of the invariant is natural in the coefficient ring.

Not `@[simp]`: with `invarNum_def` tagged, `simp` derives this from it together with `map_add`,
`map_mul`, `map_pow` and `Function.comp_apply`, so tagging it too is a `simpNF` duplicate. It is
still wanted under its own name, because the specialization arguments downstream rewrite with
`simp only` — where nothing fires unless it is named, and where the point is to move a ring hom
through the invariant *without* unfolding it into its six-term formula. This is the role Mathlib's
`map_atom`, `map_rel` and `map_normEDS` play for the rest of this API. -/
theorem map_invarNum (s n : ℤ) : f (invarNum W s n) = invarNum (f ∘ W) s n := by
  simp only [invarNum, map_add, map_mul, map_pow, Function.comp_apply]

/-- The denominator of the invariant is natural in the coefficient ring.

Not `@[simp]`, for the same reason as `map_invarNum`: `invarDenom_def` and `map_mul` derive it. -/
theorem map_invarDenom (s n : ℤ) : f (invarDenom W s n) = invarDenom (f ∘ W) s n := by
  simp only [invarDenom, map_mul, Function.comp_apply]

end IsEllipticNet
