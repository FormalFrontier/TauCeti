/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Order.Fin.Tuple
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Int.ModEq

/-!
# Index bookkeeping for the descent on the elliptic relator

Mathlib's `IsEllipticNet.atomRel_avg_sub` transfers the four-index relator from a quadruple
`a, b, c, d` to the quadruple obtained by subtracting each index from the average
`m = (a + b + c + d) / 2`, in reverse order:

`atomRel W (m - d) (m - c) (m - b) (m - a) = atomRel W a b c d`.

The descent that identifies elliptic sequences runs on that transfer, and needs to know that its
two side conditions survive it: the four indices stay of one parity, and — after taking the
absolute value of the last, which `IsEllipticNet.atomRel_abs₄` absorbs — they stay nonnegative and
strictly decreasing. This file proves both, together with the bound `6 ≤ a` that makes the descent
terminate.

## Main definitions

* `IsEllipticNet.NonnegStrictAnti₄`: the four indices are nonnegative and strictly decreasing.
  The name carries both halves of the definition — Mathlib's `StrictAnti` on the tuple, and the
  lower bound bundled alongside it because every use needs the two together.

## Main results

* `IsEllipticNet.parity_abs_avg_sub`: same parity survives the transfer, with the witness taken
  relative to the entry `atomRel_abs₄` leaves under an absolute value.
* `IsEllipticNet.nonnegStrictAnti₄_iff`: the predicate as the lower bound `0 ≤ d` together
  with the three adjacent inequalities.
* `IsEllipticNet.nonnegStrictAnti₄_abs_avg_sub`: nonnegativity and strict decrease survive it.
* `IsEllipticNet.six_le_of_parity_of_nonnegStrictAnti₄`: a strictly decreasing quadruple
  of one parity with `0 ≤ d` has `6 ≤ a` — consecutive indices differ by at least two, three
  times over.

## Implementation notes

Parity is spelled as Mathlib spells it for this API — the unbundled conjunction
`d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2`, relative to the last index, as
`IsEllipticNet.atomRel_eq` and `atomRel_avg_sub` take it — rather than as the source's bundled
predicate over `Int.negOnePow`. Matching the upstream shape means those two lemmas apply with no
conversion at the use sites, and avoids standing a second parity predicate next to Mathlib's.

The ordering half reuses Mathlib's tuple API: it is `StrictAnti ![a, b, c, d]`, not a hand-rolled
chain of three inequalities. `Mathlib/Order/Fin/Tuple.lean` states that API through `vecCons` —
`strictAnti_vecCons` and `strictAnti_vecEmpty`, both `@[simp]` — so `simp` unfolds the tuple form
into the adjacent comparisons the descent consumes, and `nonnegStrictAnti₄_iff` records that
normal form once for downstream use.

**On the imports.** The rule here is: **public** for what the public *statements* mention,
**private** for what only the proofs need. So `Mathlib.Algebra.Order.Group.Int` and
`…Group.Unbundled.Abs` are public — the statements use ℤ arithmetic and `|…|` — as is
`Mathlib.Order.Fin.Tuple`, since `NonnegStrictAnti₄` is defined by `StrictAnti ![…]` and that
module supplies the vector notation too. `Mathlib.Data.Int.ModEq` and `Mathlib.Algebra.Order.Group
.Abs` are private, each used only inside a proof — the latter for `abs_cases`, which is
`to_additive`-generated from `mabs_cases` and so appears under no literal definition of its own.

**On the hypotheses.** `nonnegStrictAnti₄_abs_avg_sub` takes `d < c`, `2 ≤ c + d`, `c < b` and
`b < a` separately, rather than a bundled `NonnegStrictAnti₄`. Those are what the transferred
ordering actually needs: the descent supplies parity, and a same-parity gap is strictly stronger
than this — `(a, b, c, d) = (4, 3, 2, 1)` satisfies these and the conclusion while failing
`d + 2 ≤ c`. Only `parity_abs_avg_sub` and `six_le_of_parity_of_nonnegStrictAnti₄` genuinely need
parity as parity.

This file does **not** import `Mathlib.NumberTheory.EllipticDivisibilitySequence`. No declaration
here mentions `atom`, `atomRel` or `rel`: the statements are about ℤ arithmetic, order and parity,
and the EDS lemmas they are *for* — `atomRel_avg_sub`, `atomRel_abs₄`, `atomRel_eq` — are named in
the prose because that is what fixes the index shapes, not because anything here needs their API.
Importing the EDS module only to reach `abs_cases` through it cost 279 build jobs.

## Provenance

Ported from J. Xu's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declarations `StrictAnti₄`, `HaveSameParity₄.transf`,
`HaveSameParity₄.strictAnti₄_transf` and `HaveSameParity₄.six_le_of_strictAnti₄`. That file's
header reads `Authors: Junyan Xu`; following this repository's convention for adapted material the
upstream authorship is credited here rather than in the copyright header. The source's
`StrictAnti₄` gains a `Nonneg` prefix here, because the predicate bundles the lower bound `0 ≤ d`
that the source's name left unsaid; the `StrictAnti` half is kept, the definition being Mathlib's
`StrictAnti` on the tuple. The dependent names follow it, and `six_le_of_parity_of_…` names the
parity hypothesis that its statement genuinely needs.

The source's surrounding transfer machinery is **not** ported, being already upstream: its
`rel₄_transf` is Mathlib's `atomRel_avg_sub`, its `rel₄_eq_net` is Mathlib's `atomRel_eq`, and its
`avg₄` is inlined there as `(a + b + c + d) / 2`. With `rel₄_transf` unneeded, so are the four
declarations existing only to prove it — `addMulSub₄`, `addMulSub₄_mul_addMulSub₄`,
`addMulSub_transf` and `avg₄_add_avg₄`. That is also why no `set_option allowUnsafeReducibility`
appears here: the one source lemma carrying it is among those not needed.
-/

public section

namespace IsEllipticNet

/-- The four indices are nonnegative and strictly decreasing. Nonnegativity is bundled in because
the descent needs it wherever it needs the ordering; the decreasing half is Mathlib's
`StrictAnti` on the tuple. -/
def NonnegStrictAnti₄ (a b c d : ℤ) : Prop := 0 ≤ d ∧ StrictAnti ![a, b, c, d]

/-- `NonnegStrictAnti₄` as the lower bound and the three adjacent inequalities. -/
@[simp]
theorem nonnegStrictAnti₄_iff (a b c d : ℤ) :
    NonnegStrictAnti₄ a b c d ↔ 0 ≤ d ∧ d < c ∧ c < b ∧ b < a := by
  unfold NonnegStrictAnti₄
  simp
  omega

/-- **Same parity survives the transfer**, for the transferred quadruple exactly as
`atomRel_avg_sub` produces it, with the last index raw. -/
private theorem parity_avg_sub {a b c d : ℤ}
    (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2) :
    ((a + b + c + d) / 2 - a) % 2 = ((a + b + c + d) / 2 - d) % 2 ∧
      ((a + b + c + d) / 2 - a) % 2 = ((a + b + c + d) / 2 - c) % 2 ∧
        ((a + b + c + d) / 2 - a) % 2 = ((a + b + c + d) / 2 - b) % 2 := by
  obtain ⟨h₁, h₂, h₃⟩ := parity
  omega

/-- **Same parity survives the transfer**, with the parity witness written relative to
`|(a + b + c + d) / 2 - a|`, the entry `atomRel_abs₄` leaves under an absolute value. -/
theorem parity_abs_avg_sub {a b c d : ℤ}
    (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2) :
    |(a + b + c + d) / 2 - a| % 2 = ((a + b + c + d) / 2 - d) % 2 ∧
      |(a + b + c + d) / 2 - a| % 2 = ((a + b + c + d) / 2 - c) % 2 ∧
        |(a + b + c + d) / 2 - a| % 2 = ((a + b + c + d) / 2 - b) % 2 := by
  have habs : |(a + b + c + d) / 2 - a| % 2 = ((a + b + c + d) / 2 - a) % 2 :=
    Int.abs_modEq_two
  obtain ⟨h₁, h₂, h₃⟩ := parity_avg_sub parity
  exact ⟨habs.trans h₁, habs.trans h₂, habs.trans h₃⟩

/-- **Nonnegativity and strict decrease survive the transfer.** The last index needs its absolute
value: `m - a` is the one difference that can be negative, `a` being the largest index. -/
theorem nonnegStrictAnti₄_abs_avg_sub {a b c d : ℤ}
    (hdc : d < c) (hcd : 2 ≤ c + d) (hcb : c < b) (hba : b < a) :
    NonnegStrictAnti₄ ((a + b + c + d) / 2 - d) ((a + b + c + d) / 2 - c)
      ((a + b + c + d) / 2 - b) |(a + b + c + d) / 2 - a| := by
  rw [nonnegStrictAnti₄_iff]
  refine ⟨abs_nonneg _, ?_, by omega, by omega⟩
  rcases abs_cases ((a + b + c + d) / 2 - a) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

/-- A strictly decreasing quadruple of one parity, bounded below by zero, has `6 ≤ a`: each of the
three consecutive gaps is at least two. This is what makes the descent terminate. -/
theorem six_le_of_parity_of_nonnegStrictAnti₄ {a b c d : ℤ}
    (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2)
    (anti : NonnegStrictAnti₄ a b c d) :
    6 ≤ a := by
  obtain ⟨h₁, h₂, h₃⟩ := parity
  rw [nonnegStrictAnti₄_iff] at anti
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  omega

end IsEllipticNet
