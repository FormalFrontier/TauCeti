/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Recurrence
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Transfer
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FinCases
import TauCeti.NumberTheory.EllipticDivisibilitySequence.SignEquivariance

/-!
# An elliptic net from its two doubling recurrences

`IsEllipticNet W` is a condition on every quadruple of integers, `IsEllipticSequence W` on every
triple. This file proves both equivalent to two families of equations indexed by a *single*
integer — the odd doubling recurrence from `m = 2` on and the even one from `m = 3` on — for a
sequence that is odd, vanishes at `0`, and has `W 1` and `W 2` nonzerodivisors.

The forward direction is `Recurrence.lean`. The reverse is the descent proved here, by
induction on the largest index `a`:

* below `6` there is no valid quadruple at all, four nonnegative same-parity indices in strict
  decrease forcing `6 ≤ a` (`Transfer.lean`);
* above it, a relator on four unconstrained indices is rewritten into relators carrying a fixed
  pair of small indices, by the three-term and ten-term expansions below;
* that reduces to the minimal same-parity pair `(a % 2 + 2, a % 2)`, where either `b + 2 < a`
  admits the transfer down to a smaller first index, or `b + 2 = a` lands on one of the two
  recurrences, chosen by the parity of `a`.

Arbitrary indices are then reduced to a valid quadruple: absolute values make them nonnegative,
coincidences collapse through Mathlib's `atomRel_same` family, and the rest are sorted.

The expansions are polynomial identities in the atoms — `atomRel` is a fixed quadratic
expression in `atom`, so both sides expand to combinations of products of two atoms and `ring`
closes them. No index arithmetic is involved, which is why they need none of the parity
hypotheses that `atom_even`, `atom_odd` and `atomRel_eq` carry.

## Main results

* `isEllipticNet_iff`: the equivalence at **four** indices, and the headline result of the file.
* `isEllipticSequence_iff`: the classical three-index equivalence, its `s = 0` case.
* `IsEllipticNet.of_rel`: the hard direction of the first, with the recurrences in relator
  form.
* `IsEllipticNet.atom_mul_atomRel_eq_of_last_eq_fst`, `…_of_last_eq_snd`,
  `IsEllipticNet.atom_mul_atomRel_eq`: the three-term and ten-term expansions that drive it.

## Implementation notes

The descent itself is private. `AtomRelVanishes` and the three lemmas lowering it are shaped by
this proof rather than by any consumer, and the interface a caller wants is the equivalence and
its hard direction.

Both levels are stated. `isEllipticNet_iff` is the stronger statement and everything is proved
through it, but `IsEllipticSequence` is the predicate Mathlib defines and that
`IsEllipticDvdSequence` is built from, so the three-index equivalence is kept named rather than
left as `(isEllipticNet_iff …).mpr … |>.isEllipticSequence` at each use. The relator-form
`isEllipticSequence_of_rel` is *not* kept: it restated `IsEllipticNet.of_rel` in the spelling
this file uses internally, and had no consumer.

That predicate carries the parity and ordering conditions *inside* it. The induction applies its
hypothesis at quadruples whose validity is not known in advance, so the recursive call has to be
a statement about indices alone.

The antisymmetry of `atomRel` under transpositions is **not** proved here: `SignEquivariance.lean`
already exports `atomRel_swap₁₂`, `atomRel_swap₂₃` and `atomRel_swap₃₄`, together with the general
`atomRelFin4_perm`. It is that general form the sorting uses. The net has no distinguished index —
`rel_eq` produces the quadruple `(2p + s, 2q + s, 2r + s, s)`, in which `s` is free — so all four
are sorted, by `Tuple.sort` composed with the reversal, rather than three against a fixed `0`.

Two parts of the source's apparatus are not needed here, each because Mathlib has absorbed the
layer that made them necessary. Its `rel₄_transf` is `atomRel_avg_sub`; and its minimal-index
definition `if Even a then 0 else 1`, with five `Int.negOnePow` lemmas about it, is `a % 2`,
about which everything needed is `omega`. Its `Tuple.sort` argument over four indices **is**
needed, and is used.

## Provenance

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declarations `rel₆_eq₃`, `rel₆_eq₃'`, `rel₆_eq₁₀`, `rel₄_iff_evenRec`, `dMin`, `cMin`,
`Rel₄OfValid`, `rel₄_fix₁_of_fix₂`, `rel₄_of_fix₂`, `rel₄_of_min₂`, `rel₄_of_anti_oddRec_evenRec`,
`rel₄_of_oddRec_evenRec` and `IsEllSequence.of_oddRec_evenRec`. That file's header reads `Authors:
David Kurniadi Angdinata`; following this repository's convention for adapted material the upstream
authorship is credited here rather than in the copyright header. J. Xu is acknowledged for the
surrounding LutzNagell development — he authors `Universal.lean` and co-authors
`DivisionPolynomialOmega.lean` at the same revision — as context for this port, not as an author of
the declarations above.

The four-index sorting and the net entry point adapt two further declarations of that same file,
`IsEllSequence.rel₄` and `IsEllSequence.net`.

The source states its expansions against its own `addMulSub` and `rel₄`, which Mathlib now
supplies as `atom` and `atomRel` with the same definitions, so those statements transfer by
renaming. Three of its declarations are deliberately **not** ported. Its `rel₆` abbreviation for
`addMulSub W k l * rel₄ W a b c d`, with the `@[simp]` lemma unfolding it, names a product
rather than a concept and exists only to shorten four statements, so it would stand a second
public spelling of `atom _ _ * atomRel _ _ _ _`; the statements below write the product out.
Its `addMulSub_sq_mul_rel₄_eq₉`, the nine-term expansion, is unused in the source itself — it
occurs there only at its own declaration — and this descent does not need it. Its swap family
`rel₄_swap₀₁`, `rel₄_swap₁₂`, `rel₄_swap₂₃` and the `relFin4_perm` built on them are already in
this repository as `SignEquivariance.lean`, and are used from there.

`rel₄_iff_evenRec` is the one source declaration carrying `set_option allowUnsafeReducibility
true` together with `attribute [local reducible] Nat.rawCast`, which #2860 declined to bring
into this repository. Stating the base cases with indices in `2 * _` and `2 * _ + 1` form lets
`atomRel_two_mul` and `atom_odd` apply directly, so neither the option nor the attribute
appears here.
-/

public section

namespace IsEllipticNet

variable {R : Type*} [CommRing R] (W : ℤ → R)

/-- **Expanding over a fixed pair, when the relator already ends at the atom's first index.**
Each relator on the right carries both `c` and `d`, so this trades one occurrence of `c` for
the pair `c, d`. -/
theorem atom_mul_atomRel_eq_of_last_eq_fst (c d m n r : ℤ) :
    atom W c d * atomRel W m n r c =
      atom W m c * atomRel W n r c d - atom W n c * atomRel W m r c d
        + atom W r c * atomRel W m n c d := by
  simp_rw [atomRel]; ring

/-- **Expanding over a fixed pair, when the relator already ends at the atom's second index.**
The companion of `atom_mul_atomRel_eq_of_last_eq_fst` with the roles of `c` and `d` exchanged
in the atoms, the relators on the right being the same three. -/
theorem atom_mul_atomRel_eq_of_last_eq_snd (c d m n r : ℤ) :
    atom W c d * atomRel W m n r d =
      atom W m d * atomRel W n r c d - atom W n d * atomRel W m r c d
        + atom W r d * atomRel W m n c d := by
  simp_rw [atomRel]; ring

/-- **Expanding over a fixed pair, for four unconstrained relator indices.** Every relator on
the right has at least one index drawn from the fixed pair `c, d`, which is what lets the
descent lower the indices it is working on. -/
theorem atom_mul_atomRel_eq (c d m n r s : ℤ) :
    atom W c d * atomRel W m n r s =
      atom W n d * atomRel W m r s c - atom W r d * atomRel W m n s c
        + atom W s d * atomRel W m n r c
      + atom W n c * atomRel W m r s d - atom W r c * atomRel W m n s d
        + atom W s c * atomRel W m n r d
      + atom W n r * atomRel W m s c d - atom W n s * atomRel W m r c d
        + atom W r s * atomRel W m n c d
      - 2 * (atom W m d * atomRel W n r s c) := by
  simp_rw [atomRel]; ring

open scoped nonZeroDivisors

/-- **The relator vanishes at a valid quadruple.** "Valid" is: one parity, nonnegative, strictly
decreasing. The two hypotheses live inside the predicate rather than outside it because the
descent applies its induction hypothesis at quadruples whose validity is not known in advance;
carrying them here means the recursive call is a `Prop` about indices alone. -/
private def AtomRelVanishes (a b c d : ℤ) : Prop :=
  (d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2) → NonnegStrictAnti₄ a b c d →
    atomRel W a b c d = 0

variable {W}

/-- The minimal same-parity pair above zero, `(a % 2 + 2, a % 2)`, has its atom a nonzerodivisor
as soon as `W 1` and `W 2` are: the two parities give `W 1 * W 1` and `W 2 * W 1`. -/
private theorem atom_emod_mem_nonZeroDivisors (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (a : ℤ) :
    atom W (a % 2 + 2) (a % 2) ∈ R⁰ := by
  rcases Int.emod_two_eq_zero_or_one a with h | h <;> rw [h] <;> norm_num [atom] <;>
    exact mul_mem ‹_› ‹_›

/-- The three relators common to both expansions used by `atomRelVanishes_of_forall_le`. Each
carries the fixed pair `c₀, d₀` in its last two places and a first index at most `a`, so each is
in range of the descent hypothesis; the chain `d₀ < c₀ < c < b < a` is what makes all three
valid quadruples. -/
private theorem atomRel_triple_eq_zero {a b c c₀ d₀ : ℤ}
    (rel : ∀ {a' b' : ℤ}, a' ≤ a → AtomRelVanishes W a' b' c₀ d₀)
    (par : c₀ % 2 = d₀ % 2) (same : d₀ % 2 = a % 2 ∧ d₀ % 2 = b % 2 ∧ d₀ % 2 = c % 2)
    (le : 0 ≤ d₀) (lt : d₀ < c₀) (hc : c₀ < c) (hcb : c < b) (hba : b < a) :
    atomRel W b c c₀ d₀ = 0 ∧ atomRel W a c c₀ d₀ = 0 ∧ atomRel W a b c₀ d₀ = 0 := by
  obtain ⟨ha, hb, hcc⟩ := same
  refine ⟨rel hba.le ⟨by omega, by omega, by omega⟩ ?_,
    rel le_rfl ⟨by omega, by omega, by omega⟩ ?_,
    rel le_rfl ⟨by omega, by omega, by omega⟩ ?_⟩ <;>
    rw [nonnegStrictAnti₄_iff] <;> omega

/-- **Lowering the last index onto a fixed pair.** Given vanishing at every quadruple
`(a', b, c₀, d₀)` with `a' ≤ a`, the relator vanishes at `(a, b, c, c₀)` outright, and at
`(a, b, c, d₀)` once `c₀ < c`. Both follow from a three-term expansion trading the relator's
last index for the pair `c₀, d₀`, after which every summand carries a factor already known to
vanish. -/
private theorem atomRelVanishes_of_forall_le {a c₀ d₀ : ℤ} (par : c₀ % 2 = d₀ % 2) (le : 0 ≤ d₀)
    (lt : d₀ < c₀) (rel : ∀ {a' b : ℤ}, a' ≤ a → AtomRelVanishes W a' b c₀ d₀)
    (mem : atom W c₀ d₀ ∈ R⁰) (b c : ℤ) :
    AtomRelVanishes W a b c c₀ ∧ (c₀ < c → AtomRelVanishes W a b c d₀) := by
  constructor
  · intro same anti
    rw [nonnegStrictAnti₄_iff] at anti
    obtain ⟨-, hc, hcb, hba⟩ := anti
    obtain ⟨h₁, h₂, h₃⟩ := atomRel_triple_eq_zero rel par
      ⟨by omega, by omega, by omega⟩ le lt hc hcb hba
    refine mem.2 _ ?_
    rw [mul_comm, atom_mul_atomRel_eq_of_last_eq_fst, h₁, h₂, h₃]
    ring
  · intro hc same anti
    rw [nonnegStrictAnti₄_iff] at anti
    obtain ⟨-, hdc, hcb, hba⟩ := anti
    obtain ⟨h₁, h₂, h₃⟩ := atomRel_triple_eq_zero rel par
      ⟨by omega, by omega, by omega⟩ le lt hc hcb hba
    refine mem.2 _ ?_
    rw [mul_comm, atom_mul_atomRel_eq_of_last_eq_snd, h₁, h₂, h₃]
    ring

/-- **Lowering an unconstrained last index.** With the previous lemma available at every `b, c`,
the ten-term expansion reaches a quadruple whose last index `d` is merely above `c₀`: each of
the ten summands carries a relator that either already ends at the fixed pair or is reachable
from it, and so vanishes. -/
private theorem atomRelVanishes_of_lt {a c₀ d₀ : ℤ} (par : c₀ % 2 = d₀ % 2) (le : 0 ≤ d₀)
    (lt : d₀ < c₀)
    (rel : ∀ {a' b : ℤ}, a' ≤ a → AtomRelVanishes W a' b c₀ d₀) (mem : atom W c₀ d₀ ∈ R⁰)
    (b c d : ℤ) (hc : c₀ < d) (par' : d % 2 = d₀ % 2) :
    AtomRelVanishes W a b c d := by
  intro same anti
  rw [nonnegStrictAnti₄_iff] at anti
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  obtain ⟨hda, hdb, hdc'⟩ := same
  have fix₁ (b' c' : ℤ) := (atomRelVanishes_of_forall_le par le lt rel mem b' c').1
  have fix₂ (b' c' : ℤ) := (atomRelVanishes_of_forall_le par le lt rel mem b' c').2
  have fixb (b' c' : ℤ) :=
    (atomRelVanishes_of_forall_le par le lt (fun h ↦ rel (h.trans hba.le)) mem b' c').1
  have e₁ := fix₁ c d ⟨by omega, by omega, by omega⟩ (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₂ := fix₁ b d ⟨by omega, by omega, by omega⟩ (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₃ := fix₁ b c ⟨by omega, by omega, by omega⟩ (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₄ := fix₂ c d hc ⟨by omega, by omega, by omega⟩ (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₅ := fix₂ b d hc ⟨by omega, by omega, by omega⟩ (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₆ := fix₂ b c (by omega) ⟨by omega, by omega, by omega⟩
    (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₇ := rel (b := d) le_rfl ⟨by omega, by omega, by omega⟩
    (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₈ := rel (b := c) le_rfl ⟨by omega, by omega, by omega⟩
    (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₉ := rel (b := b) le_rfl ⟨by omega, by omega, by omega⟩
    (by rw [nonnegStrictAnti₄_iff]; omega)
  have e₁₀ := fixb c d ⟨by omega, by omega, by omega⟩ (by rw [nonnegStrictAnti₄_iff]; omega)
  refine mem.2 _ ?_
  rw [mul_comm, atom_mul_atomRel_eq, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, e₁₀]
  ring

/-- **Only the minimal pair needs checking.** If the relator vanishes at every quadruple whose
last two indices are the minimal same-parity pair `(a % 2 + 2, a % 2)`, it vanishes at every
valid quadruple with first index `a`. The three remaining cases are `d` above the pair, `d` at
its top, and `d` at its bottom; in the `%2` spelling each is closed by `omega`, where the source
needed a chain of `Int.negOnePow` lemmas. -/
private theorem atomRelVanishes_of_min {a : ℤ} (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (rel : ∀ {a' b : ℤ}, a' ≤ a → AtomRelVanishes W a' b (a % 2 + 2) (a % 2)) (b c d : ℤ) :
    AtomRelVanishes W a b c d := by
  intro same anti
  have par : (a % 2 + 2) % 2 = a % 2 % 2 := by omega
  have le : (0 : ℤ) ≤ a % 2 := by omega
  have lt : a % 2 < a % 2 + 2 := by omega
  have mem := atom_emod_mem_nonZeroDivisors one two (W := W) a
  have hda := same.1
  obtain ⟨hd, hdc, hcb, hba⟩ := (nonnegStrictAnti₄_iff a b c d).mp anti
  rcases lt_or_ge (a % 2 + 2) d with hlt | hge
  · exact atomRelVanishes_of_lt par le lt rel mem b c d hlt (by omega) same anti
  have fix := atomRelVanishes_of_forall_le par le lt rel mem b c
  rcases hge.eq_or_lt with heq | hlt₂
  · subst heq; exact fix.1 same anti
  · have hdm : d = a % 2 := by omega
    subst hdm
    -- `c` carries the parity of `a` and exceeds `a % 2`, so it is at least `a % 2 + 2`: either
    -- the quadruple is already the minimal pair, or the previous lemma's second case applies.
    have hcmin : a % 2 + 2 = c ∨ a % 2 + 2 < c := by omega
    rcases hcmin with heq₂ | hlt₃
    · subst heq₂; exact rel le_rfl same anti
    · exact fix.2 hlt₃ same anti

/-- The even base case, as a relator: all four indices are even, so `atomRel_two_mul` applies. -/
private theorem atomRel_even_eq_rel (k : ℤ) :
    atomRel W (2 * k) (2 * (k - 1)) (2 * k % 2 + 2) (2 * k % 2) = rel W k (k - 1) 1 0 := by
  have hlast : (2 * k % 2 : ℤ) = 2 * 0 := by omega
  have hthird : (2 : ℤ) * 0 + 2 = 2 * 1 := by norm_num
  rw [hlast, hthird, atomRel_two_mul]
  norm_num

/-- The odd base case, as a relator. All four indices are odd, so `atom_odd` reduces every atom
and no reasoning about truncated division survives. The source proves the corresponding
equivalence under `set_option allowUnsafeReducibility true` together with
`attribute [local reducible] Nat.rawCast`; putting the indices in `2 * _ + 1` form removes the
need for either. -/
private theorem atomRel_odd_eq_rel (k : ℤ) :
    atomRel W (2 * k + 1) (2 * (k - 1) + 1) ((2 * k + 1) % 2 + 2) ((2 * k + 1) % 2)
      = rel W (k + 1) (k - 1) 1 0 := by
  have hlast : ((2 * k + 1) % 2 : ℤ) = 2 * 0 + 1 := by omega
  have hthird : (2 : ℤ) * 0 + 1 + 2 = 2 * 1 + 1 := by norm_num
  rw [hlast, hthird]
  simp_rw [atomRel, atom_odd, rel]
  ring_nf

/-- **At a gap of exactly two the relator vanishes at the minimal pair.** This is where the
induction bottoms out: the odd recurrence supplies the even first index and the even recurrence
the odd one. -/
private theorem atomRel_eq_zero_of_gap_two
    (oddRec : ∀ m : ℤ, 2 ≤ m → rel W (m + 1) m 1 0 = 0)
    (evenRec : ∀ m : ℤ, 3 ≤ m → rel W (m + 1) (m - 1) 1 0 = 0) {a b : ℤ} (h6 : 6 ≤ a)
    (hb : b + 2 = a) :
    atomRel W a b (a % 2 + 2) (a % 2) = 0 := by
  rcases Int.emod_two_eq_zero_or_one a with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
    -- `atomRel_even_eq_rel` is stated with its second index in `2 * _` form, which is what lets
    -- `atomRel_two_mul` reduce every atom; put `b` in that form before rewriting.
    obtain rfl : b = 2 * (k - 1) := by omega
    rw [atomRel_even_eq_rel]
    simpa using oddRec (k - 1) (by omega)
  · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
    -- Likewise `atomRel_odd_eq_rel` wants `2 * _ + 1`, which is what lets `atom_odd` reduce each
    -- atom without any reasoning about truncated division.
    obtain rfl : b = 2 * (k - 1) + 1 := by omega
    rw [atomRel_odd_eq_rel]
    exact evenRec k (by omega)

/-- **The descent.** The two doubling recurrences, holding from `m = 2` and `m = 3` on, force the
full four-index relation at every valid quadruple. The induction is on the largest index: below
`6` no valid quadruple exists, and above it `atomRelVanishes_of_min` reduces to the minimal
pair, where either the gap `b + 2 < a` admits the transfer down to a smaller first index, or
`b + 2 = a` lands on one of the two base cases according to parity. -/
private theorem atomRelVanishes_of_rel (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m : ℤ, 2 ≤ m → rel W (m + 1) m 1 0 = 0)
    (evenRec : ∀ m : ℤ, 3 ≤ m → rel W (m + 1) (m - 1) 1 0 = 0) :
    ∀ a b c d : ℤ, AtomRelVanishes W a b c d := by
  intro a
  induction a using Int.strongRec (m := 6)
  next a ha =>
    intro b c d same anti
    exact absurd ha (not_lt.mpr (six_le_of_parity_of_nonnegStrictAnti₄ same anti))
  next a h6 ih =>
    intro b c d
    refine atomRelVanishes_of_min one two ?_ b c d
    intro a' b' haa
    rcases haa.lt_or_eq with hlt | rfl
    · exact ih a' hlt b' _ _
    intro same anti
    obtain ⟨h0, h1, h2, h3⟩ := (nonnegStrictAnti₄_iff _ _ _ _).mp anti
    have hpb := same.2.1
    -- `b'` and `a'` share a parity and `b' < a'`, so the gap is at least two. A wider gap can be
    -- transferred down to a smaller first index; a gap of exactly two is where the recurrences
    -- live, and is the only place the induction bottoms out.
    have hgap : b' + 2 < a' ∨ b' + 2 = a' := by omega
    rcases hgap with hb | hb
    · rw [← atomRel_avg_sub W same, ← atomRel_abs₄]
      exact ih _ (by omega) _ _ _ (parity_abs_avg_sub same)
        (nonnegStrictAnti₄_abs_avg_sub h1 (by omega) h2 h3)
    · exact atomRel_eq_zero_of_gap_two oddRec evenRec (by omega) hb

/-- **Four pairwise distinct nonnegative indices of one parity, in any order.** The tuple is
sorted by `Tuple.sort` and the relator read off the sorted order, `atomRelFin4_perm` supplying the
sign. No index is pinned at `0` here, so there is no distinguished minimum and the sorting needs
the general permutation argument rather than the six orderings of three free indices. -/
private theorem atomRelFin4_eq_zero_of_injective (odd : W.Odd)
    (descent : ∀ a b c d : ℤ, AtomRelVanishes W a b c d) {t : Fin 4 → ℤ}
    (nonneg : ∀ i, 0 ≤ t i) (par : ∀ i j, t i % 2 = t j % 2) (inj : Function.Injective t) :
    atomRelFin4 W t = 0 := by
  set σ : Equiv.Perm (Fin 4) := Fin.revPerm.trans (Tuple.sort t) with hσ
  -- `t ∘ Tuple.sort t` is monotone and injective, hence strictly monotone; precomposing with the
  -- reversal turns that into the strict decrease the descent consumes.
  have hstrict : StrictMono (t ∘ Tuple.sort t) :=
    (Tuple.monotone_sort t).strictMono_of_injective (inj.comp (Tuple.sort t).injective)
  have hanti : ∀ i j : Fin 4, i < j → (t ∘ σ) j < (t ∘ σ) i := fun i j hij ↦ by
    simpa [hσ, Function.comp_assoc] using hstrict (Fin.rev_lt_rev.mpr hij)
  have hzero : atomRelFin4 W (t ∘ σ) = 0 := by
    rw [atomRelFin4_def]
    refine descent _ _ _ _ ⟨par _ _, par _ _, par _ _⟩ ?_
    rw [nonnegStrictAnti₄_iff]
    exact ⟨nonneg _, hanti 2 3 (by decide), hanti 1 2 (by decide), hanti 0 1 (by decide)⟩
  rw [atomRelFin4_perm odd σ t] at hzero
  exact (smul_eq_zero_iff_eq (Equiv.Perm.sign σ)).mp hzero

/-- **The relator vanishes at any quadruple of one parity.** All four indices are made
nonnegative by sign equivariance, a coincidence between any two is one of Mathlib's
`atomRel_same` lemmas, and the remaining pairwise-distinct case is sorted. This is the net
statement, and the only reduction the file needs: the sequence case is its `d = 0` instance. -/
private theorem atomRel_eq_zero_of_parity (odd : W.Odd) (zero : W 0 = 0)
    (descent : ∀ a b c d : ℤ, AtomRelVanishes W a b c d) {a b c d : ℤ}
    (parity : d % 2 = a % 2 ∧ d % 2 = b % 2 ∧ d % 2 = c % 2) :
    atomRel W a b c d = 0 := by
  obtain ⟨pa, pb, pc⟩ := parity
  rw [← atomRel_abs₁ odd, ← atomRel_abs₂ odd, ← atomRel_abs₃ odd, ← atomRel_abs₄]
  by_cases hab : |a| = |b|
  · rw [hab, atomRel_same₁₂]; simp [zero]
  by_cases hac : |a| = |c|
  · rw [← hac, atomRel_same₁₃ odd]; simp [zero]
  by_cases had : |a| = |d|
  · rw [← had, atomRel_same₁₄ odd]; simp [zero]
  by_cases hbc : |b| = |c|
  · rw [← hbc, atomRel_same₂₃]; simp [zero]
  by_cases hbd : |b| = |d|
  · rw [← hbd, atomRel_same₂₄ odd]; simp [zero]
  by_cases hcd : |c| = |d|
  · rw [← hcd, atomRel_same₃₄]; simp [zero]
  have habs : ∀ x : ℤ, |x| % 2 = x % 2 := fun _ ↦ Int.abs_modEq_two
  have hpar : ∀ i j : Fin 4, (![|a|, |b|, |c|, |d|] : Fin 4 → ℤ) i % 2 =
      (![|a|, |b|, |c|, |d|] : Fin 4 → ℤ) j % 2 := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [habs] <;> omega
  have hinj : Function.Injective (![|a|, |b|, |c|, |d|] : Fin 4 → ℤ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hzero := atomRelFin4_eq_zero_of_injective odd descent (t := ![|a|, |b|, |c|, |d|])
    (fun i ↦ by fin_cases i <;> simp [abs_nonneg]) hpar hinj
  -- `atomRelFin4_def` is the bridge back to `atomRel`; `simp` then only reduces the projections.
  rw [atomRelFin4_def] at hzero
  simpa using hzero

/-- **An elliptic net from the two doubling recurrences.** A sequence that is odd, vanishes at
`0`, has `W 1` and `W 2` nonzerodivisors, and satisfies the odd recurrence from `m = 2` and the
even one from `m = 3`, satisfies the full four-index relation at *every* quadruple. -/
theorem of_rel (odd : W.Odd) (zero : W 0 = 0) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m : ℤ, 2 ≤ m → rel W (m + 1) m 1 0 = 0)
    (evenRec : ∀ m : ℤ, 3 ≤ m → rel W (m + 1) (m - 1) 1 0 = 0) :
    IsEllipticNet W := by
  -- `rel_eq` writes `rel W p q r s` as the relator at `(2p + s, 2q + s, 2r + s, s)`, whose four
  -- indices are all congruent to `s`, so this is `atomRel_eq_zero_of_parity` at that quadruple.
  intro p q r s
  rw [rel_eq]
  exact atomRel_eq_zero_of_parity odd zero (atomRelVanishes_of_rel one two oddRec evenRec)
    ⟨by omega, by omega, by omega⟩

end IsEllipticNet

/-- **Being an elliptic net is exactly satisfying the two doubling recurrences.** For a sequence
that is odd, vanishes at `0` and has `W 1`, `W 2` nonzerodivisors, the **four**-index relation at
every quadruple is equivalent to the odd recurrence from `m = 2` and the even one from `m = 3` —
finitely many equations per index rather than a condition on quadruples.

Under these hypotheses, therefore, being an elliptic net and being an elliptic sequence are the
same condition. They are not the same condition in general: `normEDS b c d` at arbitrary
parameters need not have `W 2 = b` a nonzerodivisor, and `NormEDS.lean` obtains the net there
without this equivalence. -/
theorem isEllipticNet_iff {R : Type*} [CommRing R] {W : ℤ → R} (odd : W.Odd) (zero : W 0 = 0)
    (one : W 1 ∈ nonZeroDivisors R) (two : W 2 ∈ nonZeroDivisors R) :
    IsEllipticNet W ↔
      (∀ m : ℤ, 2 ≤ m → W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3)
        ∧ ∀ m : ℤ, 3 ≤ m → W (2 * m) * W 2 * W 1 ^ 2 =
            W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2) := by
  refine ⟨fun h ↦ ⟨fun m _ ↦ h.isEllipticSequence.rel_odd m,
    fun m _ ↦ h.isEllipticSequence.rel_even m⟩, fun ⟨hodd, heven⟩ ↦ ?_⟩
  refine IsEllipticNet.of_rel odd zero one two (fun m hm ↦ ?_) fun m hm ↦ ?_
  · rw [IsEllipticNet.rel_odd]
    linear_combination hodd m hm
  · rw [IsEllipticNet.rel_even]
    linear_combination heven m hm

/-- **Being an elliptic sequence is exactly satisfying the two doubling recurrences.** For a
sequence that is odd, vanishes at `0` and has `W 1`, `W 2` nonzerodivisors, the whole
three-index relation is equivalent to the odd recurrence from `m = 2` and the even one from
`m = 3` — finitely many equations per index rather than a condition on triples.

This is the classical statement, about the predicate `IsEllipticSequence`; `isEllipticNet_iff`
is its four-index strengthening. -/
theorem isEllipticSequence_iff {R : Type*} [CommRing R] {W : ℤ → R} (odd : W.Odd) (zero : W 0 = 0)
    (one : W 1 ∈ nonZeroDivisors R) (two : W 2 ∈ nonZeroDivisors R) :
    IsEllipticSequence W ↔
      (∀ m : ℤ, 2 ≤ m → W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3)
        ∧ ∀ m : ℤ, 3 ≤ m → W (2 * m) * W 2 * W 1 ^ 2 =
            W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2) :=
  ⟨fun h ↦ ⟨fun m _ ↦ h.rel_odd m, fun m _ ↦ h.rel_even m⟩,
    fun h ↦ ((isEllipticNet_iff odd zero one two).mpr h).isEllipticSequence⟩
