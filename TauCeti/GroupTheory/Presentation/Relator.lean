/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Auditable relator expressions

Finite group presentations in print use expressions such as powers and commutators, while
`FreeGroup` consumes flat words. This file provides a small expression language for transcribing
those published relators and compiles it to Mathlib's canonical signed-word representation
`List (α × Bool)`. In that representation `true` denotes a generator and `false` its inverse.

The central result, `TauCeti.Relator.toWord_toFreeGroup`, proves that compilation agrees with direct
structural interpretation in the free group. This makes the compiler a checked link between a
human-readable transcription and the relator used to define a presented group.

The representation and its interpretation reuse `FreeGroup.mk`, `FreeGroup.invRev`,
`commutatorElement`, and their compatibility with multiplication, inversion, and natural powers
from Mathlib.

## Main definitions

* `TauCeti.PresentationWord`: Mathlib's left-to-right list of signed generators.
* `TauCeti.Relator`: expressions built from generators, inverse, product, power, and commutator.
* `TauCeti.Relator.toWord`: compilation of an expression to a signed word.
* `TauCeti.Relator.length`: the length of that word, computed from the expression without
  expanding powers.
* `TauCeti.Relator.toFreeGroup`: direct structural interpretation of an expression.
* `TauCeti.Relator.conj` and `TauCeti.Relator.div`: the conjugate `s⁻¹ r s` and the relator `r s⁻¹`
  by which a source states an equation between two words.
* `TauCeti.Relator.relatorSet`: the free-group elements denoted by a list of expressions.

## Main result

* `TauCeti.Relator.toWord_toFreeGroup`: compilation preserves the free-group element denoted by an
  expression.

## References

This file supplies the "relator expression type compiling to signed words" target of milestone S0
of `TauCetiRoadmap/CFSGStatement/README.md`. The design is not original here: the expression
language, its five constructors, the names `PresentationWord`, `Relator.toWord`,
`Relator.toFreeGroup`, and the statement of `Relator.toWord_toFreeGroup` are adapted from the
human-owned roadmap formalization in the accompanying `TauCetiRoadmap/CFSGStatement/Suggested.lean`,
where they are pinned as target signatures (with `sorry`ed proofs) by the roadmap's authors. The
adaptation replaces that file's bespoke `GeneratorLetter`/`PresentationWord.toFreeGroup` pair by
Mathlib's `List (α × Bool)` words and `FreeGroup.mk`, generalizes the generator type from `Fin n` to
an arbitrary `α`, and discharges the compilation theorem.
-/

public section

namespace TauCeti

open scoped commutatorElement

/-- A left-to-right word in generators of `α` and their formal inverses. The Boolean convention is
the one used by `FreeGroup.mk`: `true` is a generator and `false` is its inverse. -/
abbrev PresentationWord (α : Type*) := List (α × Bool)

/-- A human-readable relator expression.

The commutator constructor is Mathlib's `commutatorElement`, that is, the convention
`⁅r, s⁆ = r * s * r⁻¹ * s⁻¹`. A source using the convention
`[r, s] = r⁻¹ * s⁻¹ * r * s` should be transcribed as `comm (inv r) (inv s)`. -/
inductive Relator (α : Type*) where
  /-- A generator. -/
  | gen (x : α)
  /-- The inverse of a relator expression. -/
  | inv (r : Relator α)
  /-- The product of two relator expressions. -/
  | mul (r s : Relator α)
  /-- A relator expression raised to a natural power. -/
  | pow (r : Relator α) (n : ℕ)
  /-- The commutator `⁅r, s⁆ = r * s * r⁻¹ * s⁻¹`. -/
  | comm (r s : Relator α)
  deriving DecidableEq

namespace Relator

/-- Compile a relator expression to a flat signed word.

Inversion uses Mathlib's `FreeGroup.invRev`, which reverses the word and flips every sign. Powers
are compiled by repeating the whole word, rather than by expanding the expression recursively. The
five equation lemmas below are the public interface: the body itself stays private. -/
def toWord {α : Type*} : Relator α → PresentationWord α
  | .gen x => [(x, true)]
  | .inv r => FreeGroup.invRev r.toWord
  | .mul r s => r.toWord ++ s.toWord
  | .pow r n => (List.replicate n r.toWord).flatten
  | .comm r s => ((r.toWord ++ s.toWord) ++ FreeGroup.invRev r.toWord) ++
      FreeGroup.invRev s.toWord

/-- Compilation of a generator. -/
@[simp]
theorem toWord_gen {α : Type*} (x : α) : (Relator.gen x).toWord = [(x, true)] := by
  rw [toWord]

/-- Compilation of an inverse. -/
@[simp]
theorem toWord_inv {α : Type*} (r : Relator α) :
    (Relator.inv r).toWord = FreeGroup.invRev r.toWord := by
  rw [toWord]

/-- Compilation of a product. -/
@[simp]
theorem toWord_mul {α : Type*} (r s : Relator α) :
    (Relator.mul r s).toWord = r.toWord ++ s.toWord := by
  rw [toWord]

/-- Compilation of a natural power. -/
@[simp]
theorem toWord_pow {α : Type*} (r : Relator α) (n : ℕ) :
    (Relator.pow r n).toWord = (List.replicate n r.toWord).flatten := by
  rw [toWord]

/-- A power of a relator compiles to a cyclically reduced word as soon as its base does.

Published relators are often a single large power, and checking the base is much cheaper than
checking the expansion: the base of the longest `TauCeti.Sporadic.co1Presentation` relator has
nine letters where its expansion has three hundred and fifty-one.
`TauCeti.isCyclicallyReduced_toWord_coxeterRelator` is the case of a base with two letters. -/
theorem isCyclicallyReduced_toWord_pow {α : Type*} {r : Relator α}
    (h : FreeGroup.IsCyclicallyReduced r.toWord) (n : ℕ) :
    FreeGroup.IsCyclicallyReduced (Relator.pow r n).toWord := by
  rw [toWord_pow]
  exact h.flatten_replicate n

/-- Compilation of a commutator. -/
@[simp]
theorem toWord_comm {α : Type*} (r s : Relator α) :
    (Relator.comm r s).toWord =
      ((r.toWord ++ s.toWord) ++ FreeGroup.invRev r.toWord) ++ FreeGroup.invRev s.toWord := by
  rw [toWord]

/-- The number of signed letters in the compiled word of a relator expression, read off the
expression itself rather than from the compiled list.

A transcribed presentation checks its published letter count against
`TauCeti.GroupPresentation.totalLength`. Computing that count through `Relator.toWord` alone forces
every power to be expanded, which for a relator such as `(adefcefgh)³⁹` is hundreds of signed-letter
constructors; this function multiplies instead of repeating, and `TauCeti.Relator.length_toWord`
certifies that the two agree.

The five equations below are the interface: a module carrying transcribed relators rewrites with
them rather than unfolding this definition. -/
def length {α : Type*} : Relator α → ℕ
  | .gen _ => 1
  | .inv r => r.length
  | .mul r s => r.length + s.length
  | .pow r n => n * r.length
  | .comm r s => r.length + s.length + r.length + s.length

/-- The structural length of a generator. -/
@[simp]
theorem length_gen {α : Type*} (x : α) : (Relator.gen x).length = 1 := by
  rw [length]

/-- The structural length of an inverse. -/
@[simp]
theorem length_inv {α : Type*} (r : Relator α) : (Relator.inv r).length = r.length := by
  rw [length]

/-- The structural length of a product. -/
@[simp]
theorem length_mul {α : Type*} (r s : Relator α) :
    (Relator.mul r s).length = r.length + s.length := by
  rw [length]

/-- The structural length of a natural power. -/
@[simp]
theorem length_pow {α : Type*} (r : Relator α) (n : ℕ) :
    (Relator.pow r n).length = n * r.length := by
  rw [length]

/-- The structural length of a commutator. -/
@[simp]
theorem length_comm {α : Type*} (r s : Relator α) :
    (Relator.comm r s).length = r.length + s.length + r.length + s.length := by
  rw [length]

/-- **The structural length is the length of the compiled word.**

This is stated in the direction that rewrites away `Relator.toWord`, so a letter count of a
transcribed presentation reduces to arithmetic on the transcribed expressions. -/
@[simp]
theorem length_toWord {α : Type*} (r : Relator α) : r.toWord.length = r.length := by
  induction r with
  | gen => simp
  | inv r ih => simp [FreeGroup.invRev, ih]
  | mul r s ihr ihs => simp [ihr, ihs]
  | pow r n ih => simp [List.length_flatten, List.sum_replicate, ih]
  | comm r s ihr ihs => simp [FreeGroup.invRev, ihr, ihs, Nat.add_assoc]

/-- Interpret a relator expression directly in the free group. This is deliberately independent of
`Relator.toWord`: the comparison theorem below checks that compilation preserves meaning. As for
`Relator.toWord`, the five equation lemmas below are the public interface. -/
def toFreeGroup {α : Type*} : Relator α → FreeGroup α
  | .gen x => FreeGroup.of x
  | .inv r => r.toFreeGroup⁻¹
  | .mul r s => r.toFreeGroup * s.toFreeGroup
  | .pow r n => r.toFreeGroup ^ n
  | .comm r s => ⁅r.toFreeGroup, s.toFreeGroup⁆

/-- Interpretation of a generator. -/
@[simp]
theorem toFreeGroup_gen {α : Type*} (x : α) : (Relator.gen x).toFreeGroup = FreeGroup.of x := by
  rw [toFreeGroup]

/-- Interpretation of an inverse. -/
@[simp]
theorem toFreeGroup_inv {α : Type*} (r : Relator α) :
    (Relator.inv r).toFreeGroup = r.toFreeGroup⁻¹ := by
  rw [toFreeGroup]

/-- Interpretation of a product. -/
@[simp]
theorem toFreeGroup_mul {α : Type*} (r s : Relator α) :
    (Relator.mul r s).toFreeGroup = r.toFreeGroup * s.toFreeGroup := by
  rw [toFreeGroup]

/-- Interpretation of a natural power. -/
@[simp]
theorem toFreeGroup_pow {α : Type*} (r : Relator α) (n : ℕ) :
    (Relator.pow r n).toFreeGroup = r.toFreeGroup ^ n := by
  rw [toFreeGroup]

/-- Interpretation of a commutator. -/
@[simp]
theorem toFreeGroup_comm {α : Type*} (r s : Relator α) :
    (Relator.comm r s).toFreeGroup = ⁅r.toFreeGroup, s.toFreeGroup⁆ := by
  rw [toFreeGroup]

/-- The conjugate `s⁻¹ * r * s`, written `r ^ s` by most of the presentation literature.

Published presentations of the larger sporadic groups state many of their relators as conjugates,
so this is the shape a transcription of such a source needs. It is a derived form rather than a
sixth constructor: `Relator.toWord` and `Relator.toFreeGroup` therefore stay total on the five
constructors, and `Relator.toWord_toFreeGroup` covers it with no extra case.

The body is exposed because a module carrying transcribed relators checks properties of its list by
kernel reduction, which needs the transcription combinators to reduce. -/
@[expose]
def conj {α : Type*} (r s : Relator α) : Relator α := .mul (.inv s) (.mul r s)

/-- The relator `r * s⁻¹`, by which a source states the equation `r = s`.

A published presentation freely mixes relators with relations, writing for instance `a = (cd)⁴`
alongside `a²`; `Relator.toFreeGroup_div` computes what this denotes, so Mathlib's `div_eq_one`
says that imposing `r s⁻¹` as a relator is imposing the source's equation `r = s`.

The body is exposed for the same reason as that of `TauCeti.Relator.conj`. -/
@[expose]
def div {α : Type*} (r s : Relator α) : Relator α := .mul r (.inv s)

/-- The conjugate expression denotes the conjugate free-group element. -/
@[simp]
theorem toFreeGroup_conj {α : Type*} (r s : Relator α) :
    (r.conj s).toFreeGroup = s.toFreeGroup⁻¹ * r.toFreeGroup * s.toFreeGroup := by
  rw [conj, toFreeGroup_mul, toFreeGroup_inv, toFreeGroup_mul, mul_assoc]

/-- The equation expression denotes the quotient of the two free-group elements. -/
@[simp]
theorem toFreeGroup_div {α : Type*} (r s : Relator α) :
    (r.div s).toFreeGroup = r.toFreeGroup / s.toFreeGroup := by
  rw [div, toFreeGroup_mul, toFreeGroup_inv, div_eq_mul_inv]

/-- The compiled word of a conjugate expression. -/
@[simp]
theorem toWord_conj {α : Type*} (r s : Relator α) :
    (r.conj s).toWord = FreeGroup.invRev s.toWord ++ (r.toWord ++ s.toWord) := by
  rw [conj, toWord_mul, toWord_inv, toWord_mul]

/-- The compiled word of an equation expression. -/
@[simp]
theorem toWord_div {α : Type*} (r s : Relator α) :
    (r.div s).toWord = r.toWord ++ FreeGroup.invRev s.toWord := by
  rw [div, toWord_mul, toWord_inv]

/-- **The commutator convention of the presentation literature.** Sources that write
`[r, s] = r⁻¹ s⁻¹ r s`, rather than Mathlib's `⁅r, s⁆ = r s r⁻¹ s⁻¹` carried by `Relator.comm`, are
transcribed by applying `Relator.comm` to the two inverses; this computes what that denotes.

This is not a `simp` lemma: `Relator.toFreeGroup_comm` and `Relator.toFreeGroup_inv` already carry
its left-hand side to `⁅r.toFreeGroup⁻¹, s.toFreeGroup⁻¹⁆`, so the statement here is the expanded
word a reviewer compares against the printed source rather than a normal form. -/
theorem toFreeGroup_comm_inv_inv {α : Type*} (r s : Relator α) :
    (Relator.comm (.inv r) (.inv s)).toFreeGroup =
      r.toFreeGroup⁻¹ * s.toFreeGroup⁻¹ * r.toFreeGroup * s.toFreeGroup := by
  rw [toFreeGroup_comm, toFreeGroup_inv, toFreeGroup_inv, commutatorElement_def, inv_inv, inv_inv]

/-- The free-group elements denoted by a list of relator expressions. -/
def relatorSet {α : Type*} (l : List (Relator α)) : Set (FreeGroup α) :=
  toFreeGroup '' {x | x ∈ l}

@[simp]
theorem mem_relatorSet {α : Type*} {l : List (Relator α)} {r : FreeGroup α} :
    r ∈ relatorSet l ↔ ∃ t ∈ l, t.toFreeGroup = r :=
  Iff.rfl

/-- Appending relator lists unions their relator sets. -/
@[simp]
theorem relatorSet_append {α : Type*} (l l' : List (Relator α)) :
    relatorSet (l ++ l') = relatorSet l ∪ relatorSet l' := by
  simp only [relatorSet, List.mem_append, Set.ofPred_or, Set.image_union]

/-- **The compiled word denotes the direct interpretation of the relator expression.**

Consequently, a reviewer may check the structured `Relator` against a published presentation while
the eventual `PresentedGroup` safely uses `FreeGroup.mk r.toWord` as its defining relation. -/
@[simp]
theorem toWord_toFreeGroup {α : Type*} (r : Relator α) :
    FreeGroup.mk r.toWord = r.toFreeGroup := by
  induction r with
  | gen => rfl
  | inv r ih => rw [toWord_inv, toFreeGroup_inv, ← FreeGroup.inv_mk, ih]
  | mul r s ihr ihs => rw [toWord_mul, toFreeGroup_mul, ← FreeGroup.mul_mk, ihr, ihs]
  | pow r n ih => rw [toWord_pow, toFreeGroup_pow, ← FreeGroup.pow_mk, ih]
  | comm r s ihr ihs =>
    rw [toWord_comm, toFreeGroup_comm, commutatorElement_def, ← FreeGroup.mul_mk,
      ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, ← FreeGroup.inv_mk, ihr, ihs]

end Relator

end TauCeti
