/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.FreeGroup.Basic

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
* `TauCeti.Relator.toFreeGroup`: direct structural interpretation of an expression.
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

@[simp]
theorem toWord_gen {α : Type*} (x : α) : (gen x).toWord = [(x, true)] := by rw [toWord]

@[simp]
theorem toWord_inv {α : Type*} (r : Relator α) :
    (inv r).toWord = FreeGroup.invRev r.toWord := by
  rw [toWord]

@[simp]
theorem toWord_mul {α : Type*} (r s : Relator α) :
    (mul r s).toWord = r.toWord ++ s.toWord := by
  rw [toWord]

@[simp]
theorem toWord_pow {α : Type*} (r : Relator α) (n : ℕ) :
    (pow r n).toWord = (List.replicate n r.toWord).flatten := by
  rw [toWord]

@[simp]
theorem toWord_comm {α : Type*} (r s : Relator α) :
    (comm r s).toWord =
      ((r.toWord ++ s.toWord) ++ FreeGroup.invRev r.toWord) ++ FreeGroup.invRev s.toWord := by
  rw [toWord]

/-- Interpret a relator expression directly in the free group. This is deliberately independent of
`Relator.toWord`: the comparison theorem below checks that compilation preserves meaning. As for
`Relator.toWord`, the five equation lemmas below are the public interface. -/
def toFreeGroup {α : Type*} : Relator α → FreeGroup α
  | .gen x => FreeGroup.of x
  | .inv r => r.toFreeGroup⁻¹
  | .mul r s => r.toFreeGroup * s.toFreeGroup
  | .pow r n => r.toFreeGroup ^ n
  | .comm r s => ⁅r.toFreeGroup, s.toFreeGroup⁆

@[simp]
theorem toFreeGroup_gen {α : Type*} (x : α) : (gen x).toFreeGroup = FreeGroup.of x := by
  rw [toFreeGroup]

@[simp]
theorem toFreeGroup_inv {α : Type*} (r : Relator α) : (inv r).toFreeGroup = r.toFreeGroup⁻¹ := by
  rw [toFreeGroup]

@[simp]
theorem toFreeGroup_mul {α : Type*} (r s : Relator α) :
    (mul r s).toFreeGroup = r.toFreeGroup * s.toFreeGroup := by
  rw [toFreeGroup]

@[simp]
theorem toFreeGroup_pow {α : Type*} (r : Relator α) (n : ℕ) :
    (pow r n).toFreeGroup = r.toFreeGroup ^ n := by
  rw [toFreeGroup]

@[simp]
theorem toFreeGroup_comm {α : Type*} (r s : Relator α) :
    (comm r s).toFreeGroup = ⁅r.toFreeGroup, s.toFreeGroup⁆ := by
  rw [toFreeGroup]

/-- The free-group elements denoted by a list of relator expressions. -/
def relatorSet {α : Type*} (l : List (Relator α)) : Set (FreeGroup α) :=
  toFreeGroup '' {x | x ∈ l}

@[simp]
theorem mem_relatorSet {α : Type*} {l : List (Relator α)} {r : FreeGroup α} :
    r ∈ relatorSet l ↔ ∃ t ∈ l, t.toFreeGroup = r :=
  Iff.rfl

/-- Appending relator lists unions their relator sets. -/
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
