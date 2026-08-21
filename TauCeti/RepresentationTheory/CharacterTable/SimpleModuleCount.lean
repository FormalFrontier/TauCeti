/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis
public import TauCeti.RingTheory.Semisimple.CenterDimension

/-!
# A finite group has at most as many irreducibles as conjugacy classes

Over a **splitting** field the irreducible representations of a finite group are exactly as many as
its conjugacy classes, and that equality is proved in
`TauCeti/RepresentationTheory/CharacterTable/Completeness.lean` over an algebraically closed field.
This file records the inequality, which holds over **every** field for which the group algebra is
semisimple, with no algebraic closure and no character theory:

`Nat.card (SimpleSubmoduleClasses k[G] k[G]) ≤ Nat.card (ConjClasses G)`.

Two facts meet. The class sums are a basis of the center of `k[G]`
(`TauCeti.finrank_center_monoidAlgebra`), so the center has dimension the number of conjugacy
classes; and the center of a semisimple algebra has dimension at least the number of isomorphism
classes of simple modules (`TauCeti.card_isotypicComponents_le_finrank_center`).

The inequality is what turns a *supply* of pairwise non-isomorphic simple modules, as many as there
are conjugacy classes, into a *classification*: there can be no others. That is how the Specht
modules are shown to exhaust the simple `ℚ[Sₙ]`-modules in
`TauCeti/RepresentationTheory/Symmetric/Specht/Completeness.lean`, over `ℚ`, which is not
algebraically closed.

## Main results

* `TauCeti.card_simpleSubmoduleClasses_le_card_conjClasses`: over a field with `k[G]` semisimple,
  the isomorphism classes of simple `k[G]`-modules are at most the conjugacy classes of `G`.

## References

* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §25 and §41.
* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 3, the group-algebra center and the count of irreducibles.
-/

public section

namespace TauCeti

open scoped MonoidAlgebra

variable (k G : Type*) [Field k] [Group G] [Finite G] [IsSemisimpleRing k[G]]

/-- **A finite group has at most as many irreducibles as conjugacy classes.** Over any field whose
group algebra is semisimple, the isomorphism classes of simple `k[G]`-modules are at most as many
as the conjugacy classes of `G`.

Equality is a splitting-field statement, and fails over `ℝ` already for a cyclic group of order
three, where the two nontrivial complex characters combine into a single two-dimensional real
irreducible. -/
theorem card_simpleSubmoduleClasses_le_card_conjClasses :
    Nat.card (SimpleSubmoduleClasses k[G] k[G]) ≤ Nat.card (ConjClasses G) := by
  rw [Nat.card_congr (simpleSubmoduleClassesEquiv k[G] k[G]), ← finrank_center_monoidAlgebra k G]
  exact card_isotypicComponents_le_finrank_center k k[G]

end TauCeti
