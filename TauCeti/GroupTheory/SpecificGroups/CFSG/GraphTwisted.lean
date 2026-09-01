/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations

/-!
# Diagram permutations of the graph-twisted families

The Steinberg endomorphism of a finite group of Lie type that is not of Suzuki--Ree type is the
field Frobenius composed with a graph automorphism `γ` of the underlying pinned Chevalley group.
That automorphism is determined by a permutation of the Bourbaki-numbered simple roots, and this
file attaches that permutation to every index it can occur for, namely to every
`TauCeti.GraphTwistedIndex`.

The permutations themselves are pinned as `Fin` data by
`TauCeti/LinearAlgebra/RootSystem/DiagramPermutations.lean`. What is new here is the assignment of
one of them to each family: the identity on the nine untwisted families, the chain reversal on
`²Aₙ`, the fork exchange on `²Dₙ`, the order-two symmetry on `²E₆`, and triality on `³D₄`. The
assignment is total on `TauCeti.GraphTwistedIndex` and defined nowhere else: the Suzuki--Ree and
Tits indices are excluded by that subtype, whose defining hypothesis discharges their branches, so
no diagram permutation is invented for a family whose Steinberg map is an odd power of a
half-Frobenius.

Two properties of the assignment are proved. Each permutation is an automorphism of the Cartan
matrix of the underlying diagram, which is what lets it be realized by an automorphism of the
pinned group; and its order is the superscript in the printed family name, recorded here as
`TauCeti.GraphTwistedIndex.twistOrder`. The relations `γ ^ 2 = 1` for `²Aₙ`, `²Dₙ` and `²E₆` and
`γ ^ 3 = 1` for `³D₄` are the uniform `TauCeti.GraphTwistedIndex.diagramPerm_pow_twistOrder`.

## Main definitions

* `TauCeti.GraphTwistedIndex.diagramPerm`: the permutation of Bourbaki-numbered simple roots that
  the Steinberg map of a graph-twisted index composes with the field Frobenius.
* `TauCeti.GraphTwistedIndex.twistOrder`: the order of that permutation, which is the superscript
  in the family name.
* `TauCeti.TypeALieIndex.toGraphTwistedIndex`, `TauCeti.TypeCLieIndex.toGraphTwistedIndex`,
  `TauCeti.TypeE6LieIndex.toGraphTwistedIndex` and
  `TauCeti.TypeDDiagramLieIndex.toGraphTwistedIndex`: the two type-A families, `Aₙ(q)` and
  `²Aₙ(q)`, the untwisted type-C family, the untwisted family `E₆(q)`, and the three families on a
  type-`D` diagram, as indices of that subtype, so that the permutations above are attached to
  them.

## Main results

* `TauCeti.GraphTwistedIndex.cartanMatrix_diagramPerm`: the permutation attached to an index is an
  automorphism of the Cartan matrix of its underlying Dynkin diagram.
* `TauCeti.GraphTwistedIndex.diagramPerm_pow_twistOrder`,
  `TauCeti.GraphTwistedIndex.orderOf_diagramPerm` and
  `TauCeti.GraphTwistedIndex.twistOrder_pos`: the twist order annihilates the permutation, is
  exactly its order, and is positive.
* `TauCeti.TypeDLieIndex.diagramPerm_toGraphTwistedIndex`,
  `TauCeti.TypeTwistedDLieIndex.twistOrder_toGraphTwistedIndex` and
  `TauCeti.TypeTrialityD4LieIndex.twistOrder_toGraphTwistedIndex`: the three families on a type-`D`
  diagram are told apart by an untwisted permutation and by twist orders two and three.

## Roadmap

This is the diagram-permutation half of item L1 of `TauCetiRoadmap/CFSGStatement/README.md`, whose
table of families and permutations it transcribes; the remaining half, the equations
`γ (x_α(t)) = x_{γ α}(t)` on the simple root subgroups, waits on the pinned ambient groups of L0.
`TauCetiRoadmap/CFSGStatement/Suggested.lean` supplies the `diagramPerm` signature and its design on
the subtype that excludes the Suzuki--Ree and Tits families.
The conventions follow Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex
Characters*, and the Bourbaki numbering fixed by the root-systems roadmap.
-/

public section

namespace TauCeti

namespace GraphTwistedIndex

open LieTypeIndex (two_le_of_twistedA_inStandardRange four_le_of_twistedD_inStandardRange
  usesHalfFrobenius_iff)

/-- The permutation `γ` of the Bourbaki-numbered simple roots that the Steinberg map of a
graph-twisted index composes with the field Frobenius.

It is the identity on the untwisted families, the chain reversal `TauCeti.graphPermA` on `²Aₙ`, the
fork exchange `TauCeti.graphPermD` on `²Dₙ`, `TauCeti.graphPermE6` on `²E₆`, and
`TauCeti.trialityPermD4` on `³D₄`. The four Suzuki--Ree and Tits constructors are not indices of
this subtype, and their branches are closed by that hypothesis rather than by a chosen value. -/
def diagramPerm : (d : GraphTwistedIndex) → Equiv.Perm (Fin d.1.rank)
  | ⟨⟨.A _ _, _⟩, _⟩ => 1
  | ⟨⟨.B _ _, _⟩, _⟩ => 1
  | ⟨⟨.C _ _, _⟩, _⟩ => 1
  | ⟨⟨.D _ _, _⟩, _⟩ => 1
  | ⟨⟨.E6 _, _⟩, _⟩ => 1
  | ⟨⟨.E7 _, _⟩, _⟩ => 1
  | ⟨⟨.E8 _, _⟩, _⟩ => 1
  | ⟨⟨.F4 _, _⟩, _⟩ => 1
  | ⟨⟨.G2 _, _⟩, _⟩ => 1
  | ⟨⟨.twistedA n _, _⟩, _⟩ => graphPermA n
  | ⟨⟨.twistedD n _, hv⟩, _⟩ =>
      graphPermD n (by
        have := four_le_of_twistedD_inStandardRange ((LieTypeIndex.valid_iff _).mp hv).1
        omega)
  | ⟨⟨.twistedE6 _, _⟩, _⟩ => graphPermE6
  | ⟨⟨.trialityD4 _, _⟩, _⟩ => trialityPermD4
  | ⟨⟨.suzuki _, _⟩, hh⟩ | ⟨⟨.reeG2 _, _⟩, hh⟩ | ⟨⟨.reeF4 _, _⟩, hh⟩ | ⟨⟨.tits, _⟩, hh⟩ =>
      absurd ((usesHalfFrobenius_iff _).mpr trivial) hh

/-- The order of the diagram permutation of a graph-twisted index: the superscript in the printed
family name. It is `1` on the untwisted families, `2` on `²Aₙ`, `²Dₙ` and `²E₆`, and `3` on
`³D₄`. -/
def twistOrder : GraphTwistedIndex → ℕ
  | ⟨⟨.A _ _, _⟩, _⟩ => 1
  | ⟨⟨.B _ _, _⟩, _⟩ => 1
  | ⟨⟨.C _ _, _⟩, _⟩ => 1
  | ⟨⟨.D _ _, _⟩, _⟩ => 1
  | ⟨⟨.E6 _, _⟩, _⟩ => 1
  | ⟨⟨.E7 _, _⟩, _⟩ => 1
  | ⟨⟨.E8 _, _⟩, _⟩ => 1
  | ⟨⟨.F4 _, _⟩, _⟩ => 1
  | ⟨⟨.G2 _, _⟩, _⟩ => 1
  | ⟨⟨.twistedA _ _, _⟩, _⟩ => 2
  | ⟨⟨.twistedD _ _, _⟩, _⟩ => 2
  | ⟨⟨.twistedE6 _, _⟩, _⟩ => 2
  | ⟨⟨.trialityD4 _, _⟩, _⟩ => 3
  | ⟨⟨.suzuki _, _⟩, hh⟩ | ⟨⟨.reeG2 _, _⟩, hh⟩ | ⟨⟨.reeF4 _, _⟩, hh⟩ | ⟨⟨.tits, _⟩, hh⟩ =>
      absurd ((usesHalfFrobenius_iff _).mpr trivial) hh

/-! ### The pinned table

The following two families of equations are the roadmap's table of families and permutations. They
are exhaustive for `TauCeti.GraphTwistedIndex`, since the Suzuki--Ree and Tits constructors are not
indices of that subtype. -/

section Untwisted

variable {n : ℕ} {q : PrimePower}

/-- The untwisted family `Aₙ(q)` is not graph-twisted. -/
@[simp] theorem diagramPerm_A (hv : (LieTypeIndex.A n q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [diagramPerm]

@[simp] theorem twistOrder_A (hv : (LieTypeIndex.A n q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [twistOrder]

/-- The untwisted family `Bₙ(q)` is not graph-twisted. -/
@[simp] theorem diagramPerm_B (hv : (LieTypeIndex.B n q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [diagramPerm]

@[simp] theorem twistOrder_B (hv : (LieTypeIndex.B n q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [twistOrder]

/-- The untwisted family `Cₙ(q)` is not graph-twisted. -/
@[simp] theorem diagramPerm_C (hv : (LieTypeIndex.C n q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [diagramPerm]

@[simp] theorem twistOrder_C (hv : (LieTypeIndex.C n q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [twistOrder]

/-- The untwisted family `Dₙ(q)` is not graph-twisted; its fork exchange is `²Dₙ(q)`. -/
@[simp] theorem diagramPerm_D (hv : (LieTypeIndex.D n q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [diagramPerm]

@[simp] theorem twistOrder_D (hv : (LieTypeIndex.D n q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [twistOrder]

/-- The untwisted family `E₆(q)` is not graph-twisted; its diagram symmetry is `²E₆(q)`. -/
@[simp] theorem diagramPerm_E6 (hv : (LieTypeIndex.E6 q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [diagramPerm]

@[simp] theorem twistOrder_E6 (hv : (LieTypeIndex.E6 q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [twistOrder]

/-- The family `E₇(q)` is not graph-twisted; the `E₇` diagram has no nontrivial symmetry. -/
@[simp] theorem diagramPerm_E7 (hv : (LieTypeIndex.E7 q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [diagramPerm]

@[simp] theorem twistOrder_E7 (hv : (LieTypeIndex.E7 q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [twistOrder]

/-- The family `E₈(q)` is not graph-twisted; the `E₈` diagram has no nontrivial symmetry. -/
@[simp] theorem diagramPerm_E8 (hv : (LieTypeIndex.E8 q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [diagramPerm]

@[simp] theorem twistOrder_E8 (hv : (LieTypeIndex.E8 q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [twistOrder]

/-- The family `F₄(q)` is not graph-twisted; the length-exchanging symmetry of the `F₄` diagram is
not an automorphism of its Cartan matrix, and enters only through the half-Frobenius of `²F₄`. -/
@[simp] theorem diagramPerm_F4 (hv : (LieTypeIndex.F4 q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [diagramPerm]

@[simp] theorem twistOrder_F4 (hv : (LieTypeIndex.F4 q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [twistOrder]

/-- The family `G₂(q)` is not graph-twisted; the length-exchanging symmetry of the `G₂` diagram is
not an automorphism of its Cartan matrix, and enters only through the half-Frobenius of `²G₂`. -/
@[simp] theorem diagramPerm_G2 (hv : (LieTypeIndex.G2 q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [diagramPerm]

@[simp] theorem twistOrder_G2 (hv : (LieTypeIndex.G2 q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 1 := by
  simp only [twistOrder]

end Untwisted

section Twisted

variable {n : ℕ} {q : PrimePower}

/- The final `rfl` in each `diagramPerm` lemma below closes the type-level reduction from
`Fin (twistedA n q).dynkinType.rank` (and the analogous exceptional types) to the displayed `Fin`
type, using the exposed definitions of `LieTypeIndex.dynkinType` and `DynkinType.rank`. In the
`twistedD` case, proof irrelevance also identifies the two rank proofs passed to `graphPermD`. -/

/-- The unitary family `²Aₙ(q)` twists by the reversal of the `Aₙ` chain. -/
@[simp] theorem diagramPerm_twistedA (hv : (LieTypeIndex.twistedA n q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = graphPermA n := by
  simp only [diagramPerm]
  rfl

@[simp] theorem twistOrder_twistedA (hv : (LieTypeIndex.twistedA n q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 2 := by
  simp only [twistOrder]

/-- The family `²Dₙ(q)` twists by the exchange of the two fork nodes of the `Dₙ` diagram. -/
@[simp] theorem diagramPerm_twistedD (hv : (LieTypeIndex.twistedD n q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ =
      graphPermD n (by
        have := four_le_of_twistedD_inStandardRange ((LieTypeIndex.valid_iff _).mp hv).1
        omega) := by
  simp only [diagramPerm]
  rfl

@[simp] theorem twistOrder_twistedD (hv : (LieTypeIndex.twistedD n q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 2 := by
  simp only [twistOrder]

/-- The family `²E₆(q)` twists by the order-two symmetry of the `E₆` diagram. -/
@[simp] theorem diagramPerm_twistedE6 (hv : (LieTypeIndex.twistedE6 q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = graphPermE6 := by
  simp only [diagramPerm]
  rfl

@[simp] theorem twistOrder_twistedE6 (hv : (LieTypeIndex.twistedE6 q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 2 := by
  simp only [twistOrder]

/-- The family `³D₄(q)` twists by triality, the order-three symmetry of the `D₄` diagram. -/
@[simp] theorem diagramPerm_trialityD4 (hv : (LieTypeIndex.trialityD4 q).Valid) :
    diagramPerm ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = trialityPermD4 := by
  simp only [diagramPerm]
  rfl

@[simp] theorem twistOrder_trialityD4 (hv : (LieTypeIndex.trialityD4 q).Valid) :
    twistOrder ⟨⟨_, hv⟩, by simp [usesHalfFrobenius_iff]⟩ = 3 := by
  simp only [twistOrder]

end Twisted

/-! ### Properties of the assignment -/

/-- The permutation attached to a graph-twisted index is an automorphism of the Cartan matrix of
its underlying Dynkin diagram. This is what allows it to be realized, on the pinned Chevalley group
of that diagram, by an automorphism permuting the simple root subgroups accordingly. -/
@[simp] theorem cartanMatrix_diagramPerm : ∀ (d : GraphTwistedIndex) (i j : Fin d.1.rank),
    d.1.dynkinType.cartanMatrix (d.diagramPerm i) (d.diagramPerm j) =
      d.1.dynkinType.cartanMatrix i j
  | ⟨⟨.A _ _, _⟩, _⟩, _, _ | ⟨⟨.B _ _, _⟩, _⟩, _, _ | ⟨⟨.C _ _, _⟩, _⟩, _, _
  | ⟨⟨.D _ _, _⟩, _⟩, _, _ | ⟨⟨.E6 _, _⟩, _⟩, _, _ | ⟨⟨.E7 _, _⟩, _⟩, _, _
  | ⟨⟨.E8 _, _⟩, _⟩, _, _ | ⟨⟨.F4 _, _⟩, _⟩, _, _ | ⟨⟨.G2 _, _⟩, _⟩, _, _ => by
      simp only [diagramPerm, Equiv.Perm.one_apply]
  | ⟨⟨.twistedA n _, _⟩, _⟩, i, j => by
      simp only [diagramPerm]; exact cartanMatrix_A_graphPermA n i j
  | ⟨⟨.twistedD n _, hv⟩, _⟩, i, j => by
      simp only [diagramPerm]
      exact cartanMatrix_D_graphPermD n
        (four_le_of_twistedD_inStandardRange ((LieTypeIndex.valid_iff _).mp hv).1) i j
  | ⟨⟨.twistedE6 _, _⟩, _⟩, i, j => by
      simp only [diagramPerm]; exact cartanMatrix_E6_graphPermE6 i j
  | ⟨⟨.trialityD4 _, _⟩, _⟩, i, j => by
      simp only [diagramPerm]; exact cartanMatrix_D4_trialityPermD4 i j
  | ⟨⟨.suzuki _, _⟩, hh⟩, _, _ | ⟨⟨.reeG2 _, _⟩, hh⟩, _, _
  | ⟨⟨.reeF4 _, _⟩, hh⟩, _, _ | ⟨⟨.tits, _⟩, hh⟩, _, _ =>
      absurd ((usesHalfFrobenius_iff _).mpr trivial) hh

/-- The twist order of an index is exactly the order of its diagram permutation, so the superscript
in the family name is not an independent convention. -/
@[simp] theorem orderOf_diagramPerm : ∀ d : GraphTwistedIndex, orderOf d.diagramPerm = d.twistOrder
  | ⟨⟨.A _ _, _⟩, _⟩ | ⟨⟨.B _ _, _⟩, _⟩ | ⟨⟨.C _ _, _⟩, _⟩ | ⟨⟨.D _ _, _⟩, _⟩ | ⟨⟨.E6 _, _⟩, _⟩
  | ⟨⟨.E7 _, _⟩, _⟩ | ⟨⟨.E8 _, _⟩, _⟩ | ⟨⟨.F4 _, _⟩, _⟩ | ⟨⟨.G2 _, _⟩, _⟩ => by
      simp only [diagramPerm, twistOrder, orderOf_one]
  | ⟨⟨.twistedA _ _, hv⟩, _⟩ => by
      simp only [diagramPerm, twistOrder]
      exact orderOf_graphPermA
        (two_le_of_twistedA_inStandardRange ((LieTypeIndex.valid_iff _).mp hv).1)
  | ⟨⟨.twistedD n _, _⟩, _⟩ => by
      simp only [diagramPerm, twistOrder]; exact orderOf_graphPermD n _
  | ⟨⟨.twistedE6 _, _⟩, _⟩ => by simp only [diagramPerm, twistOrder]; exact orderOf_graphPermE6
  | ⟨⟨.trialityD4 _, _⟩, _⟩ => by
      simp only [diagramPerm, twistOrder]; exact orderOf_trialityPermD4
  | ⟨⟨.suzuki _, _⟩, hh⟩ | ⟨⟨.reeG2 _, _⟩, hh⟩ | ⟨⟨.reeF4 _, _⟩, hh⟩ | ⟨⟨.tits, _⟩, hh⟩ =>
      absurd ((usesHalfFrobenius_iff _).mpr trivial) hh

/-- The twist order annihilates the diagram permutation. On the twisted families this is the
relation `γ ^ 2 = 1` for `²Aₙ`, `²Dₙ` and `²E₆` and `γ ^ 3 = 1` for `³D₄` required of a Steinberg
map of the form `γ ∘ Frob_q`. -/
@[simp] theorem diagramPerm_pow_twistOrder (d : GraphTwistedIndex) :
    d.diagramPerm ^ d.twistOrder = 1 := by
  rw [← orderOf_diagramPerm d]
  exact pow_orderOf_eq_one d.diagramPerm

/-- The twist order of an index is positive, being the order of a permutation of a finite set. It is
`1`, `2` or `3`, and never `0`. -/
theorem twistOrder_pos (d : GraphTwistedIndex) : 0 < d.twistOrder := by
  rw [← orderOf_diagramPerm d]
  exact orderOf_pos d.diagramPerm

end GraphTwistedIndex

/-! ### The type-A families as graph-twisted indices -/

namespace TypeALieIndex

open LieTypeIndex (not_usesHalfFrobenius_of_isTypeA)

/-- A type-A index, regarded as an ordinary-or-graph-twisted index. Neither `Aₙ(q)` nor `²Aₙ(q)`
uses a half-Frobenius, so both carry a diagram permutation: the identity on the untwisted family
and the chain reversal on the twisted one. -/
abbrev toGraphTwistedIndex (d : TypeALieIndex) : GraphTwistedIndex :=
  ⟨d.1, not_usesHalfFrobenius_of_isTypeA d.2⟩

end TypeALieIndex

/-! ### The type-C family as graph-twisted indices -/

namespace TypeCLieIndex

open LieTypeIndex (not_usesHalfFrobenius_of_isTypeC)

/-- A type-`C` index, regarded as an ordinary-or-graph-twisted index. The untwisted family does
not use a half-Frobenius and its diagram permutation is the identity. -/
abbrev toGraphTwistedIndex (d : TypeCLieIndex) : GraphTwistedIndex :=
  ⟨d.1, not_usesHalfFrobenius_of_isTypeC d.2⟩

/-- The diagram permutation of an untwisted type-`C` index is the identity. -/
@[simp]
theorem diagramPerm_eq_one (d : TypeCLieIndex) : d.toGraphTwistedIndex.diagramPerm = 1 := by
  obtain ⟨rank, q, hvalid, rfl⟩ := d.exists_eq_ofC
  simpa only [toGraphTwistedIndex] using GraphTwistedIndex.diagramPerm_C hvalid

end TypeCLieIndex

/-! ### The untwisted family `E₆(q)` as graph-twisted indices -/

namespace TypeE6LieIndex

open LieTypeIndex (not_usesHalfFrobenius_of_isTypeE6)

/-- The untwisted family `E₆(q)`, regarded as an ordinary-or-graph-twisted index. It uses no
half-Frobenius, so it carries a diagram permutation, namely the identity. -/
abbrev toGraphTwistedIndex (d : TypeE6LieIndex) : GraphTwistedIndex :=
  ⟨d.1, not_usesHalfFrobenius_of_isTypeE6 d.2⟩

/-- **The diagram permutation of the untwisted family `E₆(q)` is the identity**, which is what
places it in the untwisted row of milestone L1's table, where the Steinberg map is `Frob_q`
outright. The nontrivial symmetry of the `E₆` diagram belongs to `²E₆(q)`. -/
@[simp]
theorem diagramPerm_toGraphTwistedIndex (d : TypeE6LieIndex) :
    d.toGraphTwistedIndex.diagramPerm = 1 := by
  obtain ⟨q, rfl⟩ := d.exists_eq_of
  exact GraphTwistedIndex.diagramPerm_E6 (LieTypeIndex.valid_E6 q)

end TypeE6LieIndex

/-! ### The families on a type-`D` diagram as graph-twisted indices

The three classification-list families on a `Dₙ` diagram all take an ordinary Steinberg map, and
they are told apart by the permutation it composes with: the identity, the fork exchange, and
triality. What is recorded below of an abstract index of each subtype is the family-defining
reading: the permutation itself on the untwisted family, where it is the identity at every rank,
and its order on the two twisted families, where the permutation lives on `Fin d.1.rank` and the
pinned `TauCeti.graphPermD` and `TauCeti.trialityPermD4` on `Fin n` and `Fin 4`. Those two
permutations are named on the constructor form by `GraphTwistedIndex.diagramPerm_twistedD` and
`GraphTwistedIndex.diagramPerm_trialityD4`, which the eliminators `exists_eq_ofTwistedD` and
`exists_eq_of` reduce an abstract index to. -/

namespace TypeDDiagramLieIndex

open LieTypeIndex (not_usesHalfFrobenius_of_hasTypeDDiagram)

/-- An index on a type-`D` diagram, regarded as an ordinary-or-graph-twisted index. None of the
three families uses a half-Frobenius, so each carries a diagram permutation. -/
abbrev toGraphTwistedIndex (d : TypeDDiagramLieIndex) : GraphTwistedIndex :=
  ⟨d.1, not_usesHalfFrobenius_of_hasTypeDDiagram d.2⟩

end TypeDDiagramLieIndex

namespace TypeDLieIndex

/-- **The diagram permutation of the untwisted family `Dₙ(q)` is the identity**, which places it in
the untwisted row of milestone L1's table, where the Steinberg map is `Frob_q` outright. The two
symmetries of the `Dₙ` diagram belong to `²Dₙ(q)` and, at rank four, to `³D₄(q)`. -/
@[simp]
theorem diagramPerm_toGraphTwistedIndex (d : TypeDLieIndex) :
    d.toTypeDDiagramLieIndex.toGraphTwistedIndex.diagramPerm = 1 := by
  obtain ⟨rank, q, hvalid, rfl⟩ := d.exists_eq_ofD
  exact GraphTwistedIndex.diagramPerm_D hvalid

end TypeDLieIndex

namespace TypeTwistedDLieIndex

/-- **The family `²Dₙ(q)` has twist order two**, its diagram permutation being the exchange of the
two fork nodes of the `Dₙ` diagram. -/
@[simp]
theorem twistOrder_toGraphTwistedIndex (d : TypeTwistedDLieIndex) :
    d.toTypeDDiagramLieIndex.toGraphTwistedIndex.twistOrder = 2 := by
  obtain ⟨rank, q, hvalid, rfl⟩ := d.exists_eq_ofTwistedD
  exact GraphTwistedIndex.twistOrder_twistedD hvalid

end TypeTwistedDLieIndex

namespace TypeTrialityD4LieIndex

/-- **The family `³D₄(q)` has twist order three**, its diagram permutation being triality, the
order-three symmetry of the `D₄` diagram that three-cycles the outer nodes and fixes the centre. It
is the one family on the classification list whose twist order is three. -/
@[simp]
theorem twistOrder_toGraphTwistedIndex (d : TypeTrialityD4LieIndex) :
    d.toTypeDDiagramLieIndex.toGraphTwistedIndex.twistOrder = 3 := by
  obtain ⟨q, rfl⟩ := d.exists_eq_of
  exact GraphTwistedIndex.twistOrder_trialityD4 (LieTypeIndex.valid_trialityD4 q)

end TypeTrialityD4LieIndex

end TauCeti
