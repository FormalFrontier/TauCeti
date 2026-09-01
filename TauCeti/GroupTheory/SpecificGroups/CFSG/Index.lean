/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.OfMap

/-!
# Indices for the classification of finite simple groups

This file defines the parameters and indexing types for the eventual statement of the
classification of finite simple groups. The Lie-type index records the family, rank, and finite
field parameter as data. Its validity predicate first imposes the conventional rank and small-field
ranges and then removes the six remaining duplicate representatives. A Lie-type index also
determines its underlying untwisted Dynkin diagram, characteristic, and Frobenius parameter.

The twenty-six sporadic names and the four-way `TauCeti.CFSGIndex` complete the indexing layer. No
definition here asserts that a named group is finite or simple, and the group carriers themselves
belong to later construction milestones.

The twisted families use the Gorenstein--Lyons--Solomon and ATLAS small-field convention. Thus
`twistedA 2 q` denotes `²A₂(q)`, with a matrix realization over the field of `q²` elements, while
`q` itself is the Frobenius parameter. The Suzuki--Ree families instead record `m` in the field
order `p ^ (2 * m + 1)`.

## Main definitions

* `TauCeti.PrimePower`: a prime and positive exponent, retaining the data needed for a finite field.
* `TauCeti.LieTypeIndex` and `TauCeti.LieTypeIndex.Valid`: the Lie families and their preferred
  parameter range.
* `TauCeti.ValidLieTypeIndex`, `TauCeti.SuzukiReeIndex`, `TauCeti.GraphTwistedIndex`,
  `TauCeti.TypeALieIndex`, `TauCeti.TypeCLieIndex`, `TauCeti.TypeE6LieIndex`,
  `TauCeti.SuzukiLieIndex`, `TauCeti.TypeDDiagramLieIndex`, `TauCeti.TypeDLieIndex`,
  `TauCeti.TypeTwistedDLieIndex`, `TauCeti.TypeTrialityD4LieIndex`,
  `TauCeti.RankTwoBLieIndex`, `TauCeti.TypeB2LieIndex`, and
  `TauCeti.UnimodularLieIndex`: the restricted domains consumed by later carrier and endomorphism
  constructions.
* `TauCeti.SporadicName`: the conventional twenty-six sporadic names.
* `TauCeti.CFSGIndex`: cyclic, alternating, Lie-type, and sporadic entries in the classification
  list.

## References

This is item I0 of `TauCetiRoadmap/CFSGStatement/README.md`. The family names and parameter
conventions, including the small isomorphism exclusions, follow Gorenstein--Lyons--Solomon,
*The Classification of the Finite Simple Groups*, and Conway et al., *Atlas of Finite Groups*.
The declaration structure and definitions adapt the human-authored formal skeleton in
`TauCetiRoadmap/CFSGStatement/Suggested.lean`.
The underlying diagrams reuse the Bourbaki-numbered `TauCeti.DynkinType` supplied by the
root-systems roadmap.

For the two families on the rank-two diagram `B₂`, the names `B₂(q)` and `²B₂(2^(2m+1))`, the
retention of the rank-two symplectic family under the `B` name, and the isomorphisms that exclude
`B₂(2)`, `B₂(3)` and `²B₂(2)` are those of Gorenstein--Lyons--Solomon, Number 1, §2.2, and of the
Atlas; the diagram itself is N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II at
rank two.
-/

public section

namespace TauCeti

/-! ## Prime powers and Lie-type families -/

/-- A prime power `p ^ exponent`, retaining the prime and positive exponent needed to construct its
finite field. Unlike the proposition `IsPrimePow`, this is parameter data rather than a property of
an already specified cardinality. -/
structure PrimePower where
  /-- The prime base of the prime power. -/
  p : ℕ
  /-- The positive exponent of the prime power. -/
  exponent : ℕ
  prime_p : p.Prime
  exponent_pos : 0 < exponent
  deriving DecidableEq

namespace PrimePower

/-- Two prime-power parameters are equal when their bases and exponents are equal. -/
@[ext]
theorem ext (q r : PrimePower) (hp : q.p = r.p) (he : q.exponent = r.exponent) : q = r := by
  cases q
  cases r
  simp_all

/-- The cardinality represented by a prime-power parameter. -/
def card (q : PrimePower) : ℕ := q.p ^ q.exponent

/-- The stored cardinality is the stored base raised to the stored exponent. -/
@[simp] lemma card_def (q : PrimePower) : q.card = q.p ^ q.exponent := (rfl)

/-- The cardinality stored by a prime-power parameter is a prime power in Mathlib's sense. -/
lemma isPrimePow_card (q : PrimePower) : IsPrimePow q.card :=
  q.prime_p.isPrimePow.pow (Nat.ne_of_gt q.exponent_pos)

end PrimePower

/-- The families of finite groups of Lie type, with ranks given by Dynkin subscripts.

The ordinary and graph-twisted constructors use the small-field GLS/ATLAS parameter `q`. The three
Suzuki--Ree constructors record the integer `m` in field order `p ^ (2 * m + 1)`. The Tits group
`²F₄(2)'` is listed separately from the uniform Ree family. -/
inductive LieTypeIndex where
  | A (rank : ℕ) (q : PrimePower)
  | twistedA (rank : ℕ) (q : PrimePower)
  | B (rank : ℕ) (q : PrimePower)
  | C (rank : ℕ) (q : PrimePower)
  | D (rank : ℕ) (q : PrimePower)
  | twistedD (rank : ℕ) (q : PrimePower)
  | E6 (q : PrimePower)
  | E7 (q : PrimePower)
  | E8 (q : PrimePower)
  | F4 (q : PrimePower)
  | G2 (q : PrimePower)
  | twistedE6 (q : PrimePower)
  | trialityD4 (q : PrimePower)
  | suzuki (m : ℕ)
  | reeG2 (m : ℕ)
  | reeF4 (m : ℕ)
  | tits
  deriving DecidableEq

namespace LieTypeIndex

/-- Conventional rank and small-field restrictions on the Lie-type families. These remove the
nonsimple members and systematic low-rank or characteristic-two overlaps. This is indexing data;
it does not assert finiteness or simplicity of a group.

The `B` family starts at rank two, while `C` starts at rank three and has odd characteristic. Thus
`B₂(q) = C₂(q)` is always named `B₂(q)`, and the characteristic-two coincidence
`Bₙ(q) = Cₙ(q)` is also kept only in the `B` family. -/
def InStandardRange : LieTypeIndex → Prop
  | .A rank q => 1 ≤ rank ∧ (rank = 1 → 4 ≤ q.card)
  | .twistedA rank q => 2 ≤ rank ∧ (rank = 2 → 3 ≤ q.card)
  | .B rank q => 2 ≤ rank ∧ ¬(rank = 2 ∧ q.card = 2)
  | .C rank q => 3 ≤ rank ∧ q.p ≠ 2
  | .D rank _ => 4 ≤ rank
  | .twistedD rank _ => 4 ≤ rank
  | .G2 q => 3 ≤ q.card
  | .suzuki m | .reeG2 m | .reeF4 m => 1 ≤ m
  | .E6 _ | .E7 _ | .E8 _ | .F4 _ | .twistedE6 _ | .trialityD4 _ | .tits => True

/-- Characterization of the conventional range restrictions on every Lie-type constructor. -/
@[simp] theorem inStandardRange_iff (d : LieTypeIndex) : d.InStandardRange ↔
    match d with
    | .A rank q => 1 ≤ rank ∧ (rank = 1 → 4 ≤ q.card)
    | .twistedA rank q => 2 ≤ rank ∧ (rank = 2 → 3 ≤ q.card)
    | .B rank q => 2 ≤ rank ∧ ¬(rank = 2 ∧ q.card = 2)
    | .C rank q => 3 ≤ rank ∧ q.p ≠ 2
    | .D rank _ => 4 ≤ rank
    | .twistedD rank _ => 4 ≤ rank
    | .G2 q => 3 ≤ q.card
    | .suzuki m | .reeG2 m | .reeF4 m => 1 ≤ m
    | .E6 _ | .E7 _ | .E8 _ | .F4 _ | .twistedE6 _ | .trialityD4 _ | .tits => True :=
  Iff.rfl

instance : DecidablePred InStandardRange := fun d => by
  cases d <;> rw [inStandardRange_iff] <;> infer_instance

/-- Representatives omitted in favor of the alternating or Lie-type names selected by the CFSG
roadmap. After `InStandardRange`, these are the remaining small isomorphism coincidences. -/
def IsDuplicateRepresentative : LieTypeIndex → Prop
  | .A rank q =>
      (rank = 1 ∧ (q.card = 4 ∨ q.card = 5 ∨ q.card = 9)) ∨
      (rank = 2 ∧ q.card = 2) ∨ (rank = 3 ∧ q.card = 2)
  | .B rank q => rank = 2 ∧ q.card = 3
  | _ => False

/-- Characterization of the deliberately omitted duplicate representatives. -/
@[simp] theorem isDuplicateRepresentative_iff (d : LieTypeIndex) : d.IsDuplicateRepresentative ↔
    match d with
    | .A rank q =>
        (rank = 1 ∧ (q.card = 4 ∨ q.card = 5 ∨ q.card = 9)) ∨
        (rank = 2 ∧ q.card = 2) ∨ (rank = 3 ∧ q.card = 2)
    | .B rank q => rank = 2 ∧ q.card = 3
    | _ => False :=
  Iff.rfl

instance : DecidablePred IsDuplicateRepresentative := fun d => by
  cases d <;> rw [isDuplicateRepresentative_iff] <;> infer_instance

/-- A preferred Lie-type representative in the CFSG list. This is not a finiteness or simplicity
predicate. -/
def Valid (d : LieTypeIndex) : Prop :=
  d.InStandardRange ∧ ¬d.IsDuplicateRepresentative

/-- A Lie-type index is valid exactly when it is in range and is the preferred representative. -/
@[simp] theorem valid_iff (d : LieTypeIndex) : d.Valid ↔
    d.InStandardRange ∧ ¬d.IsDuplicateRepresentative :=
  Iff.rfl

instance : DecidablePred Valid := fun d => by
  rw [valid_iff]
  infer_instance

/-- An in-range `²Aₙ(q)` index has rank at least two: the reversal of a one-node diagram is trivial,
and `²A₁(q)` is not a name on the classification list. -/
theorem two_le_of_twistedA_inStandardRange {n : ℕ} {q : PrimePower}
    (h : (twistedA n q).InStandardRange) : 2 ≤ n :=
  ((inStandardRange_iff _).mp h).1

/-- An in-range `²Dₙ(q)` index has rank at least four, the range in which the `Dₙ` diagram has its
fork. -/
theorem four_le_of_twistedD_inStandardRange {n : ℕ} {q : PrimePower}
    (h : (twistedD n q).InStandardRange) : 4 ≤ n :=
  (inStandardRange_iff _).mp h

/-- Whether the Steinberg map for an index is an odd power of a half-Frobenius. This selects the
three Suzuki--Ree families and the Tits group, not the exceptional Dynkin types in general. -/
def UsesHalfFrobenius : LieTypeIndex → Prop
  | .suzuki _ | .reeG2 _ | .reeF4 _ | .tits => True
  | _ => False

/-- Characterization of the families whose Steinberg map uses a half-Frobenius. -/
@[simp] theorem usesHalfFrobenius_iff (d : LieTypeIndex) : d.UsesHalfFrobenius ↔
    match d with
    | .suzuki _ | .reeG2 _ | .reeF4 _ | .tits => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred UsesHalfFrobenius := fun d => by
  cases d <;> rw [usesHalfFrobenius_iff] <;> infer_instance

/-- Whether a Lie-type index belongs to one of the two type-A families, `A_r(q)` or `²A_r(q)`.

This is a constructor selector, not a mathematical property of a group. The small-field and
duplicate-representative restrictions come from the enclosing `TauCeti.ValidLieTypeIndex`; no
finiteness or simplicity is asserted here. -/
def IsTypeA : LieTypeIndex → Prop
  | .A _ _ | .twistedA _ _ => True
  | _ => False

/-- Characterization of the two type-A constructors. -/
@[simp] theorem isTypeA_iff (d : LieTypeIndex) : d.IsTypeA ↔
    match d with
    | .A _ _ | .twistedA _ _ => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred IsTypeA := fun d => by
  cases d <;> rw [isTypeA_iff] <;> infer_instance

/-- Neither type-A family uses a half-Frobenius, so both carry a diagram automorphism. -/
theorem not_usesHalfFrobenius_of_isTypeA {d : LieTypeIndex} (h : d.IsTypeA) :
    ¬ d.UsesHalfFrobenius := by
  cases d <;> simp_all [usesHalfFrobenius_iff]

/-- Whether a Lie-type index belongs to the untwisted family `C_r(q)`.

This is a constructor selector, not a mathematical property of a group. The rank, field, and
preferred-representative restrictions come from the enclosing `TauCeti.ValidLieTypeIndex`. -/
abbrev IsTypeC : LieTypeIndex → Prop
  | .C _ _ => True
  | _ => False

instance : DecidablePred IsTypeC := fun d => by
  cases d <;> infer_instance

/-- The untwisted type-C family does not use a half-Frobenius. -/
theorem not_usesHalfFrobenius_of_isTypeC {d : LieTypeIndex} (h : d.IsTypeC) :
    ¬ d.UsesHalfFrobenius := by
  cases d
  case C => simp only [usesHalfFrobenius_iff, not_false_eq_true]
  all_goals contradiction

/-- Whether a Lie-type index names the untwisted exceptional family `E₆(q)`.

This is a constructor selector, not a mathematical property of a group. It is false on the
graph-twisted family `²E₆(q)`, which shares the `E₆` diagram but takes a different Steinberg map,
and it asserts no finiteness or simplicity. -/
def IsTypeE6 : LieTypeIndex → Prop
  | .E6 _ => True
  | _ => False

/-- Characterization of the untwisted type-`E₆` constructor. -/
@[simp] theorem isTypeE6_iff (d : LieTypeIndex) : d.IsTypeE6 ↔
    match d with
    | .E6 _ => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred IsTypeE6 := fun d => by
  cases d <;> rw [isTypeE6_iff] <;> infer_instance

/-- The untwisted family `E₆(q)` does not use a half-Frobenius, so it carries a diagram
automorphism. -/
theorem not_usesHalfFrobenius_of_isTypeE6 {d : LieTypeIndex} (h : d.IsTypeE6) :
    ¬ d.UsesHalfFrobenius := by
  cases d <;> simp_all [usesHalfFrobenius_iff]

/-- **Every `E₆(q)` index is valid.** The `E₆` row of `InStandardRange` is unrestricted, and no
`E₆` parameter is a duplicate representative, so the family contributes one classification entry
for each prime power. -/
theorem valid_E6 (q : PrimePower) : (E6 q).Valid := by simp
/-- Whether a Lie-type index names the Suzuki family `²B₂(2^(2m+1))`.

This is a constructor selector, not a mathematical property of a group. The exclusion of `²B₂(2)`
comes from the enclosing `TauCeti.ValidLieTypeIndex`; no finiteness or simplicity is asserted
here. -/
def IsSuzuki : LieTypeIndex → Prop
  | .suzuki _ => True
  | _ => False

/-- Characterization of the Suzuki constructor. -/
@[simp] theorem isSuzuki_iff (d : LieTypeIndex) : d.IsSuzuki ↔
    match d with
    | .suzuki _ => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred IsSuzuki := fun d => by
  cases d <;> rw [isSuzuki_iff] <;> infer_instance

/-- The Suzuki family uses a half-Frobenius, so it carries no diagram automorphism. -/
theorem usesHalfFrobenius_of_isSuzuki {d : LieTypeIndex} (h : d.IsSuzuki) :
    d.UsesHalfFrobenius := by
  cases d <;> simp_all [usesHalfFrobenius_iff]

/-- Whether a Lie-type index names the untwisted family `Dₙ(q)`.

This is a constructor selector, not a mathematical property of a group. It is false on the two
twisted families `²Dₙ(q)` and `³D₄(q)`, which share the `Dₙ` diagram but take different Steinberg
maps, and it asserts no finiteness or simplicity. -/
def IsTypeD : LieTypeIndex → Prop
  | .D _ _ => True
  | _ => False

/-- Characterization of the untwisted type-`D` constructor. -/
@[simp] theorem isTypeD_iff (d : LieTypeIndex) : d.IsTypeD ↔
    match d with
    | .D _ _ => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred IsTypeD := fun d => by
  cases d <;> rw [isTypeD_iff] <;> infer_instance

/-- Whether a Lie-type index names the graph-twisted family `²Dₙ(q)`.

This is a constructor selector, not a mathematical property of a group. Following the
Gorenstein--Lyons--Solomon convention recorded above, the parameter `q` is the small field, the
matrix realization being over `𝔽_(q²)`. -/
def IsTypeTwistedD : LieTypeIndex → Prop
  | .twistedD _ _ => True
  | _ => False

/-- Characterization of the graph-twisted type-`D` constructor. -/
@[simp] theorem isTypeTwistedD_iff (d : LieTypeIndex) : d.IsTypeTwistedD ↔
    match d with
    | .twistedD _ _ => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred IsTypeTwistedD := fun d => by
  cases d <;> rw [isTypeTwistedD_iff] <;> infer_instance

/-- Whether a Lie-type index names the triality-twisted family `³D₄(q)`.

This is a constructor selector, not a mathematical property of a group. Its matrix realization is
over `𝔽_(q³)`, `q` again being the small field parameter. -/
def IsTypeTrialityD4 : LieTypeIndex → Prop
  | .trialityD4 _ => True
  | _ => False

/-- Characterization of the triality-twisted constructor. -/
@[simp] theorem isTypeTrialityD4_iff (d : LieTypeIndex) : d.IsTypeTrialityD4 ↔
    match d with
    | .trialityD4 _ => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred IsTypeTrialityD4 := fun d => by
  cases d <;> rw [isTypeTrialityD4_iff] <;> infer_instance

/-- **Every `³D₄(q)` index is valid.** The triality row of `InStandardRange` is unrestricted, and
no triality parameter is a duplicate representative, so the family contributes one classification
entry for each prime power. -/
theorem valid_trialityD4 (q : PrimePower) : (trialityD4 q).Valid := by simp

/-- The underlying untwisted Dynkin diagram. Twisted types map to the diagram from which they are
constructed, so all later root indices use the root-systems roadmap's Bourbaki numbering.

This is exposed because it appears in the *types* of the numbered data attached to an index: for
`TauCeti.GraphTwistedIndex.diagramPerm` on the `²Aₙ` branch to be `TauCeti.graphPermA n`, the type
`Fin (twistedA n q).dynkinType.rank` has to reduce to `Fin n`. -/
@[expose] def dynkinType : LieTypeIndex → DynkinType
  | .A n _ | .twistedA n _ => .A n
  | .B n _ => .B n
  | .C n _ => .C n
  | .D n _ | .twistedD n _ => .D n
  | .trialityD4 _ => .D 4
  | .E6 _ | .twistedE6 _ => .E6
  | .E7 _ => .E7
  | .E8 _ => .E8
  | .F4 _ | .reeF4 _ | .tits => .F4
  | .G2 _ | .reeG2 _ => .G2
  | .suzuki _ => .B 2

@[simp] theorem dynkinType_A (n : ℕ) (q : PrimePower) : (A n q).dynkinType = .A n :=
  by simp only [dynkinType]

@[simp] theorem dynkinType_twistedA (n : ℕ) (q : PrimePower) :
    (twistedA n q).dynkinType = .A n := by simp only [dynkinType]

@[simp] theorem dynkinType_B (n : ℕ) (q : PrimePower) : (B n q).dynkinType = .B n :=
  by simp only [dynkinType]

@[simp] theorem dynkinType_C (n : ℕ) (q : PrimePower) : (C n q).dynkinType = .C n :=
  by simp only [dynkinType]

@[simp] theorem dynkinType_D (n : ℕ) (q : PrimePower) : (D n q).dynkinType = .D n :=
  by simp only [dynkinType]

@[simp] theorem dynkinType_twistedD (n : ℕ) (q : PrimePower) :
    (twistedD n q).dynkinType = .D n := by simp only [dynkinType]

@[simp] theorem dynkinType_trialityD4 (q : PrimePower) :
    (trialityD4 q).dynkinType = .D 4 := by simp only [dynkinType]

@[simp] theorem dynkinType_E6 (q : PrimePower) : (E6 q).dynkinType = .E6 :=
  by simp only [dynkinType]

@[simp] theorem dynkinType_twistedE6 (q : PrimePower) :
    (twistedE6 q).dynkinType = .E6 := by simp only [dynkinType]

@[simp] theorem dynkinType_E7 (q : PrimePower) : (E7 q).dynkinType = .E7 :=
  by simp only [dynkinType]

@[simp] theorem dynkinType_E8 (q : PrimePower) : (E8 q).dynkinType = .E8 :=
  by simp only [dynkinType]

@[simp] theorem dynkinType_F4 (q : PrimePower) : (F4 q).dynkinType = .F4 :=
  by simp only [dynkinType]

@[simp] theorem dynkinType_reeF4 (m : ℕ) : (reeF4 m).dynkinType = .F4 := by simp only [dynkinType]

@[simp] theorem dynkinType_tits : tits.dynkinType = .F4 := by simp only [dynkinType]

@[simp] theorem dynkinType_G2 (q : PrimePower) : (G2 q).dynkinType = .G2 :=
  by simp only [dynkinType]

@[simp] theorem dynkinType_reeG2 (m : ℕ) : (reeG2 m).dynkinType = .G2 := by simp only [dynkinType]

@[simp] theorem dynkinType_suzuki (m : ℕ) : (suzuki m).dynkinType = .B 2 :=
  by simp only [dynkinType]

/-- The Lie-type families whose underlying Dynkin diagram has unimodular Cartan matrix, namely
`E₈`, `F₄` and `G₂`.

Both the untwisted families `E₈(q)`, `F₄(q)`, `G₂(q)` and the Ree families `²G₂(3^(2m+1))`,
`²F₄(2^(2m+1))` together with the Tits index are included: the predicate constrains the diagram
and not the Steinberg map. The Suzuki family is the one Suzuki--Ree constructor left out, its
diagram being `B₂`, whose Cartan matrix has determinant two. -/
def HasUnimodularDiagram : LieTypeIndex → Prop
  | .E8 _ | .F4 _ | .G2 _ | .reeG2 _ | .reeF4 _ | .tits => True
  | _ => False

/-- Characterization of the families with unimodular diagram. -/
@[simp] theorem hasUnimodularDiagram_iff (d : LieTypeIndex) : d.HasUnimodularDiagram ↔
    match d with
    | .E8 _ | .F4 _ | .G2 _ | .reeG2 _ | .reeF4 _ | .tits => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred HasUnimodularDiagram := fun d => by
  cases d <;> rw [hasUnimodularDiagram_iff] <;> infer_instance

/-- **An index has unimodular diagram exactly when its underlying Dynkin type is `E₈`, `F₄` or
`G₂`.** -/
theorem hasUnimodularDiagram_iff_dynkinType (d : LieTypeIndex) :
    d.HasUnimodularDiagram ↔
      (d.dynkinType = .E8 ∨ d.dynkinType = .F4 ∨ d.dynkinType = .G2) := by
  cases d <;> simp

/-- **The six families with unimodular diagram.** -/
theorem exists_eq_of_hasUnimodularDiagram {d : LieTypeIndex} (hd : d.HasUnimodularDiagram) :
    (∃ q : PrimePower, d = .E8 q ∨ d = .F4 q ∨ d = .G2 q) ∨
      (∃ m : ℕ, d = .reeG2 m ∨ d = .reeF4 m) ∨ d = .tits := by
  cases d <;> simp_all

/-- **The three untwisted families with unimodular diagram.** Removing the Suzuki--Ree
constructors from the previous list leaves `E₈(q)`, `F₄(q)` and `G₂(q)`. -/
theorem exists_eq_of_hasUnimodularDiagram_of_not_usesHalfFrobenius {d : LieTypeIndex}
    (hd : d.HasUnimodularDiagram) (hf : ¬d.UsesHalfFrobenius) :
    ∃ q : PrimePower, d = .E8 q ∨ d = .F4 q ∨ d = .G2 q := by
  cases d <;> simp_all

/-- The Lie-type families whose underlying Dynkin diagram is of type `Dₙ`: the untwisted family
`Dₙ(q)`, the graph-twisted family `²Dₙ(q)`, and the triality-twisted family `³D₄(q)`.

Like `TauCeti.LieTypeIndex.HasUnimodularDiagram` this constrains the diagram alone and says nothing
about the Steinberg map, which is what makes it the right hypothesis for data depending only on the
diagram: all three families share one carrier and one character lattice, and differ in the diagram
permutation their Steinberg map composes with, of order one, two and three respectively. -/
def HasTypeDDiagram : LieTypeIndex → Prop
  | .D _ _ | .twistedD _ _ | .trialityD4 _ => True
  | _ => False

/-- Characterization of the families on a type-`D` diagram. -/
@[simp] theorem hasTypeDDiagram_iff (d : LieTypeIndex) : d.HasTypeDDiagram ↔
    match d with
    | .D _ _ | .twistedD _ _ | .trialityD4 _ => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred HasTypeDDiagram := fun d => by
  cases d <;> rw [hasTypeDDiagram_iff] <;> infer_instance

/-- **An index has a type-`D` diagram exactly when its underlying Dynkin type is some `Dₙ`.** -/
theorem hasTypeDDiagram_iff_dynkinType (d : LieTypeIndex) :
    d.HasTypeDDiagram ↔ ∃ n : ℕ, d.dynkinType = .D n := by
  cases d <;> simp

/-- **The three families on a type-`D` diagram.** -/
theorem exists_eq_of_hasTypeDDiagram {d : LieTypeIndex} (hd : d.HasTypeDDiagram) :
    (∃ (n : ℕ) (q : PrimePower), d = .D n q ∨ d = .twistedD n q) ∨
      ∃ q : PrimePower, d = .trialityD4 q := by
  cases d <;> simp_all

/-- **No family on a type-`D` diagram uses a half-Frobenius**, so each of the three carries a
diagram permutation and an ordinary Steinberg map. -/
theorem not_usesHalfFrobenius_of_hasTypeDDiagram {d : LieTypeIndex} (hd : d.HasTypeDDiagram) :
    ¬ d.UsesHalfFrobenius := by
  cases d <;> simp_all [usesHalfFrobenius_iff]

/-- **A type-`D` diagram is not unimodular.** Consequently the adjoint Geck carrier, whose weights
span the whole character lattice exactly on the three types named by
`TauCeti.DynkinType.span_range_geckWeight_eq_top_iff`, is not the simply connected form on these
branches, and the type-`D` families need a carrier of their own. -/
theorem not_hasUnimodularDiagram_of_hasTypeDDiagram {d : LieTypeIndex}
    (hd : d.HasTypeDDiagram) : ¬ d.HasUnimodularDiagram := by
  cases d <;> simp_all

/-- The untwisted family `Dₙ(q)` is built on a type-`D` diagram. -/
theorem hasTypeDDiagram_of_isTypeD {d : LieTypeIndex} (h : d.IsTypeD) : d.HasTypeDDiagram := by
  cases d <;> simp_all

/-- The graph-twisted family `²Dₙ(q)` is built on a type-`D` diagram. -/
theorem hasTypeDDiagram_of_isTypeTwistedD {d : LieTypeIndex} (h : d.IsTypeTwistedD) :
    d.HasTypeDDiagram := by
  cases d <;> simp_all

/-- The triality-twisted family `³D₄(q)` is built on a type-`D` diagram. -/
theorem hasTypeDDiagram_of_isTypeTrialityD4 {d : LieTypeIndex} (h : d.IsTypeTrialityD4) :
    d.HasTypeDDiagram := by
  cases d <;> simp_all

/-- **The two families on the rank-two diagram `B₂`.** They are the untwisted `B₂(q)` and the
Suzuki family `²B₂(2^(2m+1))`; the converse inclusions are `dynkinType_B` and `dynkinType_suzuki`.
No rank-two `C` index appears: the `C` family starts at rank three in `InStandardRange`, so
`B₂(q) = C₂(q)` is always named in the `B` family. -/
theorem exists_eq_of_dynkinType_eq_B_two {d : LieTypeIndex} (hd : d.dynkinType = .B 2) :
    (∃ q : PrimePower, d = .B 2 q) ∨ ∃ m : ℕ, d = .suzuki m := by
  cases d <;> simp_all

/-- **The one untwisted family on the rank-two diagram `B₂`.** Removing the Suzuki constructor, the
one of the two families of `exists_eq_of_dynkinType_eq_B_two` using a half-Frobenius, leaves
`B₂(q)`. -/
theorem exists_eq_B_of_dynkinType_eq_B_two_of_not_usesHalfFrobenius {d : LieTypeIndex}
    (hd : d.dynkinType = .B 2) (hf : ¬d.UsesHalfFrobenius) :
    ∃ q : PrimePower, d = .B 2 q := by
  cases d <;> simp_all

/-- The characteristic of the field over which the ambient group will be constructed. -/
def characteristic : LieTypeIndex → ℕ
  | .A _ q | .twistedA _ q | .B _ q | .C _ q | .D _ q | .twistedD _ q
  | .E6 q | .E7 q | .E8 q | .F4 q | .G2 q | .twistedE6 q | .trialityD4 q => q.p
  | .reeG2 _ => 3
  | .suzuki _ | .reeF4 _ | .tits => 2

@[simp] theorem characteristic_A (n : ℕ) (q : PrimePower) : (A n q).characteristic = q.p :=
  by simp only [characteristic]

@[simp] theorem characteristic_twistedA (n : ℕ) (q : PrimePower) :
    (twistedA n q).characteristic = q.p := by simp only [characteristic]

@[simp] theorem characteristic_B (n : ℕ) (q : PrimePower) : (B n q).characteristic = q.p :=
  by simp only [characteristic]

@[simp] theorem characteristic_C (n : ℕ) (q : PrimePower) : (C n q).characteristic = q.p :=
  by simp only [characteristic]

@[simp] theorem characteristic_D (n : ℕ) (q : PrimePower) : (D n q).characteristic = q.p :=
  by simp only [characteristic]

@[simp] theorem characteristic_twistedD (n : ℕ) (q : PrimePower) :
    (twistedD n q).characteristic = q.p := by simp only [characteristic]

@[simp] theorem characteristic_E6 (q : PrimePower) : (E6 q).characteristic = q.p :=
  by simp only [characteristic]

@[simp] theorem characteristic_E7 (q : PrimePower) : (E7 q).characteristic = q.p :=
  by simp only [characteristic]

@[simp] theorem characteristic_E8 (q : PrimePower) : (E8 q).characteristic = q.p :=
  by simp only [characteristic]

@[simp] theorem characteristic_F4 (q : PrimePower) : (F4 q).characteristic = q.p :=
  by simp only [characteristic]

@[simp] theorem characteristic_G2 (q : PrimePower) : (G2 q).characteristic = q.p :=
  by simp only [characteristic]

@[simp] theorem characteristic_twistedE6 (q : PrimePower) :
    (twistedE6 q).characteristic = q.p := by simp only [characteristic]

@[simp] theorem characteristic_trialityD4 (q : PrimePower) :
    (trialityD4 q).characteristic = q.p := by simp only [characteristic]

@[simp] theorem characteristic_reeG2 (m : ℕ) : (reeG2 m).characteristic = 3 :=
  by simp only [characteristic]

@[simp] theorem characteristic_suzuki (m : ℕ) : (suzuki m).characteristic = 2 :=
  by simp only [characteristic]

@[simp] theorem characteristic_reeF4 (m : ℕ) : (reeF4 m).characteristic = 2 :=
  by simp only [characteristic]

@[simp] theorem characteristic_tits : tits.characteristic = 2 := by simp only [characteristic]

/-- The characteristic attached to a Lie-type index is prime. -/
theorem characteristic_prime (d : LieTypeIndex) : d.characteristic.Prime := by
  cases d <;> simp only [characteristic] <;>
    first | exact PrimePower.prime_p _ | decide

/-- The fact instance that equips `ZMod d.characteristic` with its field structure downstream.

It is stated for a bare index rather than for a `TauCeti.ValidLieTypeIndex`, so that it also
applies at an explicitly written constructor such as `LieTypeIndex.A rank q`: through
`Subtype.val ?d` the validated form is not a matchable instance key. -/
instance (d : LieTypeIndex) : Fact d.characteristic.Prime := ⟨d.characteristic_prime⟩

/-- The Frobenius/classification parameter `q`. For ordinary and graph-twisted families this is the
exponent in `Frob_q`, not the cardinality of the extension field used by a twisted matrix
realization. For Suzuki--Ree families it is their field order `p ^ (2 * m + 1)`. -/
def fieldOrder : LieTypeIndex → ℕ
  | .A _ q | .twistedA _ q | .B _ q | .C _ q | .D _ q | .twistedD _ q
  | .E6 q | .E7 q | .E8 q | .F4 q | .G2 q | .twistedE6 q | .trialityD4 q => q.card
  | .suzuki m | .reeF4 m => 2 ^ (2 * m + 1)
  | .reeG2 m => 3 ^ (2 * m + 1)
  | .tits => 2

@[simp] theorem fieldOrder_A (n : ℕ) (q : PrimePower) : (A n q).fieldOrder = q.card :=
  by simp only [fieldOrder]

@[simp] theorem fieldOrder_twistedA (n : ℕ) (q : PrimePower) :
    (twistedA n q).fieldOrder = q.card := by simp only [fieldOrder]

@[simp] theorem fieldOrder_B (n : ℕ) (q : PrimePower) : (B n q).fieldOrder = q.card :=
  by simp only [fieldOrder]

@[simp] theorem fieldOrder_C (n : ℕ) (q : PrimePower) : (C n q).fieldOrder = q.card :=
  by simp only [fieldOrder]

@[simp] theorem fieldOrder_D (n : ℕ) (q : PrimePower) : (D n q).fieldOrder = q.card :=
  by simp only [fieldOrder]

@[simp] theorem fieldOrder_twistedD (n : ℕ) (q : PrimePower) :
    (twistedD n q).fieldOrder = q.card := by simp only [fieldOrder]

@[simp] theorem fieldOrder_E6 (q : PrimePower) : (E6 q).fieldOrder = q.card :=
  by simp only [fieldOrder]

@[simp] theorem fieldOrder_E7 (q : PrimePower) : (E7 q).fieldOrder = q.card :=
  by simp only [fieldOrder]

@[simp] theorem fieldOrder_E8 (q : PrimePower) : (E8 q).fieldOrder = q.card :=
  by simp only [fieldOrder]

@[simp] theorem fieldOrder_F4 (q : PrimePower) : (F4 q).fieldOrder = q.card :=
  by simp only [fieldOrder]

@[simp] theorem fieldOrder_G2 (q : PrimePower) : (G2 q).fieldOrder = q.card :=
  by simp only [fieldOrder]

@[simp] theorem fieldOrder_twistedE6 (q : PrimePower) :
    (twistedE6 q).fieldOrder = q.card := by simp only [fieldOrder]

@[simp] theorem fieldOrder_trialityD4 (q : PrimePower) :
    (trialityD4 q).fieldOrder = q.card := by simp only [fieldOrder]

@[simp] theorem fieldOrder_suzuki (m : ℕ) : (suzuki m).fieldOrder = 2 ^ (2 * m + 1) :=
  by simp only [fieldOrder]

@[simp] theorem fieldOrder_reeF4 (m : ℕ) : (reeF4 m).fieldOrder = 2 ^ (2 * m + 1) :=
  by simp only [fieldOrder]

@[simp] theorem fieldOrder_reeG2 (m : ℕ) : (reeG2 m).fieldOrder = 3 ^ (2 * m + 1) :=
  by simp only [fieldOrder]

@[simp] theorem fieldOrder_tits : tits.fieldOrder = 2 := by simp only [fieldOrder]

/-- The exponent writing the Frobenius parameter `q` as a power of the characteristic. It is the
stored exponent of the prime power on the ordinary and graph-twisted branches, the odd number
`2 * m + 1` on the Suzuki--Ree branches, whose field order is `p ^ (2 * m + 1)`, and `1` on the
Tits branch, whose field order is the characteristic `2` itself.

This is not a second numeric parameter: `fieldOrder_eq_characteristic_pow` recovers `fieldOrder`
from it, and it exists because the `q`-power Frobenius of a field of characteristic `p` is the
`fieldExponent`-fold iterate of the `p`-power Frobenius. -/
def fieldExponent : LieTypeIndex → ℕ
  | .A _ q | .twistedA _ q | .B _ q | .C _ q | .D _ q | .twistedD _ q
  | .E6 q | .E7 q | .E8 q | .F4 q | .G2 q | .twistedE6 q | .trialityD4 q => q.exponent
  | .suzuki m | .reeF4 m | .reeG2 m => 2 * m + 1
  | .tits => 1

@[simp] theorem fieldExponent_A (n : ℕ) (q : PrimePower) : (A n q).fieldExponent = q.exponent :=
  by simp only [fieldExponent]

@[simp] theorem fieldExponent_twistedA (n : ℕ) (q : PrimePower) :
    (twistedA n q).fieldExponent = q.exponent := by simp only [fieldExponent]

@[simp] theorem fieldExponent_B (n : ℕ) (q : PrimePower) : (B n q).fieldExponent = q.exponent :=
  by simp only [fieldExponent]

@[simp] theorem fieldExponent_C (n : ℕ) (q : PrimePower) : (C n q).fieldExponent = q.exponent :=
  by simp only [fieldExponent]

@[simp] theorem fieldExponent_D (n : ℕ) (q : PrimePower) : (D n q).fieldExponent = q.exponent :=
  by simp only [fieldExponent]

@[simp] theorem fieldExponent_twistedD (n : ℕ) (q : PrimePower) :
    (twistedD n q).fieldExponent = q.exponent := by simp only [fieldExponent]

@[simp] theorem fieldExponent_E6 (q : PrimePower) : (E6 q).fieldExponent = q.exponent :=
  by simp only [fieldExponent]

@[simp] theorem fieldExponent_E7 (q : PrimePower) : (E7 q).fieldExponent = q.exponent :=
  by simp only [fieldExponent]

@[simp] theorem fieldExponent_E8 (q : PrimePower) : (E8 q).fieldExponent = q.exponent :=
  by simp only [fieldExponent]

@[simp] theorem fieldExponent_F4 (q : PrimePower) : (F4 q).fieldExponent = q.exponent :=
  by simp only [fieldExponent]

@[simp] theorem fieldExponent_G2 (q : PrimePower) : (G2 q).fieldExponent = q.exponent :=
  by simp only [fieldExponent]

@[simp] theorem fieldExponent_twistedE6 (q : PrimePower) :
    (twistedE6 q).fieldExponent = q.exponent := by simp only [fieldExponent]

@[simp] theorem fieldExponent_trialityD4 (q : PrimePower) :
    (trialityD4 q).fieldExponent = q.exponent := by simp only [fieldExponent]

@[simp] theorem fieldExponent_suzuki (m : ℕ) : (suzuki m).fieldExponent = 2 * m + 1 :=
  by simp only [fieldExponent]

@[simp] theorem fieldExponent_reeF4 (m : ℕ) : (reeF4 m).fieldExponent = 2 * m + 1 :=
  by simp only [fieldExponent]

@[simp] theorem fieldExponent_reeG2 (m : ℕ) : (reeG2 m).fieldExponent = 2 * m + 1 :=
  by simp only [fieldExponent]

@[simp] theorem fieldExponent_tits : tits.fieldExponent = 1 := by simp only [fieldExponent]

/-- The Frobenius parameter is the recorded power of the characteristic. -/
theorem fieldOrder_eq_characteristic_pow (d : LieTypeIndex) :
    d.fieldOrder = d.characteristic ^ d.fieldExponent := by
  cases d <;>
    simp only [fieldOrder, characteristic, fieldExponent, PrimePower.card_def, pow_one]

/-- The exponent writing the Frobenius parameter as a power of the characteristic is positive, so
the Frobenius parameter is never `1`. -/
theorem fieldExponent_pos (d : LieTypeIndex) : 0 < d.fieldExponent := by
  cases d <;>
    simp only [fieldExponent] <;>
    first | exact PrimePower.exponent_pos _ | positivity

/-- The Frobenius parameter is a positive power of a prime, hence at least two. -/
theorem one_lt_fieldOrder (d : LieTypeIndex) : 1 < d.fieldOrder := by
  rw [d.fieldOrder_eq_characteristic_pow]
  exact Nat.one_lt_pow d.fieldExponent_pos.ne' d.characteristic_prime.one_lt

/-- The Frobenius parameter of a Lie-type index is positive, being a power of its prime
characteristic. This is the form in which the parameter is read as the scaling factor of the
root-datum Frobenius. -/
theorem fieldOrder_pos (d : LieTypeIndex) : 0 < d.fieldOrder :=
  Nat.zero_lt_one.trans d.one_lt_fieldOrder

/-- The Frobenius parameter as a positive natural number, packaging `one_lt_fieldOrder`. This is
the form taken by the later constructions that scale by `q` and need it to be positive. -/
def fieldOrderPNat (d : LieTypeIndex) : ℕ+ :=
  d.fieldOrder.toPNat d.fieldOrder_pos

@[simp] theorem coe_fieldOrderPNat (d : LieTypeIndex) : (d.fieldOrderPNat : ℕ) = d.fieldOrder := by
  rw [fieldOrderPNat]
  rfl

end LieTypeIndex

/-- A Lie-type index satisfying its rank, field, and preferred-representative conditions. Later
carrier-valued constructions take this subtype, so they need no branch for an invalid Dynkin rank
or an excluded small group. -/
abbrev ValidLieTypeIndex : Type _ := {d : LieTypeIndex // d.Valid}

/-- A valid index whose Steinberg map is an odd power of a half-Frobenius: the three Suzuki--Ree
families together with the Tits group. -/
abbrev SuzukiReeIndex : Type _ := {d : ValidLieTypeIndex // d.1.UsesHalfFrobenius}

/-- A valid index whose Steinberg map uses ordinary Frobenius, possibly composed with a diagram
automorphism. The Suzuki--Ree and Tits branches are excluded. -/
abbrev GraphTwistedIndex : Type _ := {d : ValidLieTypeIndex // ¬ d.1.UsesHalfFrobenius}

/-- A valid index whose underlying Dynkin diagram has unimodular Cartan matrix: the six branches
`E₈(q)`, `F₄(q)`, `G₂(q)`, `²G₂(3^(2m+1))`, `²F₄(2^(2m+1))` and `²F₄(2)'`. These are the diagrams
on which the Geck carrier of the root-systems roadmap has full character span, so this subtype is
the domain of the lattice results that span buys. -/
abbrev UnimodularLieIndex : Type _ := {d : ValidLieTypeIndex // d.1.HasUnimodularDiagram}

/-- A validated index in one of the two type-A families `A_r(q)` and `²A_r(q)`.

The outer subtype is important: a raw type-A constructor with an excluded rank or field parameter
is not a `TypeALieIndex`. -/
abbrev TypeALieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsTypeA}

/-- A validated index in the untwisted type-`C` family `C_r(q)`.

In particular, its rank is at least three and its characteristic is not two. -/
abbrev TypeCLieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsTypeC}

/-- A validated index in the untwisted exceptional family `E₆(q)`.

Every `E₆(q)` is valid, by `TauCeti.LieTypeIndex.valid_E6`, so the outer subtype excludes nothing
here; it is retained because the carrier-valued constructions of milestone L0 take
`TauCeti.ValidLieTypeIndex`. The graph-twisted family `²E₆(q)`, which shares the diagram, is not of
this subtype. -/
abbrev TypeE6LieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsTypeE6}

/-- A validated index in the Suzuki family `²B₂(2^(2m+1))`.

The outer subtype is important: `²B₂(2)`, the parameter `m = 0`, is excluded from the
classification list. It is itself the Frobenius group of order twenty, whose derived subgroup is
cyclic of order five and is its own centre, so the derived-subgroup recipe collapses to the trivial
group rather than a simple one, and `²B₂(2)` is not a `SuzukiLieIndex`. The Suzuki--Ree relatives
`²G₂`, `²F₄` and the Tits group are excluded too; they are the other three constructors of
`TauCeti.SuzukiReeIndex`. -/
abbrev SuzukiLieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsSuzuki}

/-- A validated index on a type-`Dₙ` diagram: the untwisted `Dₙ(q)`, the graph-twisted `²Dₙ(q)`,
or the triality-twisted `³D₄(q)`.

The three families are collected because they share their carrier: the diagram, and hence the
character lattice and the group the classification recipe is run inside, depends only on this
subtype, while the family enters through the diagram permutation. Its rank is at least four, by
`TauCeti.TypeDDiagramLieIndex.four_le_rank`. -/
abbrev TypeDDiagramLieIndex : Type _ := {d : ValidLieTypeIndex // d.1.HasTypeDDiagram}

/-- A validated index in the untwisted type-`D` family `Dₙ(q)`.

The outer subtype is important: `D₂(q)` and `D₃(q)` are not names on the classification list, their
diagrams being `A₁ × A₁` and `A₃`, so they are not indices of this subtype. -/
abbrev TypeDLieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsTypeD}

/-- A validated index in the graph-twisted type-`D` family `²Dₙ(q)`, whose Steinberg map twists by
the exchange of the two fork nodes. Its rank is at least four, for the same reason as for the
untwisted family. -/
abbrev TypeTwistedDLieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsTypeTwistedD}

/-- A validated index in the triality-twisted family `³D₄(q)`, whose Steinberg map twists by the
order-three symmetry of the `D₄` diagram. Every `³D₄(q)` is valid, by
`TauCeti.LieTypeIndex.valid_trialityD4`. -/
abbrev TypeTrialityD4LieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsTypeTrialityD4}

/-- A validated index built on the rank-two diagram `B₂`: the untwisted family `B₂(q)` and the
Suzuki family `²B₂(2^(2m+1))`.

The condition constrains the diagram and not the Steinberg map, so it holds both of the untwisted
family, whose Steinberg map is the `q`-power Frobenius, and of the Suzuki family, whose Steinberg
map is an odd power of a half-Frobenius. No rank-two `C` index appears: the `C` family starts at
rank three in `InStandardRange`, so `B₂(q) = C₂(q)` is always named in the `B` family.

This is diagram-level indexing data only; it does not attach the pinned L0 carrier that both
branches will eventually consume. The outer subtype is important: `B₂(2)`, `B₂(3)` and `²B₂(2)`
are excluded from the classification list and are not indices of this subtype; those exclusions
are the small isomorphisms of Gorenstein--Lyons--Solomon, Number 1, §2.2. -/
abbrev RankTwoBLieIndex : Type _ := {d : ValidLieTypeIndex // d.1.dynkinType = .B 2}

/-- A validated index in the untwisted rank-two family `B₂(q)`. The Suzuki family, which shares the
diagram, is excluded by the outer predicate. -/
abbrev TypeB2LieIndex : Type _ := {d : RankTwoBLieIndex // ¬d.1.1.UsesHalfFrobenius}

namespace TypeALieIndex

/-- Introduce a valid untwisted type-A index. -/
abbrev ofA (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.A rank q).Valid) :
    TypeALieIndex :=
  ⟨⟨.A rank q, hvalid⟩, (LieTypeIndex.isTypeA_iff _).mpr trivial⟩

/-- Introduce a valid graph-twisted type-A index. -/
abbrev ofTwistedA (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.twistedA rank q).Valid) :
    TypeALieIndex :=
  ⟨⟨.twistedA rank q, hvalid⟩, (LieTypeIndex.isTypeA_iff _).mpr trivial⟩

/-- Every type-A index is one of the two introduction forms. This is the eliminator matching `ofA`
and `ofTwistedA`, so a consumer never repeats the case split over the other constructors. -/
theorem exists_eq_ofA_or_exists_eq_ofTwistedA (d : TypeALieIndex) :
    (∃ (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.A rank q).Valid),
        d = ofA rank q hvalid) ∨
      ∃ (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.twistedA rank q).Valid),
        d = ofTwistedA rank q hvalid := by
  obtain ⟨⟨d, hvalid⟩, hA⟩ := d
  revert hvalid hA
  cases d
  case A rank q => exact fun hvalid _ => .inl ⟨rank, q, hvalid, rfl⟩
  case twistedA rank q => exact fun hvalid _ => .inr ⟨rank, q, hvalid, rfl⟩
  all_goals exact fun _ hA => ((LieTypeIndex.isTypeA_iff _).mp hA).elim

end TypeALieIndex

namespace ValidLieTypeIndex

/-- The total Dynkin-diagram map, restricted along the valid-index coercion. -/
abbrev dynkinType (d : ValidLieTypeIndex) : DynkinType := d.1.dynkinType

/-- Every valid Lie-type index names a valid Dynkin type. -/
theorem dynkinType_valid (d : ValidLieTypeIndex) : d.1.dynkinType.Valid := by
  obtain ⟨d, hvalid⟩ := d
  rw [LieTypeIndex.valid_iff] at hvalid
  obtain ⟨hrange, -⟩ := hvalid
  cases d <;> simp only [LieTypeIndex.dynkinType] <;>
    rw [LieTypeIndex.inStandardRange_iff] at hrange <;>
    simp_all
  omega

/-- The rank of the underlying untwisted Dynkin diagram. This is derived from `dynkinType`, not
tabulated independently. -/
abbrev rank (d : ValidLieTypeIndex) : ℕ := d.dynkinType.rank

/-- The total characteristic map, restricted along the valid-index coercion. -/
abbrev characteristic (d : ValidLieTypeIndex) : ℕ := d.1.characteristic

/-- The characteristic attached to a valid Lie-type index is prime. -/
theorem characteristic_prime (d : ValidLieTypeIndex) : d.characteristic.Prime :=
  d.1.characteristic_prime

/-- The total Frobenius-parameter map, restricted along the valid-index coercion. -/
abbrev fieldOrder (d : ValidLieTypeIndex) : ℕ := d.1.fieldOrder

/-- The total field-exponent map, restricted along the valid-index coercion. -/
abbrev fieldExponent (d : ValidLieTypeIndex) : ℕ := d.1.fieldExponent

/-- The Frobenius parameter of a valid index is the recorded power of its characteristic. -/
theorem fieldOrder_eq_characteristic_pow (d : ValidLieTypeIndex) :
    d.fieldOrder = d.characteristic ^ d.fieldExponent :=
  d.1.fieldOrder_eq_characteristic_pow

/-- The field exponent of a valid index is positive. -/
theorem fieldExponent_pos (d : ValidLieTypeIndex) : 0 < d.fieldExponent :=
  d.1.fieldExponent_pos

/-- The Frobenius parameter of a valid index is positive. -/
theorem fieldOrder_pos (d : ValidLieTypeIndex) : 0 < d.fieldOrder :=
  d.1.fieldOrder_pos

end ValidLieTypeIndex

namespace TypeCLieIndex

open LieTypeIndex (inStandardRange_iff valid_iff)

/-- Introduce a valid type-`C` index. -/
abbrev ofC (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.C rank q).Valid) :
    TypeCLieIndex :=
  ⟨⟨.C rank q, hvalid⟩, trivial⟩

/-- Every type-C index is an introduction form `ofC rank q hvalid`. -/
theorem exists_eq_ofC (d : TypeCLieIndex) :
    ∃ (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.C rank q).Valid),
      d = ofC rank q hvalid := by
  obtain ⟨⟨d, hvalid⟩, hC⟩ := d
  revert hvalid hC
  cases d
  case C rank q => exact fun hvalid _ => ⟨rank, q, hvalid, rfl⟩
  all_goals exact fun _ hC => False.elim hC

/-- The rank of a validated type-`C` index is at least three. -/
theorem three_le_rank (d : TypeCLieIndex) : 3 ≤ d.1.rank := by
  obtain ⟨rank, q, hvalid, rfl⟩ := d.exists_eq_ofC
  simpa only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
    LieTypeIndex.dynkinType_C, DynkinType.rank_C] using
      ((inStandardRange_iff _).mp ((valid_iff _).mp hvalid).1).1

/-- A validated type-`C` index has characteristic different from two. -/
theorem characteristic_ne_two (d : TypeCLieIndex) : d.1.characteristic ≠ 2 := by
  obtain ⟨rank, q, hvalid, rfl⟩ := d.exists_eq_ofC
  simpa only [ValidLieTypeIndex.characteristic, LieTypeIndex.characteristic_C] using
    ((inStandardRange_iff _).mp ((valid_iff _).mp hvalid).1).2

end TypeCLieIndex

/-! ## The families on the `B₂` diagram

This section follows `ValidLieTypeIndex` rather than sitting beside `TypeALieIndex`, because
`rank_eq_two` reads the numbered data `TauCeti.ValidLieTypeIndex.rank` defined just above. -/

namespace RankTwoBLieIndex

/-- An index on the `B₂` diagram names the Dynkin type `B 2`. -/
@[simp] theorem dynkinType_eq (d : RankTwoBLieIndex) : d.1.dynkinType = .B 2 := d.2

/-- An index on the `B₂` diagram has rank two, that being the rank of `B₂`. -/
@[simp] theorem rank_eq_two (d : RankTwoBLieIndex) : d.1.rank = 2 :=
  congrArg DynkinType.rank d.dynkinType_eq

/-- Introduce the untwisted branch `B₂(q)`. -/
abbrev ofB (q : PrimePower) (hvalid : (LieTypeIndex.B 2 q).Valid) : RankTwoBLieIndex :=
  ⟨⟨.B 2 q, hvalid⟩, by simp⟩

/-- Introduce the Suzuki branch `²B₂(2^(2m+1))`. -/
abbrev ofSuzuki (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid) : RankTwoBLieIndex :=
  ⟨⟨.suzuki m, hvalid⟩, by simp⟩

/-- Every index on the `B₂` diagram is one of the two introduction forms. This is the eliminator
matching `ofB` and `ofSuzuki`, so a consumer never repeats the case split over the other
constructors. -/
theorem exists_eq_ofB_or_exists_eq_ofSuzuki (d : RankTwoBLieIndex) :
    (∃ (q : PrimePower) (hvalid : (LieTypeIndex.B 2 q).Valid), d = ofB q hvalid) ∨
      ∃ (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid), d = ofSuzuki m hvalid := by
  obtain ⟨⟨e, hvalid⟩, hdiag⟩ := d
  rcases LieTypeIndex.exists_eq_of_dynkinType_eq_B_two hdiag with ⟨q, rfl⟩ | ⟨m, rfl⟩
  · exact .inl ⟨q, hvalid, rfl⟩
  · exact .inr ⟨m, hvalid, rfl⟩

/-- The two branches are disjoint, so the eliminator above splits every index on the `B₂` diagram
into exactly one of them. -/
theorem ofB_ne_ofSuzuki (q : PrimePower) (hq : (LieTypeIndex.B 2 q).Valid) (m : ℕ)
    (hm : (LieTypeIndex.suzuki m).Valid) : ofB q hq ≠ ofSuzuki m hm := by
  simp [Subtype.ext_iff]

end RankTwoBLieIndex

namespace TypeB2LieIndex

/-- Introduce a valid untwisted index `B₂(q)`. Validity forces `4 ≤ q.card`, by
`four_le_fieldOrder` below. -/
abbrev of (q : PrimePower) (hvalid : (LieTypeIndex.B 2 q).Valid) : TypeB2LieIndex :=
  ⟨RankTwoBLieIndex.ofB q hvalid, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩

/-- Every untwisted rank-two type-`B` index is of the introduction form. -/
theorem exists_eq_of (d : TypeB2LieIndex) :
    ∃ (q : PrimePower) (hvalid : (LieTypeIndex.B 2 q).Valid), d = of q hvalid := by
  obtain ⟨⟨⟨e, hvalid⟩, hdiag⟩, hhalf⟩ := d
  obtain ⟨q, rfl⟩ :=
    LieTypeIndex.exists_eq_B_of_dynkinType_eq_B_two_of_not_usesHalfFrobenius hdiag hhalf
  exact ⟨q, hvalid, rfl⟩

/-- The field order of an untwisted rank-two type-`B` index is at least four. The two smaller prime
powers are excluded from the classification list as duplicate representatives. -/
theorem four_le_fieldOrder (d : TypeB2LieIndex) : 4 ≤ d.1.1.fieldOrder := by
  obtain ⟨q, hvalid, rfl⟩ := d.exists_eq_of
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff] at hvalid
  have h2 := q.isPrimePow_card.two_le
  simp only [ValidLieTypeIndex.fieldOrder, LieTypeIndex.fieldOrder_B]
  omega

end TypeB2LieIndex

namespace SuzukiLieIndex

/-- Introduce a valid Suzuki index `²B₂(2^(2m+1))`. Validity forces `1 ≤ m`. -/
abbrev of (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid) : SuzukiLieIndex :=
  ⟨⟨.suzuki m, hvalid⟩, (LieTypeIndex.isSuzuki_iff _).mpr trivial⟩

/-- Every Suzuki index is of the introduction form. This is the eliminator matching `of`, so a
consumer never repeats the case split over the other constructors. -/
theorem exists_eq_of (d : SuzukiLieIndex) :
    ∃ (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid), d = of m hvalid := by
  obtain ⟨⟨d, hvalid⟩, hs⟩ := d
  revert hvalid hs
  cases d
  case suzuki m => exact fun hvalid _ => ⟨m, hvalid, rfl⟩
  all_goals exact fun _ hs => ((LieTypeIndex.isSuzuki_iff _).mp hs).elim

/-- The Suzuki family is built on the rank-two diagram `B₂`. -/
@[simp] theorem dynkinType_eq (d : SuzukiLieIndex) : d.1.dynkinType = .B 2 := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  exact LieTypeIndex.dynkinType_suzuki m

/-- The Suzuki family has rank two, that being the rank of `B₂`. -/
@[simp] theorem rank_eq_two (d : SuzukiLieIndex) : d.1.rank = 2 :=
  congrArg DynkinType.rank d.dynkinType_eq

/-- The Suzuki family lives in characteristic two. -/
@[simp] theorem characteristic_eq_two (d : SuzukiLieIndex) : d.1.characteristic = 2 := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  exact LieTypeIndex.characteristic_suzuki m

/-- A Suzuki index is a Suzuki--Ree index: its Steinberg map is an odd power of a
half-Frobenius. -/
abbrev toSuzukiReeIndex (d : SuzukiLieIndex) : SuzukiReeIndex :=
  ⟨d.1, LieTypeIndex.usesHalfFrobenius_of_isSuzuki d.2⟩

end SuzukiLieIndex

/-! ## The untwisted family `E₆(q)`

This section, like the Suzuki one above, follows `ValidLieTypeIndex` because `rank_eq_six` reads
the numbered data `TauCeti.ValidLieTypeIndex.rank` defined there. -/

namespace TypeE6LieIndex

/-- Introduce the index `E₆(q)`. No validity hypothesis is taken: every `E₆` parameter is valid by
`TauCeti.LieTypeIndex.valid_E6`. -/
abbrev of (q : PrimePower) : TypeE6LieIndex :=
  ⟨⟨.E6 q, LieTypeIndex.valid_E6 q⟩, (LieTypeIndex.isTypeE6_iff _).mpr trivial⟩

/-- Every untwisted type-`E₆` index is of the introduction form. This is the eliminator matching
`of`, so a consumer never repeats the case split over the other constructors. -/
theorem exists_eq_of (d : TypeE6LieIndex) : ∃ q : PrimePower, d = of q := by
  obtain ⟨⟨d, hvalid⟩, hd⟩ := d
  revert hvalid hd
  cases d
  case E6 q => exact fun _ _ => ⟨q, rfl⟩
  all_goals exact fun _ hd => ((LieTypeIndex.isTypeE6_iff _).mp hd).elim

/-- The untwisted family `E₆(q)` is built on the diagram `E₆`. -/
@[simp] theorem dynkinType_eq (d : TypeE6LieIndex) : d.1.dynkinType = .E6 := by
  obtain ⟨q, rfl⟩ := d.exists_eq_of
  exact LieTypeIndex.dynkinType_E6 q

/-- The untwisted family `E₆(q)` has rank six, that being the rank of `E₆`. -/
@[simp] theorem rank_eq_six (d : TypeE6LieIndex) : d.1.rank = 6 :=
  congrArg DynkinType.rank d.dynkinType_eq

end TypeE6LieIndex

/-! ## The families on a type-`D` diagram

The untwisted `Dₙ(q)`, the graph-twisted `²Dₙ(q)` and the triality-twisted `³D₄(q)` are the three
classification-list families built on a `Dₙ` diagram. This section, like the two above, follows
`ValidLieTypeIndex` because the rank statements read the numbered data
`TauCeti.ValidLieTypeIndex.rank` defined there. -/

namespace TypeDDiagramLieIndex

variable (d : TypeDDiagramLieIndex)

/-- **The underlying Dynkin type of an index on a type-`D` diagram is `Dₙ` at the index's own
rank.**

It is deliberately not a `simp` lemma: the right-hand side mentions the rank, which is itself read
off the Dynkin type, so the rewrite would reintroduce its own left-hand side. -/
theorem dynkinType_eq : d.1.dynkinType = .D d.1.rank := by
  obtain ⟨n, hn⟩ := (LieTypeIndex.hasTypeDDiagram_iff_dynkinType d.1.1).mp d.2
  have hrank : d.1.rank = n := by
    simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType, hn, DynkinType.rank_D]
  rw [hrank]
  exact hn

/-- **The rank of a validated index on a type-`D` diagram is at least four.** This is the range on
which `Dₙ` is a valid Dynkin type, `D₂` being `A₁ × A₁` and `D₃` being `A₃` relabelled, and it is
the hypothesis the type-`D` carrier of the reductive-groups roadmap takes. -/
theorem four_le_rank : 4 ≤ d.1.rank :=
  DynkinType.valid_D.mp (d.dynkinType_eq ▸ d.1.dynkinType_valid)

end TypeDDiagramLieIndex

namespace TypeDLieIndex

/-- Introduce a valid untwisted type-`D` index. -/
abbrev ofD (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.D rank q).Valid) :
    TypeDLieIndex :=
  ⟨⟨.D rank q, hvalid⟩, (LieTypeIndex.isTypeD_iff _).mpr trivial⟩

/-- Every untwisted type-`D` index is an introduction form `ofD rank q hvalid`. This is the
eliminator matching `ofD`, so a consumer never repeats the case split over the other
constructors. -/
theorem exists_eq_ofD (d : TypeDLieIndex) :
    ∃ (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.D rank q).Valid),
      d = ofD rank q hvalid := by
  obtain ⟨⟨d, hvalid⟩, hd⟩ := d
  revert hvalid hd
  cases d
  case D rank q => exact fun hvalid _ => ⟨rank, q, hvalid, rfl⟩
  all_goals exact fun _ hd => ((LieTypeIndex.isTypeD_iff _).mp hd).elim

/-- The untwisted family `Dₙ(q)`, regarded as a family on a type-`D` diagram. -/
abbrev toTypeDDiagramLieIndex (d : TypeDLieIndex) : TypeDDiagramLieIndex :=
  ⟨d.1, LieTypeIndex.hasTypeDDiagram_of_isTypeD d.2⟩

end TypeDLieIndex

namespace TypeTwistedDLieIndex

/-- Introduce a valid graph-twisted type-`D` index. -/
abbrev ofTwistedD (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.twistedD rank q).Valid) :
    TypeTwistedDLieIndex :=
  ⟨⟨.twistedD rank q, hvalid⟩, (LieTypeIndex.isTypeTwistedD_iff _).mpr trivial⟩

/-- Every graph-twisted type-`D` index is an introduction form `ofTwistedD rank q hvalid`. -/
theorem exists_eq_ofTwistedD (d : TypeTwistedDLieIndex) :
    ∃ (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.twistedD rank q).Valid),
      d = ofTwistedD rank q hvalid := by
  obtain ⟨⟨d, hvalid⟩, hd⟩ := d
  revert hvalid hd
  cases d
  case twistedD rank q => exact fun hvalid _ => ⟨rank, q, hvalid, rfl⟩
  all_goals exact fun _ hd => ((LieTypeIndex.isTypeTwistedD_iff _).mp hd).elim

/-- The graph-twisted family `²Dₙ(q)`, regarded as a family on a type-`D` diagram. -/
abbrev toTypeDDiagramLieIndex (d : TypeTwistedDLieIndex) : TypeDDiagramLieIndex :=
  ⟨d.1, LieTypeIndex.hasTypeDDiagram_of_isTypeTwistedD d.2⟩

end TypeTwistedDLieIndex

namespace TypeTrialityD4LieIndex

/-- Introduce the index `³D₄(q)`. No validity hypothesis is taken: every triality parameter is
valid by `TauCeti.LieTypeIndex.valid_trialityD4`. -/
abbrev of (q : PrimePower) : TypeTrialityD4LieIndex :=
  ⟨⟨.trialityD4 q, LieTypeIndex.valid_trialityD4 q⟩,
    (LieTypeIndex.isTypeTrialityD4_iff _).mpr trivial⟩

/-- Every triality-twisted index is of the introduction form. -/
theorem exists_eq_of (d : TypeTrialityD4LieIndex) : ∃ q : PrimePower, d = of q := by
  obtain ⟨⟨d, hvalid⟩, hd⟩ := d
  revert hvalid hd
  cases d
  case trialityD4 q => exact fun _ _ => ⟨q, rfl⟩
  all_goals exact fun _ hd => ((LieTypeIndex.isTypeTrialityD4_iff _).mp hd).elim

/-- The triality-twisted family `³D₄(q)`, regarded as a family on a type-`D` diagram. -/
abbrev toTypeDDiagramLieIndex (d : TypeTrialityD4LieIndex) : TypeDDiagramLieIndex :=
  ⟨d.1, LieTypeIndex.hasTypeDDiagram_of_isTypeTrialityD4 d.2⟩

/-- The triality-twisted family `³D₄(q)` is built on the diagram `D₄`. -/
@[simp] theorem dynkinType_eq (d : TypeTrialityD4LieIndex) : d.1.dynkinType = .D 4 := by
  obtain ⟨q, rfl⟩ := d.exists_eq_of
  exact LieTypeIndex.dynkinType_trialityD4 q

/-- The triality-twisted family `³D₄(q)` has rank four, that being the rank of `D₄`. -/
@[simp] theorem rank_eq_four (d : TypeTrialityD4LieIndex) : d.1.rank = 4 :=
  congrArg DynkinType.rank d.dynkinType_eq

end TypeTrialityD4LieIndex

namespace UnimodularLieIndex

variable (d : UnimodularLieIndex)

/-- The index `E₈(q)`. -/
abbrev e8 (q : PrimePower) : UnimodularLieIndex :=
  ⟨⟨.E8 q, by simp⟩, by simp⟩

/-- The index `F₄(q)`. -/
abbrev f4 (q : PrimePower) : UnimodularLieIndex :=
  ⟨⟨.F4 q, by simp⟩, by simp⟩

/-- The index `G₂(q)`, for `q` at least three: `G₂(2)` is excluded from the classification list,
its recipe producing a group already named `²A₂(3)`. -/
abbrev g2 (q : PrimePower) (hq : 3 ≤ q.card) : UnimodularLieIndex :=
  ⟨⟨.G2 q, by
    simp only [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hq, not_false⟩⟩, by simp⟩

/-- The Ree index `²G₂(3^(2m+1))`, for `m` at least one: `²G₂(3)` is excluded from the
classification list, its recipe producing a group already named `A₁(8)`. -/
abbrev reeG2 (m : ℕ) (hm : 1 ≤ m) : UnimodularLieIndex :=
  ⟨⟨.reeG2 m, by
    simp only [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hm, not_false⟩⟩, by simp⟩

/-- The Ree index `²F₄(2^(2m+1))`, for `m` at least one: at `m = 0` the recipe returns the Tits
group `²F₄(2)'`, which the classification list carries under the separate name `tits`. -/
abbrev reeF4 (m : ℕ) (hm : 1 ≤ m) : UnimodularLieIndex :=
  ⟨⟨.reeF4 m, by
    simp only [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hm, not_false⟩⟩, by simp⟩

/-- The Tits index `²F₄(2)'`. -/
abbrev tits : UnimodularLieIndex :=
  ⟨⟨.tits, by simp⟩, by simp⟩

/-- The underlying untwisted Dynkin diagram of an index with unimodular diagram. -/
abbrev dynkinType : DynkinType := d.1.dynkinType

/-- That diagram is a valid Dynkin type, so the pinned Geck carrier of the root-systems roadmap is
available for it. -/
theorem dynkinType_valid : d.dynkinType.Valid := d.1.dynkinType_valid

/-- The underlying Dynkin type of an index with unimodular diagram is one of the three unimodular
types. -/
theorem dynkinType_eq_E8_or_eq_F4_or_eq_G2 :
    d.dynkinType = .E8 ∨ d.dynkinType = .F4 ∨ d.dynkinType = .G2 :=
  (LieTypeIndex.hasUnimodularDiagram_iff_dynkinType d.1.1).mp d.2

end UnimodularLieIndex

/-! ## Executable checks for the range conventions -/

private def q2 : PrimePower := ⟨2, 1, by decide, by decide⟩
private def q3 : PrimePower := ⟨3, 1, by decide, by decide⟩
private def q4 : PrimePower := ⟨2, 2, by decide, by decide⟩

example : ¬(LieTypeIndex.A 1 q2).InStandardRange := by
  norm_num [LieTypeIndex.inStandardRange_iff, q2]

example : (LieTypeIndex.A 1 q4).InStandardRange := by
  norm_num [LieTypeIndex.inStandardRange_iff, q4]

example : ¬(LieTypeIndex.A 1 q4).Valid := by
  norm_num [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff, q4]

example : (LieTypeIndex.twistedA 2 q3).Valid := by
  norm_num [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff, q3]

/-- The derived-subgroup recipe for `B₂(2)` yields the alternating group `A₆`, which the
classification list retains under its alternating name. -/
example : ¬(LieTypeIndex.B 2 q2).InStandardRange := by
  norm_num [LieTypeIndex.inStandardRange_iff, q2]

/-- Whenever it is otherwise admissible, the rank-two symplectic family is retained under the `B`
name. -/
example : (LieTypeIndex.B 2 q4).Valid := by
  norm_num [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff, q4]

/-- The representative `B₂(3)` is dropped in favor of the coincident unitary group `²A₃(2)`. -/
example : ¬(LieTypeIndex.B 2 q3).Valid := by
  norm_num [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff, q3]

/-- Even-characteristic type `C₃(2)` is carried by the coincident `B₃(2)` family. -/
example : ¬(LieTypeIndex.C 3 q2).InStandardRange := by
  norm_num [LieTypeIndex.inStandardRange_iff, q2]

/-- In odd characteristic the `B₃` and `C₃` families are both retained. -/
example : (LieTypeIndex.C 3 q3).Valid := by
  norm_num [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff, q3]

example : (LieTypeIndex.B 3 q3).Valid := by
  norm_num [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff, q3]

/-! ## Sporadic names and the full classification index -/

@[expose] public section

/-- The twenty-six sporadic group names. `Fi24Prime` denotes `Fi₂₄'`, and `B` and `M` denote
the Baby Monster and Monster. -/
inductive SporadicName where
  | M11 | M12 | M22 | M23 | M24
  | J1 | J2 | J3 | J4
  | HS | McL | He | Ru | Suz | ONan
  | Co1 | Co2 | Co3
  | Fi22 | Fi23 | Fi24Prime
  | HN | Ly | Th | B | M
  deriving DecidableEq

/-- The finite enumeration of the twenty-six sporadic group names. -/
instance : Fintype SporadicName :=
  Fintype.ofList
    [.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .McL, .He, .Ru, .Suz, .ONan,
      .Co1, .Co2, .Co3, .Fi22, .Fi23, .Fi24Prime, .HN, .Ly, .Th, .B, .M]
    (by intro x; cases x <;> simp)

end

/-- The sporadic-name enumeration has exactly twenty-six entries. -/
theorem card_sporadicName : Fintype.card SporadicName = 26 := by decide

/-- Indices for the preferred representatives on the CFSG list. The proof fields restrict the
cyclic and alternating parameters without asserting that any candidate group is finite or simple. -/
inductive CFSGIndex where
  | cyclic (p : ℕ) (prime_p : p.Prime)
  | alternating (degree : ℕ) (degree_ge_five : 5 ≤ degree)
  | lie (index : ValidLieTypeIndex)
  | sporadic (name : SporadicName)
  deriving DecidableEq

end TauCeti
