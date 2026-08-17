/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
* `TauCeti.ValidLieTypeIndex`, `TauCeti.SuzukiReeIndex`, and `TauCeti.GraphTwistedIndex`: the
  restricted domains consumed by later carrier and endomorphism constructions.
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

@[simp] lemma card_mk (p exponent : ℕ) (hp : p.Prime) (he : 0 < exponent) :
    card ⟨p, exponent, hp, he⟩ = p ^ exponent := (rfl)

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

/-- The fact instance that equips `ZMod d.characteristic` with its field structure downstream. -/
instance (d : ValidLieTypeIndex) : Fact d.characteristic.Prime := ⟨d.characteristic_prime⟩

/-- The total Frobenius-parameter map, restricted along the valid-index coercion. -/
abbrev fieldOrder (d : ValidLieTypeIndex) : ℕ := d.1.fieldOrder

end ValidLieTypeIndex

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
