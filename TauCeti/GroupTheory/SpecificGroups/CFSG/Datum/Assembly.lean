/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Steinberg
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius

/-!
# The root-datum Steinberg map of an arbitrary valid Lie-type index

The classification list splits its Lie-type families in two according to the shape of their
Steinberg endomorphism. Thirteen of the seventeen constructors take `γ ∘ Frob_q`, the field
Frobenius composed with a pinned diagram automorphism, and the remaining four -- the Suzuki, Ree
`G₂`, Ree `F₄` and Tits indices -- take an odd power of a half-Frobenius. Each half already has its
root-datum map: `TauCeti.GraphTwistedIndex.datumSteinberg` and
`TauCeti.SuzukiReeIndex.datumSteinberg`. This file joins them into the single map
`TauCeti.ValidLieTypeIndex.datumSteinberg` defined on every valid index, and records what the two
halves have in common.

The split is `TauCeti.LieTypeIndex.UsesHalfFrobenius`, and the two subtypes it cuts out are exactly
the domains of the two constructions, so the dispatcher is a `dite` on that decidable predicate and
invents nothing on either side. The two branch equations
`TauCeti.ValidLieTypeIndex.datumSteinberg_of_usesHalfFrobenius` and
`TauCeti.ValidLieTypeIndex.datumSteinberg_of_not_usesHalfFrobenius` are what a consumer reasons
with, and since the predicate is decidable on a concrete constructor they are exhaustive, as the
worked branches at the end of the file illustrate.

## What the two halves share

Neither half is uniformly a Frobenius; on the ordinary branch the nine untwisted families are the
exception, where the diagram permutation is trivial and the Steinberg map is `Frob_q` itself, by
`TauCeti.ValidLieTypeIndex.datumSteinberg_eq_datumFrobenius_iff_of_not_usesHalfFrobenius`. What
holds in general is only an order relation on each side: a graph-twisted map raised to its twist
order is `Frob_(q ^ e)`, by
`TauCeti.GraphTwistedIndex.datumSteinberg_pow_twistOrder_eq_smulId`, and a half-Frobenius power
squares to `Frob_q`, by `TauCeti.SuzukiReeIndex.datumSteinberg_mul_self`. What is uniform is that
*some* positive power is a scaling by a positive power of the characteristic, which is
`TauCeti.ValidLieTypeIndex.exists_pow_datumSteinberg_eq_smulId`. That is the defining property of a
Steinberg endomorphism in Steinberg's sense, and on the group layer it is the reason the fixed
groups of milestone L3 are finite at all; the two exponents and the two scalars are genuinely
different, which is why the uniform statement is an existential rather than one formula.

Note that the scaling factors do not follow one rule either. The graph-twisted power is the
Frobenius of the *larger* field `𝔽_(q ^ e)`, since each of the `e` factors contributes its own `q`;
the Suzuki--Ree square is the Frobenius of the field `𝔽_q` the index itself names, since there the
recorded `q = p ^ (2 * m + 1)` is already the square of what one factor contributes.

This is the root-datum layer and not the group layer: nothing here mentions a group scheme, its
points, or a finite group.

## Main definitions

* `TauCeti.ValidLieTypeIndex.datumSteinberg`: the root-datum Steinberg map of any valid Lie-type
  index.

## Main results

* `TauCeti.ValidLieTypeIndex.datumSteinberg_def`: the dispatcher itself, for a consumer reasoning
  about both branches at once.
* `TauCeti.ValidLieTypeIndex.datumSteinberg_of_usesHalfFrobenius` and
  `TauCeti.ValidLieTypeIndex.datumSteinberg_of_not_usesHalfFrobenius`: the two branch equations,
  exhaustive because the selecting predicate is decidable.
* `TauCeti.ValidLieTypeIndex.exists_pow_datumSteinberg_eq_smulId`: some positive power of the
  Steinberg map is the scaling at a positive power of the characteristic, which is the root-datum
  form of "some power of a Steinberg endomorphism is a Frobenius".
* `TauCeti.ValidLieTypeIndex.datumSteinberg_eq_datumFrobenius_iff_of_not_usesHalfFrobenius`: on the
  thirteen ordinary constructors it degenerates to the Frobenius exactly on the nine untwisted
  families.

## Roadmap

This assembles the root-datum layer of milestones L1, "ordinary and graph Steinberg maps", and L2,
"Suzuki--Ree Steinberg maps", of `TauCetiRoadmap/CFSGStatement/README.md` into a single map on every
valid index. It is the root-datum shadow of the map named in L2's completion condition, "`steinberg`
unfolds on every branch", and does not meet that condition: the condition is about the group-layer
`TauCeti.ValidLieTypeIndex.steinberg`, an endomorphism of the points of a pinned
Chevalley--Demazure group, together with its action on root subgroups, and both remain open. That
group layer waits on the carriers of milestone L0.

What this file contributes to it is not the group-level composite. On the ordinary branch that
composite already exists in another form: `TauCeti.DynkinType.geckTwistedFrobenius` realizes
`γ ∘ Frob_q` on the points of the pinned Geck carrier, for a diagram symmetry and a field order
handed to it, and satisfies L1's simple-root-subgroup equation there. What is contributed is the
branch split and the exponents. The split `TauCeti.LieTypeIndex.UsesHalfFrobenius` is decided here
once and for every valid index, against the two subtypes that carry the two constructions, so a
consumer of a total Steinberg map has one place to reason about which shape an index takes; and the
order relations below fix the exponent and the scalar on each side, the twist order and `q ^ e` on
the ordinary branch and `2` and `q` on the half-Frobenius one. Those are the root-datum readings of
the "order relations" half of L1's completion evidence and of L2's
`steinberg(m) ^ 2 = Frob_(p ^ (2 * m + 1))`. The half-Frobenius branch has no group-level
counterpart at all yet, since the special isogeny of pinned group schemes it would compose is an
upstream Layer 9 target.

The conventions follow R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80
(1968), §11, and R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex
Characters*, §1.17.
-/

public section

namespace TauCeti

namespace ValidLieTypeIndex

variable (d : ValidLieTypeIndex)

noncomputable section

/-- **The root-datum Steinberg map of a valid Lie-type index.** It is the odd half-Frobenius power
`TauCeti.SuzukiReeIndex.datumSteinberg` on the Suzuki, Ree and Tits indices, and the composite
`γ ∘ Frob_q` of `TauCeti.GraphTwistedIndex.datumSteinberg` on the other thirteen constructors. The
selecting predicate `TauCeti.LieTypeIndex.UsesHalfFrobenius` is exactly the one whose two subtypes
are the domains of those constructions, so no map is invented on either branch. -/
def datumSteinberg :
    RootPairingIsogeny (d.dynkinType.simplyConnectedRootDatum d.dynkinType_valid)
      (d.dynkinType.simplyConnectedRootDatum d.dynkinType_valid) :=
  if h : d.1.UsesHalfFrobenius then SuzukiReeIndex.datumSteinberg ⟨d, h⟩
  else GraphTwistedIndex.datumSteinberg ⟨d, h⟩

/-- **The defining equation of the root-datum Steinberg map**, exhibiting it as the `dite` on
`TauCeti.LieTypeIndex.UsesHalfFrobenius`. This is what a consumer rewrites with to reason about both
branches at once; when the predicate is already decided one way,
`TauCeti.ValidLieTypeIndex.datumSteinberg_of_usesHalfFrobenius` and
`TauCeti.ValidLieTypeIndex.datumSteinberg_of_not_usesHalfFrobenius` are the eliminators to use
instead. -/
theorem datumSteinberg_def :
    d.datumSteinberg =
      if h : d.1.UsesHalfFrobenius then SuzukiReeIndex.datumSteinberg ⟨d, h⟩
      else GraphTwistedIndex.datumSteinberg ⟨d, h⟩ := by
  rw [datumSteinberg]

/-- **The half-Frobenius branch of the Steinberg map.** On the Suzuki, Ree `G₂`, Ree `F₄` and Tits
indices it is the odd power `τ ^ (2 * m + 1)` of the selected special isogeny. -/
theorem datumSteinberg_of_usesHalfFrobenius (h : d.1.UsesHalfFrobenius) :
    d.datumSteinberg = SuzukiReeIndex.datumSteinberg ⟨d, h⟩ := by
  rw [datumSteinberg_def, dite_eq_left h]

/-- **The ordinary branch of the Steinberg map.** On the nine untwisted families and on `²Aₙ(q)`,
`²Dₙ(q)`, `²E₆(q)` and `³D₄(q)` it is the graph automorphism after the `q`-power Frobenius. -/
theorem datumSteinberg_of_not_usesHalfFrobenius (h : ¬ d.1.UsesHalfFrobenius) :
    d.datumSteinberg = GraphTwistedIndex.datumSteinberg ⟨d, h⟩ := by
  rw [datumSteinberg_def, dite_eq_right h]

/-- **The Steinberg map of a graph-twisted index degenerates to the Frobenius exactly on the
untwisted families**, where the diagram permutation is trivial. This is
`TauCeti.GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_iff` transported through the
dispatcher. -/
theorem datumSteinberg_eq_datumFrobenius_iff_of_not_usesHalfFrobenius
    (h : ¬ d.1.UsesHalfFrobenius) :
    d.datumSteinberg = d.datumFrobenius ↔ GraphTwistedIndex.diagramPerm ⟨d, h⟩ = 1 := by
  rw [datumSteinberg_of_not_usesHalfFrobenius d h]
  exact GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_iff ⟨d, h⟩

/-- **The twist-order power of an ordinary Steinberg map is a Frobenius**: `(γ ∘ Frob_q) ^ e` is
`Frob_(q ^ e)`, the Frobenius of the degree-`e` extension of the field the index names. -/
theorem datumSteinberg_pow_twistOrder_eq_smulId_of_not_usesHalfFrobenius
    (h : ¬ d.1.UsesHalfFrobenius) :
    d.datumSteinberg ^ GraphTwistedIndex.twistOrder ⟨d, h⟩ =
      RootPairingIsogeny.smulId _
        (d.1.fieldOrderPNat ^ GraphTwistedIndex.twistOrder ⟨d, h⟩) := by
  rw [datumSteinberg_of_not_usesHalfFrobenius d h]
  exact GraphTwistedIndex.datumSteinberg_pow_twistOrder_eq_smulId ⟨d, h⟩

/-- **The square of a half-Frobenius Steinberg map is the Frobenius of the index**:
`(τ ^ (2 * m + 1)) ^ 2` is `Frob_(p ^ (2 * m + 1))`, the Frobenius of the field the index itself
names. -/
theorem datumSteinberg_pow_two_eq_datumFrobenius_of_usesHalfFrobenius
    (h : d.1.UsesHalfFrobenius) :
    d.datumSteinberg ^ 2 = d.datumFrobenius := by
  rw [datumSteinberg_of_usesHalfFrobenius d h, pow_two, datumFrobenius_def]
  exact SuzukiReeIndex.datumSteinberg_mul_self ⟨d, h⟩

/-- **Some positive power of the Steinberg map is the scaling at a positive power of the
characteristic.** Since the scaling at a prime power is the root-datum shadow of the Frobenius of
the field of that order, this is the root-datum form of the property that defines a Steinberg
endomorphism: some power of it is a Frobenius. The witnessing exponent is the twist order on the
thirteen ordinary constructors and `2` on the four half-Frobenius ones, and the scalar is `q ^ e`
there and `q` here, so both are recorded existentially; the two explicit forms are
`TauCeti.ValidLieTypeIndex.datumSteinberg_pow_twistOrder_eq_smulId_of_not_usesHalfFrobenius` and
`TauCeti.ValidLieTypeIndex.datumSteinberg_pow_two_eq_datumFrobenius_of_usesHalfFrobenius`. -/
theorem exists_pow_datumSteinberg_eq_smulId :
    ∃ (n : ℕ) (c : ℕ+) (k : ℕ), 0 < n ∧ 0 < k ∧ (c : ℕ) = d.characteristic ^ k ∧
      d.datumSteinberg ^ n =
        RootPairingIsogeny.smulId
          (d.dynkinType.simplyConnectedRootDatum d.dynkinType_valid) c := by
  by_cases h : d.1.UsesHalfFrobenius
  · -- The square is the Frobenius of the field the index names, a `fieldExponent`-th power of `p`.
    refine ⟨2, d.1.fieldOrderPNat, d.fieldExponent, two_pos, d.fieldExponent_pos, ?_, ?_⟩
    · rw [LieTypeIndex.coe_fieldOrderPNat]
      exact d.fieldOrder_eq_characteristic_pow
    · rw [d.datumSteinberg_pow_two_eq_datumFrobenius_of_usesHalfFrobenius h, datumFrobenius_def]
  · -- The twist-order power is the Frobenius of the degree-`e` extension, so the exponent of `p`
    -- is multiplied by `e`.
    refine ⟨GraphTwistedIndex.twistOrder ⟨d, h⟩,
      d.1.fieldOrderPNat ^ GraphTwistedIndex.twistOrder ⟨d, h⟩,
      d.fieldExponent * GraphTwistedIndex.twistOrder ⟨d, h⟩,
      GraphTwistedIndex.twistOrder_pos ⟨d, h⟩,
      Nat.mul_pos d.fieldExponent_pos (GraphTwistedIndex.twistOrder_pos ⟨d, h⟩), ?_,
      d.datumSteinberg_pow_twistOrder_eq_smulId_of_not_usesHalfFrobenius h⟩
    rw [PNat.pow_coe, LieTypeIndex.coe_fieldOrderPNat, d.1.fieldOrder_eq_characteristic_pow,
      pow_mul]

end

end ValidLieTypeIndex

/-! ## Worked branches

The two branch equations are exhaustive because `TauCeti.LieTypeIndex.UsesHalfFrobenius` is
decidable, so on a concrete constructor the side condition is discharged by `simp`. The following
representatives cover an untwisted family, a graph-twisted one, a Suzuki--Ree one and the Tits
index. -/

section Branches

variable {n : ℕ} {q : PrimePower}

/-- On the untwisted family `Aₙ(q)` the Steinberg map is the Frobenius `Frob_q` itself, the diagram
permutation being trivial there. -/
example (hv : (LieTypeIndex.A n q).Valid) :
    ValidLieTypeIndex.datumSteinberg ⟨_, hv⟩ = ValidLieTypeIndex.datumFrobenius ⟨_, hv⟩ :=
  (ValidLieTypeIndex.datumSteinberg_eq_datumFrobenius_iff_of_not_usesHalfFrobenius ⟨_, hv⟩
    (by simp)).mpr (GraphTwistedIndex.diagramPerm_A hv)

/-- On the unitary family `²Aₙ(q)` the Steinberg map is genuinely twisted, and squaring it returns
the Frobenius of the quadratic extension `𝔽_(q ^ 2)`. -/
example (hv : (LieTypeIndex.twistedA n q).Valid) :
    ValidLieTypeIndex.datumSteinberg ⟨_, hv⟩ ^ 2 =
      RootPairingIsogeny.smulId _ ((LieTypeIndex.twistedA n q).fieldOrderPNat ^ 2) := by
  have h := ValidLieTypeIndex.datumSteinberg_pow_twistOrder_eq_smulId_of_not_usesHalfFrobenius
    (⟨_, hv⟩ : ValidLieTypeIndex) (by simp)
  rwa [GraphTwistedIndex.twistOrder_twistedA hv] at h

/-- On the Suzuki family `²B₂(2 ^ (2 * m + 1))` the Steinberg map is the odd power of the `B₂`
special isogeny. -/
example {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid) :
    ValidLieTypeIndex.datumSteinberg ⟨_, hv⟩ =
      SuzukiReeIndex.datumSteinberg ⟨⟨_, hv⟩, by simp⟩ :=
  ValidLieTypeIndex.datumSteinberg_of_usesHalfFrobenius ⟨_, hv⟩ (by simp)

/-- On the Tits index the Steinberg map is the `F₄` special isogeny itself, the `m = 0` member of
the half-Frobenius family. -/
example (hv : LieTypeIndex.tits.Valid) :
    ValidLieTypeIndex.datumSteinberg ⟨_, hv⟩ =
      SuzukiReeIndex.datumSpecialIsogeny ⟨⟨_, hv⟩, by simp⟩ :=
  (ValidLieTypeIndex.datumSteinberg_of_usesHalfFrobenius ⟨_, hv⟩ (by simp)).trans
    SuzukiReeIndex.datumSteinberg_tits

end Branches

end TauCeti
