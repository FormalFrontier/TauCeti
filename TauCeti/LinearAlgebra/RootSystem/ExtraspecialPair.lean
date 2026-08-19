/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.RootSystem.Positive

/-!
# Special and extraspecial pairs of roots

Fix a base `b` of a reduced crystallographic root pairing together with a linear order on the root
indices that is *additive*: adding a positive root to a positive root moves an index strictly
upwards. A **special pair** is a pair of positive roots `α ≺ β` whose sum is again a root, and a
special pair is **extraspecial** when its first member is as small as possible among the special
pairs with the same sum.

The point of the notion is the enumeration proved here: a positive root is the sum of an
extraspecial pair exactly when it is not simple, and that pair is then unique. Carter's
construction of a Chevalley basis chooses the sign of one structure constant `N(α, β)` for each
extraspecial pair and determines every remaining structure constant by recursion over the sum
`α + β`, which is why the two members of the pair lying strictly below their sum is recorded here
beside the enumeration. Counting the pairs, there are `|Φ⁺| - ℓ` of them, one for each non-simple
positive root.

Additivity of the order is used only for those strict inequalities: existence and uniqueness of the
extraspecial pair with a prescribed sum hold for an arbitrary linear order on the indices, and are
stated that way.

## Main definitions

* `TauCeti.IsAdditiveRootOrder`: a linear order on root indices that increases strictly when a
  positive root is added to a positive root.
* `TauCeti.IsSpecialPair`: an ordered pair of positive roots whose sum is a root.
* `TauCeti.IsExtraspecialPair`: a special pair whose first member is smallest among the special
  pairs with the same sum.
* `TauCeti.extraspecialPairs`: the set of all extraspecial pairs.

## Main results

* `TauCeti.exists_isAdditiveRootOrder`: additive orders exist, so the hypothesis is not vacuous.
  Ordering by height and breaking ties arbitrarily is one.
* `TauCeti.exists_isSpecialPair_root_eq_add`: a positive root that is not simple is the sum of a
  special pair.
* `TauCeti.existsUnique_isExtraspecialPair`: a positive root that is not simple is the sum of
  exactly one extraspecial pair.
* `TauCeti.exists_isExtraspecialPair_lt`: in an additive order both members of that pair lie
  strictly below the sum, which is the recursion step Carter's construction runs on.
* `TauCeti.IsExtraspecialPair.le_of_isPos`: the first member of an extraspecial pair is smallest
  among the first members of *all* decompositions of its sum into two positive roots, ordered or
  not.
* `TauCeti.ncard_extraspecialPairs`: there are `|Φ⁺| - ℓ` extraspecial pairs.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.

## Roadmap

Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md` asks for the split reductive group scheme
over `ℤ` to be built "via a Chevalley basis and the Kostant `ℤ`-form of the enveloping algebra".
`TauCeti.IsChevalleySystem` of `TauCeti/Algebra/Lie/Weights/Chevalley/System.lean` is that
Chevalley basis, carried as a hypothesis, and
`TauCeti.IsSl2System.isChevalleyNormalized_iff_exists_isChevalleySystem` of
`TauCeti/Algebra/Lie/Weights/Chevalley/Involution.lean` reduces producing one to normalising the
structure constants to `±(p + 1)`. Carter's §4.2 performs that normalisation by recursion over the
extraspecial pairs enumerated here. Milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` is the
downstream consumer of the assembled pinned group scheme.
-/

public section

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [CharZero R] (P : RootPairing ι R M N)

/-- A linear order on the root index type is an **additive root order** for a base `b` when adding
a positive root to a positive root strictly increases the index: if `α` and `β` are positive roots
whose sum `γ` is again a root, then the index of `α` lies strictly below the index of `γ`.

Carter orders the roots by a linear functional that is positive on the positive roots, which is
additive in this sense. Only this consequence of that choice is used below, so it is the hypothesis
carried here; `TauCeti.exists_isAdditiveRootOrder` shows that such orders exist. -/
structure IsAdditiveRootOrder [l : LinearOrder ι] (b : P.Base) : Prop where
  /-- Adding a positive root to a positive root strictly increases the index. -/
  lt_of_root_eq_add {i j k : ι} (hi : b.IsPos i) (hj : b.IsPos j)
    (hk : P.root k = P.root i + P.root j) : i < k

variable {P}

/-- **Additive root orders exist.** Ordering the indices by the height of their root and breaking
ties by an arbitrary injection into `ℕ` gives one: heights add, and a positive root has height at
least one.

The order is passed to `TauCeti.IsAdditiveRootOrder` as an explicit argument here, because it is
the object asserted to exist rather than an instance available in the context. -/
theorem exists_isAdditiveRootOrder [Finite ι] (b : P.Base) :
    ∃ l : LinearOrder ι, @IsAdditiveRootOrder ι R M N _ _ _ _ _ _ P l b := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ι
  have hinj : Function.Injective fun i : ι ↦ toLex (b.height i, f i) := by
    intro i j hij
    exact hf (by simpa using congrArg (fun p ↦ (ofLex p).2) hij)
  let l : LinearOrder ι := LinearOrder.lift' _ hinj
  refine ⟨l, ⟨fun {i j k} _hi hj hk ↦ ?_⟩⟩
  have key : toLex (b.height i, f i) < toLex (b.height k, f k) := by
    have hadd := b.height_add hk
    rw [RootPairing.Base.isPos_iff] at hj
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by omega))
  exact key

section Pairs

variable (P) [LinearOrder ι] (b : P.Base)

/-- A **special pair** for a base `b` and a linear order on the root indices is a pair of positive
roots, the first strictly below the second, whose sum is again a root. -/
structure IsSpecialPair (i j : ι) : Prop where
  /-- The first root of a special pair is positive. -/
  isPos_left : b.IsPos i
  /-- The second root of a special pair is positive. -/
  isPos_right : b.IsPos j
  /-- The first root of a special pair lies strictly below the second. -/
  lt : i < j
  /-- The sum of the two roots of a special pair is again a root. -/
  add_mem_range : P.root i + P.root j ∈ range P.root

/-- A special pair is **extraspecial** when its first root is smallest, in the chosen order, among
the first roots of all the special pairs with the same sum. -/
structure IsExtraspecialPair (i j : ι) : Prop extends IsSpecialPair P b i j where
  /-- No special pair with the same sum has a smaller first root. -/
  le_left (i' j' : ι) : IsSpecialPair P b i' j' →
    P.root i' + P.root j' = P.root i + P.root j → i ≤ i'

variable {P b}

namespace IsSpecialPair

variable {i j k : ι}

/-- The two roots of a special pair are distinct, since one lies strictly below the other. -/
theorem ne (h : IsSpecialPair P b i j) : i ≠ j := h.lt.ne

/-- The sum of a special pair is a positive root. -/
theorem isPos (h : IsSpecialPair P b i j) (hk : P.root k = P.root i + P.root j) : b.IsPos k :=
  h.isPos_left.add h.isPos_right hk

/-- The sum of a special pair is never a simple root. -/
theorem notMem_support (h : IsSpecialPair P b i j) (hk : P.root k = P.root i + P.root j) :
    k ∉ b.support :=
  fun hmem ↦ root_ne_add_of_mem_support hmem h.isPos_left h.isPos_right hk

/-- In an additive order the first root of a special pair lies strictly below the sum. -/
theorem left_lt (hb : IsAdditiveRootOrder P b) (h : IsSpecialPair P b i j)
    (hk : P.root k = P.root i + P.root j) : i < k :=
  hb.lt_of_root_eq_add h.isPos_left h.isPos_right hk

/-- In an additive order the second root of a special pair lies strictly below the sum. -/
theorem right_lt (hb : IsAdditiveRootOrder P b) (h : IsSpecialPair P b i j)
    (hk : P.root k = P.root i + P.root j) : j < k :=
  hb.lt_of_root_eq_add h.isPos_right h.isPos_left (by rw [hk]; abel)

end IsSpecialPair

variable [IsDomain R] [P.IsReduced]

omit [LinearOrder ι] in
/-- Two roots whose sum is a root are distinct: in a reduced pairing, twice a root is never a
root. -/
theorem ne_of_root_eq_add {i j k : ι} (hk : P.root k = P.root i + P.root j) : i ≠ j :=
  ((RootPairing.IsReduced.linearIndependent_iff (P := P)).mp
    (P.linearIndependent_of_add_mem_range_root' ⟨k, hk⟩)).1

/-- Two positive roots whose sum is a root are the two members of a special pair, taken in one
order or the other. -/
theorem isSpecialPair_or_swap {i j k : ι} (hi : b.IsPos i) (hj : b.IsPos j)
    (hk : P.root k = P.root i + P.root j) :
    IsSpecialPair P b i j ∨ IsSpecialPair P b j i := by
  rcases lt_or_gt_of_ne (ne_of_root_eq_add hk) with h | h
  · exact Or.inl ⟨hi, hj, h, ⟨k, hk⟩⟩
  · exact Or.inr ⟨hj, hi, h, ⟨k, by rw [hk]; abel⟩⟩

namespace IsExtraspecialPair

variable {i j i' j' : ι}

/-- The first root of an extraspecial pair is smallest among the first roots of *all* the
decompositions of its sum into two positive roots, ordered or not. -/
theorem le_of_isPos (h : IsExtraspecialPair P b i j) (hi' : b.IsPos i') (hj' : b.IsPos j')
    (hsum : P.root i' + P.root j' = P.root i + P.root j) : i ≤ i' := by
  obtain ⟨k, hk⟩ := h.add_mem_range
  rcases isSpecialPair_or_swap hi' hj' (hk.trans hsum.symm) with hs | hs
  · exact h.le_left i' j' hs hsum
  · exact (h.le_left j' i' hs (by rw [← hsum]; abel)).trans hs.lt.le

omit [IsDomain R] [P.IsReduced] in
/-- **An extraspecial pair is determined by its sum.** -/
theorem eq_of_root_add_eq (h : IsExtraspecialPair P b i j) (h' : IsExtraspecialPair P b i' j')
    (hsum : P.root i' + P.root j' = P.root i + P.root j) : i' = i ∧ j' = j := by
  have hii : i' = i :=
    le_antisymm (h'.le_left i j h.toIsSpecialPair hsum.symm)
      (h.le_left i' j' h'.toIsSpecialPair hsum)
  subst hii
  exact ⟨rfl, P.root.injective (add_left_cancel hsum)⟩

end IsExtraspecialPair

variable [Finite ι] [P.IsCrystallographic]

/-- **A positive root that is not simple is the sum of a special pair.** -/
theorem exists_isSpecialPair_root_eq_add {k : ι} (hk : b.IsPos k) (hk' : k ∉ b.support) :
    ∃ i j, IsSpecialPair P b i j ∧ P.root k = P.root i + P.root j := by
  obtain ⟨j, hj, m, hm, hmj⟩ := exists_isPos_root_eq_add_of_notMem_support hk hk'
  rcases isSpecialPair_or_swap hm (RootPairing.Base.isPos_of_mem_support hj) hmj with h | h
  · exact ⟨m, j, h, hmj⟩
  · exact ⟨j, m, h, by rw [hmj]; abel⟩

/-- **A positive root that is not simple is the sum of an extraspecial pair.** The pair is found by
minimising the first member over the special pairs with the prescribed sum. -/
theorem exists_isExtraspecialPair {k : ι} (hk : b.IsPos k) (hk' : k ∉ b.support) :
    ∃ i j, IsExtraspecialPair P b i j ∧ P.root k = P.root i + P.root j := by
  have hne :
      {i : ι | ∃ j, IsSpecialPair P b i j ∧ P.root k = P.root i + P.root j}.Nonempty := by
    obtain ⟨i, j, hij, hsum⟩ := exists_isSpecialPair_root_eq_add hk hk'
    exact ⟨i, j, hij, hsum⟩
  obtain ⟨i, hiS, hmin⟩ := Set.exists_min_image _ id (Set.toFinite _) hne
  obtain ⟨j, hij, hsum⟩ := hiS
  exact ⟨i, j, ⟨hij, fun i' j' hs hsum' ↦ hmin i' ⟨j', hs, hsum.trans hsum'.symm⟩⟩, hsum⟩

/-- **A positive root that is not simple is the sum of exactly one extraspecial pair.** -/
theorem existsUnique_isExtraspecialPair {k : ι} (hk : b.IsPos k) (hk' : k ∉ b.support) :
    ∃! p : ι × ι, IsExtraspecialPair P b p.1 p.2 ∧ P.root k = P.root p.1 + P.root p.2 := by
  obtain ⟨i, j, h, hsum⟩ := exists_isExtraspecialPair hk hk'
  refine ⟨(i, j), ⟨h, hsum⟩, ?_⟩
  rintro ⟨i', j'⟩ ⟨h', hsum'⟩
  obtain ⟨rfl, rfl⟩ := h.eq_of_root_add_eq h' (hsum'.symm.trans hsum)
  rfl

/-- **The recursion step behind Carter's construction of a Chevalley basis.** In an additive order a
positive root that is not simple is the sum of a unique extraspecial pair, and both members of that
pair lie strictly below it. A structure constant attached to a root can therefore be defined by
recursion along the order, with the extraspecial pairs carrying the free sign choices. -/
theorem exists_isExtraspecialPair_lt (hb : IsAdditiveRootOrder P b) {k : ι} (hk : b.IsPos k)
    (hk' : k ∉ b.support) :
    ∃ i j, IsExtraspecialPair P b i j ∧ P.root k = P.root i + P.root j ∧ i < k ∧ j < k := by
  obtain ⟨i, j, h, hsum⟩ := exists_isExtraspecialPair hk hk'
  exact ⟨i, j, h, hsum, h.toIsSpecialPair.left_lt hb hsum, h.toIsSpecialPair.right_lt hb hsum⟩

end Pairs

section Counting

variable [LinearOrder ι]

variable (P) in
/-- The set of extraspecial pairs of a base, relative to a linear order on the root indices. -/
def extraspecialPairs (b : P.Base) : Set (ι × ι) := {p | IsExtraspecialPair P b p.1 p.2}

variable (P) in
@[simp]
theorem mem_extraspecialPairs (b : P.Base) {p : ι × ι} :
    p ∈ extraspecialPairs P b ↔ IsExtraspecialPair P b p.1 p.2 := Iff.rfl

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- **Extraspecial pairs biject with the non-simple positive roots**, by taking the sum. -/
theorem bijOn_add_extraspecialPairs :
    Set.BijOn (fun p : ι × ι ↦ P.root p.1 + P.root p.2) (extraspecialPairs P b)
      (P.root '' (posRoots P b \ (b.support : Set ι))) := by
  refine ⟨fun p hp ↦ ?_, fun p hp q hq hpq ↦ ?_, fun x hx ↦ ?_⟩
  · have hp' : IsExtraspecialPair P b p.1 p.2 := hp
    obtain ⟨k, hk⟩ := hp'.add_mem_range
    exact ⟨k, ⟨(mem_posRoots P b k).mpr (hp'.toIsSpecialPair.isPos hk),
      by simpa using hp'.toIsSpecialPair.notMem_support hk⟩, hk⟩
  · have hp' : IsExtraspecialPair P b p.1 p.2 := hp
    have hq' : IsExtraspecialPair P b q.1 q.2 := hq
    obtain ⟨h1, h2⟩ := hq'.eq_of_root_add_eq hp' hpq
    exact Prod.ext h1 h2
  · obtain ⟨k, ⟨hk, hk'⟩, rfl⟩ := hx
    obtain ⟨i, j, h, hsum⟩ :=
      exists_isExtraspecialPair ((mem_posRoots P b k).mp hk) (by simpa using hk')
    exact ⟨(i, j), h, hsum.symm⟩

/-- **There are `|Φ⁺| - ℓ` extraspecial pairs**, one for each positive root that is not simple. -/
theorem ncard_extraspecialPairs :
    (extraspecialPairs P b).ncard = (posRoots P b).ncard - b.support.card := by
  have hbij := bijOn_add_extraspecialPairs b
  calc (extraspecialPairs P b).ncard
      = ((fun p : ι × ι ↦ P.root p.1 + P.root p.2) '' extraspecialPairs P b).ncard :=
        hbij.injOn.ncard_image.symm
    _ = (P.root '' (posRoots P b \ (b.support : Set ι))).ncard := by rw [hbij.image_eq]
    _ = (posRoots P b \ (b.support : Set ι)).ncard :=
        Set.ncard_image_of_injective _ P.root.injective
    _ = (posRoots P b).ncard - b.support.card := by
        rw [Set.ncard_sdiff (support_subset_posRoots P b) (Set.toFinite _), Set.ncard_coe_finset]

end Counting

end TauCeti
