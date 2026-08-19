/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PinnedTwist
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations

/-!
# Numbered data for the Suzuki--Ree isogenies

The exceptional isogenies used to construct the Suzuki and Ree groups exchange long and short
simple roots. Their action on a simple root subgroup also raises its parameter to an exponent:
the exponent is `1` on a long simple root and the defining characteristic on a short simple root.
This file attaches both the length-exchanging permutation and the exponent convention to
`TauCeti.SuzukiReeIndex`.

The assignment is a genuine choice. Reversing the two exponents would still make the square of the
exceptional isogeny a prime-field Frobenius, so the square relation alone does not determine which
isogeny the later construction uses. Defining the exponent through
`TauCeti.DynkinType.IsLongSimpleRoot` ties it to the Bourbaki numbering and root-length convention
already fixed by the root-systems development, without introducing a second table for `B₂`, `G₂`,
and `F₄`.

The permutation selector has only the four half-Frobenius branches: Suzuki and Ree `G₂` use the
rank-two node swap, while Ree `F₄` and Tits use diagram reversal. Milestone L2 must reduce every
branch to the corresponding pinned permutation when selecting the upstream special isogeny, so the
four branch equations are simp lemmas rather than the selector body being exposed.

The Steinberg map of a Suzuki--Ree index is not the exceptional isogeny `τ` itself but its odd
power `τ ^ (2 * m + 1)`, for the constructor parameter `m`. That odd power still permutes the
numbered simple roots by the length permutation, because the permutation is an involution, and it
raises the parameter of the `i`-th simple root subgroup to
`TauCeti.SuzukiReeIndex.steinbergExponent`, which is `p ^ m` on a long simple root and `p ^ (m + 1)`
on a short one. Those two exponents multiply, along the length permutation, to the field order
`p ^ (2 * m + 1)`, which is the exponent form of `steinberg ^ 2 = Frob_q`. The last two results here
say exactly that, for an arbitrary map acting on an arbitrary pinned family by the
exceptional-isogeny equation, so that the pinned ambient group of milestone L0 can be substituted
for the family once it exists.

## Main definitions

* `TauCeti.SuzukiReeIndex.lengthPerm` selects the length-exchanging permutation used by the
  exceptional isogeny.
* `TauCeti.SuzukiReeIndex.exponent` is `1` on long simple roots and the characteristic on short
  simple roots.
* `TauCeti.SuzukiReeIndex.parameter` is the constructor parameter `m`, and
  `TauCeti.SuzukiReeIndex.steinbergExponent` the exponent by which the odd power
  `τ ^ (2 * m + 1)` raises a simple root subgroup parameter.

## Main results

* `TauCeti.SuzukiReeIndex.lengthPerm_suzuki`, `TauCeti.SuzukiReeIndex.lengthPerm_reeG2`,
  `TauCeti.SuzukiReeIndex.lengthPerm_reeF4`, and `TauCeti.SuzukiReeIndex.lengthPerm_tits` are the
  branch equations naming the selected permutation on each half-Frobenius family.
* `TauCeti.SuzukiReeIndex.isLongSimpleRoot_lengthPerm` proves that this permutation exchanges long
  and short simple roots, and `TauCeti.SuzukiReeIndex.lengthPerm_lengthPerm` that it is an
  involution.
* `TauCeti.SuzukiReeIndex.cartanMatrix_lengthPerm`: it carries the Cartan matrix of the underlying
  diagram to the transposed matrix, so, unlike the graph automorphisms of
  `TauCeti.GraphTwistedIndex.diagramPerm`, it is not a diagram symmetry.
* `TauCeti.SuzukiReeIndex.exponent_of_isLongSimpleRoot`,
  `TauCeti.SuzukiReeIndex.exponent_of_not_isLongSimpleRoot`,
  `TauCeti.SuzukiReeIndex.exponent_eq_one_iff` and
  `TauCeti.SuzukiReeIndex.exponent_eq_characteristic_iff` compute and characterize the two
  exponents, and `TauCeti.SuzukiReeIndex.exponent_mul_exponent_lengthPerm` multiplies the two
  exponents of a length-exchanged pair to the characteristic.
* `TauCeti.SuzukiReeIndex.fieldOrder_eq_characteristic_pow`: the field order is the odd power
  `p ^ (2 * m + 1)`, and
  `TauCeti.SuzukiReeIndex.steinbergExponent_mul_steinbergExponent_lengthPerm` multiplies the two
  Steinberg exponents of a length-exchanged pair to it.
* `TauCeti.SuzukiReeIndex.isPinnedTwist_steinberg` and
  `TauCeti.SuzukiReeIndex.isPinnedTwist_steinberg_sq`: the odd power of a map acting on a pinned
  family by the exceptional-isogeny equation acts by the Steinberg exponents, and its square raises
  every parameter to the field order.

The permutation, the exponents, and their branch equations are the Suzuki--Ree numbered-data part
of milestone I0 in `TauCetiRoadmap/CFSGStatement/README.md`; the odd power and its exponents are
milestone L2, whose remaining part is the selection of the upstream special isogeny `τ_X` itself.
The exponent convention follows Carter, *Simple Groups of Lie Type*. The permutations and numbering
follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, plates II, VIII, and IX, as fixed by
the CFSG and root-systems roadmaps.
-/

public section

namespace TauCeti

namespace SuzukiReeIndex

-- Transporting the root-length predicate together with its index type avoids dependent rewriting
-- through `DynkinType.rank`, which is precisely the dependency that `finCongr` packages.
private theorem isLongSimpleRoot_reindexPerm {t u : DynkinType} (h : t = u)
    (p : Equiv.Perm (Fin u.rank))
    (hp : ∀ j, u.IsLongSimpleRoot (p j) ↔ ¬u.IsLongSimpleRoot j) (i : Fin t.rank) :
    t.IsLongSimpleRoot
        ((finCongr (congrArg DynkinType.rank h)).symm.permCongr p i) ↔
      ¬t.IsLongSimpleRoot i := by
  subst u
  simpa [finCongr_refl, Equiv.permCongr_def] using hp i

/-- The length-exchanging permutation used by the exceptional isogeny attached to a Suzuki--Ree
index: the node swap for `B₂` and `G₂`, and reversal for `F₄`.

The four branch equations `lengthPerm_suzuki`, `lengthPerm_reeG2`, `lengthPerm_reeF4`, and
`lengthPerm_tits` name the selected permutation on each family, so no consumer needs this body. -/
def lengthPerm (e : SuzukiReeIndex) : Equiv.Perm (Fin e.1.rank) :=
  match e with
  | ⟨⟨.A _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedA _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.B _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.C _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.D _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedD _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E6 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E7 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E8 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.F4 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.G2 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedE6 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.trialityD4 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.suzuki m, hvalid⟩, _⟩ =>
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_suzuki, DynkinType.rank_B])).symm.permCongr lengthPermRankTwo
  | ⟨⟨.reeG2 m, hvalid⟩, _⟩ =>
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_reeG2, DynkinType.rank_G2])).symm.permCongr lengthPermRankTwo
  | ⟨⟨.reeF4 m, hvalid⟩, _⟩ =>
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_reeF4, DynkinType.rank_F4])).symm.permCongr lengthPermF4
  | ⟨⟨.tits, hvalid⟩, _⟩ =>
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_tits, DynkinType.rank_F4])).symm.permCongr lengthPermF4

/-- A Suzuki index selects the rank-two node swap, transported along the `B₂` numbering. -/
@[simp] theorem lengthPerm_suzuki (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid) :
    lengthPerm ⟨⟨.suzuki m, hvalid⟩, by simp⟩ =
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_suzuki, DynkinType.rank_B])).symm.permCongr
        lengthPermRankTwo := by
  simp only [lengthPerm]

/-- A Ree `G₂` index selects the rank-two node swap, transported along the `G₂` numbering. -/
@[simp] theorem lengthPerm_reeG2 (m : ℕ) (hvalid : (LieTypeIndex.reeG2 m).Valid) :
    lengthPerm ⟨⟨.reeG2 m, hvalid⟩, by simp⟩ =
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_reeG2, DynkinType.rank_G2])).symm.permCongr
        lengthPermRankTwo := by
  simp only [lengthPerm]

/-- A Ree `F₄` index selects the `F₄` diagram reversal. -/
@[simp] theorem lengthPerm_reeF4 (m : ℕ) (hvalid : (LieTypeIndex.reeF4 m).Valid) :
    lengthPerm ⟨⟨.reeF4 m, hvalid⟩, by simp⟩ =
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_reeF4, DynkinType.rank_F4])).symm.permCongr lengthPermF4 := by
  simp only [lengthPerm]

/-- The Tits index selects the `F₄` diagram reversal. -/
@[simp] theorem lengthPerm_tits :
    lengthPerm ⟨⟨.tits, by simp⟩, by simp⟩ =
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_tits, DynkinType.rank_F4])).symm.permCongr lengthPermF4 := by
  simp only [lengthPerm]

/-- The length permutation selected by a Suzuki--Ree index exchanges long and short simple roots
in the Bourbaki numbering of its underlying untwisted Dynkin diagram. -/
@[simp]
theorem isLongSimpleRoot_lengthPerm (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.1.dynkinType.IsLongSimpleRoot (e.lengthPerm i) ↔
      ¬e.1.dynkinType.IsLongSimpleRoot i := by
  simp only [ValidLieTypeIndex.dynkinType, ValidLieTypeIndex.rank] at i ⊢
  obtain ⟨⟨d, hvalid⟩, hhalf⟩ := e
  cases d <;> try simp at hhalf
  case suzuki =>
    convert isLongSimpleRoot_reindexPerm (LieTypeIndex.dynkinType_suzuki _)
      lengthPermRankTwo isLongSimpleRoot_lengthPermRankTwo_iff_not_isLongSimpleRoot_B2 i using 1
    all_goals simp only [lengthPerm_suzuki]
    rfl
  case reeG2 =>
    convert isLongSimpleRoot_reindexPerm (LieTypeIndex.dynkinType_reeG2 _)
      lengthPermRankTwo isLongSimpleRoot_lengthPermRankTwo_iff_not_isLongSimpleRoot_G2 i using 1
    all_goals simp only [lengthPerm_reeG2]
    rfl
  case reeF4 =>
    convert isLongSimpleRoot_reindexPerm (LieTypeIndex.dynkinType_reeF4 _)
      lengthPermF4 isLongSimpleRoot_lengthPermF4_iff_not_isLongSimpleRoot_F4 i using 1
    all_goals simp only [lengthPerm_reeF4]
    rfl
  case tits =>
    convert isLongSimpleRoot_reindexPerm LieTypeIndex.dynkinType_tits lengthPermF4
      isLongSimpleRoot_lengthPermF4_iff_not_isLongSimpleRoot_F4 i using 1
    all_goals simp only [lengthPerm_tits]
    rfl

/-- The exponent attached to a numbered simple root subgroup by the exceptional isogeny: `1` on a
long simple root and the defining characteristic on a short simple root.

The long-root predicate is the root-systems development's Bourbaki-numbered predicate, rather than
a second family-by-family table. -/
def exponent (e : SuzukiReeIndex) (i : Fin e.1.rank) : ℕ :=
  if e.1.dynkinType.IsLongSimpleRoot i then 1 else e.1.characteristic

/-- The exceptional isogeny uses exponent `1` on long simple root subgroups. -/
@[simp]
theorem exponent_of_isLongSimpleRoot (e : SuzukiReeIndex) (i : Fin e.1.rank)
    (hi : e.1.dynkinType.IsLongSimpleRoot i) : e.exponent i = 1 := by
  simp [exponent, hi]

/-- The exceptional isogeny uses the defining characteristic as its exponent on short simple root
subgroups. -/
@[simp]
theorem exponent_of_not_isLongSimpleRoot (e : SuzukiReeIndex) (i : Fin e.1.rank)
    (hi : ¬e.1.dynkinType.IsLongSimpleRoot i) : e.exponent i = e.1.characteristic := by
  simp [exponent, hi]

/-- A root-subgroup exponent is `1` exactly on a long simple root. -/
@[simp]
theorem exponent_eq_one_iff (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i = 1 ↔ e.1.dynkinType.IsLongSimpleRoot i := by
  simp [exponent, e.1.characteristic_prime.ne_one]

/-- A root-subgroup exponent is the defining characteristic exactly on a short simple root. -/
@[simp]
theorem exponent_eq_characteristic_iff (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i = e.1.characteristic ↔ ¬e.1.dynkinType.IsLongSimpleRoot i := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · simp only [exponent_of_isLongSimpleRoot e i hi, hi, not_true_eq_false, iff_false]
    exact e.1.characteristic_prime.ne_one.symm
  · simp only [exponent_of_not_isLongSimpleRoot e i hi, hi, not_false_eq_true]

/-- Every root-subgroup exponent is positive. -/
theorem exponent_pos (e : SuzukiReeIndex) (i : Fin e.1.rank) : 0 < e.exponent i := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · simp only [exponent_of_isLongSimpleRoot e i hi, Nat.zero_lt_one]
  · rw [exponent_of_not_isLongSimpleRoot e i hi]
    exact e.1.characteristic_prime.pos

/-- Every root-subgroup exponent is at most the defining characteristic. -/
theorem exponent_le_characteristic (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i ≤ e.1.characteristic := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · rw [exponent_of_isLongSimpleRoot e i hi]
    exact e.1.characteristic_prime.one_lt.le
  · simp only [exponent_of_not_isLongSimpleRoot e i hi, le_refl]

/-- The two possible values of a root-subgroup exponent. -/
theorem exponent_eq_one_or_eq_characteristic (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i = 1 ∨ e.exponent i = e.1.characteristic := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · exact Or.inl (exponent_of_isLongSimpleRoot e i hi)
  · exact Or.inr (exponent_of_not_isLongSimpleRoot e i hi)

/-! ### The length permutation is an involution transposing the Cartan matrix -/

-- As for `isLongSimpleRoot_reindexPerm`, transporting a property of a pinned permutation together
-- with its index type avoids dependent rewriting through `DynkinType.rank`.
private theorem involutive_reindexPerm {t u : DynkinType} (h : t = u) (p : Equiv.Perm (Fin u.rank))
    (hp : ∀ j, p (p j) = j) (i : Fin t.rank) :
    ((finCongr (congrArg DynkinType.rank h)).symm.permCongr p)
        (((finCongr (congrArg DynkinType.rank h)).symm.permCongr p) i) = i := by
  subst u
  simpa [finCongr_refl, Equiv.permCongr_def] using hp i

private theorem cartanMatrix_reindexPerm {t u : DynkinType} (h : t = u)
    (p : Equiv.Perm (Fin u.rank))
    (hp : ∀ j k, u.cartanMatrix (p j) (p k) = u.cartanMatrix k j) (i j : Fin t.rank) :
    t.cartanMatrix (((finCongr (congrArg DynkinType.rank h)).symm.permCongr p) i)
        (((finCongr (congrArg DynkinType.rank h)).symm.permCongr p) j) =
      t.cartanMatrix j i := by
  subst u
  simpa [finCongr_refl, Equiv.permCongr_def] using hp i j

/-- The length permutation selected by a Suzuki--Ree index is an involution: the exceptional
isogeny exchanges the long and short simple roots, so applying it twice returns each node. -/
@[simp]
theorem lengthPerm_lengthPerm (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.lengthPerm (e.lengthPerm i) = i := by
  simp only [ValidLieTypeIndex.rank] at i ⊢
  obtain ⟨⟨d, hvalid⟩, hhalf⟩ := e
  cases d <;> try simp at hhalf
  case suzuki =>
    rw [lengthPerm_suzuki]
    exact involutive_reindexPerm (LieTypeIndex.dynkinType_suzuki _) lengthPermRankTwo
      lengthPermRankTwo_lengthPermRankTwo i
  case reeG2 =>
    rw [lengthPerm_reeG2]
    exact involutive_reindexPerm (LieTypeIndex.dynkinType_reeG2 _) lengthPermRankTwo
      lengthPermRankTwo_lengthPermRankTwo i
  case reeF4 =>
    rw [lengthPerm_reeF4]
    exact involutive_reindexPerm (LieTypeIndex.dynkinType_reeF4 _) lengthPermF4
      lengthPermF4_lengthPermF4 i
  case tits =>
    rw [lengthPerm_tits]
    exact involutive_reindexPerm LieTypeIndex.dynkinType_tits lengthPermF4
      lengthPermF4_lengthPermF4 i

/-- The length permutation selected by a Suzuki--Ree index carries the Cartan matrix of its
underlying untwisted diagram to the transposed matrix.

This is what distinguishes it from the graph automorphisms of
`TauCeti.GraphTwistedIndex.diagramPerm`, which preserve their Cartan matrix
(`TauCeti.GraphTwistedIndex.cartanMatrix_diagramPerm`). A permutation transposing the Cartan matrix
is a symmetry of the *dual* diagram, so it is not realized by an automorphism of the pinned group;
it is realized by a special isogeny, which is why these four families need a half-Frobenius. -/
theorem cartanMatrix_lengthPerm (e : SuzukiReeIndex) (i j : Fin e.1.rank) :
    e.1.dynkinType.cartanMatrix (e.lengthPerm i) (e.lengthPerm j) =
      e.1.dynkinType.cartanMatrix j i := by
  simp only [ValidLieTypeIndex.dynkinType, ValidLieTypeIndex.rank] at i j ⊢
  obtain ⟨⟨d, hvalid⟩, hhalf⟩ := e
  cases d <;> try simp at hhalf
  case suzuki =>
    rw [lengthPerm_suzuki]
    exact cartanMatrix_reindexPerm (LieTypeIndex.dynkinType_suzuki _) lengthPermRankTwo
      cartanMatrix_B2_lengthPermRankTwo i j
  case reeG2 =>
    rw [lengthPerm_reeG2]
    exact cartanMatrix_reindexPerm (LieTypeIndex.dynkinType_reeG2 _) lengthPermRankTwo
      cartanMatrix_G2_lengthPermRankTwo i j
  case reeF4 =>
    rw [lengthPerm_reeF4]
    exact cartanMatrix_reindexPerm (LieTypeIndex.dynkinType_reeF4 _) lengthPermF4
      cartanMatrix_F4_lengthPermF4 i j
  case tits =>
    rw [lengthPerm_tits]
    exact cartanMatrix_reindexPerm LieTypeIndex.dynkinType_tits lengthPermF4
      cartanMatrix_F4_lengthPermF4 i j

/-- The exponents attached to a simple root and to its partner under the length permutation
multiply to the defining characteristic.

This is the relation that makes the square of the exceptional isogeny the prime-field Frobenius:
one factor is `1` and the other is the characteristic, in one order or the other. -/
theorem exponent_mul_exponent_lengthPerm (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i * e.exponent (e.lengthPerm i) = e.1.characteristic := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · rw [exponent_of_isLongSimpleRoot e i hi,
      exponent_of_not_isLongSimpleRoot e _ fun h => (isLongSimpleRoot_lengthPerm e i).mp h hi,
      one_mul]
  · rw [exponent_of_not_isLongSimpleRoot e i hi,
      exponent_of_isLongSimpleRoot e _ ((isLongSimpleRoot_lengthPerm e i).mpr hi), mul_one]

/-! ### The Steinberg exponents -/

/-- The constructor parameter `m` of a Suzuki--Ree index. The three Suzuki--Ree families are
`²B₂(2 ^ (2 * m + 1))`, `²G₂(3 ^ (2 * m + 1))` and `²F₄(2 ^ (2 * m + 1))`, whose Steinberg map is
the odd power `τ ^ (2 * m + 1)` of the exceptional isogeny; the Tits index is the `F₄` isogeny
itself, so its parameter is `0`. -/
def parameter (e : SuzukiReeIndex) : ℕ :=
  match e with
  | ⟨⟨.A _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedA _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.B _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.C _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.D _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedD _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E6 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E7 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E8 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.F4 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.G2 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedE6 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.trialityD4 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.suzuki m, _⟩, _⟩ | ⟨⟨.reeG2 m, _⟩, _⟩ | ⟨⟨.reeF4 m, _⟩, _⟩ => m
  | ⟨⟨.tits, _⟩, _⟩ => 0

/-- A Suzuki index carries its own constructor parameter. -/
@[simp] theorem parameter_suzuki (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid) :
    parameter ⟨⟨.suzuki m, hvalid⟩, by simp⟩ = m := by simp only [parameter]

/-- A Ree `G₂` index carries its own constructor parameter. -/
@[simp] theorem parameter_reeG2 (m : ℕ) (hvalid : (LieTypeIndex.reeG2 m).Valid) :
    parameter ⟨⟨.reeG2 m, hvalid⟩, by simp⟩ = m := by simp only [parameter]

/-- A Ree `F₄` index carries its own constructor parameter. -/
@[simp] theorem parameter_reeF4 (m : ℕ) (hvalid : (LieTypeIndex.reeF4 m).Valid) :
    parameter ⟨⟨.reeF4 m, hvalid⟩, by simp⟩ = m := by simp only [parameter]

/-- The Tits index is the exceptional isogeny itself, so its parameter is `0`. -/
@[simp] theorem parameter_tits : parameter ⟨⟨.tits, by simp⟩, by simp⟩ = 0 := by
  simp only [parameter]

/-- The field order of a Suzuki--Ree index is the odd power `p ^ (2 * m + 1)` of its
characteristic, so the parameter is not a second numeric datum. -/
theorem fieldOrder_eq_characteristic_pow (e : SuzukiReeIndex) :
    e.1.fieldOrder = e.1.characteristic ^ (2 * e.parameter + 1) := by
  obtain ⟨⟨d, hvalid⟩, hhalf⟩ := e
  cases d <;> try simp at hhalf
  case suzuki m =>
    simp only [ValidLieTypeIndex.fieldOrder, ValidLieTypeIndex.characteristic, parameter,
      LieTypeIndex.fieldOrder_suzuki, LieTypeIndex.characteristic_suzuki]
  case reeG2 m =>
    simp only [ValidLieTypeIndex.fieldOrder, ValidLieTypeIndex.characteristic, parameter,
      LieTypeIndex.fieldOrder_reeG2, LieTypeIndex.characteristic_reeG2]
  case reeF4 m =>
    simp only [ValidLieTypeIndex.fieldOrder, ValidLieTypeIndex.characteristic, parameter,
      LieTypeIndex.fieldOrder_reeF4, LieTypeIndex.characteristic_reeF4]
  case tits =>
    simp only [ValidLieTypeIndex.fieldOrder, ValidLieTypeIndex.characteristic, parameter,
      LieTypeIndex.fieldOrder_tits, LieTypeIndex.characteristic_tits, Nat.mul_zero, Nat.zero_add,
      pow_one]

/-- The exponent by which the Steinberg map `τ ^ (2 * m + 1)` of a Suzuki--Ree index raises the
parameter of the `i`-th simple root subgroup: `p ^ m` on a long simple root and `p ^ (m + 1)` on a
short one.

The `2 * m` even factors of the odd power contribute `p ^ m` at every node, since the exceptional
isogeny raises to the two exponents `1` and `p` alternately along the length permutation; the
remaining factor contributes the exponent of the node itself. -/
def steinbergExponent (e : SuzukiReeIndex) (i : Fin e.1.rank) : ℕ :=
  e.1.characteristic ^ e.parameter * e.exponent i

/-- The Steinberg map raises a long simple root parameter to the `p ^ m`-th power. -/
@[simp]
theorem steinbergExponent_of_isLongSimpleRoot (e : SuzukiReeIndex) (i : Fin e.1.rank)
    (hi : e.1.dynkinType.IsLongSimpleRoot i) :
    e.steinbergExponent i = e.1.characteristic ^ e.parameter := by
  rw [steinbergExponent, exponent_of_isLongSimpleRoot e i hi, mul_one]

/-- The Steinberg map raises a short simple root parameter to the `p ^ (m + 1)`-th power. -/
@[simp]
theorem steinbergExponent_of_not_isLongSimpleRoot (e : SuzukiReeIndex) (i : Fin e.1.rank)
    (hi : ¬e.1.dynkinType.IsLongSimpleRoot i) :
    e.steinbergExponent i = e.1.characteristic ^ (e.parameter + 1) := by
  rw [steinbergExponent, exponent_of_not_isLongSimpleRoot e i hi, pow_succ]

/-- **The Steinberg exponents multiply to the field order along the length permutation.**

This is the exponent form of `steinberg m ^ 2 = Frob_(p ^ (2 * m + 1))`: applying the Steinberg map
twice returns each node, having raised its parameter to the `q`-th power for `q` the field order of
the index. -/
theorem steinbergExponent_mul_steinbergExponent_lengthPerm (e : SuzukiReeIndex)
    (i : Fin e.1.rank) :
    e.steinbergExponent i * e.steinbergExponent (e.lengthPerm i) = e.1.fieldOrder := by
  rw [steinbergExponent, steinbergExponent, fieldOrder_eq_characteristic_pow, mul_mul_mul_comm,
    ← pow_add, exponent_mul_exponent_lengthPerm, ← pow_succ, two_mul]

/-- Every Steinberg exponent is positive. -/
theorem steinbergExponent_pos (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    0 < e.steinbergExponent i :=
  Nat.mul_pos (Nat.pow_pos e.1.characteristic_prime.pos) (exponent_pos e i)

/-- Every Steinberg exponent divides the field order. -/
theorem steinbergExponent_dvd_fieldOrder (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.steinbergExponent i ∣ e.1.fieldOrder :=
  Dvd.intro _ (e.steinbergExponent_mul_steinbergExponent_lengthPerm i)

/-! ### The Steinberg map as an odd power of the exceptional isogeny

The two results below are the form in which milestone L2 will consume the conventions above, once
the pinned ambient group and its special isogeny exist: for *any* map of *any* type acting on a
pinned family by the exceptional-isogeny equation, the odd power `τ ^ (2 * m + 1)` acts by the
Steinberg exponents, and its square raises every parameter to the field order. -/

section PinnedTwist

variable {G R : Type*} [Monoid R] (e : SuzukiReeIndex) {x : Fin e.1.rank → R → G} {τ : G → G}

/-- The Steinberg map of a Suzuki--Ree index, as the odd power `τ ^ (2 * m + 1)` of a map acting on
a pinned family by the exceptional-isogeny equation: it still permutes the numbered simple roots by
the length permutation, and raises the `i`-th parameter to the Steinberg exponent. -/
theorem isPinnedTwist_steinberg (h : IsPinnedTwist x e.lengthPerm e.exponent τ) :
    IsPinnedTwist x e.lengthPerm e.steinbergExponent τ^[2 * e.parameter + 1] :=
  h.iterate_two_mul_add_one e.lengthPerm_lengthPerm e.exponent_mul_exponent_lengthPerm e.parameter

/-- The square of that Steinberg map fixes every numbered simple root and raises every parameter to
the field order of the index: the relation `steinberg m ^ 2 = Frob_q` on the pinned family. -/
theorem isPinnedTwist_steinberg_sq (h : IsPinnedTwist x e.lengthPerm e.exponent τ) :
    IsPinnedTwist x 1 (fun _ => e.1.fieldOrder) τ^[2 * (2 * e.parameter + 1)] := by
  have key := (e.isPinnedTwist_steinberg h).sq e.lengthPerm_lengthPerm
    e.steinbergExponent_mul_steinbergExponent_lengthPerm
  rwa [← Function.iterate_mul, Nat.mul_comm (2 * e.parameter + 1) 2] at key

end PinnedTwist

end SuzukiReeIndex

end TauCeti
