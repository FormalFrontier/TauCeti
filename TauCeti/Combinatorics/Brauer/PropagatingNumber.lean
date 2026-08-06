/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Fintype.Prod
public import TauCeti.Combinatorics.Brauer.Diagram

/-!
# The propagating number of a Brauer diagram

The **propagating number** of a Brauer diagram is the number of its through strands, the arcs
joining a bottom point to a top point. It is the statistic that stratifies the Brauer algebra:
composing diagrams can destroy through strands but never create them, so the diagrams of
propagating number at most `r` span an ideal, and these ideals are the chain underlying the cell
structure of the algebra.

This file introduces the four boundary sets of a diagram -- the bottom and top endpoints of its
through strands, the bottom endpoints of its caps and the top endpoints of its cups -- defines
`propagatingNumber` as the cardinality of the first of them, and establishes the basic
constraints on it. Following an arc matches the bottom endpoints of the through strands with
their top endpoints, so a diagram has as many caps as cups
(`BrauerDiagram.card_bottomCap_eq_card_topCup`); the caps in turn match the remaining bottom
points among themselves, so there is an even number of them and the propagating number has the
same parity as the number of strands (`BrauerDiagram.propagatingNumber_mod_two`).

The two extreme values are identified with the two families of diagrams that carry no
horizontal arc at all and, at the opposite end, nothing else: the diagrams of propagating number
`k` are the `k !` permutation diagrams, and the diagrams of propagating number `0` are the pairs
consisting of a perfect matching of the bottom points and a perfect matching of the top points,
so on `2 * m` strands there are `((2 * m - 1)‼) ^ 2` of them.

## Main definitions

* `TauCeti.BrauerDiagram.bottomThrough`, `topThrough`, `bottomCap`, `topCup`: the boundary points
  carrying an arc of each kind.
* `TauCeti.BrauerDiagram.throughEquiv`: a through strand matches its bottom endpoint with its top
  endpoint.
* `TauCeti.BrauerDiagram.propagatingNumber`: the number of through strands.
* `TauCeti.BrauerDiagram.capMatching`: the perfect matching of the capped bottom points.
* `TauCeti.propagatingNumberZeroEquiv`: the diagrams with no through strand are the pairs of a
  matching of the bottom points and a matching of the top points.

## Main results

* `TauCeti.BrauerDiagram.card_bottomCap_eq_card_topCup`: a diagram has as many caps as cups.
* `TauCeti.BrauerDiagram.propagatingNumber_mod_two`: the propagating number of a diagram on `k`
  strands has the same parity as `k`.
* `TauCeti.card_propagatingNumber_eq_card`: there are `k !` diagrams of propagating number `k`.
* `TauCeti.card_propagatingNumber_eq_zero`: there are `((2 * m - 1)‼) ^ 2` diagrams on `2 * m`
  strands with no through strand.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9.
-/

public section

open scoped Nat

namespace TauCeti

namespace BrauerDiagram

variable {k : ℕ} (D : BrauerDiagram k)

/-- A bottom point lies on a cap exactly when it does not lie on a through strand. -/
theorem isCap_inl_iff (i : Fin k) : D.IsCap (Sum.inl i) ↔ ¬D.IsThrough (Sum.inl i) := by
  rcases h : D.val (Sum.inl i) with j | j <;> simp [isCap_def, isThrough_def, h]

/-- A top point lies on a cup exactly when it does not lie on a through strand. -/
theorem isCup_inr_iff (j : Fin k) : D.IsCup (Sum.inr j) ↔ ¬D.IsThrough (Sum.inr j) := by
  rcases h : D.val (Sum.inr j) with i | i <;> simp [isCup_def, isThrough_def, h]

/-- The bottom endpoints of the through strands of `D`. -/
def bottomThrough : Finset (Fin k) := Finset.univ.filter fun i => D.IsThrough (Sum.inl i)

/-- The top endpoints of the through strands of `D`. -/
def topThrough : Finset (Fin k) := Finset.univ.filter fun j => D.IsThrough (Sum.inr j)

/-- The bottom endpoints of the caps of `D`. -/
def bottomCap : Finset (Fin k) := Finset.univ.filter fun i => D.IsCap (Sum.inl i)

/-- The top endpoints of the cups of `D`. -/
def topCup : Finset (Fin k) := Finset.univ.filter fun j => D.IsCup (Sum.inr j)

@[simp]
theorem mem_bottomThrough {i : Fin k} : i ∈ D.bottomThrough ↔ D.IsThrough (Sum.inl i) := by
  simp [bottomThrough]

@[simp]
theorem mem_topThrough {j : Fin k} : j ∈ D.topThrough ↔ D.IsThrough (Sum.inr j) := by
  simp [topThrough]

@[simp]
theorem mem_bottomCap {i : Fin k} : i ∈ D.bottomCap ↔ D.IsCap (Sum.inl i) := by simp [bottomCap]

@[simp]
theorem mem_topCup {j : Fin k} : j ∈ D.topCup ↔ D.IsCup (Sum.inr j) := by simp [topCup]

/-- The capped bottom points are the ones that no through strand reaches. -/
theorem bottomCap_eq_compl : D.bottomCap = D.bottomThroughᶜ := by
  ext i
  simp [isCap_inl_iff]

/-- The cupped top points are the ones that no through strand reaches. -/
theorem topCup_eq_compl : D.topCup = D.topThroughᶜ := by
  ext j
  simp [isCup_inr_iff]

/-- **Following an arc through** matches the bottom endpoints of the through strands of `D` with
their top endpoints. -/
def throughEquiv :
    {i : Fin k // D.IsThrough (Sum.inl i)} ≃ {j : Fin k // D.IsThrough (Sum.inr j)} where
  toFun i := ⟨(D.val (Sum.inl i.1)).getRight (isRight_val_inl i.2), by
    rw [show Sum.inr ((D.val (Sum.inl i.1)).getRight (isRight_val_inl i.2))
        = D.val (Sum.inl i.1) from Sum.inr_getRight _ _]
    exact (D.isThrough_val _).mpr i.2⟩
  invFun j := ⟨(D.val (Sum.inr j.1)).getLeft (isLeft_val_inr j.2), by
    rw [show Sum.inl ((D.val (Sum.inr j.1)).getLeft (isLeft_val_inr j.2))
        = D.val (Sum.inr j.1) from Sum.inl_getLeft _ _]
    exact (D.isThrough_val _).mpr j.2⟩
  left_inv i := Subtype.ext <| (Sum.getLeft_eq_iff _).mpr <| by
    rw [Sum.inr_getRight]
    exact D.apply_apply _
  right_inv j := Subtype.ext <| (Sum.getRight_eq_iff _).mpr <| by
    rw [Sum.inl_getLeft]
    exact D.apply_apply _

/-- A diagram has as many bottom endpoints of through strands as top endpoints. -/
theorem card_bottomThrough_eq_card_topThrough : D.bottomThrough.card = D.topThrough.card := by
  rw [bottomThrough, topThrough, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr D.throughEquiv

/-- **A diagram has as many caps as cups.** -/
theorem card_bottomCap_eq_card_topCup : D.bottomCap.card = D.topCup.card := by
  rw [bottomCap_eq_compl, topCup_eq_compl, Finset.card_compl, Finset.card_compl,
    card_bottomThrough_eq_card_topThrough]

/-- The **propagating number** of a Brauer diagram: the number of its through strands. -/
@[expose]
def propagatingNumber : ℕ := D.bottomThrough.card

theorem propagatingNumber_eq_card_bottomThrough :
    D.propagatingNumber = D.bottomThrough.card := rfl

theorem propagatingNumber_eq_card_topThrough : D.propagatingNumber = D.topThrough.card :=
  D.card_bottomThrough_eq_card_topThrough

/-- The through strands are at most as many as the strands. -/
theorem propagatingNumber_le : D.propagatingNumber ≤ k := by
  rw [propagatingNumber_eq_card_bottomThrough]
  simpa using Finset.card_le_univ D.bottomThrough

/-- Every bottom point is either the endpoint of a through strand or the endpoint of a cap. -/
theorem propagatingNumber_add_card_bottomCap : D.propagatingNumber + D.bottomCap.card = k := by
  rw [propagatingNumber_eq_card_bottomThrough, bottomCap_eq_compl, Finset.card_add_card_compl,
    Fintype.card_fin]

/-- The map sending a capped bottom point to the other end of its cap. -/
private def capFun (i : {i : Fin k // D.IsCap (Sum.inl i)}) : {i : Fin k // D.IsCap (Sum.inl i)} :=
  ⟨(D.val (Sum.inl i.1)).getLeft ((D.isCap_def _).mp i.2).2, by
    rw [show Sum.inl ((D.val (Sum.inl i.1)).getLeft ((D.isCap_def _).mp i.2).2)
        = D.val (Sum.inl i.1) from Sum.inl_getLeft _ _]
    exact (D.isCap_val _).mpr i.2⟩

private theorem inl_capFun (i : {i : Fin k // D.IsCap (Sum.inl i)}) :
    Sum.inl (D.capFun i).1 = D.val (Sum.inl i.1) := Sum.inl_getLeft _ _

private theorem capFun_involutive : Function.Involutive D.capFun := fun i =>
  Subtype.ext <| Sum.inl_injective <| by
    rw [inl_capFun D (D.capFun i), inl_capFun D i, D.apply_apply]

private theorem capFun_ne (i : {i : Fin k // D.IsCap (Sum.inl i)}) : D.capFun i ≠ i := fun h =>
  D.apply_ne (Sum.inl i.1) (by rw [← inl_capFun D i, h])

/-- The perfect matching that a diagram induces on its capped bottom points: the caps pair those
points off among themselves. -/
def capMatching : PerfectMatching {i : Fin k // D.IsCap (Sum.inl i)} :=
  .mk (capFun_involutive D).toPerm (fun i => by simpa using capFun_involutive D i)
    fun i => by simpa using capFun_ne D i

/-- A diagram has an even number of caps: they pair off the bottom points that no through strand
reaches. -/
theorem even_card_bottomCap : Even D.bottomCap.card := by
  rw [bottomCap, ← Fintype.card_subtype]
  exact even_card_of_nonempty_perfectMatching _ ⟨D.capMatching⟩

/-- **The propagating number has the parity of the number of strands.** -/
theorem propagatingNumber_mod_two : D.propagatingNumber % 2 = k % 2 := by
  obtain ⟨r, hr⟩ := D.even_card_bottomCap
  have h := D.propagatingNumber_add_card_bottomCap
  omega

/-- A diagram propagates every strand exactly when it has no horizontal arc. -/
theorem propagatingNumber_eq_card_iff : D.propagatingNumber = k ↔ ∀ x, D.IsThrough x := by
  constructor
  · intro h x
    have hb : D.bottomThrough = Finset.univ :=
      Finset.eq_univ_of_card _ (by
        rw [← propagatingNumber_eq_card_bottomThrough, h, Fintype.card_fin])
    have ht : D.topThrough = Finset.univ :=
      Finset.eq_univ_of_card _ (by
        rw [← propagatingNumber_eq_card_topThrough, h, Fintype.card_fin])
    rcases x with i | j
    · exact (D.mem_bottomThrough).mp (hb ▸ Finset.mem_univ i)
    · exact (D.mem_topThrough).mp (ht ▸ Finset.mem_univ j)
  · intro h
    rw [propagatingNumber_eq_card_bottomThrough,
      Finset.eq_univ_of_forall fun i => (D.mem_bottomThrough).mpr (h _), Finset.card_fin]

@[simp]
theorem propagatingNumber_permToBrauer (σ : Equiv.Perm (Fin k)) :
    (permToBrauer σ).propagatingNumber = k :=
  (propagatingNumber_eq_card_iff _).mpr (isThrough_permToBrauer σ)

/-- A diagram propagates no strand exactly when every arc is horizontal. -/
theorem propagatingNumber_eq_zero_iff : D.propagatingNumber = 0 ↔ ∀ x, ¬D.IsThrough x := by
  constructor
  · intro h x
    have hb : D.bottomThrough = ∅ :=
      Finset.card_eq_zero.mp (by rw [← propagatingNumber_eq_card_bottomThrough, h])
    have ht : D.topThrough = ∅ :=
      Finset.card_eq_zero.mp (by rw [← propagatingNumber_eq_card_topThrough, h])
    rcases x with i | j
    · exact fun hi => (Finset.eq_empty_iff_forall_notMem.mp hb i) ((D.mem_bottomThrough).mpr hi)
    · exact fun hj => (Finset.eq_empty_iff_forall_notMem.mp ht j) ((D.mem_topThrough).mpr hj)
  · intro h
    rw [propagatingNumber_eq_card_bottomThrough, Finset.card_eq_zero,
      Finset.eq_empty_iff_forall_notMem]
    exact fun i hi => h _ ((D.mem_bottomThrough).mp hi)

/-- A diagram propagates no strand exactly when it is split: no arc crosses between the bottom
and the top boundary. -/
theorem propagatingNumber_eq_zero_iff_isSplit :
    D.propagatingNumber = 0 ↔ PerfectMatching.IsSplit D := by
  rw [propagatingNumber_eq_zero_iff, PerfectMatching.isSplit_iff]
  refine forall_congr' fun x => ?_
  rw [D.isThrough_def x]
  exact not_not

/-- Only an even number of strands admits a diagram with no through strand. -/
theorem even_of_propagatingNumber_eq_zero (h : D.propagatingNumber = 0) : Even k := by
  obtain ⟨r, hr⟩ := D.even_card_bottomCap
  have hk := D.propagatingNumber_add_card_bottomCap
  exact ⟨r, by omega⟩

end BrauerDiagram

/-- **The diagrams that propagate every strand are the permutation diagrams**, so there are `k !`
of them. -/
theorem card_propagatingNumber_eq_card (k : ℕ) :
    Fintype.card {D : BrauerDiagram k // D.propagatingNumber = k} = k ! := by
  rw [← card_brauerDiagram_forall_isThrough k]
  exact Fintype.card_congr
    (Equiv.subtypeEquivRight fun D => BrauerDiagram.propagatingNumber_eq_card_iff D)

/-- **The diagrams with no through strand are the pairs consisting of a perfect matching of the
bottom points and a perfect matching of the top points.** -/
def propagatingNumberZeroEquiv (k : ℕ) :
    {D : BrauerDiagram k // D.propagatingNumber = 0} ≃
      PerfectMatching (Fin k) × PerfectMatching (Fin k) :=
  (Equiv.subtypeEquivRight fun D => BrauerDiagram.propagatingNumber_eq_zero_iff_isSplit D).trans
    PerfectMatching.sumEquiv

/-- **The number of Brauer diagrams with no through strand.** On `2 * m` strands there are
`((2 * m - 1)‼) ^ 2` of them: one perfect matching of the bottom points and one of the top
points, chosen independently. -/
theorem card_propagatingNumber_eq_zero (m : ℕ) :
    Fintype.card {D : BrauerDiagram (2 * m) // D.propagatingNumber = 0} = ((2 * m - 1)‼) ^ 2 := by
  rw [Fintype.card_congr (propagatingNumberZeroEquiv (2 * m)), Fintype.card_prod,
    card_perfectMatching (Fin (2 * m)) (Fintype.card_fin _), sq]

-- On two strands the cap-cup diagram is the only one with no through strand, and the two
-- permutation diagrams are the other two of the three diagrams in all.
example : Fintype.card {D : BrauerDiagram 2 // D.propagatingNumber = 0} = 1 := by
  have h := card_propagatingNumber_eq_zero 1
  norm_num at h
  exact h

end TauCeti
