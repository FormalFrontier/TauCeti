/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Diagram

/-!
# The boundary points of a Brauer diagram

Every boundary point of a Brauer diagram lies on exactly one of a through strand, a cap or a
cup. This file sorts the boundary points accordingly -- the bottom and top endpoints of the
through strands, the bottom endpoints of the caps and the top endpoints of the cups -- and
follows an arc from one of its endpoints to the other.

Following a through strand matches the bottom endpoints of the through strands with their top
endpoints (`BrauerDiagram.throughEquiv`); since the capped bottom points and the cupped top
points are the points those two sets leave over, a diagram has as many capped bottom points as
cupped top points (`BrauerDiagram.card_bottomCap_eq_card_topCup`), that is, as many caps as
cups. Following a cap instead matches the capped bottom points among themselves
(`BrauerDiagram.capMatching`), so they are even in number; following a cup likewise matches the
cupped top points among themselves (`BrauerDiagram.cupMatching`).

These are the data that vertical stacking consumes: composing `D₁` with `D₂` identifies the
bottom boundary of `D₁` with the top boundary of `D₂` and reads the arcs of the composite by
concatenating through strands (`throughEquiv`) along that middle boundary. Counting the closed
loops that form there, by alternately following the caps of `D₁` (`capMatching`) and the cups of
`D₂` (`cupMatching`), is done in `TauCeti/Combinatorics/Brauer/LoopCount.lean`.

## Main definitions

* `TauCeti.BrauerDiagram.bottomThrough`, `topThrough`, `bottomCap`, `topCup`: the boundary points
  carrying an arc of each kind.
* `TauCeti.BrauerDiagram.throughEquiv`: a through strand matches its bottom endpoint with its top
  endpoint.
* `TauCeti.BrauerDiagram.capMatching`, `TauCeti.BrauerDiagram.cupMatching`: the perfect matchings
  of the capped bottom points and of the cupped top points.

## Main results

* `TauCeti.BrauerDiagram.card_bottomCap_eq_card_topCup`: a diagram has as many capped bottom
  points as cupped top points, hence as many caps as cups.
* `TauCeti.BrauerDiagram.even_card_bottomCap`: a diagram has an even number of capped bottom
  points.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9.
-/

public section

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
  toFun i := ⟨(D.val (Sum.inl i.1)).getRight (isRight_val_inl i.2), by simpa using i.2⟩
  invFun j := ⟨(D.val (Sum.inr j.1)).getLeft (isLeft_val_inr j.2), by simpa using j.2⟩
  left_inv i := Subtype.ext <| (Sum.getLeft_eq_iff _).mpr <| by
    rw [Sum.inr_getRight]
    exact D.apply_apply _
  right_inv j := Subtype.ext <| (Sum.getRight_eq_iff _).mpr <| by
    rw [Sum.inl_getLeft]
    exact D.apply_apply _

/-- The top endpoint that `BrauerDiagram.throughEquiv` assigns to a bottom point is the point
that the diagram matches with it. -/
@[simp]
theorem inr_throughEquiv (i : {i : Fin k // D.IsThrough (Sum.inl i)}) :
    Sum.inr (D.throughEquiv i).1 = D.val (Sum.inl i.1) := Sum.inr_getRight _ _

/-- The bottom endpoint that `BrauerDiagram.throughEquiv` assigns to a top point is the point
that the diagram matches with it. -/
@[simp]
theorem inl_throughEquiv_symm (j : {j : Fin k // D.IsThrough (Sum.inr j)}) :
    Sum.inl (D.throughEquiv.symm j).1 = D.val (Sum.inr j.1) := Sum.inl_getLeft _ _

/-- A diagram has as many bottom endpoints of through strands as top endpoints. -/
theorem card_bottomThrough_eq_card_topThrough : D.bottomThrough.card = D.topThrough.card := by
  rw [bottomThrough, topThrough, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr D.throughEquiv

/-- **A diagram has as many capped bottom points as cupped top points**, hence as many caps as
cups. -/
theorem card_bottomCap_eq_card_topCup : D.bottomCap.card = D.topCup.card := by
  rw [bottomCap_eq_compl, topCup_eq_compl, Finset.card_compl, Finset.card_compl,
    card_bottomThrough_eq_card_topThrough]

/-- The map sending a capped bottom point to the other end of its cap. -/
private def capFun (i : {i : Fin k // D.IsCap (Sum.inl i)}) : {i : Fin k // D.IsCap (Sum.inl i)} :=
  ⟨(D.val (Sum.inl i.1)).getLeft ((D.isCap_def _).mp i.2).2, by simpa using i.2⟩

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

/-- `BrauerDiagram.capMatching` matches a capped bottom point with the other end of its cap. -/
@[simp]
theorem inl_capMatching (i : {i : Fin k // D.IsCap (Sum.inl i)}) :
    Sum.inl (D.capMatching.val i).1 = D.val (Sum.inl i.1) := by
  simpa [capMatching] using inl_capFun D i

/-- **A diagram has an even number of capped bottom points**: the caps pair those points off
among themselves. -/
theorem even_card_bottomCap : Even D.bottomCap.card := by
  rw [bottomCap, ← Fintype.card_subtype]
  exact even_card_of_nonempty_perfectMatching _ ⟨D.capMatching⟩

/-- The map sending a cupped top point to the other end of its cup. -/
private def cupFun (j : {j : Fin k // D.IsCup (Sum.inr j)}) : {j : Fin k // D.IsCup (Sum.inr j)} :=
  ⟨(D.val (Sum.inr j.1)).getRight ((D.isCup_def _).mp j.2).2, by simpa using j.2⟩

private theorem inr_cupFun (j : {j : Fin k // D.IsCup (Sum.inr j)}) :
    Sum.inr (D.cupFun j).1 = D.val (Sum.inr j.1) := Sum.inr_getRight _ _

private theorem cupFun_involutive : Function.Involutive D.cupFun := fun j =>
  Subtype.ext <| Sum.inr_injective <| by
    rw [inr_cupFun D (D.cupFun j), inr_cupFun D j, D.apply_apply]

private theorem cupFun_ne (j : {j : Fin k // D.IsCup (Sum.inr j)}) : D.cupFun j ≠ j := fun h =>
  D.apply_ne (Sum.inr j.1) (by rw [← inr_cupFun D j, h])

/-- The perfect matching that a diagram induces on its cupped top points: the cups pair those
points off among themselves. -/
def cupMatching : PerfectMatching {j : Fin k // D.IsCup (Sum.inr j)} :=
  .mk (cupFun_involutive D).toPerm (fun j => by simpa using cupFun_involutive D j)
    fun j => by simpa using cupFun_ne D j

/-- `BrauerDiagram.cupMatching` matches a cupped top point with the other end of its cup. -/
@[simp]
theorem inr_cupMatching (j : {j : Fin k // D.IsCup (Sum.inr j)}) :
    Sum.inr (D.cupMatching.val j).1 = D.val (Sum.inr j.1) := by
  simpa [cupMatching] using inr_cupFun D j

end BrauerDiagram

end TauCeti
