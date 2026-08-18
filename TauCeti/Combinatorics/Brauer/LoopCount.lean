/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lemmas
public import TauCeti.Combinatorics.Brauer.Compose

/-!
# The middle loops of a stack of two Brauer diagrams

Stacking the Brauer diagram `D₁` above `D₂` identifies the bottom boundary of `D₁` with the top
boundary of `D₂`; the arcs of the two diagrams that meet that middle boundary form strands, and
`TauCeti.composeDiagram` reads off the matching those strands induce on the outer boundary. Some
of the arcs do not reach the outer boundary at all: they close up into **loops** in the middle.
The multiplication of the Brauer algebra on the diagram basis is the composite diagram weighted
by `δ` raised to the number of those loops, so that number is what this file counts.

Both arcs at a middle point `a` -- the arc of `D₁` at its bottom point `a`, and the arc of `D₂`
at its top point `a` -- stay in the middle exactly when the first is a cap of `D₁` and the
second a cup of `D₂` (`TauCeti.IsMiddleVertex`). Joining two middle points whenever an arc of
either kind runs between them gives a graph on the middle boundary
(`TauCeti.MiddleAdj`) in which every point carries at most one arc of each diagram, so a
connected component all of whose points carry both is a cycle: a closed middle loop. That is the
definition used here: `TauCeti.OnMiddleLoop` says that every point reachable from `a` carries
both of its arcs, and `TauCeti.middleLoopCount` counts the loops by counting their least points.

The count is honest in both directions. It is positive as soon as a cap of `D₁` and a cup of
`D₂` join the same pair of middle points (`TauCeti.middleLoopCount_pos_of_val_eq`), which is the
loop that makes the Brauer generator `e` satisfy `e * e = δ • e`; and it vanishes when either
diagram is a permutation diagram (`TauCeti.middleLoopCount_permToBrauer_left` and
`TauCeti.middleLoopCount_permToBrauer_right`), which is why the loop-weighted multiplication will
restrict along `TauCeti.permToBrauer` to the group algebra of the symmetric group. Loops are also
disjoint from the strands that `TauCeti.composeDiagram` reads: no strand starting at the outer
boundary ever visits a point of a middle loop
(`TauCeti.not_onMiddleLoop_of_reflTransGen_stackStep`), so the composite diagram and the loop
count are independent pieces of the same multiplication.

## Main definitions

* `TauCeti.MiddleAdj`: the middle graph of the stack of `D₁` above `D₂`.
* `TauCeti.IsMiddleVertex`: both arcs at a middle point stay in the middle.
* `TauCeti.OnMiddleLoop`: a middle point lies on a closed middle loop.
* `TauCeti.middleLoopCount`: the number of closed middle loops, the exponent of `δ` in the loop
  rule of the Brauer algebra.

## Main results

* `TauCeti.middleLoopCount_eq_zero_iff`: the count vanishes exactly when no middle point lies on
  a loop.
* `TauCeti.middleLoopCount_pos_of_val_eq`: a cap of `D₁` and a cup of `D₂` on the same pair of
  middle points close up into a loop.
* `TauCeti.middleLoopCount_permToBrauer_left`, `TauCeti.middleLoopCount_permToBrauer_right`:
  stacking with a permutation diagram creates no loop.
* `TauCeti.two_mul_middleLoopCount_le`: a loop uses at least two of the `k` middle points, so
  there are at most `k / 2` loops.
* `TauCeti.not_onMiddleLoop_of_reflTransGen_stackStep`: a strand of the stack never visits a
  point of a middle loop.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9.
-/

public section

namespace TauCeti

variable {k : ℕ}

/-- The middle point at which a boundary point of one of the two stacked diagrams sits, read off
by forgetting which of the two boundaries it lies on. Applied to a middle state of
`TauCeti.stackStep` it is the middle point the strand has reached. -/
def middlePoint : Fin k ⊕ Fin k → Fin k := Sum.elim id id

/-- The middle point of a bottom boundary point is its index. -/
@[simp]
theorem middlePoint_inl (a : Fin k) : middlePoint (Sum.inl a) = a := (rfl)

/-- The middle point of a top boundary point is its index. -/
@[simp]
theorem middlePoint_inr (a : Fin k) : middlePoint (Sum.inr a) = a := (rfl)

/-- **The middle graph of a stack.** Two points `a` and `b` of the middle boundary of the stack
of `D₁` above `D₂` are adjacent when a cap of `D₁` or a cup of `D₂` joins them: an arc that
stays in the middle instead of running out to the outer boundary. -/
def MiddleAdj (D₁ D₂ : BrauerDiagram k) (a b : Fin k) : Prop :=
  D₁.val (Sum.inl a) = Sum.inl b ∨ D₂.val (Sum.inr a) = Sum.inr b

/-- Adjacency in the middle graph is a cap of `D₁` or a cup of `D₂` between the two points. -/
theorem middleAdj_def (D₁ D₂ : BrauerDiagram k) (a b : Fin k) :
    MiddleAdj D₁ D₂ a b ↔
      D₁.val (Sum.inl a) = Sum.inl b ∨ D₂.val (Sum.inr a) = Sum.inr b := (Iff.rfl)

/-- **Both arcs at a middle point stay in the middle**: the arc of `D₁` at the bottom point `a`
is a cap, and the arc of `D₂` at the top point `a` is a cup. These are exactly the middle points
that a strand cannot leave the stack through. -/
def IsMiddleVertex (D₁ D₂ : BrauerDiagram k) (a : Fin k) : Prop :=
  D₁.IsCap (Sum.inl a) ∧ D₂.IsCup (Sum.inr a)

/-- Keeping both arcs in the middle is being capped by `D₁` and cupped by `D₂`. -/
theorem isMiddleVertex_def (D₁ D₂ : BrauerDiagram k) (a : Fin k) :
    IsMiddleVertex D₁ D₂ a ↔ D₁.IsCap (Sum.inl a) ∧ D₂.IsCup (Sum.inr a) := (Iff.rfl)

/-- **A middle point lies on a closed loop** of the stack of `D₁` above `D₂` when every middle
point reachable from it in the middle graph keeps both of its arcs in the middle. Each point of
the middle graph carries at most one arc of `D₁` and at most one arc of `D₂`, so such a
connected component is a cycle alternating between caps of `D₁` and cups of `D₂`: a loop that
closes up in the middle. -/
def OnMiddleLoop (D₁ D₂ : BrauerDiagram k) (a : Fin k) : Prop :=
  ∀ b, Relation.ReflTransGen (MiddleAdj D₁ D₂) a b → IsMiddleVertex D₁ D₂ b

/-- Lying on a closed middle loop is every reachable middle point keeping both of its arcs in
the middle. -/
theorem onMiddleLoop_def (D₁ D₂ : BrauerDiagram k) (a : Fin k) :
    OnMiddleLoop D₁ D₂ a ↔
      ∀ b, Relation.ReflTransGen (MiddleAdj D₁ D₂) a b → IsMiddleVertex D₁ D₂ b := (Iff.rfl)

/-- `a` is the least middle point of the closed middle loop it lies on. Each loop has exactly
one such point, so these count the loops. -/
def IsMiddleLoopMin (D₁ D₂ : BrauerDiagram k) (a : Fin k) : Prop :=
  OnMiddleLoop D₁ D₂ a ∧ ∀ b, Relation.ReflTransGen (MiddleAdj D₁ D₂) a b → a ≤ b

/-- Being the least point of a loop is lying on a loop and being below every reachable point. -/
theorem isMiddleLoopMin_def (D₁ D₂ : BrauerDiagram k) (a : Fin k) :
    IsMiddleLoopMin D₁ D₂ a ↔
      OnMiddleLoop D₁ D₂ a ∧ ∀ b, Relation.ReflTransGen (MiddleAdj D₁ D₂) a b → a ≤ b := (Iff.rfl)

/-- **The middle-loop count of a stack of two Brauer diagrams**: the number of loops that close
up in the middle when `D₁` is stacked above `D₂`, counted by their least middle points. This is
the exponent of `δ` in the loop rule that weights the multiplication of the Brauer algebra on
the diagram basis, `D₁ * D₂ = δ ^ middleLoopCount D₁ D₂ • composeDiagram D₁ D₂`. -/
noncomputable def middleLoopCount (D₁ D₂ : BrauerDiagram k) : ℕ :=
  {a : Fin k | IsMiddleLoopMin D₁ D₂ a}.ncard

/-- The middle-loop count is the number of least points of closed middle loops. -/
theorem middleLoopCount_def (D₁ D₂ : BrauerDiagram k) :
    middleLoopCount D₁ D₂ = {a : Fin k | IsMiddleLoopMin D₁ D₂ a}.ncard := (rfl)

variable {D₁ D₂ : BrauerDiagram k}

/-! ### The middle graph -/

/-- The middle graph is symmetric: an arc joining `a` to `b` joins `b` to `a`. -/
theorem MiddleAdj.symm {a b : Fin k} (h : MiddleAdj D₁ D₂ a b) : MiddleAdj D₁ D₂ b a := by
  rcases h with h | h
  · exact Or.inl (D₁.apply_eq_of_apply_eq h)
  · exact Or.inr (D₂.apply_eq_of_apply_eq h)

/-- Reachability in the middle graph is symmetric. -/
theorem MiddleAdj.reflTransGen_symm {a b : Fin k}
    (h : Relation.ReflTransGen (MiddleAdj D₁ D₂) a b) :
    Relation.ReflTransGen (MiddleAdj D₁ D₂) b a :=
  Relation.ReflTransGen.mono (fun _ _ huv => MiddleAdj.symm huv) b a
    (Relation.ReflTransGen.swap b a h)

/-- A cap of `D₁` at the bottom middle point `a` lands at the middle point read off its far
end, the point `BrauerDiagram.capMatching` pairs `a` with. -/
theorem BrauerDiagram.val_inl_eq_inl_middlePoint {D : BrauerDiagram k} {a : Fin k}
    (h : D.IsCap (Sum.inl a)) :
    D.val (Sum.inl a) = Sum.inl (middlePoint (D.val (Sum.inl a))) := by
  rw [← D.inl_capMatching ⟨a, h⟩, middlePoint_inl]

/-- A cup of `D₂` at the top middle point `a` lands at the middle point read off its far end,
the point `BrauerDiagram.cupMatching` pairs `a` with. -/
theorem BrauerDiagram.val_inr_eq_inr_middlePoint {D : BrauerDiagram k} {a : Fin k}
    (h : D.IsCup (Sum.inr a)) :
    D.val (Sum.inr a) = Sum.inr (middlePoint (D.val (Sum.inr a))) := by
  rw [← D.inr_cupMatching ⟨a, h⟩, middlePoint_inr]

/-! ### Points on a closed middle loop -/

/-- A point of a closed middle loop keeps both of its arcs in the middle. -/
theorem OnMiddleLoop.isMiddleVertex {a : Fin k} (h : OnMiddleLoop D₁ D₂ a) :
    IsMiddleVertex D₁ D₂ a :=
  h a .refl

/-- Lying on a closed middle loop is a property of the whole connected component. -/
theorem OnMiddleLoop.reflTransGen {a b : Fin k} (ha : OnMiddleLoop D₁ D₂ a)
    (hab : Relation.ReflTransGen (MiddleAdj D₁ D₂) a b) : OnMiddleLoop D₁ D₂ b :=
  fun c hc => ha c (hab.trans hc)

/-- The cap of `D₁` at a point of a closed middle loop runs to another point of the same
loop. -/
theorem OnMiddleLoop.capPartner {a : Fin k} (h : OnMiddleLoop D₁ D₂ a) :
    OnMiddleLoop D₁ D₂ (middlePoint (D₁.val (Sum.inl a))) :=
  h.reflTransGen (.single (Or.inl (BrauerDiagram.val_inl_eq_inl_middlePoint h.isMiddleVertex.1)))

/-- The cup of `D₂` at a point of a closed middle loop runs to another point of the same
loop. -/
theorem OnMiddleLoop.cupPartner {a : Fin k} (h : OnMiddleLoop D₁ D₂ a) :
    OnMiddleLoop D₁ D₂ (middlePoint (D₂.val (Sum.inr a))) :=
  h.reflTransGen (.single (Or.inr (BrauerDiagram.val_inr_eq_inr_middlePoint h.isMiddleVertex.2)))

/-- **A loop has a least point.** Every point of a closed middle loop reaches the least point of
that loop. -/
theorem OnMiddleLoop.exists_isMiddleLoopMin {a : Fin k} (ha : OnMiddleLoop D₁ D₂ a) :
    ∃ m, IsMiddleLoopMin D₁ D₂ m ∧ Relation.ReflTransGen (MiddleAdj D₁ D₂) a m := by
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image
    {b : Fin k | Relation.ReflTransGen (MiddleAdj D₁ D₂) a b} id (Set.toFinite _) ⟨a, .refl⟩
  refine ⟨m, ⟨ha.reflTransGen hm, fun c hc => hmin c (hm.trans hc)⟩, hm⟩

/-! ### The count -/

/-- **No loop, no count.** The middle-loop count vanishes exactly when no middle point lies on a
closed loop. -/
theorem middleLoopCount_eq_zero_iff :
    middleLoopCount D₁ D₂ = 0 ↔ ∀ a, ¬OnMiddleLoop D₁ D₂ a := by
  rw [middleLoopCount_def, Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
  refine ⟨fun h a ha => ?_, fun h a ha => h a ha.1⟩
  obtain ⟨m, hm, -⟩ := ha.exists_isMiddleLoopMin
  exact h m hm

/-- A middle point on a closed loop makes the count positive. -/
theorem middleLoopCount_pos_of_onMiddleLoop {a : Fin k} (ha : OnMiddleLoop D₁ D₂ a) :
    0 < middleLoopCount D₁ D₂ :=
  Nat.pos_of_ne_zero fun h => (middleLoopCount_eq_zero_iff.mp h) a ha

/-- **A cap of `D₁` matching a cup of `D₂` closes up into a loop.** If the middle points `a` and
`b` are joined both by a cap of `D₁` and by a cup of `D₂`, then `a` lies on a closed middle
loop, namely the two-point loop `{a, b}`. -/
theorem onMiddleLoop_of_val_eq {a b : Fin k} (h₁ : D₁.val (Sum.inl a) = Sum.inl b)
    (h₂ : D₂.val (Sum.inr a) = Sum.inr b) : OnMiddleLoop D₁ D₂ a := by
  have h₁' : D₁.val (Sum.inl b) = Sum.inl a := D₁.apply_eq_of_apply_eq h₁
  have h₂' : D₂.val (Sum.inr b) = Sum.inr a := D₂.apply_eq_of_apply_eq h₂
  have hverta : IsMiddleVertex D₁ D₂ a := by
    constructor <;> simp [BrauerDiagram.isCap_def, BrauerDiagram.isCup_def, h₁, h₂]
  have hvertb : IsMiddleVertex D₁ D₂ b := by
    constructor <;> simp [BrauerDiagram.isCap_def, BrauerDiagram.isCup_def, h₁', h₂']
  intro c hc
  have key : c = a ∨ c = b := by
    induction hc with
    | refl => exact Or.inl rfl
    | @tail u v _ huv ih =>
      rcases ih with rfl | rfl
      · rcases huv with huv | huv
        · exact Or.inr (Sum.inl_injective (h₁ ▸ huv).symm)
        · exact Or.inr (Sum.inr_injective (h₂ ▸ huv).symm)
      · rcases huv with huv | huv
        · exact Or.inl (Sum.inl_injective (h₁' ▸ huv).symm)
        · exact Or.inl (Sum.inr_injective (h₂' ▸ huv).symm)
  rcases key with rfl | rfl
  · exact hverta
  · exact hvertb

/-- **The two-point loop counts.** A cap of `D₁` and a cup of `D₂` joining the same pair of
middle points force at least one closed middle loop. This is the loop behind the Brauer relation
`e * e = δ • e`. -/
theorem middleLoopCount_pos_of_val_eq {a b : Fin k} (h₁ : D₁.val (Sum.inl a) = Sum.inl b)
    (h₂ : D₂.val (Sum.inr a) = Sum.inr b) : 0 < middleLoopCount D₁ D₂ :=
  middleLoopCount_pos_of_onMiddleLoop (onMiddleLoop_of_val_eq h₁ h₂)

/-! ### Stacking with a permutation diagram -/

/-- A middle point whose arc in `D₁` runs through to the outer boundary lies on no middle
loop. -/
theorem not_onMiddleLoop_of_isThrough_left {a : Fin k} (h : D₁.IsThrough (Sum.inl a)) :
    ¬OnMiddleLoop D₁ D₂ a := fun ha =>
  D₁.not_isThrough_of_isCap (Sum.inl a) ha.isMiddleVertex.1 h

/-- A middle point whose arc in `D₂` runs through to the outer boundary lies on no middle
loop. -/
theorem not_onMiddleLoop_of_isThrough_right {a : Fin k} (h : D₂.IsThrough (Sum.inr a)) :
    ¬OnMiddleLoop D₁ D₂ a := fun ha =>
  D₂.not_isThrough_of_isCup (Sum.inr a) ha.isMiddleVertex.2 h

/-- **A permutation diagram on top creates no loop.** -/
@[simp]
theorem middleLoopCount_permToBrauer_left (σ : Equiv.Perm (Fin k)) (D : BrauerDiagram k) :
    middleLoopCount (permToBrauer σ) D = 0 :=
  middleLoopCount_eq_zero_iff.mpr fun _ =>
    not_onMiddleLoop_of_isThrough_left (BrauerDiagram.isThrough_permToBrauer σ _)

/-- **A permutation diagram underneath creates no loop.** -/
@[simp]
theorem middleLoopCount_permToBrauer_right (D : BrauerDiagram k) (σ : Equiv.Perm (Fin k)) :
    middleLoopCount D (permToBrauer σ) = 0 :=
  middleLoopCount_eq_zero_iff.mpr fun _ =>
    not_onMiddleLoop_of_isThrough_right (BrauerDiagram.isThrough_permToBrauer σ _)

/-! ### How many loops there can be -/

/-- **A loop uses at least two middle points**, and distinct loops are disjoint, so there are at
most `k / 2` closed middle loops on `k` strands. -/
theorem two_mul_middleLoopCount_le (D₁ D₂ : BrauerDiagram k) :
    2 * middleLoopCount D₁ D₂ ≤ k := by
  set S : Set (Fin k) := {a | IsMiddleLoopMin D₁ D₂ a} with hSdef
  set f : Fin k → Fin k := fun a => middlePoint (D₁.val (Sum.inl a))
  have hval : ∀ a ∈ S, D₁.val (Sum.inl a) = Sum.inl (f a) := fun a ha =>
    BrauerDiagram.val_inl_eq_inl_middlePoint ha.1.isMiddleVertex.1
  have hadj : ∀ a ∈ S, MiddleAdj D₁ D₂ a (f a) := fun a ha => Or.inl (hval a ha)
  have hne : ∀ a ∈ S, f a ≠ a := by
    intro a ha hfa
    exact D₁.apply_ne (Sum.inl a) (by rw [hval a ha, hfa])
  have hinj : Set.InjOn f S := by
    intro a ha a' ha' h
    have : D₁.val (Sum.inl a) = D₁.val (Sum.inl a') := by rw [hval a ha, hval a' ha', h]
    exact Sum.inl_injective (D₁.val.injective this)
  have hdisj : Disjoint S (f '' S) := by
    rw [Set.disjoint_left]
    rintro b hb ⟨a, ha, rfl⟩
    have hab : Relation.ReflTransGen (MiddleAdj D₁ D₂) a (f a) := .single (hadj a ha)
    exact hne a ha (le_antisymm (hb.2 a (MiddleAdj.reflTransGen_symm hab)) (ha.2 _ hab))
  have hcard : (S ∪ f '' S).ncard = S.ncard + S.ncard := by
    rw [Set.ncard_union_eq hdisj, hinj.ncard_image]
  have hle : (S ∪ f '' S).ncard ≤ (Set.univ : Set (Fin k)).ncard :=
    Set.ncard_le_ncard (Set.subset_univ _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, hcard] at hle
  rw [middleLoopCount_def, ← hSdef]
  omega

/-! ### Loops are disjoint from the strands of the composite -/

/-- **A strand entering the middle boundary enters at a point off every loop.** The first arc of
a strand of the stack crosses the middle boundary along a through strand of one of the two
diagrams, so the middle point it reaches keeps one of its arcs out of the middle. -/
theorem not_onMiddleLoop_of_stackStart (D₁ D₂ : BrauerDiagram k) {x s : Fin k ⊕ Fin k}
    (h : stackStart D₁ D₂ x = Sum.inr s) : ¬OnMiddleLoop D₁ D₂ (middlePoint s) := by
  rcases x with i | j
  · rw [stackStart_inl] at h
    rcases hv : D₂.val (Sum.inl i) with i' | a
    · rw [hv] at h; simp at h
    · rw [hv] at h
      simp only [Sum.elim_inr, Sum.inr.injEq] at h
      subst h
      intro ha
      have hcup := ha.isMiddleVertex.2
      rw [BrauerDiagram.isCup_def, middlePoint_inl, D₂.apply_eq_of_apply_eq hv] at hcup
      simp at hcup
  · rw [stackStart_inr] at h
    rcases hv : D₁.val (Sum.inr j) with a | j'
    · rw [hv] at h
      simp only [Sum.elim_inl, Sum.inr.injEq] at h
      subst h
      intro ha
      have hcap := ha.isMiddleVertex.1
      rw [BrauerDiagram.isCap_def, middlePoint_inr, D₁.apply_eq_of_apply_eq hv] at hcap
      simp at hcap
    · rw [hv] at h; simp at h

/-- **Loops are closed under following a strand backwards.** If the arc continuing a strand from
the middle state `u` stays in the middle, at a middle state `v` sitting on a loop, then `u` sits
on that same loop. -/
theorem onMiddleLoop_of_stackStep (D₁ D₂ : BrauerDiagram k) {u v : Fin k ⊕ Fin k}
    (h : stackStep D₁ D₂ u = Sum.inr v) (hv : OnMiddleLoop D₁ D₂ (middlePoint v)) :
    OnMiddleLoop D₁ D₂ (middlePoint u) := by
  rcases u with a | a
  · rw [stackStep_inl] at h
    rcases hd : D₁.val (Sum.inl a) with a' | j
    · rw [hd] at h
      simp only [Sum.elim_inl, Sum.inr.injEq] at h
      subst h
      rw [middlePoint_inr] at hv
      rw [middlePoint_inl]
      exact hv.reflTransGen (.single (Or.inl (D₁.apply_eq_of_apply_eq hd)))
    · rw [hd] at h; simp at h
  · rw [stackStep_inr] at h
    rcases hd : D₂.val (Sum.inr a) with i | a'
    · rw [hd] at h; simp at h
    · rw [hd] at h
      simp only [Sum.elim_inr, Sum.inr.injEq] at h
      subst h
      rw [middlePoint_inl] at hv
      rw [middlePoint_inr]
      exact hv.reflTransGen (.single (Or.inr (D₂.apply_eq_of_apply_eq hd)))

/-- **A strand of the stack never visits a middle loop.** Following the strand that starts at
the outer point `x` through the middle boundary, every middle state it reaches sits at a middle
point off every closed loop. Together with `TauCeti.composeDiagram_val_eq_iff`, which describes
the arcs of the composite by exactly these strands, this is the sense in which the composite
diagram and the middle-loop count record disjoint parts of the stack. -/
theorem not_onMiddleLoop_of_reflTransGen_stackStep (D₁ D₂ : BrauerDiagram k)
    {x s t : Fin k ⊕ Fin k} (hstart : stackStart D₁ D₂ x = Sum.inr s)
    (hpath : Relation.ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t) :
    ¬OnMiddleLoop D₁ D₂ (middlePoint t) := by
  induction hpath with
  | refl => exact not_onMiddleLoop_of_stackStart D₁ D₂ hstart
  | @tail u v _ hstep ih => exact fun hv => ih (onMiddleLoop_of_stackStep D₁ D₂ hstep hv)

end TauCeti
