/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.Combinatorics.Brauer.Relabel

/-!
# Composing Brauer diagrams

Two Brauer diagrams on `k` strands are composed by **vertical stacking**: place `D₁` above `D₂`,
identify the bottom boundary of `D₁` with the top boundary of `D₂`, and read off the matching
induced on the outer boundary. A strand of the composite starts at an outer point, follows an
arc of one diagram, crosses the middle boundary into the other diagram, and repeats until it
emerges at another outer point; `TauCeti.composeDiagram` is the Brauer diagram of those strands.
It is the multiplication of the Brauer algebra on the diagram basis, up to the power of `δ`
counting the loops that close up in the middle.

A strand is followed here by iterating a single permutation of the stacked boundary points -- the
arcs of the two diagrams, followed by the gluing that identifies the two copies of the middle
boundary -- and stopping the first time an outer point is reached. That the result is again a
perfect matching rests on two identities: the gluing conjugates that permutation into its
inverse, so walking from the far end of a strand retraces it, and the permutation is a gluing
followed by a fixed-point-free involution, so a strand cannot return to its own starting point.

Stacking a permutation diagram onto a diagram creates no new strand, because a permutation diagram
has neither a cap nor a cup: it only renames the boundary points that the strands of the other
diagram end at, that is, it relabels that boundary in the sense of
`TauCeti.BrauerDiagram.relabel`. The consequence that Layer 9 of the Schur--Weyl roadmap is after
is the multiplicativity `TauCeti.composeDiagram_permToBrauer`: stacking two permutation diagrams
gives the permutation diagram of the product, so `σ ↦ permToBrauer σ` turns the group law of `Sₖ`
into the multiplication of the Brauer algebra on the diagram basis. That is the sense in which the
symmetric group sits inside the Brauer algebra: once the loop-weighted multiplication of the
Brauer algebra is available, this is what will make it restrict to the group algebra `ℂ[Sₖ]` along
`permToBrauer`, since no loop can close up in the middle when one of the two diagrams has only
through strands. The middle-loop count itself is built in
`TauCeti/Combinatorics/Brauer/LoopCount.lean`.

## Main definitions

* `TauCeti.composeDiagram`: the composite of two Brauer diagrams, `D₁` stacked above `D₂`.
* `TauCeti.stackStart`, `TauCeti.stackStep`: the first arc of a strand of the stack, and the arc
  continuing it from a point of the middle boundary.

## Main results

* `TauCeti.composeDiagram_val_eq_iff`: the composite matches two outer points exactly when a
  strand joins them, that is, when following the arcs of the two diagrams from the one leads
  through finitely many points of the middle boundary to the other.
* `TauCeti.composeDiagram_val_inl_eq_inl_of_cap_lower`,
  `TauCeti.composeDiagram_val_inr_eq_inr_of_cup_upper`,
  `TauCeti.composeDiagram_val_inl_eq_inr_of_through`,
  `TauCeti.composeDiagram_val_inr_eq_inl_of_through`,
  `TauCeti.composeDiagram_val_inl_eq_inl_of_cap_upper`,
  `TauCeti.composeDiagram_val_inr_eq_inr_of_cup_lower`: the arcs of the composite along the
  strands that leave the middle boundary after at most two crossings.
* `TauCeti.BrauerDiagram.composeDiagram_val_inl_eq_inr_throughEquiv`: a through strand of `D₂`
  continued by a through strand of `D₁` is a through strand of the composite.
* `TauCeti.BrauerDiagram.composeDiagram_val_inl_eq_inl_capMatching`,
  `TauCeti.BrauerDiagram.composeDiagram_val_inr_eq_inr_cupMatching`: the caps of `D₂` are caps of
  the composite, and the cups of `D₁` are cups of the composite.
* `TauCeti.composeDiagram_permToBrauer_left` and
  `TauCeti.composeDiagram_permToBrauer_right`: stacking a permutation diagram above or below a
  diagram relabels that diagram's top or bottom boundary.
* `TauCeti.composeDiagram_permToBrauer`: stacking permutation diagrams multiplies the
  permutations.
* `TauCeti.composeDiagram_permToBrauer_one_left` and
  `TauCeti.composeDiagram_permToBrauer_one_right`: the identity diagram is a two-sided identity
  for stacking.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9.
-/

public section

namespace TauCeti

variable {k : ℕ}

/-- The boundary points of `D₁` stacked above `D₂`. The points `Sum.inl x` are the outer
boundary of the composite: `Sum.inl (Sum.inl i)` is its bottom point `i`, a bottom point of `D₂`,
and `Sum.inl (Sum.inr j)` its top point `j`, a top point of `D₁`. The points `Sum.inr x` are the
middle boundary, taken twice: `Sum.inr (Sum.inl a)` is the middle point `a` seen as a top point
of `D₂`, and `Sum.inr (Sum.inr a)` the same point seen as a bottom point of `D₁`. -/
private abbrev StackPt (k : ℕ) := (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k)

/-- The boundary of the lower diagram inside the stacked boundary. -/
private def lowerPt : Fin k ⊕ Fin k → StackPt k
  | Sum.inl i => Sum.inl (Sum.inl i)
  | Sum.inr a => Sum.inr (Sum.inl a)

/-- The boundary of the upper diagram inside the stacked boundary. -/
private def upperPt : Fin k ⊕ Fin k → StackPt k
  | Sum.inl a => Sum.inr (Sum.inr a)
  | Sum.inr j => Sum.inl (Sum.inr j)

private theorem lowerPt_injective : Function.Injective (lowerPt (k := k)) := by
  rintro (i | a) (i' | a') h <;> simp_all [lowerPt]

private theorem upperPt_injective : Function.Injective (upperPt (k := k)) := by
  rintro (a | j) (a' | j') h <;> simp_all [upperPt]

namespace BrauerDiagram

variable (D₁ D₂ : BrauerDiagram k)

/-- The arcs of the two stacked diagrams, as an involution of the stacked boundary points. -/
private def stackFun : StackPt k → StackPt k
  | Sum.inl (Sum.inl i) => lowerPt (D₂.val (Sum.inl i))
  | Sum.inl (Sum.inr j) => upperPt (D₁.val (Sum.inr j))
  | Sum.inr (Sum.inl a) => lowerPt (D₂.val (Sum.inr a))
  | Sum.inr (Sum.inr a) => upperPt (D₁.val (Sum.inl a))

private theorem stackFun_lowerPt (x : Fin k ⊕ Fin k) :
    stackFun D₁ D₂ (lowerPt x) = lowerPt (D₂.val x) := by
  rcases x with i | a <;> rfl

private theorem stackFun_upperPt (x : Fin k ⊕ Fin k) :
    stackFun D₁ D₂ (upperPt x) = upperPt (D₁.val x) := by
  rcases x with a | j <;> rfl

private theorem exists_lowerPt_or_upperPt (p : StackPt k) :
    (∃ x, p = lowerPt x) ∨ ∃ x, p = upperPt x := by
  rcases p with (i | j) | (a | a)
  exacts [Or.inl ⟨Sum.inl i, rfl⟩, Or.inr ⟨Sum.inr j, rfl⟩, Or.inl ⟨Sum.inr a, rfl⟩,
    Or.inr ⟨Sum.inl a, rfl⟩]

private theorem stackFun_involutive : Function.Involutive (stackFun D₁ D₂) := by
  intro p
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := exists_lowerPt_or_upperPt p
  · rw [stackFun_lowerPt, stackFun_lowerPt, D₂.apply_apply]
  · rw [stackFun_upperPt, stackFun_upperPt, D₁.apply_apply]

private theorem stackFun_ne (p : StackPt k) : stackFun D₁ D₂ p ≠ p := by
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := exists_lowerPt_or_upperPt p
  · rw [stackFun_lowerPt]
    exact fun h => D₂.apply_ne x (lowerPt_injective h)
  · rw [stackFun_upperPt]
    exact fun h => D₁.apply_ne x (upperPt_injective h)

/-- The gluing that identifies the two copies of the middle boundary; it fixes the outer
boundary. -/
private def glue : StackPt k → StackPt k
  | Sum.inl x => Sum.inl x
  | Sum.inr x => Sum.inr x.swap

private theorem glue_involutive : Function.Involutive (glue (k := k)) := by
  rintro (x | x) <;> simp [glue]

private theorem glue_inl (x : Fin k ⊕ Fin k) : glue (Sum.inl x) = Sum.inl x := rfl

private theorem isLeft_glue (p : StackPt k) : (glue p).isLeft = p.isLeft := by
  rcases p with x | x <;> rfl

private theorem isLeft_of_glue_eq {p : StackPt k} (h : glue p = p) : p.isLeft := by
  rcases p with x | x
  · rfl
  · rcases x with a | a <;> simp [glue] at h

/-- Following a strand one step: an arc of one of the two diagrams, then the gluing. -/
private def walk : Equiv.Perm (StackPt k) :=
  (stackFun_involutive D₁ D₂).toPerm.trans (glue_involutive (k := k)).toPerm

private theorem walk_apply (p : StackPt k) : walk D₁ D₂ p = glue (stackFun D₁ D₂ p) := rfl

private theorem walk_inl_inl (i : Fin k) :
    walk D₁ D₂ (Sum.inl (Sum.inl i)) = glue (lowerPt (D₂.val (Sum.inl i))) := rfl

private theorem walk_inl_inr (j : Fin k) :
    walk D₁ D₂ (Sum.inl (Sum.inr j)) = glue (upperPt (D₁.val (Sum.inr j))) := rfl

private theorem walk_inr_inl (a : Fin k) :
    walk D₁ D₂ (Sum.inr (Sum.inl a)) = glue (lowerPt (D₂.val (Sum.inr a))) := rfl

private theorem walk_inr_inr (a : Fin k) :
    walk D₁ D₂ (Sum.inr (Sum.inr a)) = glue (upperPt (D₁.val (Sum.inl a))) := rfl

private theorem walk_inv_apply (p : StackPt k) :
    (walk D₁ D₂)⁻¹ p = stackFun D₁ D₂ (glue p) := rfl

private theorem glue_walk (p : StackPt k) :
    glue (walk D₁ D₂ p) = (walk D₁ D₂)⁻¹ (glue p) := by
  rw [walk_apply, glue_involutive, walk_inv_apply, glue_involutive]

private theorem glue_walk_pow (n : ℕ) (p : StackPt k) :
    glue ((walk D₁ D₂ ^ n) p) = ((walk D₁ D₂ ^ n)⁻¹) (glue p) := by
  rw [← inv_pow]
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, glue_walk, ih]

/-- Walking `j` steps from the far end of a strand retraces `j` of its steps. -/
private theorem walk_pow_of_walk_pow {x y : Fin k ⊕ Fin k} {n j : ℕ} (hj : j ≤ n)
    (h : (walk D₁ D₂ ^ n) (Sum.inl x) = Sum.inl y) :
    (walk D₁ D₂ ^ j) (Sum.inl y) = glue ((walk D₁ D₂ ^ (n - j)) (Sum.inl x)) := by
  have hjn : j + (n - j) = n := by omega
  have hsplit : (walk D₁ D₂ ^ j) ((walk D₁ D₂ ^ (n - j)) (Sum.inl x)) = Sum.inl y := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, hjn, h]
  have h₁ : glue ((walk D₁ D₂ ^ j) (Sum.inl y)) = ((walk D₁ D₂ ^ j)⁻¹) (Sum.inl y) := by
    rw [glue_walk_pow, glue_inl]
  have h₂ : ((walk D₁ D₂ ^ j)⁻¹) (Sum.inl y) = (walk D₁ D₂ ^ (n - j)) (Sum.inl x) := by
    rw [← hsplit]
    simp
  rw [← h₂, ← h₁, glue_involutive]

private theorem exists_isLeft_walk_pow (x : Fin k ⊕ Fin k) :
    ∃ n, ((walk D₁ D₂ ^ (n + 1)) (Sum.inl x)).isLeft := by
  refine ⟨orderOf (walk D₁ D₂) - 1, ?_⟩
  rw [Nat.sub_add_cancel (orderOf_pos _), pow_orderOf_eq_one]
  rfl

/-- The number of times the strand starting at the outer point `x` crosses the middle
boundary. -/
private def exitTime (x : Fin k ⊕ Fin k) : ℕ := Nat.find (exists_isLeft_walk_pow D₁ D₂ x)

private theorem isLeft_walk_pow_exitTime (x : Fin k ⊕ Fin k) :
    ((walk D₁ D₂ ^ (exitTime D₁ D₂ x + 1)) (Sum.inl x)).isLeft :=
  Nat.find_spec (exists_isLeft_walk_pow D₁ D₂ x)

private theorem not_isLeft_walk_pow_of_lt (x : Fin k ⊕ Fin k) {m : ℕ}
    (hm : m < exitTime D₁ D₂ x) : ¬((walk D₁ D₂ ^ (m + 1)) (Sum.inl x)).isLeft :=
  Nat.find_min (exists_isLeft_walk_pow D₁ D₂ x) hm

/-- The outer point at which the strand starting at the outer point `x` emerges. -/
private def stackVal (x : Fin k ⊕ Fin k) : Fin k ⊕ Fin k :=
  ((walk D₁ D₂ ^ (exitTime D₁ D₂ x + 1)) (Sum.inl x)).getLeft (isLeft_walk_pow_exitTime D₁ D₂ x)

private theorem inl_stackVal (x : Fin k ⊕ Fin k) :
    Sum.inl (stackVal D₁ D₂ x) = (walk D₁ D₂ ^ (exitTime D₁ D₂ x + 1)) (Sum.inl x) :=
  Sum.inl_getLeft _ _

/-- A strand that reaches the outer boundary for the first time after `n + 1` steps emerges
where those steps end. -/
private theorem stackVal_eq_of_exit {x y : Fin k ⊕ Fin k} {n : ℕ}
    (hn : (walk D₁ D₂ ^ (n + 1)) (Sum.inl x) = Sum.inl y)
    (hmin : ∀ m < n, ¬((walk D₁ D₂ ^ (m + 1)) (Sum.inl x)).isLeft) :
    stackVal D₁ D₂ x = y := by
  have hexit : exitTime D₁ D₂ x = n := (Nat.find_eq_iff _).mpr ⟨by rw [hn]; rfl, hmin⟩
  apply Sum.inl_injective
  rw [inl_stackVal, hexit, hn]

private theorem stackVal_involutive : Function.Involutive (stackVal D₁ D₂) := by
  intro x
  have h : (walk D₁ D₂ ^ (exitTime D₁ D₂ x + 1)) (Sum.inl x) = Sum.inl (stackVal D₁ D₂ x) :=
    (inl_stackVal D₁ D₂ x).symm
  have key : ∀ j ≤ exitTime D₁ D₂ x + 1, (walk D₁ D₂ ^ j) (Sum.inl (stackVal D₁ D₂ x))
      = glue ((walk D₁ D₂ ^ (exitTime D₁ D₂ x + 1 - j)) (Sum.inl x)) :=
    fun j hj => walk_pow_of_walk_pow D₁ D₂ hj h
  refine stackVal_eq_of_exit D₁ D₂ (n := exitTime D₁ D₂ x) ?_ fun m hm => ?_
  · have hend := key (exitTime D₁ D₂ x + 1) le_rfl
    rwa [Nat.sub_self, pow_zero, Equiv.Perm.one_apply, glue_inl] at hend
  · have hstep := key (m + 1) (by omega)
    have hsub : exitTime D₁ D₂ x + 1 - (m + 1) = exitTime D₁ D₂ x - m - 1 + 1 := by omega
    rw [hstep, isLeft_glue, hsub]
    exact not_isLeft_walk_pow_of_lt D₁ D₂ x (by omega)

private theorem stackVal_ne (x : Fin k ⊕ Fin k) : stackVal D₁ D₂ x ≠ x := by
  intro hx
  have h : (walk D₁ D₂ ^ (exitTime D₁ D₂ x + 1)) (Sum.inl x) = Sum.inl x := by
    rw [← inl_stackVal, hx]
  have key : ∀ j ≤ exitTime D₁ D₂ x + 1, (walk D₁ D₂ ^ j) (Sum.inl x)
      = glue ((walk D₁ D₂ ^ (exitTime D₁ D₂ x + 1 - j)) (Sum.inl x)) :=
    fun j hj => walk_pow_of_walk_pow D₁ D₂ hj h
  rcases Nat.even_or_odd (exitTime D₁ D₂ x + 1) with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hmid := key r (by omega)
    have hsub : exitTime D₁ D₂ x + 1 - r = r := by omega
    have hpred : r - 1 + 1 = r := by omega
    rw [hsub] at hmid
    refine not_isLeft_walk_pow_of_lt D₁ D₂ x (m := r - 1) (by omega) ?_
    rw [hpred]
    exact isLeft_of_glue_eq hmid.symm
  · have hmid := key (r + 1) (by omega)
    have hsub : exitTime D₁ D₂ x + 1 - (r + 1) = r := by omega
    rw [hsub, pow_succ', Equiv.Perm.mul_apply, walk_apply] at hmid
    exact stackFun_ne D₁ D₂ _ (glue_involutive.injective hmid)

end BrauerDiagram

/-- **Vertical stacking of Brauer diagrams.** `composeDiagram D₁ D₂` places `D₁` above `D₂`,
identifies the bottom boundary of `D₁` with the top boundary of `D₂`, and matches two points of
the outer boundary when a strand joins them: a strand follows an arc of one diagram, crosses the
middle boundary into the other, and repeats until it reaches the outer boundary again. This is
the multiplication of the Brauer algebra on the diagram basis, up to the power of `δ` counting
the loops that close up in the middle. -/
def composeDiagram (D₁ D₂ : BrauerDiagram k) : BrauerDiagram k :=
  .mk (BrauerDiagram.stackVal_involutive D₁ D₂).toPerm
    (fun x => by simpa using BrauerDiagram.stackVal_involutive D₁ D₂ x)
    fun x => by simpa using BrauerDiagram.stackVal_ne D₁ D₂ x

/-- Following a strand of the stack of `D₁` above `D₂` one arc further, from a **middle state**:
a point of the middle boundary together with the diagram the strand runs through next. The
middle state `Sum.inl a` is the middle point `a` reached as a bottom point of the upper diagram
`D₁`, so the strand next follows the arc of `D₁` at `Sum.inl a`; the middle state `Sum.inr a` is
the middle point `a` reached as a top point of the lower diagram `D₂`, so the strand next follows
the arc of `D₂` at `Sum.inr a`. The value is `Sum.inl y` when that arc leaves the stack at the
outer point `y`, and `Sum.inr t` when it crosses the middle boundary again, at the middle state
`t`. -/
def stackStep (D₁ D₂ : BrauerDiagram k) : Fin k ⊕ Fin k → (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k)
  | Sum.inl a =>
    (D₁.val (Sum.inl a)).elim (fun a' => Sum.inr (Sum.inr a')) fun j => Sum.inl (Sum.inr j)
  | Sum.inr a =>
    (D₂.val (Sum.inr a)).elim (fun i => Sum.inl (Sum.inl i)) fun a' => Sum.inr (Sum.inl a')

/-- Following the strand of the stack of `D₁` above `D₂` that starts at the outer point `x` along
its first arc, an arc of `D₂` at a bottom point `x = Sum.inl i` and an arc of `D₁` at a top point
`x = Sum.inr j`. The value is `Sum.inl y` when that arc already leaves the stack, at the outer
point `y`, and `Sum.inr s` when it crosses the middle boundary, at the middle state `s` of
`TauCeti.stackStep`. -/
def stackStart (D₁ D₂ : BrauerDiagram k) : Fin k ⊕ Fin k → (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k)
  | Sum.inl i =>
    (D₂.val (Sum.inl i)).elim (fun i' => Sum.inl (Sum.inl i')) fun a => Sum.inr (Sum.inl a)
  | Sum.inr j =>
    (D₁.val (Sum.inr j)).elim (fun a => Sum.inr (Sum.inr a)) fun j' => Sum.inl (Sum.inr j')

/-- A strand at the middle point `a`, about to run up through `D₁`, follows the arc of `D₁`
at `Sum.inl a`. -/
@[simp]
theorem stackStep_inl (D₁ D₂ : BrauerDiagram k) (a : Fin k) : stackStep D₁ D₂ (Sum.inl a) =
    (D₁.val (Sum.inl a)).elim (fun a' => Sum.inr (Sum.inr a')) fun j => Sum.inl (Sum.inr j) :=
  (rfl)

/-- A strand at the middle point `a`, about to run down through `D₂`, follows the arc of `D₂`
at `Sum.inr a`. -/
@[simp]
theorem stackStep_inr (D₁ D₂ : BrauerDiagram k) (a : Fin k) : stackStep D₁ D₂ (Sum.inr a) =
    (D₂.val (Sum.inr a)).elim (fun i => Sum.inl (Sum.inl i)) fun a' => Sum.inr (Sum.inl a') :=
  (rfl)

/-- A strand starting at the bottom point `i` of the stack follows the arc of `D₂` at
`Sum.inl i`. -/
@[simp]
theorem stackStart_inl (D₁ D₂ : BrauerDiagram k) (i : Fin k) : stackStart D₁ D₂ (Sum.inl i) =
    (D₂.val (Sum.inl i)).elim (fun i' => Sum.inl (Sum.inl i')) fun a => Sum.inr (Sum.inl a) :=
  (rfl)

/-- A strand starting at the top point `j` of the stack follows the arc of `D₁` at
`Sum.inr j`. -/
@[simp]
theorem stackStart_inr (D₁ D₂ : BrauerDiagram k) (j : Fin k) : stackStart D₁ D₂ (Sum.inr j) =
    (D₁.val (Sum.inr j)).elim (fun a => Sum.inr (Sum.inr a)) fun j' => Sum.inl (Sum.inr j') :=
  (rfl)

namespace BrauerDiagram

variable (D₁ D₂ : BrauerDiagram k)

private theorem composeDiagram_val (x : Fin k ⊕ Fin k) :
    (composeDiagram D₁ D₂).val x = stackVal D₁ D₂ x := by
  simp [composeDiagram]

/-- The first step of the walk, read off the first arc of the strand. The middle state `s` sits
at the stacked point `Sum.inr s.swap`. -/
private theorem walk_inl_eq (x : Fin k ⊕ Fin k) :
    walk D₁ D₂ (Sum.inl x) = (stackStart D₁ D₂ x).elim Sum.inl fun s => Sum.inr s.swap := by
  rcases x with i | j
  · rcases h : D₂.val (Sum.inl i) with i' | a <;>
      simp [walk_inl_inl, stackStart_inl, h, glue, lowerPt]
  · rcases h : D₁.val (Sum.inr j) with a | j' <;>
      simp [walk_inl_inr, stackStart_inr, h, glue, upperPt]

/-- A later step of the walk, read off the next arc of the strand. -/
private theorem walk_inr_swap (s : Fin k ⊕ Fin k) :
    walk D₁ D₂ (Sum.inr s.swap) = (stackStep D₁ D₂ s).elim Sum.inl fun t => Sum.inr t.swap := by
  rcases s with a | a
  · rcases h : D₁.val (Sum.inl a) with a' | j <;>
      simp [walk_inr_inr, stackStep_inl, h, glue, upperPt]
  · rcases h : D₂.val (Sum.inr a) with i | a' <;>
      simp [walk_inr_inl, stackStep_inr, h, glue, lowerPt]

/-- A strand whose first arc crosses the middle boundary at the middle state `s` is walked from
`s` on. -/
private theorem walk_pow_succ_inl {x s : Fin k ⊕ Fin k} (h : stackStart D₁ D₂ x = Sum.inr s)
    (m : ℕ) : (walk D₁ D₂ ^ (m + 1)) (Sum.inl x) = (walk D₁ D₂ ^ m) (Sum.inr s.swap) := by
  rw [pow_succ, Equiv.Perm.mul_apply, walk_inl_eq, h]
  rfl

/-- A chain of middle states is walked without meeting the outer boundary. -/
private theorem exists_walk_pow_of_reflTransGen {s t : Fin k ⊕ Fin k}
    (h : Relation.ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t) :
    ∃ n, (walk D₁ D₂ ^ n) (Sum.inr s.swap) = Sum.inr t.swap ∧
      ∀ m ≤ n, ¬((walk D₁ D₂ ^ m) (Sum.inr s.swap)).isLeft := by
  induction h with
  | refl => exact ⟨0, by simp, fun m hm => by rw [Nat.le_zero.mp hm]; simp⟩
  | @tail u v _ hstep ih =>
    obtain ⟨n, hn, hmin⟩ := ih
    have hnext : (walk D₁ D₂ ^ (n + 1)) (Sum.inr s.swap) = Sum.inr v.swap := by
      rw [pow_succ', Equiv.Perm.mul_apply, hn, walk_inr_swap, hstep]
      rfl
    refine ⟨n + 1, hnext, fun m hm => ?_⟩
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact hmin m (by omega)
    · rw [Nat.le_antisymm hm hge, hnext]
      simp

/-- A walk that stays off the outer boundary follows a chain of middle states. -/
private theorem exists_reflTransGen_of_walk_pow (s : Fin k ⊕ Fin k) (n : ℕ)
    (h : ∀ m ≤ n, ¬((walk D₁ D₂ ^ m) (Sum.inr s.swap)).isLeft) :
    ∃ t, (walk D₁ D₂ ^ n) (Sum.inr s.swap) = Sum.inr t.swap ∧
      Relation.ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t := by
  induction n with
  | zero => exact ⟨s, by simp, .refl⟩
  | succ n ih =>
    obtain ⟨t, ht, hpath⟩ := ih fun m hm => h m (by omega)
    have hnext : (walk D₁ D₂ ^ (n + 1)) (Sum.inr s.swap)
        = (stackStep D₁ D₂ t).elim Sum.inl fun u => Sum.inr u.swap := by
      rw [pow_succ', Equiv.Perm.mul_apply, ht, walk_inr_swap]
    rcases hstep : stackStep D₁ D₂ t with y | u
    · exact absurd (by rw [hnext, hstep]; rfl) (h (n + 1) le_rfl)
    · exact ⟨u, by rw [hnext, hstep]; rfl, hpath.tail hstep⟩

end BrauerDiagram

variable (D₁ D₂ : BrauerDiagram k)

/-- The middle leg of the strand. If the strand from `x` crosses the middle boundary at `s` and
the stack exits at `y`, then it reaches some middle state `t` from which `stackStep` leaves at `y`.
The exit time cannot be zero, because the first step lands in the middle. -/
private theorem exists_reflTransGen_stackStep_eq_inl_of_stackStart_eq_inr
    {x y s : Fin k ⊕ Fin k} (hstart : stackStart D₁ D₂ x = Sum.inr s)
    (hexit : (BrauerDiagram.walk D₁ D₂ ^ (BrauerDiagram.exitTime D₁ D₂ x + 1)) (Sum.inl x)
      = Sum.inl y) :
    ∃ t, Relation.ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t ∧
      stackStep D₁ D₂ t = Sum.inl y := by
  have hshift := BrauerDiagram.walk_pow_succ_inl D₁ D₂ hstart
  obtain ⟨n, hn⟩ : ∃ n, BrauerDiagram.exitTime D₁ D₂ x = n + 1 := by
    rcases Nat.eq_zero_or_pos (BrauerDiagram.exitTime D₁ D₂ x) with h₀ | h₀
    · rw [h₀, hshift 0] at hexit
      exact absurd hexit (by simp)
    · exact ⟨BrauerDiagram.exitTime D₁ D₂ x - 1, by omega⟩
  rw [hn] at hexit
  obtain ⟨t, ht, hpath⟩ := BrauerDiagram.exists_reflTransGen_of_walk_pow D₁ D₂ s n
    fun m hm => by
      rw [← hshift]
      exact BrauerDiagram.not_isLeft_walk_pow_of_lt D₁ D₂ x (by omega)
  refine ⟨t, hpath, ?_⟩
  rw [hshift (n + 1), pow_succ', Equiv.Perm.mul_apply, ht,
    BrauerDiagram.walk_inr_swap] at hexit
  rcases hstep : stackStep D₁ D₂ t with y' | u
  · rw [hstep] at hexit
    simpa using hexit
  · rw [hstep] at hexit
    exact absurd hexit (by simp)

/-- Forward direction of `composeDiagram_val_eq_iff`: if the stack sends `x` to `y`, then the
strand from `x` either leaves at `y` immediately or crosses the middle boundary, runs through
finitely many middle states, and leaves at `y`. -/
private theorem stackStart_eq_or_exists_reflTransGen_of_composeDiagram_val
    {x y : Fin k ⊕ Fin k} (hxy : (composeDiagram D₁ D₂).val x = y) :
    stackStart D₁ D₂ x = Sum.inl y ∨
      ∃ s t, stackStart D₁ D₂ x = Sum.inr s ∧
        Relation.ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t ∧
          stackStep D₁ D₂ t = Sum.inl y := by
  rw [BrauerDiagram.composeDiagram_val] at hxy
  have hexit : (BrauerDiagram.walk D₁ D₂ ^ (BrauerDiagram.exitTime D₁ D₂ x + 1)) (Sum.inl x)
      = Sum.inl y := by rw [← BrauerDiagram.inl_stackVal, hxy]
  rcases hstart : stackStart D₁ D₂ x with y' | s
  · left
    have h₁ : BrauerDiagram.walk D₁ D₂ (Sum.inl x) = Sum.inl y' := by
      rw [BrauerDiagram.walk_inl_eq, hstart]; rfl
    rcases Nat.eq_zero_or_pos (BrauerDiagram.exitTime D₁ D₂ x) with h₀ | h₀
    · rwa [h₀, zero_add, pow_one, h₁] at hexit
    · exact absurd (by rw [zero_add, pow_one, h₁]; rfl)
        (BrauerDiagram.not_isLeft_walk_pow_of_lt D₁ D₂ x h₀)
  · obtain ⟨t, hpath, hstep⟩ :=
      exists_reflTransGen_stackStep_eq_inl_of_stackStart_eq_inr D₁ D₂ hstart hexit
    exact Or.inr ⟨s, t, rfl, hpath, hstep⟩

/-- Backward direction of `composeDiagram_val_eq_iff`: a strand that leaves the stack at `y`,
immediately or after finitely many middle states, witnesses that the stack sends `x` to `y`. -/
private theorem composeDiagram_val_eq_of_stackStart_eq_or_exists_reflTransGen
    {x y : Fin k ⊕ Fin k}
    (h :
    stackStart D₁ D₂ x = Sum.inl y ∨
      ∃ s t, stackStart D₁ D₂ x = Sum.inr s ∧
        Relation.ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t ∧
          stackStep D₁ D₂ t = Sum.inl y) :
    (composeDiagram D₁ D₂).val x = y := by
  rw [BrauerDiagram.composeDiagram_val]
  rcases h with h | ⟨s, t, hstart, hpath, hstep⟩
  · refine BrauerDiagram.stackVal_eq_of_exit D₁ D₂ (n := 0) ?_ (by simp)
    rw [zero_add, pow_one, BrauerDiagram.walk_inl_eq, h]
    rfl
  · obtain ⟨n, hn, hmin⟩ := BrauerDiagram.exists_walk_pow_of_reflTransGen D₁ D₂ hpath
    have hshift := BrauerDiagram.walk_pow_succ_inl D₁ D₂ hstart
    refine BrauerDiagram.stackVal_eq_of_exit D₁ D₂ (n := n + 1) ?_ fun m hm => ?_
    · rw [hshift (n + 1), pow_succ', Equiv.Perm.mul_apply, hn,
        BrauerDiagram.walk_inr_swap, hstep]
      rfl
    · rw [hshift m]
      exact hmin m (by omega)

/-- **The strands of a stack of two Brauer diagrams.** The composite of `D₁` above `D₂` matches
the outer points `x` and `y` exactly when the strand starting at `x` emerges at `y`: either its
first arc already leaves the stack at `y`, or it crosses the middle boundary at a middle state
`s`, runs from there through finitely many further middle states to a middle state `t`, and
leaves the stack at `y` from `t`. -/
theorem composeDiagram_val_eq_iff {x y : Fin k ⊕ Fin k} :
    (composeDiagram D₁ D₂).val x = y ↔
      stackStart D₁ D₂ x = Sum.inl y ∨
        ∃ s t, stackStart D₁ D₂ x = Sum.inr s ∧
          Relation.ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t ∧
            stackStep D₁ D₂ t = Sum.inl y :=
  ⟨stackStart_eq_or_exists_reflTransGen_of_composeDiagram_val D₁ D₂,
    composeDiagram_val_eq_of_stackStart_eq_or_exists_reflTransGen D₁ D₂⟩

/-- **A cap of the lower diagram is a cap of the composite.** -/
theorem composeDiagram_val_inl_eq_inl_of_cap_lower {i i' : Fin k}
    (h : D₂.val (Sum.inl i) = Sum.inl i') :
    (composeDiagram D₁ D₂).val (Sum.inl i) = Sum.inl i' :=
  (composeDiagram_val_eq_iff D₁ D₂).mpr <| Or.inl <| by rw [stackStart_inl, h, Sum.elim_inl]

/-- **A cup of the upper diagram is a cup of the composite.** -/
theorem composeDiagram_val_inr_eq_inr_of_cup_upper {j j' : Fin k}
    (h : D₁.val (Sum.inr j) = Sum.inr j') :
    (composeDiagram D₁ D₂).val (Sum.inr j) = Sum.inr j' :=
  (composeDiagram_val_eq_iff D₁ D₂).mpr <| Or.inl <| by rw [stackStart_inr, h, Sum.elim_inr]

/-- **A through strand of the lower diagram continued by a through strand of the upper diagram
is a through strand of the composite.** -/
theorem composeDiagram_val_inl_eq_inr_of_through {i a j : Fin k}
    (h₂ : D₂.val (Sum.inl i) = Sum.inr a) (h₁ : D₁.val (Sum.inl a) = Sum.inr j) :
    (composeDiagram D₁ D₂).val (Sum.inl i) = Sum.inr j :=
  (composeDiagram_val_eq_iff D₁ D₂).mpr <| Or.inr
    ⟨Sum.inl a, Sum.inl a, by rw [stackStart_inl, h₂, Sum.elim_inr], .refl,
      by rw [stackStep_inl, h₁, Sum.elim_inr]⟩

/-- **A through strand of the composite, read from its top endpoint.** -/
theorem composeDiagram_val_inr_eq_inl_of_through {i a j : Fin k}
    (h₁ : D₁.val (Sum.inr j) = Sum.inl a) (h₂ : D₂.val (Sum.inr a) = Sum.inl i) :
    (composeDiagram D₁ D₂).val (Sum.inr j) = Sum.inl i :=
  (composeDiagram_val_eq_iff D₁ D₂).mpr <| Or.inr
    ⟨Sum.inr a, Sum.inr a, by rw [stackStart_inr, h₁, Sum.elim_inl], .refl,
      by rw [stackStep_inr, h₂, Sum.elim_inl]⟩

/-- **A cap of the upper diagram, reached by two through strands of the lower one, is a cap of
the composite.** -/
theorem composeDiagram_val_inl_eq_inl_of_cap_upper {i a a' i' : Fin k}
    (h₂ : D₂.val (Sum.inl i) = Sum.inr a) (h₁ : D₁.val (Sum.inl a) = Sum.inl a')
    (h₂' : D₂.val (Sum.inr a') = Sum.inl i') :
    (composeDiagram D₁ D₂).val (Sum.inl i) = Sum.inl i' :=
  (composeDiagram_val_eq_iff D₁ D₂).mpr <| Or.inr
    ⟨Sum.inl a, Sum.inr a', by rw [stackStart_inl, h₂, Sum.elim_inr],
      .single (by rw [stackStep_inl, h₁, Sum.elim_inl]), by rw [stackStep_inr, h₂', Sum.elim_inl]⟩

/-- **A cup of the lower diagram, reached by two through strands of the upper one, is a cup of
the composite.** -/
theorem composeDiagram_val_inr_eq_inr_of_cup_lower {j a a' j' : Fin k}
    (h₁ : D₁.val (Sum.inr j) = Sum.inl a) (h₂ : D₂.val (Sum.inr a) = Sum.inr a')
    (h₁' : D₁.val (Sum.inl a') = Sum.inr j') :
    (composeDiagram D₁ D₂).val (Sum.inr j) = Sum.inr j' :=
  (composeDiagram_val_eq_iff D₁ D₂).mpr <| Or.inr
    ⟨Sum.inr a, Sum.inl a', by rw [stackStart_inr, h₁, Sum.elim_inl],
      .single (by rw [stackStep_inr, h₂, Sum.elim_inr]), by rw [stackStep_inl, h₁', Sum.elim_inr]⟩

namespace BrauerDiagram

/-- **A through strand of `D₂` continued by a through strand of `D₁` is a through strand of the
composite**: the composite joins the bottom endpoint of a through strand of `D₂` to the top
endpoint of the through strand of `D₁` that continues it. -/
theorem composeDiagram_val_inl_eq_inr_throughEquiv
    (i : {i : Fin k // D₂.IsThrough (Sum.inl i)})
    (h : D₁.IsThrough (Sum.inl (D₂.throughEquiv i).1)) :
    (composeDiagram D₁ D₂).val (Sum.inl i.1) = Sum.inr (D₁.throughEquiv ⟨_, h⟩).1 :=
  composeDiagram_val_inl_eq_inr_of_through D₁ D₂ (D₂.inr_throughEquiv i).symm
    (D₁.inr_throughEquiv ⟨_, h⟩).symm

/-- **The caps of `D₂` are caps of the composite**: the composite matches a capped bottom point
of `D₂` with the other end of that cap. -/
theorem composeDiagram_val_inl_eq_inl_capMatching (i : {i : Fin k // D₂.IsCap (Sum.inl i)}) :
    (composeDiagram D₁ D₂).val (Sum.inl i.1) = Sum.inl (D₂.capMatching.val i).1 :=
  composeDiagram_val_inl_eq_inl_of_cap_lower D₁ D₂ (D₂.inl_capMatching i).symm

/-- **The cups of `D₁` are cups of the composite**: the composite matches a cupped top point of
`D₁` with the other end of that cup. -/
theorem composeDiagram_val_inr_eq_inr_cupMatching (j : {j : Fin k // D₁.IsCup (Sum.inr j)}) :
    (composeDiagram D₁ D₂).val (Sum.inr j.1) = Sum.inr (D₁.cupMatching.val j).1 :=
  composeDiagram_val_inr_eq_inr_of_cup_upper D₁ D₂ (D₁.inr_cupMatching j).symm

/-- Every capped bottom point of `D₂` is a capped bottom point of the composite. -/
theorem bottomCap_subset_bottomCap_composeDiagram :
    D₂.bottomCap ⊆ (composeDiagram D₁ D₂).bottomCap := by
  intro i hi
  rw [mem_bottomCap] at hi ⊢
  obtain ⟨i', hi'⟩ : ∃ i', D₂.val (Sum.inl i) = Sum.inl i' :=
    ⟨_, (Sum.inl_getLeft _ ((D₂.isCap_def _).mp hi).2).symm⟩
  rw [isCap_def, composeDiagram_val_inl_eq_inl_of_cap_lower D₁ D₂ hi']
  exact ⟨rfl, rfl⟩

/-- Every cupped top point of `D₁` is a cupped top point of the composite. -/
theorem topCup_subset_topCup_composeDiagram : D₁.topCup ⊆ (composeDiagram D₁ D₂).topCup := by
  intro j hj
  rw [mem_topCup] at hj ⊢
  obtain ⟨j', hj'⟩ : ∃ j', D₁.val (Sum.inr j) = Sum.inr j' :=
    ⟨_, (Sum.inr_getRight _ ((D₁.isCup_def _).mp hj).2).symm⟩
  rw [isCup_def, composeDiagram_val_inr_eq_inr_of_cup_upper D₁ D₂ hj']
  exact ⟨rfl, rfl⟩

/-- A bottom endpoint of a through strand of the composite is a bottom endpoint of a through
strand of `D₂`. -/
theorem bottomThrough_composeDiagram_subset :
    (composeDiagram D₁ D₂).bottomThrough ⊆ D₂.bottomThrough := by
  intro i hi
  rw [mem_bottomThrough] at hi ⊢
  by_contra hne
  have hcap : D₂.IsCap (Sum.inl i) := (D₂.isCap_inl_iff i).mpr hne
  exact not_isThrough_of_isCap _ _
    ((mem_bottomCap _).mp
      (bottomCap_subset_bottomCap_composeDiagram D₁ D₂ ((mem_bottomCap _).mpr hcap))) hi

/-- A top endpoint of a through strand of the composite is a top endpoint of a through strand of
`D₁`. -/
theorem topThrough_composeDiagram_subset :
    (composeDiagram D₁ D₂).topThrough ⊆ D₁.topThrough := by
  intro j hj
  rw [mem_topThrough] at hj ⊢
  by_contra hne
  have hcup : D₁.IsCup (Sum.inr j) := (D₁.isCup_inr_iff j).mpr hne
  exact not_isThrough_of_isCup _ _
    ((mem_topCup _).mp (topCup_subset_topCup_composeDiagram D₁ D₂ ((mem_topCup _).mpr hcup))) hj

end BrauerDiagram

/-! ### Stacking with a permutation diagram -/

variable (D : BrauerDiagram k) (σ τ : Equiv.Perm (Fin k))

open BrauerDiagram in
/-- **Stacking a permutation diagram on top relabels the top boundary.** No strand of `D` is
extended past the middle boundary, because the permutation diagram has no cap: a through strand of
`D` ending at the middle point `a` is continued by the single strand of `permToBrauer σ` above it,
which leaves at the top point `σ a`. -/
@[simp]
theorem composeDiagram_permToBrauer_left : composeDiagram (permToBrauer σ) D = D.relabel 1 σ := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rcases x with i | j
  · rcases h : D.val (Sum.inl i) with i' | a
    · rw [composeDiagram_val_inl_eq_inl_of_cap_lower _ D h]
      simp [h, Equiv.Perm.one_def]
    · rw [composeDiagram_val_inl_eq_inr_of_through (D₁ := permToBrauer σ) (D₂ := D) (j := σ a) h
        (permToBrauer_val_inl σ a)]
      simp [h, Equiv.Perm.one_def]
  · rcases h : D.val (Sum.inr (σ.symm j)) with i | a
    · rw [composeDiagram_val_inr_eq_inl_of_through (D₁ := permToBrauer σ) (D₂ := D)
        (a := σ.symm j) (permToBrauer_val_inr σ j) h]
      simp [h, Equiv.Perm.one_def]
    · rw [composeDiagram_val_inr_eq_inr_of_cup_lower (D₁ := permToBrauer σ) (D₂ := D)
        (a := σ.symm j) (j' := σ a) (permToBrauer_val_inr σ j) h (permToBrauer_val_inl σ a)]
      simp [h, Equiv.Perm.one_def]

open BrauerDiagram in
/-- **Stacking a permutation diagram underneath relabels the bottom boundary.** No strand of `D`
is extended past the middle boundary, because the permutation diagram has no cup: the strand of
`permToBrauer τ` starting at the bottom point `i` reaches the middle point `τ i`, where the arc of
`D` takes over. -/
@[simp]
theorem composeDiagram_permToBrauer_right :
    composeDiagram D (permToBrauer τ) = D.relabel τ⁻¹ 1 := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rcases x with i | j
  · rcases h : D.val (Sum.inl (τ i)) with a' | j'
    · rw [composeDiagram_val_inl_eq_inl_of_cap_upper (D₁ := D) (D₂ := permToBrauer τ) (a := τ i)
        (i' := τ.symm a') (permToBrauer_val_inl τ i) h (permToBrauer_val_inr τ a')]
      simp [h, Equiv.Perm.inv_def, Equiv.Perm.one_def]
    · rw [composeDiagram_val_inl_eq_inr_of_through (D₁ := D) (D₂ := permToBrauer τ) (a := τ i)
        (permToBrauer_val_inl τ i) h]
      simp [h, Equiv.Perm.inv_def, Equiv.Perm.one_def]
  · rcases h : D.val (Sum.inr j) with a | j'
    · rw [composeDiagram_val_inr_eq_inl_of_through (D₁ := D) (D₂ := permToBrauer τ) (a := a)
        h (permToBrauer_val_inr τ a)]
      simp [h, Equiv.Perm.inv_def, Equiv.Perm.one_def]
    · rw [composeDiagram_val_inr_eq_inr_of_cup_upper (D₁ := D) (D₂ := permToBrauer τ) h]
      simp [h, Equiv.Perm.inv_def, Equiv.Perm.one_def]

/-- **Stacking permutation diagrams multiplies the permutations.** So the inclusion of the
symmetric group into the Brauer diagrams turns the group law into vertical stacking; no loop
closes up in the middle, since a permutation diagram has neither a cap nor a cup.

This and the two identity laws below are not `simp` lemmas: they are the special cases of
`TauCeti.composeDiagram_permToBrauer_left` and `TauCeti.composeDiagram_permToBrauer_right` in
which the relabelling is one that `simp` already carries out, so `simp` proves them and tagging
them would leave them out of simp-normal form. -/
theorem composeDiagram_permToBrauer :
    composeDiagram (permToBrauer σ) (permToBrauer τ) = permToBrauer (σ * τ) := by
  rw [composeDiagram_permToBrauer_left, BrauerDiagram.relabel_permToBrauer, inv_one, mul_one]

/-- **The identity diagram is a left identity for stacking.** -/
theorem composeDiagram_permToBrauer_one_left : composeDiagram (permToBrauer 1) D = D := by
  rw [composeDiagram_permToBrauer_left, BrauerDiagram.relabel_one_one]

/-- **The identity diagram is a right identity for stacking.** -/
theorem composeDiagram_permToBrauer_one_right : composeDiagram D (permToBrauer 1) = D := by
  rw [composeDiagram_permToBrauer_right, inv_one, BrauerDiagram.relabel_one_one]

end TauCeti
