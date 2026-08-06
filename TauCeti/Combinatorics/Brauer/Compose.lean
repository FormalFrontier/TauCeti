/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.Combinatorics.Brauer.Boundary

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

## Main definitions

* `TauCeti.composeDiagram`: the composite of two Brauer diagrams, `D₁` stacked above `D₂`.

## Main results

* `TauCeti.composeDiagram_val_inl_eq_inl_of_cap_lower`,
  `TauCeti.composeDiagram_val_inr_eq_inr_of_cup_upper`,
  `TauCeti.composeDiagram_val_inl_eq_inr_of_through`,
  `TauCeti.composeDiagram_val_inr_eq_inl_of_through`,
  `TauCeti.composeDiagram_val_inl_eq_inl_of_cap_upper`,
  `TauCeti.composeDiagram_val_inr_eq_inr_of_cup_lower`: the arcs of the composite along the
  strands that leave the middle boundary after at most two crossings.
* `TauCeti.BrauerDiagram.inr_throughEquiv_composeDiagram`: a through strand of `D₂` continued by
  a through strand of `D₁` is a through strand of the composite.
* `TauCeti.BrauerDiagram.inl_capMatching_composeDiagram`,
  `TauCeti.BrauerDiagram.inr_cupMatching_composeDiagram`: the caps of `D₂` are caps of the
  composite, and the cups of `D₁` are cups of the composite.
* `TauCeti.composeDiagram_permToBrauer_one_left`,
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

namespace BrauerDiagram

variable (D₁ D₂ : BrauerDiagram k)

private theorem composeDiagram_val (x : Fin k ⊕ Fin k) :
    (composeDiagram D₁ D₂).val x = stackVal D₁ D₂ x := by
  simp [composeDiagram]

end BrauerDiagram

variable (D₁ D₂ : BrauerDiagram k)

/-- **A cap of the lower diagram is a cap of the composite.** -/
theorem composeDiagram_val_inl_eq_inl_of_cap_lower {i i' : Fin k}
    (h : D₂.val (Sum.inl i) = Sum.inl i') :
    (composeDiagram D₁ D₂).val (Sum.inl i) = Sum.inl i' := by
  rw [BrauerDiagram.composeDiagram_val]
  refine BrauerDiagram.stackVal_eq_of_exit D₁ D₂ (n := 0) ?_ (by simp)
  rw [pow_one, BrauerDiagram.walk_inl_inl, h]
  rfl

/-- **A cup of the upper diagram is a cup of the composite.** -/
theorem composeDiagram_val_inr_eq_inr_of_cup_upper {j j' : Fin k}
    (h : D₁.val (Sum.inr j) = Sum.inr j') :
    (composeDiagram D₁ D₂).val (Sum.inr j) = Sum.inr j' := by
  rw [BrauerDiagram.composeDiagram_val]
  refine BrauerDiagram.stackVal_eq_of_exit D₁ D₂ (n := 0) ?_ (by simp)
  rw [pow_one, BrauerDiagram.walk_inl_inr, h]
  rfl

/-- **A through strand of the lower diagram continued by a through strand of the upper diagram
is a through strand of the composite.** -/
theorem composeDiagram_val_inl_eq_inr_of_through {i a j : Fin k}
    (h₂ : D₂.val (Sum.inl i) = Sum.inr a) (h₁ : D₁.val (Sum.inl a) = Sum.inr j) :
    (composeDiagram D₁ D₂).val (Sum.inl i) = Sum.inr j := by
  have hstep : BrauerDiagram.walk D₁ D₂ (Sum.inl (Sum.inl i)) = Sum.inr (Sum.inr a) := by
    rw [BrauerDiagram.walk_inl_inl, h₂]
    rfl
  rw [BrauerDiagram.composeDiagram_val]
  refine BrauerDiagram.stackVal_eq_of_exit D₁ D₂ (n := 1) ?_ fun m hm => ?_
  · rw [pow_succ', Equiv.Perm.mul_apply, pow_one, hstep, BrauerDiagram.walk_inr_inr, h₁]
    rfl
  · have hm0 : m = 0 := by omega
    rw [hm0, zero_add, pow_one, hstep]
    simp

/-- **A through strand of the composite, read from its top endpoint.** -/
theorem composeDiagram_val_inr_eq_inl_of_through {i a j : Fin k}
    (h₁ : D₁.val (Sum.inr j) = Sum.inl a) (h₂ : D₂.val (Sum.inr a) = Sum.inl i) :
    (composeDiagram D₁ D₂).val (Sum.inr j) = Sum.inl i :=
  (composeDiagram D₁ D₂).apply_eq_of_apply_eq
    (composeDiagram_val_inl_eq_inr_of_through D₁ D₂ (D₂.apply_eq_of_apply_eq h₂)
      (D₁.apply_eq_of_apply_eq h₁))

/-- **A cap of the upper diagram, reached by two through strands of the lower one, is a cap of
the composite.** -/
theorem composeDiagram_val_inl_eq_inl_of_cap_upper {i a a' i' : Fin k}
    (h₂ : D₂.val (Sum.inl i) = Sum.inr a) (h₁ : D₁.val (Sum.inl a) = Sum.inl a')
    (h₂' : D₂.val (Sum.inr a') = Sum.inl i') :
    (composeDiagram D₁ D₂).val (Sum.inl i) = Sum.inl i' := by
  have hstep : BrauerDiagram.walk D₁ D₂ (Sum.inl (Sum.inl i)) = Sum.inr (Sum.inr a) := by
    rw [BrauerDiagram.walk_inl_inl, h₂]
    rfl
  have hstep' : BrauerDiagram.walk D₁ D₂ (Sum.inr (Sum.inr a)) = Sum.inr (Sum.inl a') := by
    rw [BrauerDiagram.walk_inr_inr, h₁]
    rfl
  rw [BrauerDiagram.composeDiagram_val]
  refine BrauerDiagram.stackVal_eq_of_exit D₁ D₂ (n := 2) ?_ fun m hm => ?_
  · rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, pow_one, hstep, hstep',
      BrauerDiagram.walk_inr_inl, h₂']
    rfl
  · have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl
    · rw [zero_add, pow_one, hstep]
      simp
    · rw [pow_succ', Equiv.Perm.mul_apply, pow_one, hstep, hstep']
      simp

/-- **A cup of the lower diagram, reached by two through strands of the upper one, is a cup of
the composite.** -/
theorem composeDiagram_val_inr_eq_inr_of_cup_lower {j a a' j' : Fin k}
    (h₁ : D₁.val (Sum.inr j) = Sum.inl a) (h₂ : D₂.val (Sum.inr a) = Sum.inr a')
    (h₁' : D₁.val (Sum.inl a') = Sum.inr j') :
    (composeDiagram D₁ D₂).val (Sum.inr j) = Sum.inr j' := by
  have hstep : BrauerDiagram.walk D₁ D₂ (Sum.inl (Sum.inr j)) = Sum.inr (Sum.inl a) := by
    rw [BrauerDiagram.walk_inl_inr, h₁]
    rfl
  have hstep' : BrauerDiagram.walk D₁ D₂ (Sum.inr (Sum.inl a)) = Sum.inr (Sum.inr a') := by
    rw [BrauerDiagram.walk_inr_inl, h₂]
    rfl
  rw [BrauerDiagram.composeDiagram_val]
  refine BrauerDiagram.stackVal_eq_of_exit D₁ D₂ (n := 2) ?_ fun m hm => ?_
  · rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, pow_one, hstep, hstep',
      BrauerDiagram.walk_inr_inr, h₁']
    rfl
  · have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl
    · rw [zero_add, pow_one, hstep]
      simp
    · rw [pow_succ', Equiv.Perm.mul_apply, pow_one, hstep, hstep']
      simp

namespace BrauerDiagram

/-- **A through strand of `D₂` continued by a through strand of `D₁` is a through strand of the
composite**: the composite joins the bottom endpoint of a through strand of `D₂` to the top
endpoint of the through strand of `D₁` that continues it. -/
theorem inr_throughEquiv_composeDiagram (i : {i : Fin k // D₂.IsThrough (Sum.inl i)})
    (h : D₁.IsThrough (Sum.inl (D₂.throughEquiv i).1)) :
    (composeDiagram D₁ D₂).val (Sum.inl i.1) = Sum.inr (D₁.throughEquiv ⟨_, h⟩).1 :=
  composeDiagram_val_inl_eq_inr_of_through D₁ D₂ (D₂.inr_throughEquiv i).symm
    (D₁.inr_throughEquiv ⟨_, h⟩).symm

/-- **The caps of `D₂` are caps of the composite**: the composite matches a capped bottom point
of `D₂` with the other end of that cap. -/
theorem inl_capMatching_composeDiagram (i : {i : Fin k // D₂.IsCap (Sum.inl i)}) :
    (composeDiagram D₁ D₂).val (Sum.inl i.1) = Sum.inl (D₂.capMatching.val i).1 :=
  composeDiagram_val_inl_eq_inl_of_cap_lower D₁ D₂ (D₂.inl_capMatching i).symm

/-- **The cups of `D₁` are cups of the composite**: the composite matches a cupped top point of
`D₁` with the other end of that cup. -/
theorem inr_cupMatching_composeDiagram (j : {j : Fin k // D₁.IsCup (Sum.inr j)}) :
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

/-- **The identity diagram is a left identity for stacking.** -/
@[simp]
theorem composeDiagram_permToBrauer_one_left (D : BrauerDiagram k) :
    composeDiagram (permToBrauer 1) D = D := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rcases x with i | j
  · rcases h : D.val (Sum.inl i) with i' | a
    · exact composeDiagram_val_inl_eq_inl_of_cap_lower _ D h
    · exact composeDiagram_val_inl_eq_inr_of_through (D₁ := permToBrauer 1) (D₂ := D) (j := a) h
        (by rw [BrauerDiagram.permToBrauer_val_inl]; rfl)
  · rcases h : D.val (Sum.inr j) with i | j'
    · exact composeDiagram_val_inr_eq_inl_of_through (D₁ := permToBrauer 1) (D₂ := D) (a := j)
        (by rw [BrauerDiagram.permToBrauer_val_inr]; rfl) h
    · exact composeDiagram_val_inr_eq_inr_of_cup_lower (D₁ := permToBrauer 1) (D₂ := D) (a := j)
        (j' := j') (by rw [BrauerDiagram.permToBrauer_val_inr]; rfl) h
        (by rw [BrauerDiagram.permToBrauer_val_inl]; rfl)

/-- **The identity diagram is a right identity for stacking.** -/
@[simp]
theorem composeDiagram_permToBrauer_one_right (D : BrauerDiagram k) :
    composeDiagram D (permToBrauer 1) = D := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rcases x with i | j
  · rcases h : D.val (Sum.inl i) with i' | a
    · exact composeDiagram_val_inl_eq_inl_of_cap_upper (D₁ := D) (D₂ := permToBrauer 1) (a := i)
        (i' := i') (by rw [BrauerDiagram.permToBrauer_val_inl]; rfl) h
        (by rw [BrauerDiagram.permToBrauer_val_inr]; rfl)
    · exact composeDiagram_val_inl_eq_inr_of_through (D₁ := D) (D₂ := permToBrauer 1) (a := i)
        (by rw [BrauerDiagram.permToBrauer_val_inl]; rfl) h
  · rcases h : D.val (Sum.inr j) with i | j'
    · exact composeDiagram_val_inr_eq_inl_of_through (D₁ := D) (D₂ := permToBrauer 1) (a := i)
        h (by rw [BrauerDiagram.permToBrauer_val_inr]; rfl)
    · exact composeDiagram_val_inr_eq_inr_of_cup_upper (D₁ := D) (D₂ := permToBrauer 1) h

end TauCeti
