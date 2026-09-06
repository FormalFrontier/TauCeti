/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.StrongExchange

/-!
# The Bruhat order on a Coxeter group

Let `cs : CoxeterSystem M W` be a Coxeter system. The **Bruhat graph** of `cs` has an edge from `u`
to `w` whenever `w = t * u` for a reflection `t` and `w` is the longer of the two; the **Bruhat
order** `cs.BruhatLE` is the reachability relation of that graph, the reflexive transitive closure
of the edge relation.

Two things make this a well-behaved order rather than a bare relation, and both are proved here.
It is a **partial order**: an edge strictly increases the length, so a cycle would have to be
constant, and `cs.bruhatPartialOrder` packages the three order axioms as data. And it has the
**subword description**: if `u ≤ w` then `u` is spelled by a sublist of *every* word spelling `w`,
reduced or not (`CoxeterSystem.BruhatLE.exists_sublist_wordProd_eq`). Since a reduced word for `w`
is in particular a word for `w`, the subword description does not depend on which reduced word is
chosen — the point of the classical definition "`u ≤ w` when some reduced word for `w` has a
subword spelling `u`", which would otherwise be a definition per reduced word.

The subword description is exactly the strong exchange condition of
`TauCeti/GroupTheory/Coxeter/StrongExchange.lean`, iterated along the chain: an edge `u → w`
means `u = t * w` for a reflection `t` that shortens `w`, and strong exchange deletes one letter
of any word for `w` to spell `u`. No reducedness is needed anywhere in that argument, which is
why the resulting statement quantifies over all words.

The converse — that a subword of a reduced word for `w` spells an element `≤ w`, and hence that
the two descriptions of the order agree — is the other half of the subword property and is **not**
proved here. It needs the lifting property, which compares `u` and `s * u` against `w` and `s * w`
for a simple reflection `s`, and is a genuinely separate argument. What is available here in that
direction is the one-letter case, `CoxeterSystem.bruhatLE_wordProd_eraseIdx`: deleting a single
letter of a reduced word does move down the Bruhat order.

## Main definitions

* `CoxeterSystem.BruhatStep`: the edge relation of the Bruhat graph, `w = t * u` for a reflection
  `t` with `ℓ u < ℓ w`.
* `CoxeterSystem.BruhatLE`: the Bruhat order, the reflexive transitive closure of `BruhatStep`.
* `CoxeterSystem.bruhatPartialOrder`: the Bruhat order as a `PartialOrder` on `W`.

## Main results

* `CoxeterSystem.BruhatLE.length_le` and `CoxeterSystem.BruhatLE.length_lt_of_ne`: the length is
  monotone along the order, and strictly monotone below the top.
* `CoxeterSystem.BruhatLE.antisymm`: **the Bruhat order is antisymmetric**, so together with
  reflexivity and transitivity it is a partial order.
* `CoxeterSystem.one_bruhatLE` and `CoxeterSystem.bruhatLE_one_iff`: the identity is the least
  element.
* `CoxeterSystem.bruhatLE_inv_iff`: the order is invariant under inversion.
* `CoxeterSystem.BruhatLE.exists_sublist_wordProd_eq` and
  `CoxeterSystem.BruhatLE.exists_sublist_wordProd_eq_length_eq`: **an element below `w` is spelled
  by a sublist of every word spelling `w`**, and by a *reduced* such sublist.
* `CoxeterSystem.bruhatLE_wordProd_eraseIdx`: deleting one letter of a reduced word moves down the
  order.

## References

This is the "Bruhat order's basic well-definedness" item under "Consequences" in Layer 3 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, the root-system-free Coxeter
combinatorics that layer collects; the strong exchange condition it consumes is the first item of
the same layer.

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.1 and 2.2.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitres IV-VI, Ch. IV, §1, Exercise 3.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 5.9.
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) {u v w : W}

local prefix:100 "ℓ " => cs.length
local prefix:100 "π " => cs.wordProd
local prefix:100 "lis " => cs.leftInvSeq

/-! ### The Bruhat graph -/

/-- One step up in the Bruhat order: `w` is obtained from `u` by multiplying by a reflection, and
is the longer of the two. This is the edge relation of the Bruhat graph of `cs`. -/
def BruhatStep (u w : W) : Prop := ∃ t : W, cs.IsReflection t ∧ w = t * u ∧ ℓ u < ℓ w

theorem bruhatStep_iff :
    cs.BruhatStep u w ↔ ∃ t : W, cs.IsReflection t ∧ w = t * u ∧ ℓ u < ℓ w :=
  Iff.rfl

theorem bruhatStep_mul_left {t : W} (ht : cs.IsReflection t) (h : ℓ u < ℓ (t * u)) :
    cs.BruhatStep u (t * u) :=
  ⟨t, ht, rfl, h⟩

section

variable {cs}

theorem BruhatStep.length_lt (h : cs.BruhatStep u w) : ℓ u < ℓ w := by
  obtain ⟨-, -, -, h⟩ := h
  exact h

theorem BruhatStep.ne (h : cs.BruhatStep u w) : u ≠ w := by
  rintro rfl
  exact absurd h.length_lt (lt_irrefl _)

/-- The Bruhat graph is invariant under inversion: conjugating the reflection of an edge by `u`
turns an edge `u → w` into an edge `u⁻¹ → w⁻¹`. -/
theorem BruhatStep.inv (h : cs.BruhatStep u w) : cs.BruhatStep u⁻¹ w⁻¹ := by
  obtain ⟨t, ht, rfl, hlt⟩ := h
  refine ⟨u⁻¹ * t * u, by simpa using ht.conj u⁻¹, ?_, ?_⟩
  · rw [mul_inv_rev, ht.inv]
    group
  · rwa [cs.length_inv, cs.length_inv]

end

/-- A reflection lies above the identity in the Bruhat graph: its length is odd, hence positive. -/
theorem bruhatStep_one {t : W} (ht : cs.IsReflection t) : cs.BruhatStep 1 t := by
  refine ⟨t, ht, by rw [mul_one], ?_⟩
  rw [cs.length_one]
  exact ht.odd_length.pos

/-- Multiplying by a reflection always produces an edge of the Bruhat graph, in one direction or
the other: a reflection never preserves the length. -/
theorem bruhatStep_or_bruhatStep_mul_left {t : W} (ht : cs.IsReflection t) (u : W) :
    cs.BruhatStep u (t * u) ∨ cs.BruhatStep (t * u) u := by
  rcases lt_or_gt_of_ne (Ne.symm (ht.length_mul_right_ne u)) with h | h
  · exact Or.inl (cs.bruhatStep_mul_left ht h)
  · exact Or.inr ⟨t, ht, by rw [← mul_assoc, ht.mul_self, one_mul], h⟩

/-- Appending a simple reflection on the right is an edge of the Bruhat graph whenever it
lengthens: the conjugate `w * s i * w⁻¹` is the reflection realizing it. -/
theorem bruhatStep_mul_simple (i : B) (h : ℓ w < ℓ (w * cs.simple i)) :
    cs.BruhatStep w (w * cs.simple i) := by
  refine ⟨w * cs.simple i * w⁻¹, (cs.isReflection_simple i).conj w, ?_, h⟩
  group

/-- Prepending a simple reflection is an edge of the Bruhat graph whenever it lengthens. -/
theorem bruhatStep_simple_mul (i : B) (h : ℓ w < ℓ (cs.simple i * w)) :
    cs.BruhatStep w (cs.simple i * w) :=
  cs.bruhatStep_mul_left (cs.isReflection_simple i) h

/-- Deleting a letter of a word is an edge of the Bruhat graph as soon as it shortens: the entry
of the left inversion sequence at that position is the reflection realizing it. -/
theorem bruhatStep_wordProd_eraseIdx {ω : List B} {j : ℕ} (hj : j < ω.length)
    (h : ℓ (π (ω.eraseIdx j)) < ℓ (π ω)) : cs.BruhatStep (π (ω.eraseIdx j)) (π ω) := by
  have hj' : j < (lis ω).length := by rwa [cs.length_leftInvSeq]
  have hmem : (lis ω).getD j 1 ∈ lis ω := by
    rw [List.getD_eq_getElem (lis ω) 1 hj']
    exact List.getElem_mem hj'
  have ht := cs.isReflection_of_mem_leftInvSeq ω hmem
  refine ⟨(lis ω).getD j 1, ht, ?_, h⟩
  rw [← cs.getD_leftInvSeq_mul_wordProd ω j, ← mul_assoc, ht.mul_self, one_mul]

/-! ### The Bruhat order -/

/-- **The Bruhat order** on a Coxeter group: `u ≤ w` when `w` is reachable from `u` in the Bruhat
graph, that is, when a chain of reflections leads from `u` up to `w` with the length increasing at
each step. -/
def BruhatLE (u w : W) : Prop := Relation.ReflTransGen cs.BruhatStep u w

theorem bruhatLE_iff_reflTransGen :
    cs.BruhatLE u w ↔ Relation.ReflTransGen cs.BruhatStep u w :=
  Iff.rfl

@[refl]
theorem bruhatLE_refl (w : W) : cs.BruhatLE w w := Relation.ReflTransGen.refl

section

variable {cs}

theorem BruhatStep.bruhatLE (h : cs.BruhatStep u w) : cs.BruhatLE u w :=
  Relation.ReflTransGen.single h

@[trans]
theorem BruhatLE.trans (h₁ : cs.BruhatLE u v) (h₂ : cs.BruhatLE v w) : cs.BruhatLE u w :=
  Relation.ReflTransGen.trans h₁ h₂

theorem BruhatLE.tail (h : cs.BruhatLE u v) (hs : cs.BruhatStep v w) : cs.BruhatLE u w :=
  Relation.ReflTransGen.tail h hs

/-- **The length is monotone along the Bruhat order**, each edge increasing it. -/
theorem BruhatLE.length_le (h : cs.BruhatLE u w) : ℓ u ≤ ℓ w := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans hs.length_lt.le

/-- Below the top, the length increases **strictly**: a nontrivial chain has at least one edge. -/
theorem BruhatLE.length_lt_of_ne (h : cs.BruhatLE u w) (hne : u ≠ w) : ℓ u < ℓ w := by
  obtain rfl | ⟨v, hs, hv⟩ := Relation.ReflTransGen.cases_head h
  · exact absurd rfl hne
  · exact hs.length_lt.trans_le (BruhatLE.length_le hv)

/-- **The Bruhat order is antisymmetric**: a two-way chain cannot increase the length. -/
theorem BruhatLE.antisymm (h₁ : cs.BruhatLE u w) (h₂ : cs.BruhatLE w u) : u = w := by
  by_contra hne
  exact absurd ((h₁.length_lt_of_ne hne).trans (h₂.length_lt_of_ne (Ne.symm hne))) (lt_irrefl _)

/-- The Bruhat order is invariant under inversion. -/
theorem BruhatLE.inv (h : cs.BruhatLE u w) : cs.BruhatLE u⁻¹ w⁻¹ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail hs.inv

end

@[simp]
theorem bruhatLE_inv_iff : cs.BruhatLE u⁻¹ w⁻¹ ↔ cs.BruhatLE u w :=
  ⟨fun h => by simpa using h.inv, BruhatLE.inv⟩

/-- **The identity is the least element** of the Bruhat order: a left descent supplies an edge one
step down, and the length decreases. -/
theorem one_bruhatLE (w : W) : cs.BruhatLE 1 w := by
  suffices H : ∀ n : ℕ, ∀ w : W, ℓ w ≤ n → cs.BruhatLE 1 w from H (ℓ w) w le_rfl
  intro n
  induction n with
  | zero =>
    intro w hw
    rw [Nat.le_zero, cs.length_eq_zero_iff] at hw
    exact hw ▸ Relation.ReflTransGen.refl
  | succ n ih =>
    intro w hw
    rcases eq_or_ne w 1 with rfl | hne
    · exact Relation.ReflTransGen.refl
    obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hne
    have hi' : ℓ (cs.simple i * w) + 1 = ℓ w := cs.isLeftDescent_iff.mp hi
    have hstep : cs.BruhatStep (cs.simple i * w) w := by
      refine ⟨cs.simple i, cs.isReflection_simple i, ?_, by omega⟩
      rw [← mul_assoc, cs.simple_mul_simple_self, one_mul]
    exact (ih (cs.simple i * w) (by omega)).tail hstep

@[simp]
theorem bruhatLE_one_iff : cs.BruhatLE w 1 ↔ w = 1 :=
  ⟨fun h => h.antisymm (cs.one_bruhatLE w), fun h => h ▸ Relation.ReflTransGen.refl⟩

/-- **The Bruhat order as a partial order** on the Coxeter group. It is stated as data rather than
as an instance: a Coxeter group carries no order of its own, and a second Coxeter system on the
same group would give a different one. -/
@[instance_reducible]
def bruhatPartialOrder : PartialOrder W where
  le := cs.BruhatLE
  le_refl := cs.bruhatLE_refl
  le_trans _ _ _ := BruhatLE.trans
  le_antisymm _ _ := BruhatLE.antisymm

theorem bruhatPartialOrder_le : cs.bruhatPartialOrder.le = cs.BruhatLE := (rfl)

/-! ### The subword description -/

section

variable {cs}

/-- **An element below `w` is spelled by a sublist of every word spelling `w`.** The word need not
be reduced, so in particular the subword description of the Bruhat order does not depend on which
reduced word for `w` is chosen.

Each edge of the chain from `u` to `w` deletes one letter, by the strong exchange condition: an
edge `v → w` says that a reflection `t` carries `w` to the shorter `v`, and strong exchange then
spells `v` by `w`'s word with one letter gone. -/
theorem BruhatLE.exists_sublist_wordProd_eq {u w : W} (h : cs.BruhatLE u w) :
    ∀ ω : List B, π ω = w → ∃ σ : List B, σ.Sublist ω ∧ π σ = u := by
  induction h with
  | refl => exact fun ω hω => ⟨ω, List.Sublist.refl ω, hω⟩
  | @tail v w _ hs ih =>
    intro ω hω
    obtain ⟨t, ht, rfl, hlt⟩ := hs
    have hinv : cs.IsLeftInversion (π ω) t := by
      refine ⟨ht, ?_⟩
      rw [hω, ← mul_assoc, ht.mul_self, one_mul]
      exact hlt
    obtain ⟨j, hj, hje⟩ := strongExchange cs hinv
    have hv : π (ω.eraseIdx j) = v := by
      rw [← hje, hω, ← mul_assoc, ht.mul_self, one_mul]
    obtain ⟨σ, hσ, hσprod⟩ := ih (ω.eraseIdx j) hv
    exact ⟨σ, hσ.trans (List.eraseIdx_sublist ω j), hσprod⟩

/-- **An element below `w` is spelled by a reduced sublist of every word spelling `w`**, whose
length is therefore its own Coxeter length. This refines
`CoxeterSystem.BruhatLE.exists_sublist_wordProd_eq` by shrinking the sublist to a reduced one. -/
theorem BruhatLE.exists_sublist_wordProd_eq_length_eq {u w : W} (h : cs.BruhatLE u w)
    (ω : List B) (hω : π ω = w) :
    ∃ σ : List B, σ.Sublist ω ∧ π σ = u ∧ σ.length = ℓ u := by
  obtain ⟨σ, hσ, hσprod⟩ := h.exists_sublist_wordProd_eq ω hω
  obtain ⟨σ', hσ', hσ'red, hσ'prod⟩ := cs.exists_isReduced_sublist σ
  exact ⟨σ', hσ'.trans hσ, hσ'prod.trans hσprod, by rw [← hσ'red.eq, hσ'prod, hσprod]⟩

end

/-- **Deleting one letter of a reduced word moves down the Bruhat order.** This is the one-letter
case of the converse of `CoxeterSystem.BruhatLE.exists_sublist_wordProd_eq`; the general case is
the other half of the subword property and is not proved here. -/
theorem bruhatLE_wordProd_eraseIdx {ω : List B} (hω : cs.IsReduced ω) {j : ℕ}
    (hj : j < ω.length) : cs.BruhatLE (π (ω.eraseIdx j)) (π ω) := by
  refine (cs.bruhatStep_wordProd_eraseIdx hj ?_).bruhatLE
  have h₁ := cs.length_wordProd_le (ω.eraseIdx j)
  have h₂ := List.length_eraseIdx_add_one hj
  rw [hω.eq]
  omega

end CoxeterSystem
