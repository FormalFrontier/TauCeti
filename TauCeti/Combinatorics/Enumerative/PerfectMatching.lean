/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Perfect matchings of a finite type

A **perfect matching** of a type `α` is a permutation of `α` that is an involution without
fixed points; equivalently, it partitions `α` into the unordered pairs `{a, f a}`. This file
defines perfect matchings, shows that a perfect matching restricted to the complement of one
of its arcs is again a perfect matching, and counts the perfect matchings of a finite type:
a type of cardinality `2 * m` has `(2 * m - 1)‼` of them, and a type of odd cardinality has
none.

The counting theorem is the combinatorial content behind the dimension of the Brauer algebra;
see `TauCeti/Combinatorics/Brauer/Diagram.lean`.

## Main definitions

* `TauCeti.IsPerfectMatching f`: the permutation `f` is an involution with no fixed point.
* `TauCeti.PerfectMatching α`: the type of perfect matchings of `α`.
* `TauCeti.PerfectMatching.restrict`: the perfect matching induced on the complement of an arc.
* `TauCeti.PerfectMatching.extend`: the perfect matching obtained by adjoining an arc.
* `TauCeti.PerfectMatching.fiberEquiv`: the two constructions above are mutually inverse.

## Main results

* `TauCeti.even_card_of_nonempty_perfectMatching`: a matched type has even cardinality.
* `TauCeti.card_perfectMatching`: a type of cardinality `2 * m` has `(2 * m - 1)‼` perfect
  matchings.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9.
-/

public section

open scoped Nat

namespace TauCeti

universe u

variable {α : Type u}

/-- A permutation of `α` is a **perfect matching** when it is an involution with no fixed
point, so that it pairs off the elements of `α`. -/
@[expose]
def IsPerfectMatching (f : Equiv.Perm α) : Prop :=
  (∀ a, f (f a) = a) ∧ ∀ a, f a ≠ a

instance instDecidableIsPerfectMatching [DecidableEq α] [Fintype α] (f : Equiv.Perm α) :
    Decidable (IsPerfectMatching f) :=
  inferInstanceAs (Decidable ((∀ a, f (f a) = a) ∧ ∀ a, f a ≠ a))

/-- The type of perfect matchings of `α`, a subtype of `Equiv.Perm α` so that the finiteness
and decidability instances of permutations carry over unchanged. -/
@[expose]
def PerfectMatching (α : Type u) := {f : Equiv.Perm α // IsPerfectMatching f}

namespace PerfectMatching

instance [DecidableEq α] [Fintype α] : Fintype (PerfectMatching α) :=
  inferInstanceAs (Fintype {f : Equiv.Perm α // IsPerfectMatching f})

instance [DecidableEq α] [Fintype α] : DecidableEq (PerfectMatching α) :=
  inferInstanceAs (DecidableEq {f : Equiv.Perm α // IsPerfectMatching f})

variable {a b : α} {D : PerfectMatching α}

/-- A perfect matching is an involution. -/
@[simp]
theorem apply_apply (D : PerfectMatching α) (x : α) : D.val (D.val x) = x := D.prop.1 x

/-- A perfect matching moves every point. -/
@[simp]
theorem apply_ne (D : PerfectMatching α) (x : α) : D.val x ≠ x := D.prop.2 x

/-- The two ends of an arc determine each other. -/
theorem apply_eq_of_apply_eq (D : PerfectMatching α) {x y : α} (h : D.val x = y) :
    D.val y = x := by rw [← h, D.apply_apply]

/-- A perfect matching that joins `a` to `b` preserves the complement of `{a, b}`. -/
theorem apply_ne_and_ne_iff (hab : D.val a = b) (x : α) :
    (D.val x ≠ a ∧ D.val x ≠ b) ↔ (x ≠ a ∧ x ≠ b) := by
  have hba : D.val b = a := D.apply_eq_of_apply_eq hab
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun h => h₂ (h ▸ hab), fun h => h₁ (h ▸ hba)⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun h => h₂ ?_, fun h => h₁ ?_⟩
    · rw [← hab, ← D.apply_eq_of_apply_eq h]
    · rw [← hba, ← D.apply_eq_of_apply_eq h]

/-- The perfect matching induced on the complement of the arc joining `a` to `b`. -/
def restrict (D : PerfectMatching α) (hab : D.val a = b) :
    PerfectMatching {x : α // x ≠ a ∧ x ≠ b} :=
  ⟨D.val.subtypePerm (apply_ne_and_ne_iff hab), fun x => Subtype.ext (D.apply_apply x.val),
    fun x h => D.apply_ne x.val (congrArg Subtype.val h)⟩

@[simp]
theorem restrict_apply_coe (D : PerfectMatching α) (hab : D.val a = b)
    (x : {x : α // x ≠ a ∧ x ≠ b}) : ((D.restrict hab).val x : α) = D.val x := (rfl)

section Extend

variable [DecidableEq α]

/-- The permutation of `α` that acts as `E` away from `{a, b}` and swaps `a` with `b`; it
underlies `PerfectMatching.extend`. -/
private def extendPerm (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) : Equiv.Perm α :=
  Equiv.swap a b * Equiv.Perm.ofSubtype E.val

/-- Away from `{a, b}`, the extended permutation acts through `E`. -/
private theorem extendPerm_apply_of_mem (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) {x : α}
    (hx : x ≠ a ∧ x ≠ b) : extendPerm E x = (E.val ⟨x, hx⟩ : α) := by
  have hmem : Equiv.Perm.ofSubtype E.val x = (E.val ⟨x, hx⟩ : α) :=
    Equiv.Perm.ofSubtype_apply_of_mem E.val hx
  have hne := (E.val ⟨x, hx⟩).2
  rw [extendPerm, Equiv.Perm.mul_apply, hmem, Equiv.swap_apply_of_ne_of_ne hne.1 hne.2]

/-- The extended permutation sends `a` to `b`. -/
private theorem extendPerm_apply_left (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    extendPerm E a = b := by
  rw [extendPerm, Equiv.Perm.mul_apply,
    Equiv.Perm.ofSubtype_apply_of_not_mem E.val (by simp), Equiv.swap_apply_left]

/-- The extended permutation sends `b` to `a`. -/
private theorem extendPerm_apply_right (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    extendPerm E b = a := by
  rw [extendPerm, Equiv.Perm.mul_apply,
    Equiv.Perm.ofSubtype_apply_of_not_mem E.val (by simp), Equiv.swap_apply_right]

/-- The perfect matching of `α` obtained from a perfect matching of the complement of
`{a, b}` by adjoining the arc joining `a` to `b`. -/
def extend (hab : a ≠ b) (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) : PerfectMatching α := by
  refine ⟨extendPerm E, fun x => ?_, fun x => ?_⟩
  · by_cases hx : x ≠ a ∧ x ≠ b
    · rw [extendPerm_apply_of_mem E hx, extendPerm_apply_of_mem E (E.val ⟨x, hx⟩).2]
      exact congrArg Subtype.val (E.apply_apply ⟨x, hx⟩)
    · rcases not_and_or.mp hx with hx | hx
      · rw [not_ne_iff.mp hx, extendPerm_apply_left, extendPerm_apply_right]
      · rw [not_ne_iff.mp hx, extendPerm_apply_right, extendPerm_apply_left]
  · by_cases hx : x ≠ a ∧ x ≠ b
    · rw [extendPerm_apply_of_mem E hx]
      exact fun h => E.apply_ne ⟨x, hx⟩ (Subtype.ext h)
    · rcases not_and_or.mp hx with hx | hx
      · rw [not_ne_iff.mp hx, extendPerm_apply_left]; exact hab.symm
      · rw [not_ne_iff.mp hx, extendPerm_apply_right]; exact hab

/-- Away from `{a, b}`, the extended matching acts through `E`. -/
theorem extend_apply_of_mem (hab : a ≠ b) (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) {x : α}
    (hx : x ≠ a ∧ x ≠ b) : (extend hab E).val x = (E.val ⟨x, hx⟩ : α) :=
  extendPerm_apply_of_mem E hx

/-- Adjoining the arc `{a, b}` sends `a` to `b`. -/
@[simp]
theorem extend_apply_left (hab : a ≠ b) (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    (extend hab E).val a = b := extendPerm_apply_left E

/-- Adjoining the arc `{a, b}` sends `b` to `a`. -/
@[simp]
theorem extend_apply_right (hab : a ≠ b) (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    (extend hab E).val b = a := extendPerm_apply_right E

/-- Adjoining an arc and then restricting it away recovers the smaller matching. -/
theorem restrict_extend (hab : a ≠ b) (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    (extend hab E).restrict (extend_apply_left hab E) = E := by
  refine Subtype.ext (Equiv.ext fun x => Subtype.ext ?_)
  rw [restrict_apply_coe, extend_apply_of_mem hab E x.2]

/-- Restricting away an arc and then adjoining it back recovers the original matching. -/
theorem extend_restrict (hab : a ≠ b) (D : PerfectMatching α) (h : D.val a = b) :
    extend hab (D.restrict h) = D := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  by_cases hx : x ≠ a ∧ x ≠ b
  · rw [extend_apply_of_mem hab _ hx, restrict_apply_coe]
  · rcases not_and_or.mp hx with hx | hx
    · rw [not_ne_iff.mp hx, extend_apply_left]; exact h.symm
    · rw [not_ne_iff.mp hx, extend_apply_right]
      exact (D.apply_eq_of_apply_eq h).symm

/-- Restricting away an arc and adjoining it back are mutually inverse: the perfect matchings
of `α` joining `a` to `b` are the perfect matchings of the complement of `{a, b}`. -/
def fiberEquiv (hab : a ≠ b) :
    {D : PerfectMatching α // D.val a = b} ≃ PerfectMatching {x : α // x ≠ a ∧ x ≠ b} where
  toFun D := D.1.restrict D.2
  invFun E := ⟨extend hab E, extend_apply_left hab E⟩
  left_inv D := Subtype.ext (extend_restrict hab D.1 D.2)
  right_inv E := restrict_extend hab E

/-- The fiber equivalence restricts away the arc joining `a` to `b`. -/
@[simp]
theorem fiberEquiv_apply (hab : a ≠ b) (D : {D : PerfectMatching α // D.val a = b}) :
    fiberEquiv hab D = D.1.restrict D.2 := (rfl)

/-- The inverse of the fiber equivalence adjoins the arc joining `a` to `b`. -/
@[simp]
theorem fiberEquiv_symm_apply (hab : a ≠ b) (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    ((fiberEquiv hab).symm E : PerfectMatching α) = extend hab E := (rfl)

end Extend

end PerfectMatching

/-- Deleting two distinct points from a finite type drops its cardinality by two. -/
private theorem card_subtype_ne_ne {α : Type u} [Fintype α] [DecidableEq α] {a b : α}
    (hab : a ≠ b) : Fintype.card {x : α // x ≠ a ∧ x ≠ b} = Fintype.card α - 2 := by
  have hcompl : Fintype.card {x : α // x ≠ a ∧ x ≠ b}
      = Fintype.card {x : α // ¬(x = a ∨ x = b)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun _ => not_or.symm)
  rw [hcompl, Fintype.card_subtype_compl, Fintype.card_subtype_eq_or_eq_of_ne hab]

private theorem even_card_aux :
    ∀ (n : ℕ) {α : Type u} [Fintype α], Fintype.card α = n →
      Nonempty (PerfectMatching α) → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α _ hcard hne
    classical
    obtain ⟨D⟩ := hne
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, rfl⟩
    obtain ⟨a⟩ := (Fintype.card_pos_iff (α := α)).mp (by omega)
    have hab : a ≠ D.val a := (D.apply_ne a).symm
    have hlt : 1 < Fintype.card α := Fintype.one_lt_card_iff_nontrivial.mpr ⟨a, D.val a, hab⟩
    have hsub : Fintype.card {x : α // x ≠ a ∧ x ≠ D.val a} = n - 2 := by
      rw [card_subtype_ne_ne hab, hcard]
    obtain ⟨r, hr⟩ := ih (n - 2) (by omega) hsub ⟨D.restrict rfl⟩
    exact ⟨r + 1, by omega⟩

/-- A type carrying a perfect matching has even cardinality: the arcs pair its elements. -/
theorem even_card_of_nonempty_perfectMatching (α : Type u) [Fintype α]
    (h : Nonempty (PerfectMatching α)) : Even (Fintype.card α) :=
  even_card_aux _ rfl h

/-- A type of odd cardinality carries no perfect matching. -/
theorem isEmpty_perfectMatching_of_not_even {α : Type u} [Fintype α]
    (h : ¬Even (Fintype.card α)) : IsEmpty (PerfectMatching α) :=
  ⟨fun D => h (even_card_of_nonempty_perfectMatching α ⟨D⟩)⟩

private theorem card_perfectMatching_aux :
    ∀ (m : ℕ) {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α = 2 * m →
      Fintype.card (PerfectMatching α) = (2 * m - 1)‼ := by
  intro m
  induction m with
  | zero =>
    intro α _ _ hcard
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp (by omega)
    have : Subsingleton (PerfectMatching α) :=
      ⟨fun D E => Subtype.ext (Equiv.ext fun x => isEmptyElim x)⟩
    have : Unique (PerfectMatching α) :=
      uniqueOfSubsingleton ⟨1, fun a => isEmptyElim a, fun a => isEmptyElim a⟩
    rw [Fintype.card_unique]
    rfl
  | succ m ih =>
    intro α _ _ hcard
    obtain ⟨a⟩ := (Fintype.card_pos_iff (α := α)).mp (by omega)
    have key : ∀ b ∈ Finset.univ.erase a,
        (Finset.univ.filter fun D : PerfectMatching α => D.val a = b).card = (2 * m - 1)‼ := by
      intro b hb
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      have hsub : Fintype.card {x : α // x ≠ a ∧ x ≠ b} = 2 * m := by
        rw [card_subtype_ne_ne hba.symm, hcard]
        omega
      calc (Finset.univ.filter fun D : PerfectMatching α => D.val a = b).card
          = Fintype.card {D : PerfectMatching α // D.val a = b} := (Fintype.card_subtype _).symm
        _ = Fintype.card (PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :=
            Fintype.card_congr (PerfectMatching.fiberEquiv hba.symm)
        _ = (2 * m - 1)‼ := ih hsub
    have hmem : ∀ D ∈ (Finset.univ : Finset (PerfectMatching α)),
        D.val a ∈ Finset.univ.erase a :=
      fun D _ => Finset.mem_erase.mpr ⟨D.apply_ne a, Finset.mem_univ _⟩
    have hodd : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    have herase : (Finset.univ.erase a).card = 2 * m + 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
      omega
    calc Fintype.card (PerfectMatching α)
        = (Finset.univ : Finset (PerfectMatching α)).card := Finset.card_univ.symm
      _ = ∑ b ∈ Finset.univ.erase a,
            (Finset.univ.filter fun D : PerfectMatching α => D.val a = b).card :=
          Finset.card_eq_sum_card_fiberwise hmem
      _ = (Finset.univ.erase a).card * (2 * m - 1)‼ := Finset.sum_const_nat key
      _ = (2 * m + 1) * (2 * m - 1)‼ := by rw [herase]
      _ = (2 * m + 1)‼ := (Nat.doubleFactorial_add_one (2 * m)).symm
      _ = (2 * (m + 1) - 1)‼ := by rw [hodd]

/-- **The number of perfect matchings of a finite type.** A type with `2 * m` elements has
exactly `(2 * m - 1)‼ = 1 · 3 · 5 ⋯ (2 * m - 1)` perfect matchings. -/
theorem card_perfectMatching (α : Type u) [Fintype α] [DecidableEq α] {m : ℕ}
    (hcard : Fintype.card α = 2 * m) : Fintype.card (PerfectMatching α) = (2 * m - 1)‼ :=
  card_perfectMatching_aux m hcard

end TauCeti
