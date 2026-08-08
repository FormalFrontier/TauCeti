/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Circular.ZMod

/-!
# Complementary cyclic intervals in finite grids

This file records finite-set bookkeeping for the clockwise open cyclic intervals used by
toroidal grid rectangles. For distinct endpoints `a` and `b`, the two arcs `cIoo a b` and
`cIoo b a` are disjoint and together contain exactly the points other than `a` and `b`.

These lemmas are deliberately stated at the one-dimensional `Fin n` level. Rectangle-pair
arguments for the grid differential can then apply them independently in the column and row
directions before taking products.

## Main results

* `TauCeti.Grid.disjoint_cIoo_swap`: opposite open arcs are disjoint.
* `TauCeti.Grid.mem_cIoo_or_mem_cIoo_swap_iff`: a point lies in one opposite arc exactly when
  it is not an endpoint.
* `TauCeti.Grid.cIoo_union_swap`: the two opposite arcs cover the endpoint complement.
* `TauCeti.Grid.card_cIoo_add_card_cIoo_swap`: the two arc lengths add to `n - 2`.
* `TauCeti.Grid.cIoo_image_rev`: reversing a clockwise open arc by `Fin.rev` gives the clockwise
  open arc with reversed, exchanged endpoints.
* `TauCeti.Grid.Noninterleaving`: two endpoint pairs lie on the same cyclic side of each other.
* `TauCeti.Grid.noninterleaving_rev`: non-interleaving is preserved by reversing every endpoint
  with `Fin.rev`, exchanging the two endpoints within each pair.

## References

This supplies a prerequisite for `TauCetiRoadmap/HeegaardFloer/README.md`, Lane G.3, "The
complexes and `∂² = 0`", where the annular cases in the juxtaposition proof use the fact that
the two complementary cyclic intervals partition the non-endpoint columns or rows. The
terminology follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace Grid

variable {n : ℕ}

/-- The clockwise open cyclic interval from `a` to `b` in `Fin n`.

If `a < b` in the standard representatives, this is the ordinary open interval
`a < x < b`. If `b ≤ a` and `a ≠ b`, it wraps around `0`, so it is the union of
`a < x` and `x < b`. The interval from a point to itself is empty. -/
noncomputable def cIoo (a b : Fin n) : Finset (Fin n) :=
  ((Set.finite_univ : (Set.univ : Set (Fin n)).Finite).subset
    (Set.subset_univ (Set.cIoo a b : Set (Fin n)))).toFinset

/-- Membership in a clockwise open cyclic interval, unfolded as inequalities between the
standard representatives. -/
@[simp]
theorem mem_cIoo (a b x : Fin n) :
    x ∈ cIoo a b ↔
      a ≠ b ∧
        if a.val < b.val then
          a.val < x.val ∧ x.val < b.val
        else
          a.val < x.val ∨ x.val < b.val := by
  rw [cIoo]
  simp only [Set.Finite.mem_toFinset, Set.mem_cIoo, Fin.sbtw_iff, Fin.lt_def]
  constructor
  · rintro (⟨hax, hxb⟩ | ⟨hxb, hba⟩ | ⟨hba, hax⟩)
    · exact ⟨fun hab => by omega, by simp [hax, hxb]⟩
    · exact ⟨fun hab => by omega, by simp [Nat.not_lt_of_gt hba, hxb]⟩
    · exact ⟨fun hab => by omega, by simp [Nat.not_lt_of_gt hba, hax]⟩
  · intro h
    by_cases hab : a.val < b.val
    · exact Or.inl (by simpa [hab] using h.2)
    · have hba : b.val < a.val := by
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt hab) (by omega)
      rcases (by simpa [hab] using h.2) with hax | hxb
      · exact Or.inr (Or.inr ⟨hba, hax⟩)
      · exact Or.inr (Or.inl ⟨hxb, hba⟩)

/-- The open cyclic interval from a point to itself is empty. -/
@[simp]
theorem cIoo_self (a : Fin n) : cIoo a a = ∅ := by
  ext x
  simp

/-- The initial endpoint is not in its open cyclic interval. -/
theorem left_notMem_cIoo (a b : Fin n) : a ∉ cIoo a b := by
  intro ha
  rw [mem_cIoo] at ha
  by_cases hab : a.val < b.val
  · have hinside : a.val < a.val ∧ a.val < b.val := by
      simpa only [hab, if_true] using ha.2
    exact Nat.lt_irrefl a.val hinside.1
  · have hinside : a.val < a.val ∨ a.val < b.val := by
      simpa only [hab, if_false] using ha.2
    cases hinside with
    | inl hlt => exact Nat.lt_irrefl a.val hlt
    | inr hlt => exact hab hlt

/-- The terminal endpoint is not in its open cyclic interval. -/
theorem right_notMem_cIoo (a b : Fin n) : b ∉ cIoo a b := by
  intro hb
  rw [mem_cIoo] at hb
  by_cases hab : a.val < b.val
  · have hinside : a.val < b.val ∧ b.val < b.val := by
      simpa only [hab, if_true] using hb.2
    exact Nat.lt_irrefl b.val hinside.2
  · have hinside : a.val < b.val ∨ b.val < b.val := by
      simpa only [hab, if_false] using hb.2
    cases hinside with
    | inl hlt => exact hab hlt
    | inr hlt => exact Nat.lt_irrefl b.val hlt

/-- Two oriented cyclic intervals have non-interleaving endpoint pairs.

The endpoints `a₀`, `a₁` lie on the same side of the pair `b₀`, `b₁`, and conversely. This
two-sided formulation handles shared-endpoint cases uniformly. -/
@[expose] def Noninterleaving (a₀ a₁ b₀ b₁ : Fin n) : Prop :=
  (a₀ ∈ cIoo b₀ b₁ ↔ a₁ ∈ cIoo b₀ b₁) ∧
    (b₀ ∈ cIoo a₀ a₁ ↔ b₁ ∈ cIoo a₀ a₁)

/-- The defining endpoint-side conditions for `Grid.Noninterleaving`. -/
theorem noninterleaving_iff (a₀ a₁ b₀ b₁ : Fin n) :
    Noninterleaving a₀ a₁ b₀ b₁ ↔
      (a₀ ∈ cIoo b₀ b₁ ↔ a₁ ∈ cIoo b₀ b₁) ∧
        (b₀ ∈ cIoo a₀ a₁ ↔ b₁ ∈ cIoo a₀ a₁) :=
  Iff.rfl

/-- An endpoint pair is non-interleaving with itself. -/
@[simp]
theorem noninterleaving_self (a₀ a₁ : Fin n) : Noninterleaving a₀ a₁ a₀ a₁ := by
  simp [Noninterleaving]

/-- Non-interleaving is symmetric in the two endpoint pairs. -/
theorem noninterleaving_comm {a₀ a₁ b₀ b₁ : Fin n} :
    Noninterleaving a₀ a₁ b₀ b₁ ↔ Noninterleaving b₀ b₁ a₀ a₁ := by
  rw [Noninterleaving, Noninterleaving]
  exact and_comm

/-- A point cannot lie in both open cyclic intervals with the same endpoints but opposite
orientations. -/
private theorem not_mem_cIoo_and_cIoo_swap (a b x : Fin n) :
    ¬(x ∈ cIoo a b ∧ x ∈ cIoo b a) := by
  rw [mem_cIoo, mem_cIoo]
  rintro ⟨hxab, hxba⟩
  by_cases hab : a.val < b.val
  · have hxab' : a.val < x.val ∧ x.val < b.val := by
      simpa [hab] using hxab.2
    have hbxa : ¬ b.val < a.val := Nat.not_lt.mpr (Nat.le_of_lt hab)
    have hxba' : b.val < x.val ∨ x.val < a.val := by
      simpa [hbxa] using hxba.2
    omega
  · have hxab' : a.val < x.val ∨ x.val < b.val := by
      simpa [hab] using hxab.2
    have hba : b.val < a.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hab) (by omega)
    have hxba' : b.val < x.val ∧ x.val < a.val := by
      simpa [hba] using hxba.2
    omega

/-- Opposite open cyclic intervals with the same endpoints are disjoint. -/
theorem disjoint_cIoo_swap (a b : Fin n) : Disjoint (cIoo a b) (cIoo b a) := by
  rw [Finset.disjoint_iff_ne]
  intro x hx y hy hxy
  subst hxy
  exact not_mem_cIoo_and_cIoo_swap a b x ⟨hx, hy⟩

/-- Membership in one of the two opposite cyclic intervals is the same as being neither
endpoint. -/
theorem mem_cIoo_or_mem_cIoo_swap_iff {a b x : Fin n} (h : a ≠ b) :
    x ∈ cIoo a b ∨ x ∈ cIoo b a ↔ x ≠ a ∧ x ≠ b := by
  constructor
  · rintro (hx | hx)
    · exact ⟨fun hxa => left_notMem_cIoo a b (hxa ▸ hx),
        fun hxb => right_notMem_cIoo a b (hxb ▸ hx)⟩
    · exact ⟨fun hxa => right_notMem_cIoo b a (hxa ▸ hx),
        fun hxb => left_notMem_cIoo b a (hxb ▸ hx)⟩
  · intro hx
    by_cases hab : a.val < b.val
    · by_cases hax : a.val < x.val
      · by_cases hxb : x.val < b.val
        · exact Or.inl ((mem_cIoo a b x).mpr ⟨h, by simp [hab, hax, hxb]⟩)
        · exact Or.inr ((mem_cIoo b a x).mpr ⟨h.symm, by
            have hbxa : ¬ b.val < a.val := Nat.not_lt.mpr (Nat.le_of_lt hab)
            have hbx : b.val < x.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hxb) (by omega)
            simp [hbxa, hbx]⟩)
      · exact Or.inr ((mem_cIoo b a x).mpr ⟨h.symm, by
          have hbxa : ¬ b.val < a.val := Nat.not_lt.mpr (Nat.le_of_lt hab)
          have hxa : x.val < a.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hax) (by omega)
          simp [hbxa, hxa]⟩)
    · have hba : b.val < a.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hab) (by omega)
      by_cases hbx : b.val < x.val
      · by_cases hxa : x.val < a.val
        · exact Or.inr ((mem_cIoo b a x).mpr ⟨h.symm, by simp [hba, hbx, hxa]⟩)
        · exact Or.inl ((mem_cIoo a b x).mpr ⟨h, by
            have hax : a.val < x.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hxa) (by omega)
            simp [hab, hax]⟩)
      · exact Or.inl ((mem_cIoo a b x).mpr ⟨h, by
          have hxb : x.val < b.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hbx) (by omega)
          simp [hab, hxb]⟩)

/-- A point outside the clockwise interval from `a` to `b` is either an endpoint or lies in
the opposite clockwise interval. -/
theorem not_mem_cIoo_iff {a b x : Fin n} (h : a ≠ b) :
    x ∉ cIoo a b ↔ x = a ∨ x = b ∨ x ∈ cIoo b a := by
  constructor
  · intro hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr (Or.inl hxb)
    · exact Or.inr (Or.inr ((mem_cIoo_or_mem_cIoo_swap_iff h).mpr ⟨hxa, hxb⟩ |>.resolve_left hx))
  · intro hx
    rcases hx with hxa | hxb | hx
    · rw [hxa]
      exact left_notMem_cIoo a b
    · rw [hxb]
      exact right_notMem_cIoo a b
    · intro hxab
      exact not_mem_cIoo_and_cIoo_swap a b x ⟨hxab, hx⟩

/-- The two opposite cyclic intervals cover exactly the complement of their endpoints. -/
@[simp]
theorem cIoo_union_swap {a b : Fin n} (h : a ≠ b) :
    cIoo a b ∪ cIoo b a = (Finset.univ.erase a).erase b := by
  ext x
  rw [Finset.mem_union, mem_cIoo_or_mem_cIoo_swap_iff h]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨hxa, hxb⟩
    exact ⟨hxb, hxa⟩
  · rintro ⟨hxb, hxa⟩
    exact ⟨hxa, hxb⟩

/-- The opposite cyclic interval is the endpoint complement with the first interval removed. -/
theorem cIoo_swap_eq_erase_erase_sdiff {a b : Fin n} (h : a ≠ b) :
    cIoo b a = (Finset.univ.erase a).erase b \ cIoo a b := by
  ext x
  constructor
  · intro hx
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · rw [← cIoo_union_swap h]
      exact Finset.mem_union_right _ hx
    · intro hxab
      exact not_mem_cIoo_and_cIoo_swap a b x ⟨hxab, hx⟩
  · intro hx
    have hxu : x ∈ cIoo a b ∪ cIoo b a := by
      rw [cIoo_union_swap h]
      exact (Finset.mem_sdiff.mp hx).1
    rcases Finset.mem_union.mp hxu with hxab | hxba
    · exact ((Finset.mem_sdiff.mp hx).2 hxab).elim
    · exact hxba

/-- The two complementary cyclic intervals have total cardinality `n - 2`. -/
theorem card_cIoo_add_card_cIoo_swap {a b : Fin n} (h : a ≠ b) :
    (cIoo a b).card + (cIoo b a).card = n - 2 := by
  have hcard := congrArg Finset.card (cIoo_union_swap h)
  rw [Finset.card_union_of_disjoint (disjoint_cIoo_swap a b)] at hcard
  have hbmem : b ∈ (Finset.univ : Finset (Fin n)).erase a := by
    simp [h.symm]
  rw [Finset.card_erase_of_mem hbmem, Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard

/-- In a grid of size at most two, every open cyclic interval is empty. There are no grid points
strictly between two endpoints on either of the two complementary arcs. -/
theorem cIoo_eq_empty_of_le_two (hn : n ≤ 2) (a b : Fin n) : cIoo a b = ∅ := by
  by_cases hab : a = b
  · simp [hab]
  · apply Finset.card_eq_zero.mp
    have hsum := card_cIoo_add_card_cIoo_swap hab
    have hcard : (cIoo a b).card = 0 := by omega
    exact hcard

/-- A clockwise open cyclic interval reversed by `Fin.rev` is the clockwise open cyclic interval
with the two endpoints reversed and exchanged.

Coordinate reversal reverses the cyclic order, so it turns the clockwise arc from `a` to `b` into
the clockwise arc from `bᵒ` to `aᵒ`. -/
theorem cIoo_image_rev (a b : Fin n) : (cIoo a b).image Fin.rev = cIoo b.rev a.rev := by
  ext y
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_cIoo] at hx ⊢
    obtain ⟨hne, hc⟩ := hx
    refine ⟨fun h => hne (Fin.rev_injective h).symm, ?_⟩
    have ha := a.isLt; have hb := b.isLt; have hx' := x.isLt
    simp only [Fin.val_rev]
    split_ifs at hc ⊢ <;> omega
  · intro hy
    refine ⟨Fin.rev y, ?_, Fin.rev_rev y⟩
    rw [mem_cIoo] at hy ⊢
    obtain ⟨hne, hc⟩ := hy
    refine ⟨fun h => hne (by rw [h]), ?_⟩
    have ha := a.isLt; have hb := b.isLt; have hy' := y.isLt
    simp only [Fin.val_rev] at hc ⊢
    split_ifs at hc ⊢ <;> omega

/-- Membership in a clockwise open arc with both endpoints and the queried point reversed by
`Fin.rev`. Since coordinate reversal reverses the cyclic order, the reversed point lies in the
reversed arc exactly when the original point lies in the opposite arc. -/
theorem mem_cIoo_rev_rev (a b x : Fin n) :
    x.rev ∈ cIoo a.rev b.rev ↔ x ∈ cIoo b a := by
  rw [← cIoo_image_rev b a, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← Fin.rev_injective hyx]
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Non-interleaving is preserved by reversing every endpoint with `Fin.rev`, with the cyclic
orientation reversal accounted for by exchanging the two endpoints within each pair. -/
theorem noninterleaving_rev (a₀ a₁ b₀ b₁ : Fin n) :
    Noninterleaving a₀.rev a₁.rev b₀.rev b₁.rev ↔ Noninterleaving a₁ a₀ b₁ b₀ := by
  rw [Noninterleaving, Noninterleaving]
  simp only [mem_cIoo_rev_rev]
  tauto

end Grid

end TauCeti
