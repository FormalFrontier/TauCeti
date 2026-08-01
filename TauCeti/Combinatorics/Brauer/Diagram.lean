/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Fintype.Sum
public import TauCeti.Combinatorics.Enumerative.PerfectMatching

/-!
# Brauer diagrams

A **Brauer diagram** on `k` strands is a perfect matching of the `2 * k` boundary points
`Fin k ⊕ Fin k`, where `Sum.inl i` is the `i`-th bottom point and `Sum.inr j` the `j`-th top
point; the matched pairs are the arcs of the diagram. Brauer diagrams index a basis of the
Brauer algebra `B_k(δ)`, which acts on the `k`-th tensor power of the defining representation
of an orthogonal or symplectic group. The image of that action is the centralizer of the
group, but the action is faithful, so that `B_k(δ)` is itself that centralizer, only when the
defining representation is large enough relative to `k`.

Every boundary point lies on exactly one of three kinds of arc: a **through strand**, joining
a bottom point to a top point; a **cap**, joining two bottom points; or a **cup**, joining two
top points. The diagrams with no cap and no cup are exactly the diagrams `permToBrauer σ` of
permutations `σ : Equiv.Perm (Fin k)`, so there are `k !` of them among the `(2 * k - 1)‼`
diagrams in all.

## Main definitions

* `TauCeti.BrauerDiagram k`: the Brauer diagrams on `k` strands.
* `TauCeti.BrauerDiagram.IsThrough`, `IsCap`, `IsCup`: the three kinds of arc.
* `TauCeti.permToBrauer`: the diagram of a permutation.
* `TauCeti.permToBrauerEquiv`: permutations are the diagrams all of whose arcs go through.

## Main results

* `TauCeti.card_brauerDiagram`: there are `(2 * k - 1)‼` Brauer diagrams on `k` strands.
* `TauCeti.BrauerDiagram.isThrough_or_isCap_or_isCup`, together with the three exclusivity
  lemmas: every boundary point lies on an arc of exactly one of the three kinds.
* `TauCeti.card_brauerDiagram_forall_isThrough`: there are `k !` diagrams all of whose arcs go
  through.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9.
-/

public section

open scoped Nat

namespace TauCeti

/-- A **Brauer diagram** on `k` strands: a perfect matching of the `2 * k` boundary points
`Fin k ⊕ Fin k`, with `Sum.inl i` the `i`-th bottom point and `Sum.inr j` the `j`-th top
point.  The value `D.val x` is the boundary point that the diagram matches with `x`. -/
abbrev BrauerDiagram (k : ℕ) := PerfectMatching (Fin k ⊕ Fin k)

/-- **The number of Brauer diagrams.** There are `(2 * k - 1)‼` perfect matchings of the
`2 * k` boundary points, hence `(2 * k - 1)‼` Brauer diagrams on `k` strands. -/
theorem card_brauerDiagram (k : ℕ) : Fintype.card (BrauerDiagram k) = (2 * k - 1)‼ :=
  card_perfectMatching (Fin k ⊕ Fin k) (by simp [Fintype.card_sum, two_mul])

-- On two strands there are three Brauer diagrams: the identity, the crossing, and the cap-cup.
example : Fintype.card (BrauerDiagram 2) = 3 := by
  rw [card_brauerDiagram]
  decide

namespace BrauerDiagram

variable {k : ℕ} (D : BrauerDiagram k) (x : Fin k ⊕ Fin k)

/-- The boundary point `x` lies on a **through strand**: it is matched with a point on the
opposite boundary. -/
def IsThrough : Prop := (D.val x).isLeft ≠ x.isLeft

/-- The boundary point `x` lies on a **cap**: it is a bottom point matched with another bottom
point. -/
def IsCap : Prop := x.isLeft ∧ (D.val x).isLeft

/-- The boundary point `x` lies on a **cup**: it is a top point matched with another top
point. -/
def IsCup : Prop := x.isRight ∧ (D.val x).isRight

instance : Decidable (D.IsThrough x) :=
  inferInstanceAs (Decidable ((D.val x).isLeft ≠ x.isLeft))

instance : Decidable (D.IsCap x) := inferInstanceAs (Decidable (x.isLeft ∧ (D.val x).isLeft))

instance : Decidable (D.IsCup x) := inferInstanceAs (Decidable (x.isRight ∧ (D.val x).isRight))

/-- Lying on a through strand means being matched across the two boundaries. -/
theorem isThrough_def : D.IsThrough x ↔ (D.val x).isLeft ≠ x.isLeft := Iff.rfl

/-- Lying on a cap means being a bottom point matched with a bottom point. -/
theorem isCap_def : D.IsCap x ↔ x.isLeft ∧ (D.val x).isLeft := Iff.rfl

/-- Lying on a cup means being a top point matched with a top point. -/
theorem isCup_def : D.IsCup x ↔ x.isRight ∧ (D.val x).isRight := Iff.rfl

/-- Every boundary point lies on a through strand, on a cap, or on a cup. -/
theorem isThrough_or_isCap_or_isCup : D.IsThrough x ∨ D.IsCap x ∨ D.IsCup x := by
  rcases x with i | i
  · rcases h : D.val (Sum.inl i) with j | j <;> simp [IsThrough, IsCap, IsCup, h]
  · rcases h : D.val (Sum.inr i) with j | j <;> simp [IsThrough, IsCap, IsCup, h]

/-- A cap is not a through strand. -/
theorem not_isThrough_of_isCap (h : D.IsCap x) : ¬D.IsThrough x := by
  simp [IsThrough, h.1, h.2]

/-- A cup is not a through strand. -/
theorem not_isThrough_of_isCup (h : D.IsCup x) : ¬D.IsThrough x := by
  rcases x with i | i
  · simp [IsCup] at h
  · rcases hx : D.val (Sum.inr i) with j | j
    · rw [IsCup, hx] at h; simp at h
    · simp [IsThrough, hx]

/-- A cap is not a cup. -/
theorem not_isCup_of_isCap (h : D.IsCap x) : ¬D.IsCup x := by
  rcases x with i | i
  · simp [IsCup]
  · simp [IsCap] at h

/-- Lying on a through strand is a property of the arc, not of the endpoint chosen. -/
@[simp]
theorem isThrough_val : D.IsThrough (D.val x) ↔ D.IsThrough x := by
  simp only [IsThrough, D.apply_apply]
  exact ne_comm

/-- Lying on a cap is a property of the arc, not of the endpoint chosen. -/
@[simp]
theorem isCap_val : D.IsCap (D.val x) ↔ D.IsCap x := by
  simp only [IsCap, D.apply_apply]
  exact and_comm

/-- Lying on a cup is a property of the arc, not of the endpoint chosen. -/
@[simp]
theorem isCup_val : D.IsCup (D.val x) ↔ D.IsCup x := by
  simp only [IsCup, D.apply_apply]
  exact and_comm

end BrauerDiagram

/-- The **permutation diagram** of `σ`, joining the bottom point `i` to the top point `σ i`. -/
def permToBrauer {k : ℕ} (σ : Equiv.Perm (Fin k)) : BrauerDiagram k :=
  .mk ((Equiv.sumComm (Fin k) (Fin k)).trans (Equiv.sumCongr σ.symm σ))
    (fun x => by rcases x with i | i <;> simp) fun x => by rcases x with i | i <;> simp

namespace BrauerDiagram

variable {k : ℕ}

@[simp]
theorem permToBrauer_val_inl (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    (permToBrauer σ).val (Sum.inl i) = Sum.inr (σ i) := by simp [permToBrauer]

@[simp]
theorem permToBrauer_val_inr (σ : Equiv.Perm (Fin k)) (j : Fin k) :
    (permToBrauer σ).val (Sum.inr j) = Sum.inl (σ.symm j) := by simp [permToBrauer]

/-- A permutation diagram has no cap and no cup: every arc goes through. -/
@[simp]
theorem isThrough_permToBrauer (σ : Equiv.Perm (Fin k)) (x : Fin k ⊕ Fin k) :
    (permToBrauer σ).IsThrough x := by rcases x with i | i <;> simp [IsThrough]

variable {D : BrauerDiagram k}

/-- A bottom point on a through strand is matched with a top point. -/
theorem isRight_val_inl {i : Fin k} (hi : D.IsThrough (Sum.inl i)) :
    (D.val (Sum.inl i)).isRight := by
  rcases h : D.val (Sum.inl i) with j | j
  · rw [IsThrough, h] at hi; simp at hi
  · simp

/-- A top point on a through strand is matched with a bottom point. -/
theorem isLeft_val_inr {j : Fin k} (hj : D.IsThrough (Sum.inr j)) :
    (D.val (Sum.inr j)).isLeft := by
  rcases h : D.val (Sum.inr j) with i | i
  · simp
  · rw [IsThrough, h] at hj; simp at hj

/-- The permutation read off a Brauer diagram all of whose arcs go through: it sends the
bottom point `i` to the top point matched with it. -/
noncomputable def throughPerm (D : BrauerDiagram k) (hD : ∀ x, D.IsThrough x) :
    Equiv.Perm (Fin k) :=
  Equiv.ofBijective (fun i => (D.val (Sum.inl i)).getRight (isRight_val_inl (hD (Sum.inl i))))
    (Finite.injective_iff_bijective.mp fun i i' h => by
      have h₁ : D.val (Sum.inl i) = D.val (Sum.inl i') := by
        rw [← Sum.inr_getRight _ (isRight_val_inl (hD (Sum.inl i))),
          ← Sum.inr_getRight _ (isRight_val_inl (hD (Sum.inl i'))), h]
      simpa using D.val.injective h₁)

@[simp]
theorem throughPerm_apply (hD : ∀ x, D.IsThrough x) (i : Fin k) :
    throughPerm D hD i = (D.val (Sum.inl i)).getRight (isRight_val_inl (hD (Sum.inl i))) := (rfl)

/-- The diagram of the permutation read off a through diagram is the diagram itself. -/
@[simp]
theorem permToBrauer_throughPerm (hD : ∀ x, D.IsThrough x) :
    permToBrauer (throughPerm D hD) = D := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rcases x with i | j
  · rw [permToBrauer_val_inl, throughPerm_apply, Sum.inr_getRight]
  · obtain ⟨m, hm⟩ : ∃ m, D.val (Sum.inr j) = Sum.inl m :=
      ⟨_, (Sum.inl_getLeft _ (isLeft_val_inr (hD (Sum.inr j)))).symm⟩
    rw [permToBrauer_val_inr, hm, Sum.inl.injEq, Equiv.symm_apply_eq, throughPerm_apply]
    exact ((Sum.getRight_eq_iff _).mpr (by rw [← hm, D.apply_apply])).symm

/-- The permutation read off the diagram of `σ` is `σ`. -/
@[simp]
theorem throughPerm_permToBrauer (σ : Equiv.Perm (Fin k)) :
    throughPerm (permToBrauer σ) (isThrough_permToBrauer σ) = σ :=
  Equiv.ext fun i => (Sum.getRight_eq_iff _).mpr (permToBrauer_val_inl σ i)

end BrauerDiagram

/-- **Permutations are exactly the Brauer diagrams with no horizontal arc.** -/
noncomputable def permToBrauerEquiv (k : ℕ) :
    Equiv.Perm (Fin k) ≃ {D : BrauerDiagram k // ∀ x, D.IsThrough x} where
  toFun σ := ⟨permToBrauer σ, BrauerDiagram.isThrough_permToBrauer σ⟩
  invFun D := BrauerDiagram.throughPerm D.1 D.2
  left_inv σ := BrauerDiagram.throughPerm_permToBrauer σ
  right_inv D := Subtype.ext (BrauerDiagram.permToBrauer_throughPerm D.2)

@[simp]
theorem permToBrauerEquiv_apply {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (permToBrauerEquiv k σ : BrauerDiagram k) = permToBrauer σ := (rfl)

@[simp]
theorem permToBrauerEquiv_symm_apply {k : ℕ} (D : {D : BrauerDiagram k // ∀ x, D.IsThrough x}) :
    (permToBrauerEquiv k).symm D = BrauerDiagram.throughPerm D.1 D.2 := (rfl)

/-- The Brauer diagrams with no cap and no cup are `k !` in number. -/
theorem card_brauerDiagram_forall_isThrough (k : ℕ) :
    Fintype.card {D : BrauerDiagram k // ∀ x, D.IsThrough x} = k ! := by
  rw [← Fintype.card_congr (permToBrauerEquiv k), Fintype.card_perm, Fintype.card_fin]

/-- The permutation diagram determines the permutation. -/
theorem permToBrauer_injective (k : ℕ) : Function.Injective (permToBrauer (k := k)) :=
  fun _ _ h => (permToBrauerEquiv k).injective (Subtype.ext h)

end TauCeti
