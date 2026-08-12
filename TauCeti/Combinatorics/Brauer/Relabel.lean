/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.Brauer.Compose

/-!
# Stacking a Brauer diagram with a permutation diagram

A permutation diagram carries no cap and no cup, so stacking it onto a Brauer diagram creates no
new strand: it only renames the boundary points that the strands of the other diagram end at.
This file makes that precise. Renaming the bottom points of a diagram by `σ` and its top points by
`τ` is `TauCeti.BrauerDiagram.relabel`, the conjugation of the underlying perfect matching by
`Equiv.Perm.sumCongr σ τ`, and the two main results are

`(permToBrauer σ) ∘ D = D.relabel 1 σ`  and  `D ∘ (permToBrauer τ) = D.relabel τ⁻¹ 1`,

writing `∘` for `TauCeti.composeDiagram`. Relabelling composes as
`(D.relabel σ τ).relabel σ' τ' = D.relabel (σ' * σ) (τ' * τ)`, so stacking permutation diagrams on
the two sides of a diagram is an action of `Sₖ × Sₖ` on the Brauer diagrams; the identity diagram
being a two-sided identity for stacking is the trivial case.

The consequence that Layer 9 of the Schur--Weyl roadmap is after is the multiplicativity
`TauCeti.composeDiagram_permToBrauer`: stacking two permutation diagrams gives the permutation
diagram of the product, so `σ ↦ permToBrauer σ` turns the group law of `Sₖ` into the
multiplication of the Brauer algebra on the diagram basis. That is the sense in which the
symmetric group sits inside the Brauer algebra: once the loop-weighted multiplication of the
Brauer algebra is available, this is what will make it restrict to the group algebra `ℂ[Sₖ]`
along `permToBrauer`, since no loop can close up in the middle when one of the two diagrams has
only through strands. The middle-loop count itself is not built here.

Relabelling moves the arcs of a diagram around but does not change their kinds, so it preserves
the numbers of caps, of cups and of through strands
(`TauCeti.BrauerDiagram.bottomCap_relabel` and its companions). Stacking with a permutation
diagram therefore leaves those numbers alone as well; the number of through strands is the
statistic that stratifies the Brauer algebra, and it is constant on each `Sₖ × Sₖ` orbit.

## Main definitions

* `TauCeti.BrauerDiagram.relabel`: renaming the bottom points of a Brauer diagram by `σ` and its
  top points by `τ`.

## Main results

* `TauCeti.composeDiagram_permToBrauer_left` and
  `TauCeti.composeDiagram_permToBrauer_right`: stacking a permutation diagram above or below a
  diagram relabels that diagram's top or bottom boundary.
* `TauCeti.composeDiagram_permToBrauer`: stacking permutation diagrams multiplies the
  permutations.
* `TauCeti.composeDiagram_permToBrauer_one_left` and
  `TauCeti.composeDiagram_permToBrauer_one_right`: the identity diagram is a two-sided identity
  for stacking.
* `TauCeti.BrauerDiagram.relabel_relabel`: relabelling twice is relabelling by the product, so
  `Sₖ × Sₖ` acts on the Brauer diagrams.
* `TauCeti.BrauerDiagram.bottomCap_relabel`, `TauCeti.BrauerDiagram.topCup_relabel` and
  `TauCeti.BrauerDiagram.bottomThrough_relabel`: relabelling permutes the capped, cupped and
  through boundary points, so it preserves their numbers.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9, the `permToBrauer` build item.
-/

public section

namespace TauCeti

namespace BrauerDiagram

variable {k : ℕ}

/-- **Relabelling the boundary of a Brauer diagram**: `σ` renames its bottom points and `τ` its
top points, the arc joining `x` to `y` becoming the arc joining the renamed `x` to the renamed
`y`. -/
def relabel (D : BrauerDiagram k) (σ τ : Equiv.Perm (Fin k)) : BrauerDiagram k :=
  PerfectMatching.congr (Equiv.Perm.sumCongr σ τ) D

variable (D : BrauerDiagram k) (σ τ : Equiv.Perm (Fin k))

/-- Relabelling is the conjugation of the underlying perfect matching by the renaming
`Equiv.Perm.sumCongr σ τ` of the boundary points. -/
theorem relabel_def : D.relabel σ τ = PerfectMatching.congr (Equiv.Perm.sumCongr σ τ) D := (rfl)

/-- Relabelling carries the arc at `x` to the arc at the renamed `x`. -/
theorem relabel_val_map (x : Fin k ⊕ Fin k) :
    (D.relabel σ τ).val (Sum.map σ τ x) = Sum.map σ τ (D.val x) := by
  rw [relabel_def]
  exact PerfectMatching.congr_val_apply_apply (Equiv.Perm.sumCongr σ τ) D x

@[simp]
theorem relabel_val_inl (i : Fin k) :
    (D.relabel σ τ).val (Sum.inl i) = Sum.map σ τ (D.val (Sum.inl (σ.symm i))) := by
  have h := relabel_val_map D σ τ (Sum.inl (σ.symm i))
  rwa [Sum.map_inl, Equiv.apply_symm_apply] at h

@[simp]
theorem relabel_val_inr (j : Fin k) :
    (D.relabel σ τ).val (Sum.inr j) = Sum.map σ τ (D.val (Sum.inr (τ.symm j))) := by
  have h := relabel_val_map D σ τ (Sum.inr (τ.symm j))
  rwa [Sum.map_inr, Equiv.apply_symm_apply] at h

/-- Relabelling by the identity permutations changes nothing. -/
@[simp]
theorem relabel_one_one : D.relabel 1 1 = D := by
  rw [relabel_def, Equiv.Perm.one_def, Equiv.Perm.sumCongr_refl, PerfectMatching.congr_refl]

/-- **Relabelling twice is relabelling by the product.** With
`TauCeti.BrauerDiagram.relabel_one_one` this makes relabelling an action of `Sₖ × Sₖ` on the
Brauer diagrams on `k` strands. -/
theorem relabel_relabel (σ' τ' : Equiv.Perm (Fin k)) :
    (D.relabel σ τ).relabel σ' τ' = D.relabel (σ' * σ) (τ' * τ) := by
  rw [relabel_def, relabel_def, relabel_def, PerfectMatching.congr_trans,
    Equiv.Perm.sumCongr_trans]
  rfl

/-- Relabelling is injective: relabelling back by the inverses recovers the diagram. -/
theorem relabel_injective : Function.Injective fun D : BrauerDiagram k => D.relabel σ τ :=
  fun _ _ h => by
    simpa [relabel_relabel] using congrArg (fun D : BrauerDiagram k => D.relabel σ⁻¹ τ⁻¹) h

/-- **Relabelling a permutation diagram** conjugates the permutation: renaming the bottom points
by `σ` and the top points by `τ` turns the strand `i ↦ ρ i` into the strand `σ i ↦ τ (ρ i)`. -/
@[simp]
theorem relabel_permToBrauer (ρ : Equiv.Perm (Fin k)) :
    (permToBrauer ρ).relabel σ τ = permToBrauer (τ * ρ * σ⁻¹) := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rcases x with i | j
  · simp [Equiv.Perm.mul_apply]
  · rw [relabel_val_inr, permToBrauer_val_inr, Sum.map_inl, permToBrauer_val_inr]
    simp only [← Equiv.Perm.inv_def, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply]

/-! ### Relabelling preserves the kinds of the arcs -/

/-- Relabelling carries a through strand starting at the bottom to a through strand. -/
@[simp]
theorem isThrough_relabel_inl (i : Fin k) :
    (D.relabel σ τ).IsThrough (Sum.inl (σ i)) ↔ D.IsThrough (Sum.inl i) := by
  rw [isThrough_def, isThrough_def, relabel_val_inl, Equiv.symm_apply_apply]
  cases D.val (Sum.inl i) <;> simp

/-- Relabelling carries a through strand starting at the top to a through strand. -/
@[simp]
theorem isThrough_relabel_inr (j : Fin k) :
    (D.relabel σ τ).IsThrough (Sum.inr (τ j)) ↔ D.IsThrough (Sum.inr j) := by
  rw [isThrough_def, isThrough_def, relabel_val_inr, Equiv.symm_apply_apply]
  cases D.val (Sum.inr j) <;> simp

/-- Relabelling carries a cap to a cap. -/
@[simp]
theorem isCap_relabel (i : Fin k) :
    (D.relabel σ τ).IsCap (Sum.inl (σ i)) ↔ D.IsCap (Sum.inl i) := by
  rw [isCap_inl_iff, isCap_inl_iff, isThrough_relabel_inl]

/-- Relabelling carries a cup to a cup. -/
@[simp]
theorem isCup_relabel (j : Fin k) :
    (D.relabel σ τ).IsCup (Sum.inr (τ j)) ↔ D.IsCup (Sum.inr j) := by
  rw [isCup_inr_iff, isCup_inr_iff, isThrough_relabel_inr]

/-- The capped bottom points of a relabelled diagram are the renamed capped bottom points. -/
theorem bottomCap_relabel : (D.relabel σ τ).bottomCap = D.bottomCap.image σ := by
  ext i
  rw [mem_bottomCap, Finset.mem_image]
  refine ⟨fun hi => ⟨σ.symm i, (mem_bottomCap _).mpr ?_, σ.apply_symm_apply i⟩, ?_⟩
  · rwa [← isCap_relabel D σ τ (σ.symm i), Equiv.apply_symm_apply]
  · rintro ⟨i', hi', rfl⟩
    exact (isCap_relabel D σ τ i').mpr ((mem_bottomCap _).mp hi')

/-- The cupped top points of a relabelled diagram are the renamed cupped top points. -/
theorem topCup_relabel : (D.relabel σ τ).topCup = D.topCup.image τ := by
  ext j
  rw [mem_topCup, Finset.mem_image]
  refine ⟨fun hj => ⟨τ.symm j, (mem_topCup _).mpr ?_, τ.apply_symm_apply j⟩, ?_⟩
  · rwa [← isCup_relabel D σ τ (τ.symm j), Equiv.apply_symm_apply]
  · rintro ⟨j', hj', rfl⟩
    exact (isCup_relabel D σ τ j').mpr ((mem_topCup _).mp hj')

/-- The bottom endpoints of the through strands of a relabelled diagram are the renamed ones. -/
theorem bottomThrough_relabel : (D.relabel σ τ).bottomThrough = D.bottomThrough.image σ := by
  ext i
  rw [mem_bottomThrough, Finset.mem_image]
  refine ⟨fun hi => ⟨σ.symm i, (mem_bottomThrough _).mpr ?_, σ.apply_symm_apply i⟩, ?_⟩
  · rwa [← isThrough_relabel_inl D σ τ (σ.symm i), Equiv.apply_symm_apply]
  · rintro ⟨i', hi', rfl⟩
    exact (isThrough_relabel_inl D σ τ i').mpr ((mem_bottomThrough _).mp hi')

/-- Relabelling does not change the number of caps. -/
@[simp]
theorem card_bottomCap_relabel : (D.relabel σ τ).bottomCap.card = D.bottomCap.card := by
  rw [bottomCap_relabel, Finset.card_image_of_injective _ σ.injective]

/-- Relabelling does not change the number of cups. -/
@[simp]
theorem card_topCup_relabel : (D.relabel σ τ).topCup.card = D.topCup.card := by
  rw [topCup_relabel, Finset.card_image_of_injective _ τ.injective]

/-- Relabelling does not change the number of through strands. -/
@[simp]
theorem card_bottomThrough_relabel :
    (D.relabel σ τ).bottomThrough.card = D.bottomThrough.card := by
  rw [bottomThrough_relabel, Finset.card_image_of_injective _ σ.injective]

end BrauerDiagram

/-! ### Stacking with a permutation diagram -/

variable {k : ℕ} (D : BrauerDiagram k) (σ τ : Equiv.Perm (Fin k))

open BrauerDiagram in
/-- **Stacking a permutation diagram on top relabels the top boundary.** No strand of `D` is
extended past the middle boundary, because the permutation diagram has no cap: a through strand of
`D` ending at the middle point `a` is continued by the single strand of `permToBrauer σ` above it,
which leaves at the top point `σ a`. -/
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
closes up in the middle, since a permutation diagram has neither a cap nor a cup. -/
@[simp]
theorem composeDiagram_permToBrauer :
    composeDiagram (permToBrauer σ) (permToBrauer τ) = permToBrauer (σ * τ) := by
  rw [composeDiagram_permToBrauer_left, BrauerDiagram.relabel_permToBrauer, inv_one, mul_one]

/-- **The identity diagram is a left identity for stacking.** -/
@[simp]
theorem composeDiagram_permToBrauer_one_left : composeDiagram (permToBrauer 1) D = D := by
  rw [composeDiagram_permToBrauer_left, BrauerDiagram.relabel_one_one]

/-- **The identity diagram is a right identity for stacking.** -/
@[simp]
theorem composeDiagram_permToBrauer_one_right : composeDiagram D (permToBrauer 1) = D := by
  rw [composeDiagram_permToBrauer_right, inv_one, BrauerDiagram.relabel_one_one]

/-- Stacking a permutation diagram on top does not change the number of caps. -/
theorem card_bottomCap_composeDiagram_permToBrauer_left :
    (composeDiagram (permToBrauer σ) D).bottomCap.card = D.bottomCap.card := by
  rw [composeDiagram_permToBrauer_left, BrauerDiagram.card_bottomCap_relabel]

/-- Stacking a permutation diagram underneath does not change the number of caps. -/
theorem card_bottomCap_composeDiagram_permToBrauer_right :
    (composeDiagram D (permToBrauer τ)).bottomCap.card = D.bottomCap.card := by
  rw [composeDiagram_permToBrauer_right, BrauerDiagram.card_bottomCap_relabel]

/-- Stacking a permutation diagram on top does not change the number of cups. -/
theorem card_topCup_composeDiagram_permToBrauer_left :
    (composeDiagram (permToBrauer σ) D).topCup.card = D.topCup.card := by
  rw [composeDiagram_permToBrauer_left, BrauerDiagram.card_topCup_relabel]

/-- Stacking a permutation diagram underneath does not change the number of cups. -/
theorem card_topCup_composeDiagram_permToBrauer_right :
    (composeDiagram D (permToBrauer τ)).topCup.card = D.topCup.card := by
  rw [composeDiagram_permToBrauer_right, BrauerDiagram.card_topCup_relabel]

end TauCeti
