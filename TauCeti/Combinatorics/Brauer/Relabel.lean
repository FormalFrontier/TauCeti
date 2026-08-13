/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.Brauer.Boundary

/-!
# Relabelling the boundary of a Brauer diagram

Renaming the bottom points of a Brauer diagram by a permutation `σ` and its top points by a
permutation `τ` gives another Brauer diagram, `TauCeti.BrauerDiagram.relabel`: the arc joining `x`
to `y` becomes the arc joining the renamed `x` to the renamed `y`, so the underlying perfect
matching is conjugated by the renaming `Equiv.Perm.sumCongr σ τ` of the boundary points.

Relabelling twice is relabelling by the product,
`(D.relabel σ τ).relabel σ' τ' = D.relabel (σ' * σ) (τ' * τ)`, so relabelling is an action of
`Sₖ × Sₖ` on the Brauer diagrams on `k` strands. It moves the arcs of a diagram around but does
not change their kinds, so it preserves the numbers of caps, of cups and of through strands. The
number of through strands is the statistic that stratifies the Brauer algebra, so that statistic
is constant on each `Sₖ × Sₖ` orbit.

Relabelling is exactly what stacking a permutation diagram onto a Brauer diagram does, since a
permutation diagram has neither a cap nor a cup and so extends no strand of the other diagram past
the middle boundary; that is `TauCeti.composeDiagram_permToBrauer_left` and
`TauCeti.composeDiagram_permToBrauer_right`, in `TauCeti/Combinatorics/Brauer/Compose.lean`, which
imports this file.

## Main definitions

* `TauCeti.BrauerDiagram.relabel`: renaming the bottom points of a Brauer diagram by `σ` and its
  top points by `τ`.

## Main results

* `TauCeti.BrauerDiagram.relabel_relabel`: relabelling twice is relabelling by the product, so
  `Sₖ × Sₖ` acts on the Brauer diagrams.
* `TauCeti.BrauerDiagram.relabel_permToBrauer`: relabelling a permutation diagram conjugates the
  permutation.
* `TauCeti.BrauerDiagram.bottomCap_relabel`, `TauCeti.BrauerDiagram.topCup_relabel`,
  `TauCeti.BrauerDiagram.bottomThrough_relabel` and `TauCeti.BrauerDiagram.topThrough_relabel`:
  relabelling permutes the capped, cupped and through boundary points, so it preserves their
  numbers.

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

/-- The arc of a relabelled diagram at the bottom point `i` is the renamed arc at the bottom point
`σ.symm i` that `i` was renamed from. -/
@[simp]
theorem relabel_val_inl (i : Fin k) :
    (D.relabel σ τ).val (Sum.inl i) = Sum.map σ τ (D.val (Sum.inl (σ.symm i))) := by
  have h := relabel_val_map D σ τ (Sum.inl (σ.symm i))
  rwa [Sum.map_inl, Equiv.apply_symm_apply] at h

/-- The arc of a relabelled diagram at the top point `j` is the renamed arc at the top point
`τ.symm j` that `j` was renamed from. -/
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
@[simp]
theorem relabel_relabel (σ' τ' : Equiv.Perm (Fin k)) :
    (D.relabel σ τ).relabel σ' τ' = D.relabel (σ' * σ) (τ' * τ) := by
  rw [relabel_def, relabel_def, relabel_def, PerfectMatching.congr_trans,
    Equiv.Perm.sumCongr_trans]
  rfl

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

/-- **Relabelling carries a through strand to a through strand**: the renamed point lies on a
through strand of the relabelled diagram exactly when the point lies on a through strand. -/
@[simp]
theorem isThrough_relabel (x : Fin k ⊕ Fin k) :
    (D.relabel σ τ).IsThrough (Sum.map σ τ x) ↔ D.IsThrough x := by
  rw [isThrough_def, isThrough_def, relabel_val_map, Sum.isLeft_map, Sum.isLeft_map]

/-- **Relabelling carries a cap to a cap.** -/
@[simp]
theorem isCap_relabel (x : Fin k ⊕ Fin k) :
    (D.relabel σ τ).IsCap (Sum.map σ τ x) ↔ D.IsCap x := by
  rw [isCap_def, isCap_def, relabel_val_map, Sum.isLeft_map, Sum.isLeft_map]

/-- **Relabelling carries a cup to a cup.** -/
@[simp]
theorem isCup_relabel (x : Fin k ⊕ Fin k) :
    (D.relabel σ τ).IsCup (Sum.map σ τ x) ↔ D.IsCup x := by
  rw [isCup_def, isCup_def, relabel_val_map, Sum.isRight_map, Sum.isRight_map]

/-- Relabelling carries a through strand starting at the bottom to a through strand. -/
@[simp]
theorem isThrough_relabel_inl (i : Fin k) :
    (D.relabel σ τ).IsThrough (Sum.inl (σ i)) ↔ D.IsThrough (Sum.inl i) :=
  Sum.map_inl σ τ i ▸ isThrough_relabel D σ τ (Sum.inl i)

/-- Relabelling carries a through strand starting at the top to a through strand. -/
@[simp]
theorem isThrough_relabel_inr (j : Fin k) :
    (D.relabel σ τ).IsThrough (Sum.inr (τ j)) ↔ D.IsThrough (Sum.inr j) :=
  Sum.map_inr σ τ j ▸ isThrough_relabel D σ τ (Sum.inr j)

/-- Relabelling carries a cap to a cap, read off at the bottom boundary. -/
@[simp]
theorem isCap_relabel_inl (i : Fin k) :
    (D.relabel σ τ).IsCap (Sum.inl (σ i)) ↔ D.IsCap (Sum.inl i) :=
  Sum.map_inl σ τ i ▸ isCap_relabel D σ τ (Sum.inl i)

/-- Relabelling carries a cup to a cup, read off at the top boundary. -/
@[simp]
theorem isCup_relabel_inr (j : Fin k) :
    (D.relabel σ τ).IsCup (Sum.inr (τ j)) ↔ D.IsCup (Sum.inr j) :=
  Sum.map_inr σ τ j ▸ isCup_relabel D σ τ (Sum.inr j)

/-- The capped bottom points of a relabelled diagram are the renamed capped bottom points.

Not a `simp` lemma: rewriting by it takes `TauCeti.BrauerDiagram.card_bottomCap_relabel` out of
simp-normal form, and `simp` cannot finish the resulting cardinality goal on its own. -/
theorem bottomCap_relabel : (D.relabel σ τ).bottomCap = D.bottomCap.image σ := by
  ext i
  rw [mem_bottomCap, Finset.mem_image]
  refine ⟨fun hi => ⟨σ.symm i, (mem_bottomCap _).mpr ?_, σ.apply_symm_apply i⟩, ?_⟩
  · rwa [← isCap_relabel_inl D σ τ (σ.symm i), Equiv.apply_symm_apply]
  · rintro ⟨i', hi', rfl⟩
    exact (isCap_relabel_inl D σ τ i').mpr ((mem_bottomCap _).mp hi')

/-- The cupped top points of a relabelled diagram are the renamed cupped top points.

Not a `simp` lemma, for the reason given for `TauCeti.BrauerDiagram.bottomCap_relabel`. -/
theorem topCup_relabel : (D.relabel σ τ).topCup = D.topCup.image τ := by
  ext j
  rw [mem_topCup, Finset.mem_image]
  refine ⟨fun hj => ⟨τ.symm j, (mem_topCup _).mpr ?_, τ.apply_symm_apply j⟩, ?_⟩
  · rwa [← isCup_relabel_inr D σ τ (τ.symm j), Equiv.apply_symm_apply]
  · rintro ⟨j', hj', rfl⟩
    exact (isCup_relabel_inr D σ τ j').mpr ((mem_topCup _).mp hj')

/-- The bottom endpoints of the through strands of a relabelled diagram are the renamed ones.

Not a `simp` lemma, for the reason given for `TauCeti.BrauerDiagram.bottomCap_relabel`. -/
theorem bottomThrough_relabel : (D.relabel σ τ).bottomThrough = D.bottomThrough.image σ := by
  ext i
  rw [mem_bottomThrough, Finset.mem_image]
  refine ⟨fun hi => ⟨σ.symm i, (mem_bottomThrough _).mpr ?_, σ.apply_symm_apply i⟩, ?_⟩
  · rwa [← isThrough_relabel_inl D σ τ (σ.symm i), Equiv.apply_symm_apply]
  · rintro ⟨i', hi', rfl⟩
    exact (isThrough_relabel_inl D σ τ i').mpr ((mem_bottomThrough _).mp hi')

/-- The top endpoints of the through strands of a relabelled diagram are the renamed ones.

Not a `simp` lemma, for the reason given for `TauCeti.BrauerDiagram.bottomCap_relabel`. -/
theorem topThrough_relabel : (D.relabel σ τ).topThrough = D.topThrough.image τ := by
  ext j
  rw [mem_topThrough, Finset.mem_image]
  refine ⟨fun hj => ⟨τ.symm j, (mem_topThrough _).mpr ?_, τ.apply_symm_apply j⟩, ?_⟩
  · rwa [← isThrough_relabel_inr D σ τ (τ.symm j), Equiv.apply_symm_apply]
  · rintro ⟨j', hj', rfl⟩
    exact (isThrough_relabel_inr D σ τ j').mpr ((mem_topThrough _).mp hj')

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

/-- Relabelling does not change the number of through strands, counted at the top. -/
@[simp]
theorem card_topThrough_relabel : (D.relabel σ τ).topThrough.card = D.topThrough.card := by
  rw [topThrough_relabel, Finset.card_image_of_injective _ τ.injective]

end BrauerDiagram

end TauCeti
