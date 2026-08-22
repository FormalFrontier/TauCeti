/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Refreshing two coordinates of a finite product measure

Over a finite product `Measure.pi μ` of sigma-finite measures, overwriting two *distinct*
probability coordinates by an independent pair samples the same law: the map

`(z, s, t) ↦ Function.update (Function.update z a s) b t`

pushes `(Measure.pi μ) ⊗ (μ a ⊗ μ b)` forward to `Measure.pi μ`. The two overwritten coordinates
carry the fresh samples and the remaining coordinates keep the ones they had, which is the product
law again.

For `a = b` the pair degenerates to a single refresh because the second update overwrites the
first. The distinctness hypothesis records the two-slot factorisation needed by consumers of this
construction.

## Main statements

* `TauCeti.measurePreserving_update_update` — the two-coordinate refresh is measure
  preserving.

## Implementation

The proof splits the product into the coordinates `{a, b}` and their complement using Mathlib's
measure-preserving product equivalences. The fresh pair replaces the selected coordinates, while
the complementary coordinates are projected from the original assignment; recombining the two
parts is pointwise the double update.
-/

public section

open Function MeasureTheory Set

open scoped ENNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]

/-- Overwriting the two distinct coordinates `a` and `b` of a product-distributed assignment by an
independent pair leaves the product law unchanged. -/
theorem measurePreserving_update_update (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] {a b : ι} [IsProbabilityMeasure (μ a)]
    [IsProbabilityMeasure (μ b)] (hab : a ≠ b) :
    MeasurePreserving
      (fun w : (∀ i, α i) × α a × α b => update (update w.1 a w.2.1) b w.2.2)
      ((Measure.pi μ).prod ((μ a).prod (μ b))) (Measure.pi μ) := by
  let s : Finset ι := {a}
  let t : Finset ι := {b}
  have hdis : Disjoint s t := by simp [s, t, hab]
  let p : ι → Prop := fun i => i ∈ s ∪ t
  let splitEquiv := MeasurableEquiv.piEquivPiSubtypeProd α p
  let unionEquiv := MeasurableEquiv.piFinsetUnion α hdis
  let singleA := (MeasurableEquiv.piUnique fun i : s => α i).symm
  let singleB := (MeasurableEquiv.piUnique fun i : t => α i).symm
  have singleA_apply (u : α a) : singleA u ⟨a, by simp [s]⟩ = u := by
    simp only [singleA, MeasurableEquiv.piUnique_symm_apply]
    unfold uniqueElim
    rfl
  have singleB_apply (v : α b) : singleB v ⟨b, by simp [t]⟩ = v := by
    simp only [singleB, MeasurableEquiv.piUnique_symm_apply]
    unfold uniqueElim
    rfl
  -- `MeasurableEquiv.piFinsetUnion` is by definition `Equiv.piFinsetUnion` carrying the
  -- measurability proofs, and Mathlib states the componentwise lemmas
  -- `Equiv.piFinsetUnion_left`/`_right` only for the bare equivalence. Bridge the two once here,
  -- so that neither case below unfolds the measurable-equivalence wrapper again.
  have unionEquiv_coe (w : ((i : s) → α i) × ((i : t) → α i)) :
      unionEquiv w = Equiv.piFinsetUnion α hdis w := rfl
  have unionEquiv_a (u : α a) (v : α b) (ha : a ∈ s ∪ t) :
      unionEquiv (singleA u, singleB v) ⟨a, ha⟩ = u := by
    rw [unionEquiv_coe, Equiv.piFinsetUnion_left α hdis (by simp [s]) ha]
    exact singleA_apply u
  have unionEquiv_b (u : α a) (v : α b) (hb : b ∈ s ∪ t) :
      unionEquiv (singleA u, singleB v) ⟨b, hb⟩ = v := by
    rw [unionEquiv_coe, Equiv.piFinsetUnion_right α hdis (by simp [t]) hb]
    exact singleB_apply v
  have splitEquiv_symm_apply (x : ∀ i : Subtype p, α i)
      (y : ∀ i : {i // ¬p i}, α i) (i : ι) :
      splitEquiv.symm (x, y) i = if hi : p i then x ⟨i, hi⟩ else y ⟨i, hi⟩ :=
    Equiv.piEquivPiSubtypeProd_symm_apply p α (x, y) i
  have splitEquiv_snd_apply (z : ∀ i, α i) (i : ι) (hi : ¬p i) :
      (splitEquiv z).2 ⟨i, hi⟩ = z i := rfl
  have hsplit := measurePreserving_piEquivPiSubtypeProd μ p
  have hsingleA : MeasurePreserving singleA (μ a) (Measure.pi fun i : s => μ i) := by
    simpa [singleA, s] using MeasurePreserving.symm
      (MeasurableEquiv.piUnique fun i : s => α i)
      (measurePreserving_piUnique fun i : s => μ i)
  have hsingleB : MeasurePreserving singleB (μ b) (Measure.pi fun i : t => μ i) := by
    simpa [singleB, t] using MeasurePreserving.symm
      (MeasurableEquiv.piUnique fun i : t => α i)
      (measurePreserving_piUnique fun i : t => μ i)
  have hselected := (measurePreserving_piFinsetUnion hdis μ).comp (hsingleA.prod hsingleB)
  have hpi : (@Measure.pi (Subtype p) (fun i => α i)
      (Finset.Subtype.fintype (s ∪ t)) (fun i => inferInstance) fun i => μ i) =
      @Measure.pi (Subtype p) (fun i => α i) (Subtype.fintype p)
        (fun i => inferInstance) fun i => μ i := by
    congr 1
    exact Subsingleton.elim _ _
  let _ : IsProbabilityMeasure (@Measure.pi (Subtype p) (fun i => α i) (Subtype.fintype p)
      (fun i => inferInstance) fun i => μ i) := by
    rw [← hpi, ← hselected.map_eq]
    exact Measure.isProbabilityMeasure_map hselected.measurable.aemeasurable
  have hrest := measurePreserving_snd.comp hsplit
  have hcombine := (hselected.prod hrest).comp
    (Measure.measurePreserving_swap (μ := Measure.pi μ) (ν := (μ a).prod (μ b)))
  have hcombine' : MeasurePreserving
      (Prod.map ((MeasurableEquiv.piFinsetUnion α hdis) ∘ Prod.map singleA singleB)
        (Prod.snd ∘ MeasurableEquiv.piEquivPiSubtypeProd α p) ∘ Prod.swap)
      ((Measure.pi μ).prod ((μ a).prod (μ b)))
      ((@Measure.pi (Subtype p) (fun i => α i) (Subtype.fintype p)
          (fun i => inferInstance) fun i => μ i).prod
        (Measure.pi fun i : {i // ¬p i} => μ i)) := by
    refine ⟨hcombine.measurable, ?_⟩
    exact hcombine.map_eq.trans
      (congrArg (fun m => m.prod (Measure.pi fun i : {i // ¬p i} => μ i)) hpi)
  have hrefresh := (MeasurePreserving.symm splitEquiv hsplit).comp hcombine'
  refine hrefresh.congr (by fun_prop) (ae_of_all _ fun w => ?_)
  funext i
  -- `MeasurePreserving.comp` stores this composite function definitionally; expose it once, then
  -- use the application lemmas above for all measurable-equivalence wrappers.
  change splitEquiv.symm
      (unionEquiv (singleA w.2.1, singleB w.2.2), (splitEquiv w.1).2) i =
    update (update w.1 a w.2.1) b w.2.2 i
  rw [splitEquiv_symm_apply]
  by_cases hia : i = a
  · subst i
    simp only [p, s, t, Finset.mem_union, Finset.mem_singleton, true_or, dite_true]
    rw [unionEquiv_a]
    simp [hab]
  · by_cases hib : i = b
    · subst i
      rw [update_self]
      simp only [p, s, t, Finset.mem_union, Finset.mem_singleton, or_true, dite_true]
      rw [unionEquiv_b]
    · simp only [p, s, t, Finset.mem_union, Finset.mem_singleton, hia, hib, false_or,
        dite_false]
      rw [splitEquiv_snd_apply]
      rw [update_of_ne hib, update_of_ne hia]

end TauCeti
