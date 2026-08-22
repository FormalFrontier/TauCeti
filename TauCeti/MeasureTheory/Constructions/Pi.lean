/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Refreshing two coordinates of a finite product of probability measures

Over a finite product `Measure.pi μ` of probability measures, overwriting two *distinct*
coordinates by an independent pair samples the same law: the map

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

The measure-preserving statement is checked on measurable boxes through `Measure.pi_eq`. The
preimage of a box `univ.pi s` is again a box: the two fresh coordinates are constrained by `s a`
and `s b`, and the ambient assignment by `s` with those two entries relaxed to `Set.univ` — which
is `Function.update (Function.update s a univ) b univ`, so the same three evaluation rules for a
doubly updated function drive both the set computation and the product computation.
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
    [∀ i, IsProbabilityMeasure (μ i)] {a b : ι} (hab : a ≠ b) :
    MeasurePreserving
      (fun w : (∀ i, α i) × α a × α b => update (update w.1 a w.2.1) b w.2.2)
      ((Measure.pi μ).prod ((μ a).prod (μ b))) (Measure.pi μ) := by
  have hmeas : Measurable
      fun w : (∀ i, α i) × α a × α b => update (update w.1 a w.2.1) b w.2.2 := by fun_prop
  refine ⟨hmeas, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  -- The three evaluation rules for a doubly updated assignment.
  have hzb : ∀ (z : ∀ i, α i) (u : α a) (t : α b), update (update z a u) b t b = t :=
    fun z u t => update_self b t (update z a u)
  have hza : ∀ (z : ∀ i, α i) (u : α a) (t : α b), update (update z a u) b t a = u := by
    intro z u t
    rw [update_of_ne hab t (update z a u), update_self a u z]
  have hzo : ∀ (z : ∀ i, α i) (u : α a) (t : α b) (i : ι), i ≠ a → i ≠ b →
      update (update z a u) b t i = z i := by
    intro z u t i hia hib
    rw [update_of_ne hib t (update z a u), update_of_ne hia u z]
  -- The assignment box: `s` with the two overwritten entries relaxed to `Set.univ`.
  set s' : ∀ i, Set (α i) := update (update s a univ) b univ with hs'
  have hs'b : s' b = univ := by rw [hs']; exact update_self b univ (update s a univ)
  have hs'a : s' a = univ := by
    rw [hs', update_of_ne hab univ (update s a univ), update_self a univ s]
  have hs'o : ∀ i, i ≠ a → i ≠ b → s' i = s i := by
    intro i hia hib
    rw [hs', update_of_ne hib univ (update s a univ), update_of_ne hia univ s]
  have hpre :
      (fun w : (∀ i, α i) × α a × α b => update (update w.1 a w.2.1) b w.2.2) ⁻¹'
          univ.pi s =
      (univ.pi s') ×ˢ (s a ×ˢ s b) := by
    ext ⟨z, u, t⟩
    simp only [mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_, ?_⟩
      · by_cases hib : i = b
        · rw [hib, hs'b]; exact mem_univ t
        · by_cases hia : i = a
          · rw [hia, hs'a]; exact mem_univ u
          · rw [hs'o i hia hib]
            have := h i
            rwa [hzo z u t i hia hib] at this
      · have := h a; rwa [hza] at this
      · have := h b; rwa [hzb] at this
    · rintro ⟨hz, hu, ht⟩ i
      by_cases hib : i = b
      · subst hib
        rw [hzb]
        exact ht
      · by_cases hia : i = a
        · subst hia
          rw [hza]
          exact hu
        · rw [hzo z u t i hia hib]
          have := hz i
          rwa [hs'o i hia hib] at this
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    Measure.prod_prod, Measure.pi_pi]
  have hb' : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩
  have hrest : ∏ i ∈ (Finset.univ.erase a).erase b, μ i (s' i)
      = ∏ i ∈ (Finset.univ.erase a).erase b, μ i (s i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hs'o i (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi))
      (Finset.ne_of_mem_erase hi)]
  have h1 : (∏ i ∈ (Finset.univ.erase a).erase b, μ i (s i)) * μ b (s b) * μ a (s a)
      = ∏ i, μ i (s i) := by
    rw [Finset.prod_erase_mul (Finset.univ.erase a) (fun i => μ i (s i)) hb',
      Finset.prod_erase_mul Finset.univ (fun i => μ i (s i)) (Finset.mem_univ a)]
  have h2 : (∏ i ∈ (Finset.univ.erase a).erase b, μ i (s' i)) * μ b (s' b) * μ a (s' a)
      = ∏ i, μ i (s' i) := by
    rw [Finset.prod_erase_mul (Finset.univ.erase a) (fun i => μ i (s' i)) hb',
      Finset.prod_erase_mul Finset.univ (fun i => μ i (s' i)) (Finset.mem_univ a)]
  calc (∏ i, μ i (s' i)) * (μ a (s a) * μ b (s b))
      = ((∏ i ∈ (Finset.univ.erase a).erase b, μ i (s' i)) * μ b (s' b) * μ a (s' a))
          * (μ a (s a) * μ b (s b)) := by rw [h2]
    _ = (∏ i ∈ (Finset.univ.erase a).erase b, μ i (s i)) * μ b (s b) * μ a (s a) := by
        rw [hrest, hs'a, hs'b, measure_univ (μ := μ a), measure_univ (μ := μ b)]
        ring
    _ = ∏ i, μ i (s i) := h1

end TauCeti
