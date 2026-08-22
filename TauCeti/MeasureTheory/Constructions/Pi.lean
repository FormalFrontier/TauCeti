/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Refreshing two coordinates of a finite product of probability measures

Over a finite product `Measure.pi fun _ : ι => μ` of copies of one probability measure, overwriting
two *distinct* coordinates by an independent pair samples the same law: the map

`(z, s, t) ↦ Function.update (Function.update z a s) b t`

pushes `(Measure.pi fun _ => μ) ⊗ (μ ⊗ μ)` forward to `Measure.pi fun _ => μ`. The two overwritten
coordinates carry the fresh sample and the remaining coordinates keep the ones they had, which is
the product law again. Combined with Fubini this turns an integral over `ι → Ω` into an outer
integral over the ambient assignment and an inner *double* integral over the two singled-out
coordinates — what an estimate that treats two coordinates specially needs.

The hypothesis `a ≠ b` is essential: for `a = b` the second update overwrites the first, and the
first coordinate of the fresh pair is discarded.

## Main statements

* `TauCeti.MeasureTheory.measurePreserving_update_update` — the two-coordinate refresh is measure
  preserving;
* `TauCeti.MeasureTheory.integral_pi_eq_integral_integral_update` — the resulting Fubini identity.

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

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]

/-- Overwriting the two distinct coordinates `a` and `b` of a product-distributed assignment by an
independent pair leaves the product law unchanged. -/
theorem measurePreserving_update_update (μ : Measure Ω) [IsProbabilityMeasure μ] {a b : ι}
    (hab : a ≠ b) :
    MeasurePreserving (fun w : (ι → Ω) × Ω × Ω => update (update w.1 a w.2.1) b w.2.2)
      ((Measure.pi fun _ : ι => μ).prod (μ.prod μ)) (Measure.pi fun _ : ι => μ) := by
  have hmeas : Measurable
      fun w : (ι → Ω) × Ω × Ω => update (update w.1 a w.2.1) b w.2.2 := by fun_prop
  refine ⟨hmeas, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  -- The three evaluation rules for a doubly updated assignment.
  have hzb : ∀ (z : ι → Ω) (u t : Ω), update (update z a u) b t b = t :=
    fun z u t => update_self b t (update z a u)
  have hza : ∀ (z : ι → Ω) (u t : Ω), update (update z a u) b t a = u := by
    intro z u t
    rw [update_of_ne hab t (update z a u), update_self a u z]
  have hzo : ∀ (z : ι → Ω) (u t : Ω) (i : ι), i ≠ a → i ≠ b →
      update (update z a u) b t i = z i := by
    intro z u t i hia hib
    rw [update_of_ne hib t (update z a u), update_of_ne hia u z]
  -- The assignment box: `s` with the two overwritten entries relaxed to `Set.univ`.
  set s' : ι → Set Ω := update (update s a univ) b univ with hs'
  have hs'b : s' b = univ := by rw [hs']; exact update_self b univ (update s a univ)
  have hs'a : s' a = univ := by
    rw [hs', update_of_ne hab univ (update s a univ), update_self a univ s]
  have hs'o : ∀ i, i ≠ a → i ≠ b → s' i = s i := by
    intro i hia hib
    rw [hs', update_of_ne hib univ (update s a univ), update_of_ne hia univ s]
  have hpre : (fun w : (ι → Ω) × Ω × Ω => update (update w.1 a w.2.1) b w.2.2) ⁻¹' univ.pi s =
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
      · rw [hib, hzb]; rw [hib] at *; exact ht
      · by_cases hia : i = a
        · rw [hia, hza]; rw [hia] at *; exact hu
        · rw [hzo z u t i hia hib]
          have := hz i
          rwa [hs'o i hia hib] at this
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    Measure.prod_prod, Measure.pi_pi]
  have hb' : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩
  have hrest : ∏ i ∈ (Finset.univ.erase a).erase b, μ (s' i)
      = ∏ i ∈ (Finset.univ.erase a).erase b, μ (s i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hs'o i (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi))
      (Finset.ne_of_mem_erase hi)]
  have h1 : (∏ i ∈ (Finset.univ.erase a).erase b, μ (s i)) * μ (s b) * μ (s a)
      = ∏ i, μ (s i) := by
    rw [Finset.prod_erase_mul (Finset.univ.erase a) (fun i => μ (s i)) hb',
      Finset.prod_erase_mul Finset.univ (fun i => μ (s i)) (Finset.mem_univ a)]
  have h2 : (∏ i ∈ (Finset.univ.erase a).erase b, μ (s' i)) * μ (s' b) * μ (s' a)
      = ∏ i, μ (s' i) := by
    rw [Finset.prod_erase_mul (Finset.univ.erase a) (fun i => μ (s' i)) hb',
      Finset.prod_erase_mul Finset.univ (fun i => μ (s' i)) (Finset.mem_univ a)]
  calc (∏ i, μ (s' i)) * (μ (s a) * μ (s b))
      = ((∏ i ∈ (Finset.univ.erase a).erase b, μ (s' i)) * μ (s' b) * μ (s' a))
          * (μ (s a) * μ (s b)) := by rw [h2]
    _ = (∏ i ∈ (Finset.univ.erase a).erase b, μ (s i)) * μ (s b) * μ (s a) := by
        rw [hrest, hs'a, hs'b, measure_univ]; ring
    _ = ∏ i, μ (s i) := h1

/-- **Fubini after a two-coordinate refresh.** An integral over `ι → Ω` against a finite product of
copies of a probability measure is an outer integral over the assignment and an inner integral over
a fresh independent pair placed at the two distinct coordinates `a` and `b`. -/
theorem integral_pi_eq_integral_integral_update {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure Ω) [IsProbabilityMeasure μ] {a b : ι} (hab : a ≠ b)
    {f : (ι → Ω) → E} (hf : Integrable f (Measure.pi fun _ : ι => μ)) :
    ∫ z, (∫ p : Ω × Ω, f (update (update z a p.1) b p.2) ∂μ.prod μ)
        ∂(Measure.pi fun _ : ι => μ)
      = ∫ x, f x ∂(Measure.pi fun _ : ι => μ) := by
  set g : (ι → Ω) × Ω × Ω → ι → Ω :=
    fun w => update (update w.1 a w.2.1) b w.2.2 with hg
  have hmp := measurePreserving_update_update (ι := ι) μ hab
  have hcomp : Integrable (fun w => f (g w))
      ((Measure.pi fun _ : ι => μ).prod (μ.prod μ)) :=
    hmp.integrable_comp_of_integrable hf
  have hae : AEStronglyMeasurable f
      (Measure.map g ((Measure.pi fun _ : ι => μ).prod (μ.prod μ))) := by
    rw [hmp.map_eq]
    exact hf.aestronglyMeasurable
  calc ∫ z, (∫ p : Ω × Ω, f (update (update z a p.1) b p.2) ∂μ.prod μ)
        ∂(Measure.pi fun _ : ι => μ)
      = ∫ w, f (g w) ∂((Measure.pi fun _ : ι => μ).prod (μ.prod μ)) :=
        (integral_prod _ hcomp).symm
    _ = ∫ x, f x ∂(Measure.map g ((Measure.pi fun _ : ι => μ).prod (μ.prod μ))) :=
        (integral_map hmp.measurable.aemeasurable hae).symm
    _ = ∫ x, f x ∂(Measure.pi fun _ : ι => μ) := by rw [hmp.map_eq]

end MeasureTheory

end TauCeti
