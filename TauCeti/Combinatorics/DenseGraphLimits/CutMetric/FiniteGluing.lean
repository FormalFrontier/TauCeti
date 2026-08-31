/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.ProbabilityMassFunction.Finite

/-!
# Finite coupling gluing

For finite probability spaces, this file gives the elementary gluing formula used by the
finite-step reduction of the graphon cut-distance triangle inequality.  If `π` is a law on
`α × β` and `σ` is a law on `β × γ` with the same `β` marginal, the glued law on
`α × β × γ` has mass

`π (a, b) * σ (b, c) / ν b`,

where `ν` is the common middle marginal.  At a zero-mass middle atom the formula is explicitly
defined to be zero.  Such atoms carry no mass in either input law, so this branch does not affect
the marginals; making it visible is important when the finite law is later obtained by partitioning
an arbitrary probability carrier.

The construction is deliberately at the `PMF` level.  It is not a second measure-level gluing
theorem: `TauCeti.MeasureTheory.exists_glue_of_countable_middle` already provides that result.
This finite API records the actual matrix calculation that the arbitrary-carrier triangle proof
will consume.

## Main definitions

* `finiteGluing` is the normalized finite gluing, with an explicit zero-mass branch.

## Main results

* `finiteGluing_apply` gives the formula;
* `finiteGluing_map_left` and `finiteGluing_map_right` recover the two input laws;
* `finiteGluing_map_outer` records the outer coupling produced by the gluing.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 6.5.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 design-validation milestone
  preceding `cutDist_triangle`: finite coupling gluing with zero-mass middle atoms explicit.
-/

public section

noncomputable section

open scoped BigOperators ENNReal

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable [instFintypeα : Fintype α] [instFintypeβ : Fintype β] [instFintypeγ : Fintype γ]

namespace PMF

variable (π : PMF (α × β)) (σ : PMF (β × γ))

/-- The mass of the middle atom `b` in the first input law. -/
def finiteGluingMiddleMass (π : PMF (α × β)) (b : β) : ℝ≥0∞ := π.map Prod.snd b

/-- The unnormalised finite gluing weight.  The zero branch is the canonical harmless value at a
zero-mass middle atom. -/
private def finiteGluingWeight (π : PMF (α × β)) (σ : PMF (β × γ))
    (b : β) (a : α) (c : γ) : ℝ≥0∞ :=
  if finiteGluingMiddleMass π b = 0 then 0
  else π (a, b) * σ (b, c) / finiteGluingMiddleMass π b

private theorem middleMass_eq_sum (π : PMF (α × β)) (b : β) :
    (let _ := Fintype.card β; finiteGluingMiddleMass π b = ∑ a, π (a, b)) := by
  classical
  rw [finiteGluingMiddleMass, PMF.map_apply]
  calc
    (∑' a : α × β, if b = a.2 then π a else 0) =
        ∑ a : α, ∑ b' : β, if b = b' then π (a, b') else 0 := by
      rw [tsum_fintype, Fintype.sum_prod_type]
    _ = ∑ a : α, π (a, b) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp

private theorem middleMass_eq_sum_right (σ : PMF (β × γ)) (b : β) :
    (let _ := Fintype.card β; σ.map Prod.fst b = ∑ c, σ (b, c)) := by
  classical
  rw [PMF.map_apply]
  calc
    (∑' a : β × γ, if b = a.1 then σ a else 0) =
        ∑ b' : β, ∑ c : γ, if b = b' then σ (b', c) else 0 := by
      rw [tsum_fintype, Fintype.sum_prod_type]
    _ = ∑ c : γ, σ (b, c) := by
      simp

private theorem middleMass_eq_zero_iff (π : PMF (α × β)) (b : β) :
  (let _ := Fintype.card α; let _ := Fintype.card β;
    finiteGluingMiddleMass π b = 0 ↔ ∀ a, π (a, b) = 0) := by
  classical
  rw [middleMass_eq_sum]
  simp

private theorem finiteGluingWeight_sum (π : PMF (α × β)) (σ : PMF (β × γ))
    (h : π.map Prod.snd = σ.map Prod.fst) :
    ∑ p : α × β × γ, finiteGluingWeight π σ p.2.1 p.1 p.2.2 = 1 := by
  classical
  have hmid : ∀ b, finiteGluingMiddleMass π b = σ.map Prod.fst b := by
    intro b
    simpa only [finiteGluingMiddleMass] using congrArg (fun q : PMF β => q b) h
  have hslice : ∀ b, ∑ a, ∑ c,
      finiteGluingWeight π σ b a c = finiteGluingMiddleMass π b := by
    intro b
    by_cases hb : finiteGluingMiddleMass π b = 0
    · have hb' : finiteGluingMiddleMass π b = 0 ↔ ∀ a, π (a, b) = 0 := by
        simpa using middleMass_eq_zero_iff π b
      rw [hb'] at hb
      have hb' : finiteGluingMiddleMass π b = 0 := by
        rw [middleMass_eq_sum]
        simp [hb]
      rw [hb']
      simp [finiteGluingWeight, hb']
    · simp only [finiteGluingWeight, hb, ↓reduceIte]
      calc
        ∑ a, ∑ c, π (a, b) * σ (b, c) / finiteGluingMiddleMass π b =
            ∑ a, (π (a, b) * ∑ c, σ (b, c)) /
              finiteGluingMiddleMass π b := by
                apply Finset.sum_congr rfl
                intro a ha
                simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
        _ = ((∑ a, π (a, b)) * (∑ c, σ (b, c))) /
              finiteGluingMiddleMass π b := by
                  simp only [div_eq_mul_inv, Finset.sum_mul]
        _ = finiteGluingMiddleMass π b := by
          have hσ : ∑ c, σ (b, c) = finiteGluingMiddleMass π b := by
            rw [← middleMass_eq_sum_right σ b, ← hmid b]
          rw [hσ]
          rw [← middleMass_eq_sum π b]
          apply ENNReal.mul_div_cancel_right hb
          exact (π.map Prod.snd).apply_ne_top b
  calc
    (∑ p : α × β × γ, finiteGluingWeight π σ p.2.1 p.1 p.2.2) =
        ∑ b : β, ∑ a : α, ∑ c : γ, finiteGluingWeight π σ b a c := by
          -- Expand the right-associated product type before swapping the two outer sums.
          simp only [Fintype.sum_prod_type]
          rw [Finset.sum_comm]
    _ = ∑ b : β, finiteGluingMiddleMass π b := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hslice b
    _ = 1 := by
      simp only [finiteGluingMiddleMass]
      simpa only [tsum_fintype] using (π.map Prod.snd).tsum_coe

/-- The finite gluing of two laws with a common middle marginal.  At a zero-mass middle atom the
formula is zero; this is the only branch needed to make the construction total. -/
def finiteGluing (h : π.map Prod.snd = σ.map Prod.fst) : PMF (α × β × γ) :=
  PMF.ofFintype (fun p => finiteGluingWeight π σ p.2.1 p.1 p.2.2) (finiteGluingWeight_sum π σ h)

/-- The pointwise finite gluing formula. -/
@[simp]
theorem finiteGluing_apply (h : π.map Prod.snd = σ.map Prod.fst) (a : α) (b : β) (c : γ) :
    finiteGluing π σ h (a, b, c) =
      if finiteGluingMiddleMass π b = 0 then 0 else
        π (a, b) * σ (b, c) / finiteGluingMiddleMass π b := by
  congr 1

variable {δ : Type*} [instFintypeδ : Fintype δ] [DecidableEq δ]

private theorem finiteGluing_map_apply (h : π.map Prod.snd = σ.map Prod.fst)
    (f : α × β × γ → δ) (x : δ) :
    (let _ := Fintype.card δ; (finiteGluing π σ h).map f x =
      ∑ p with f p = x, finiteGluingWeight π σ p.2.1 p.1 p.2.2) := by
  classical
  rw [finiteGluing, PMF.map_ofFintype]
  simp only [PMF.ofFintype_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hx : f a = x <;> simp [hx]

/-- The `(α, β)` marginal of a finite gluing is its first input law. -/
theorem finiteGluing_map_left (h : π.map Prod.snd = σ.map Prod.fst) :
    (finiteGluing π σ h).map (fun p => (p.1, p.2.1)) = π := by
  classical
  apply PMF.ext
  intro p
  calc
    (finiteGluing π σ h).map (fun p => (p.1, p.2.1)) p =
        ∑ x : α × β × γ with (x.1, x.2.1) = p,
          finiteGluingWeight π σ x.2.1 x.1 x.2.2 :=
      finiteGluing_map_apply π σ h (fun q : α × β × γ => (q.1, q.2.1)) p
    _ = ∑ c, finiteGluingWeight π σ p.2 p.1 c := by
        apply Finset.sum_bij (fun (x : α × β × γ) _ => x.2.2)
        · intro x hx
          simp_all
        · intro a₁ h₁ a₂ h₂ he
          rcases a₁ with ⟨a₁, b₁, c₁⟩
          rcases a₂ with ⟨a₂, b₂, c₂⟩
          simp_all [Prod.ext_iff]
        · intro c hc
          exact ⟨(p.1, p.2, c), by simp, rfl⟩
        · intro x hx
          rcases x with ⟨a, b, c⟩
          simp_all [Prod.ext_iff]
    _ = π p := by
      have hmid : finiteGluingMiddleMass π p.2 = σ.map Prod.fst p.2 := by
        simpa only [finiteGluingMiddleMass] using congrArg (fun q : PMF β => q p.2) h
      by_cases hb : finiteGluingMiddleMass π p.2 = 0
      · have hb' : finiteGluingMiddleMass π p.2 = 0 ↔ ∀ a, π (a, p.2) = 0 := by
          simpa using middleMass_eq_zero_iff π p.2
        rw [hb'] at hb
        simp [finiteGluingWeight, hb p.1]
      · simp only [finiteGluingWeight, hb, ↓reduceIte]
        calc
          (∑ c, π (p.1, p.2) * σ (p.2, c) /
              finiteGluingMiddleMass π p.2) =
              (π (p.1, p.2) * ∑ c, σ (p.2, c)) /
                finiteGluingMiddleMass π p.2 := by
                  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
          _ = π p := by
            rw [← middleMass_eq_sum_right σ p.2, ← hmid]
            apply ENNReal.mul_div_cancel_right hb
            exact (π.map Prod.snd).apply_ne_top p.2

/-- The `(β, γ)` marginal of a finite gluing is its second input law. -/
theorem finiteGluing_map_right (h : π.map Prod.snd = σ.map Prod.fst) :
    (finiteGluing π σ h).map (fun p => (p.2.1, p.2.2)) = σ := by
  classical
  apply PMF.ext
  intro p
  calc
    (finiteGluing π σ h).map (fun p => (p.2.1, p.2.2)) p =
        ∑ x : α × β × γ with (x.2.1, x.2.2) = p,
          finiteGluingWeight π σ x.2.1 x.1 x.2.2 :=
      finiteGluing_map_apply π σ h (fun q : α × β × γ => (q.2.1, q.2.2)) p
    _ = ∑ a, finiteGluingWeight π σ p.1 a p.2 := by
        apply Finset.sum_bij (fun (x : α × β × γ) _ => x.1)
        · intro x hx
          simp_all
        · intro a₁ h₁ a₂ h₂ he
          rcases a₁ with ⟨a₁, b₁, c₁⟩
          rcases a₂ with ⟨a₂, b₂, c₂⟩
          simp_all [Prod.ext_iff]
        · intro a ha
          exact ⟨(a, p.1, p.2), by simp, rfl⟩
        · intro x hx
          simp_all
    _ = σ p := by
      have hmid : finiteGluingMiddleMass π p.1 = σ.map Prod.fst p.1 := by
        simpa only [finiteGluingMiddleMass] using congrArg (fun q : PMF β => q p.1) h
      by_cases hb : finiteGluingMiddleMass π p.1 = 0
      · have hb' : finiteGluingMiddleMass π p.1 = 0 ↔ ∀ a, π (a, p.1) = 0 := by
          simpa using middleMass_eq_zero_iff π p.1
        rw [hb'] at hb
        have hmzero : finiteGluingMiddleMass π p.1 = 0 := by
          rw [middleMass_eq_sum]
          simp [hb]
        have hσzero : ∀ c, σ (p.1, c) = 0 := by
          rw [middleMass_eq_sum_right σ p.1] at hmid
          have hz : ∑ c, σ (p.1, c) = 0 := hmid.symm.trans hmzero
          have hz' : (fun c : γ => σ (p.1, c)) = 0 :=
            (Fintype.sum_eq_zero_iff_of_nonneg
              (fun c : γ => (zero_le : (0 : ℝ≥0∞) ≤ σ (p.1, c)))).mp hz
          exact fun c => congrFun hz' c
        simp [finiteGluingWeight, hb, hσzero p.2]
      · simp only [finiteGluingWeight, hb, ↓reduceIte]
        calc
          (∑ a, π (a, p.1) * σ (p.1, p.2) /
              finiteGluingMiddleMass π p.1) =
              ((∑ a, π (a, p.1)) * σ (p.1, p.2)) /
                finiteGluingMiddleMass π p.1 := by
                  simp only [div_eq_mul_inv, Finset.sum_mul]
          _ = σ p := by
            rw [← middleMass_eq_sum π p.1, mul_comm]
            apply ENNReal.mul_div_cancel_right hb
            exact (π.map Prod.snd).apply_ne_top p.1

/-- The outer `(α, γ)` marginal of a finite gluing is a coupling of the outer marginals. -/
theorem finiteGluing_map_outer (h : π.map Prod.snd = σ.map Prod.fst) :
    ((finiteGluing π σ h).map (fun p => (p.1, p.2.2))).map Prod.fst = π.map Prod.fst ∧
      ((finiteGluing π σ h).map (fun p => (p.1, p.2.2))).map Prod.snd = σ.map Prod.snd := by
  classical
  constructor
  · rw [PMF.map_comp]
    calc
      (finiteGluing π σ h).map (Prod.fst ∘ fun p => (p.1, p.2.2)) =
          (finiteGluing π σ h).map
            (Prod.fst ∘ fun p => (p.1, p.2.1)) := by
              congr 1
      _ = ((finiteGluing π σ h).map (fun p => (p.1, p.2.1))).map Prod.fst := by
        rw [PMF.map_comp]
      _ = π.map Prod.fst := by rw [finiteGluing_map_left]
  · rw [PMF.map_comp]
    calc
      (finiteGluing π σ h).map (Prod.snd ∘ fun p => (p.1, p.2.2)) =
          (finiteGluing π σ h).map
            (Prod.snd ∘ fun p => (p.2.1, p.2.2)) := by
              congr 1
      _ = ((finiteGluing π σ h).map (fun p => (p.2.1, p.2.2))).map Prod.snd := by
        rw [PMF.map_comp]
      _ = σ.map Prod.snd := by rw [finiteGluing_map_right]

end PMF
