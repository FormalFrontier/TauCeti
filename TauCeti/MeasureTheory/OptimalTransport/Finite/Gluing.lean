/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Finite.TransportMatrix

/-!
# Finite coupling gluing

For finite probability spaces, this file gives the elementary gluing formula used by finite
coupling arguments.  If `π` is a law on
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
* `outerGluing` is its outer `(α, γ)` projection.

## Main results

* `finiteGluing_apply` gives the formula;
* `map_prodMap_id_fst_finiteGluing` and `map_snd_finiteGluing` recover the two input laws.
* `map_fst_outerGluing` and `map_snd_outerGluing` identify the outer coupling's marginals.

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

/-- The unnormalised finite gluing weight.  The zero branch is the canonical harmless value at a
zero-mass middle atom. -/
private def finiteGluingWeight (π : PMF (α × β)) (σ : PMF (β × γ))
    (b : β) (a : α) (c : γ) : ℝ≥0∞ :=
  if π.map Prod.snd b = 0 then 0
  else π (a, b) * σ (b, c) / π.map Prod.snd b

omit instFintypeα instFintypeβ instFintypeγ in
private theorem middleMass_eq_zero_iff (π : PMF (α × β)) (b : β) [Finite α] :
    π.map Prod.snd b = 0 ↔ ∀ a, π (a, b) = 0 := by
  classical
  let _ := Fintype.ofFinite α
  rw [TauCeti.PMF.map_snd_apply]
  simp

omit instFintypeα instFintypeβ instFintypeγ in
private theorem map_fst_eq_zero_iff (σ : PMF (β × γ)) (b : β) [Finite γ] :
    σ.map Prod.fst b = 0 ↔ ∀ c, σ (b, c) = 0 := by
  classical
  let _ := Fintype.ofFinite γ
  rw [TauCeti.PMF.map_fst_apply]
  simp

private theorem finiteGluingWeight_sum (π : PMF (α × β)) (σ : PMF (β × γ))
    (h : π.map Prod.snd = σ.map Prod.fst) :
    ∑ p : α × β × γ, finiteGluingWeight π σ p.2.1 p.1 p.2.2 = 1 := by
  classical
  have hmid : ∀ b, π.map Prod.snd b = σ.map Prod.fst b := by
    intro b
    exact congrArg (fun q : PMF β => q b) h
  have hslice : ∀ b, ∑ a, ∑ c,
      finiteGluingWeight π σ b a c = π.map Prod.snd b := by
    intro b
    by_cases hb : π.map Prod.snd b = 0
    · simp [finiteGluingWeight, hb]
    · simp only [finiteGluingWeight, hb, ↓reduceIte]
      calc
        ∑ a, ∑ c, π (a, b) * σ (b, c) / π.map Prod.snd b =
            ∑ a, (π (a, b) * ∑ c, σ (b, c)) /
              π.map Prod.snd b := by
                apply Finset.sum_congr rfl
                intro a ha
                simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
        _ = ((∑ a, π (a, b)) * (∑ c, σ (b, c))) /
              π.map Prod.snd b := by
                  simp only [div_eq_mul_inv, Finset.sum_mul]
        _ = π.map Prod.snd b := by
          have hσ : ∑ c, σ (b, c) = π.map Prod.snd b := by
            rw [← TauCeti.PMF.map_fst_apply σ b, ← hmid b]
          rw [hσ]
          rw [← TauCeti.PMF.map_snd_apply π b]
          apply ENNReal.mul_div_cancel_right hb
          exact (π.map Prod.snd).apply_ne_top b
  calc
    (∑ p : α × β × γ, finiteGluingWeight π σ p.2.1 p.1 p.2.2) =
        ∑ b : β, ∑ a : α, ∑ c : γ, finiteGluingWeight π σ b a c := by
          -- Expand the right-associated product type before swapping the two outer sums.
          simp only [Fintype.sum_prod_type]
          rw [Finset.sum_comm]
    _ = ∑ b : β, π.map Prod.snd b := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hslice b
    _ = 1 := by
      simpa only [tsum_fintype] using (π.map Prod.snd).tsum_coe

/-- The finite gluing of two laws with a common middle marginal.  At a zero-mass middle atom the
formula is explicitly set to zero, making the intended value at such atoms visible. -/
def finiteGluing (h : π.map Prod.snd = σ.map Prod.fst) : PMF (α × β × γ) :=
  PMF.ofFintype (fun p => finiteGluingWeight π σ p.2.1 p.1 p.2.2) (finiteGluingWeight_sum π σ h)

/-- The outer `(α, γ)` projection of a finite gluing. -/
def outerGluing (h : π.map Prod.snd = σ.map Prod.fst) : PMF (α × γ) :=
  (finiteGluing π σ h).map (fun p => (p.1, p.2.2))

/-- The pointwise finite gluing formula. -/
@[simp]
theorem finiteGluing_apply (h : π.map Prod.snd = σ.map Prod.fst) (a : α) (b : β) (c : γ) :
    finiteGluing π σ h (a, b, c) =
      if π.map Prod.snd b = 0 then 0 else
        π (a, b) * σ (b, c) / π.map Prod.snd b := by
  rw [finiteGluing, PMF.ofFintype_apply]
  rfl

variable {δ : Type*} [instFintypeδ : Fintype δ] [DecidableEq δ]

omit instFintypeδ in
private theorem finiteGluing_map_apply (h : π.map Prod.snd = σ.map Prod.fst)
    (f : α × β × γ → δ) (x : δ) [Finite δ] :
    (finiteGluing π σ h).map f x =
      ∑ p with f p = x, finiteGluingWeight π σ p.2.1 p.1 p.2.2 := by
  classical
  let _ := Fintype.ofFinite δ
  rw [finiteGluing, PMF.map_ofFintype]
  simp only [PMF.ofFintype_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hx : f a = x <;> simp [hx]

/-- The pointwise outer gluing formula. -/
@[simp]
theorem outerGluing_apply (h : π.map Prod.snd = σ.map Prod.fst) (a : α) (c : γ) :
    outerGluing π σ h (a, c) =
      ∑ b, if π.map Prod.snd b = 0 then 0 else
        π (a, b) * σ (b, c) / π.map Prod.snd b := by
  classical
  rw [outerGluing, finiteGluing_map_apply π σ h
    (fun p : α × β × γ => (p.1, p.2.2)) (a, c)]
  apply Finset.sum_bij (fun (x : α × β × γ) _ => x.2.1)
  · intro x hx
    simp_all
  · intro x₁ h₁ x₂ h₂ he
    rcases x₁ with ⟨a₁, b₁, c₁⟩
    rcases x₂ with ⟨a₂, b₂, c₂⟩
    simp_all [Prod.ext_iff]
  · intro b hb
    exact ⟨(a, b, c), by simp, rfl⟩
  · intro x hx
    rcases x with ⟨a', b', c'⟩
    have hx' : a' = a ∧ c' = c := by
      simpa [Prod.ext_iff] using hx
    rcases hx' with ⟨rfl, rfl⟩
    rfl

/-- The `(α, β)` marginal of a finite gluing is its first input law. -/
@[simp]
theorem map_prodMap_id_fst_finiteGluing (h : π.map Prod.snd = σ.map Prod.fst) :
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
      have hmid : π.map Prod.snd p.2 = σ.map Prod.fst p.2 := by
        exact congrArg (fun q : PMF β => q p.2) h
      by_cases hb : π.map Prod.snd p.2 = 0
      · have hπzero : ∀ a, π (a, p.2) = 0 :=
          (middleMass_eq_zero_iff π p.2).mp hb
        simp [finiteGluingWeight, hb, hπzero p.1]
      · simp only [finiteGluingWeight, hb, ↓reduceIte]
        calc
          (∑ c, π (p.1, p.2) * σ (p.2, c) /
              π.map Prod.snd p.2) =
                (π (p.1, p.2) * ∑ c, σ (p.2, c)) /
                π.map Prod.snd p.2 := by
                  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
          _ = π p := by
            rw [← TauCeti.PMF.map_fst_apply σ p.2, ← hmid]
            apply ENNReal.mul_div_cancel_right hb
            exact (π.map Prod.snd).apply_ne_top p.2

/-- The `(β, γ)` marginal of a finite gluing is its second input law. -/
@[simp]
theorem map_snd_finiteGluing (h : π.map Prod.snd = σ.map Prod.fst) :
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
      have hmid : π.map Prod.snd p.1 = σ.map Prod.fst p.1 := by
        exact congrArg (fun q : PMF β => q p.1) h
      by_cases hb : π.map Prod.snd p.1 = 0
      · have hσzero : ∀ c, σ (p.1, c) = 0 :=
          (map_fst_eq_zero_iff σ p.1).mp (hmid.symm.trans hb)
        simp [finiteGluingWeight, hb, hσzero p.2]
      · simp only [finiteGluingWeight, hb, ↓reduceIte]
        calc
          (∑ a, π (a, p.1) * σ (p.1, p.2) /
              π.map Prod.snd p.1) =
              ((∑ a, π (a, p.1)) * σ (p.1, p.2)) /
                π.map Prod.snd p.1 := by
                  simp only [div_eq_mul_inv, Finset.sum_mul]
          _ = σ p := by
            rw [← TauCeti.PMF.map_snd_apply π p.1, mul_comm]
            apply ENNReal.mul_div_cancel_right hb
            exact (π.map Prod.snd).apply_ne_top p.1

/-- The first marginal of the outer projection is the first marginal of the first input law. -/
@[simp]
theorem map_fst_outerGluing (h : π.map Prod.snd = σ.map Prod.fst) :
    (outerGluing π σ h).map Prod.fst = π.map Prod.fst := by
  have hfun : (Prod.fst : α × γ → α) ∘ (fun p : α × β × γ => (p.1, p.2.2)) =
      Prod.fst ∘ (fun p : α × β × γ => (p.1, p.2.1)) := by
    funext p
    rfl
  rw [outerGluing, PMF.map_comp]
  rw [hfun, ← PMF.map_comp]
  simpa only [Function.comp_apply] using
    congrArg (fun q : PMF (α × β) => q.map Prod.fst)
      (map_prodMap_id_fst_finiteGluing π σ h)

/-- The second marginal of the outer projection is the second marginal of the second input law. -/
@[simp]
theorem map_snd_outerGluing (h : π.map Prod.snd = σ.map Prod.fst) :
    (outerGluing π σ h).map Prod.snd = σ.map Prod.snd := by
  have hfun : (Prod.snd : α × γ → γ) ∘ (fun p : α × β × γ => (p.1, p.2.2)) =
      Prod.snd ∘ (fun p : α × β × γ => (p.2.1, p.2.2)) := by
    funext p
    rfl
  rw [outerGluing, PMF.map_comp]
  rw [hfun, ← PMF.map_comp]
  simpa only [Function.comp_apply] using
    congrArg (fun q : PMF (β × γ) => q.map Prod.snd)
      (map_snd_finiteGluing π σ h)


end PMF
