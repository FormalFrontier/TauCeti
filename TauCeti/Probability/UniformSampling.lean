/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.UniformOn
import Mathlib.Data.Fintype.BigOperators

/-!
# Uniform sampling with and without replacement

This file gives the finite sampling estimate underlying quantitative finite de Finetti theorems.
When the finite function space `ι → κ` is nonempty, a uniform random map `x : ι → κ` has two
coordinates collide with probability at most

`(Fintype.card ι).choose 2 / Fintype.card κ`.

When the function space is empty, Mathlib's `uniformOn` is instead the zero measure, and the same
inequality remains valid under that convention.

When injective maps exist, conditioning the random map to be injective is uniform sampling without
replacement.  The main results compare every event under the uniform measures on all maps and on
injective maps, with the collision bound as error.  These inequalities remain valid when no
injective map exists (when Mathlib's `uniformOn` is the zero measure); in the feasible case they are
the coupling step used to compare a finite exchangeable law with the product of its empirical
measure.

The proof is the classical union bound over the unordered pairs of coordinates.  It uses
Mathlib's `ProbabilityTheory.uniformOn`, `measure_biUnion_finset_le`, and
`Fintype.card_product_filter_lt`; no sampling distribution is redefined here.

## Main results

* `uniformOn_not_injective_le` bounds the probability of a collision;
* `uniformOn_le_univ_add_compl` and `uniformOn_univ_le_add_compl` give the general conditioning
  comparison;
* `uniformOn_injective_le_add` and `uniformOn_univ_le_injective_add` compare arbitrary events
  under sampling without and with replacement;
* `uniformOn_injective_le_add_choose_two_div` and
  `uniformOn_univ_le_injective_add_choose_two_div` give the quantitative forms.

This advances Layer 8, "finite de Finetti bounds", of the Exchangeability roadmap.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private noncomputable def eqAtEquiv (i j : ι) (hij : i ≠ j) :
    {x : ι → κ // x i = x j} ≃ ({a : ι // a ≠ j} → κ) := by
  classical
  exact
    { toFun := fun x a => x.1 a.1
      invFun := fun x =>
        ⟨fun a => if ha : a = j then x ⟨i, hij⟩ else x ⟨a, ha⟩, by simp [hij]⟩
      left_inv := fun x => by
        ext a
        by_cases ha : a = j
        · subst a
          dsimp only
          rw [dite_eq_left rfl]
          exact x.2
        · dsimp only
          rw [dite_eq_right ha]
      right_inv := fun x => by
        funext a
        dsimp only
        rw [dite_eq_right a.2] }

private theorem card_eqAt (i j : ι) (hij : i ≠ j) :
    Set.ncard {x : ι → κ | x i = x j} =
      Fintype.card κ ^ (Fintype.card ι - 1) := by
  classical
  calc
    Set.ncard {x : ι → κ | x i = x j} = Fintype.card {x : ι → κ // x i = x j} :=
      Eq.symm (Set.fintypeCard_eq_ncard {x : ι → κ | x i = x j})
    _ = Fintype.card ({a : ι // a ≠ j} → κ) :=
      Fintype.card_congr (eqAtEquiv i j hij)
    _ = Fintype.card κ ^ (Fintype.card ι - 1) := by
      rw [Fintype.card_fun, Fintype.card_subtype_compl]
      simp

omit [Fintype ι] in
/-- Under uniform sampling with replacement, two distinct coordinates agree with probability
`1 / Fintype.card κ`.

The result is stated for arbitrary finite index and value types.  The only measurable structure
needed is discreteness of finite sets, expressed by `MeasurableSingletonClass`. -/
@[simp]
theorem uniformOn_apply_eq_apply [Finite ι] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] [Nonempty κ]
    (i j : ι) (hij : i ≠ j) :
    uniformOn (Set.univ : Set (ι → κ)) {x | x i = x j} =
      1 / (Fintype.card κ : ℝ≥0∞) := by
  classical
  let finiteIota : Fintype ι := Fintype.ofFinite ι
  let _ := finiteIota
  let hfinite : Set.Finite {x : ι → κ | x i = x j} := Set.toFinite _
  rw [uniformOn_univ, Measure.count_apply_finite _ hfinite,
    ← Set.ncard_eq_toFinset_card _ hfinite, card_eqAt i j hij, Fintype.card_fun]
  have hι : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hκ : (Fintype.card κ : ℝ≥0∞) ≠ 0 := by simp
  have hcard_succ : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
  rw [hcard_succ, pow_succ]
  have hpow_zero : (Fintype.card κ : ℝ≥0∞) ^ (Fintype.card ι - 1) ≠ 0 :=
    pow_ne_zero _ hκ
  have hpow_top : (Fintype.card κ : ℝ≥0∞) ^ (Fintype.card ι - 1) ≠ ∞ := by simp
  simpa [div_eq_mul_inv] using ENNReal.mul_div_mul_left (1 : ℝ≥0∞)
    (Fintype.card κ) hpow_zero hpow_top

private def coordinatePairs (ι : Type*) [Fintype ι] [LinearOrder ι] : Finset (ι × ι) :=
  Finset.univ.filter fun p => p.1 < p.2

private theorem mem_coordinatePairs [LinearOrder ι] (p : ι × ι) :
    p ∈ coordinatePairs ι ↔ p.1 < p.2 := by
  simp [coordinatePairs]

private theorem card_coordinatePairs [LinearOrder ι] :
    (coordinatePairs ι).card = (Fintype.card ι).choose 2 := by
  simpa [coordinatePairs] using Fintype.card_product_filter_lt (α := ι)

omit [Fintype κ] in
private theorem not_injective_set_eq_iUnion [LinearOrder ι] :
    {x : ι → κ | ¬Function.Injective x} =
      ⋃ p ∈ coordinatePairs ι, {x | x p.1 = x p.2} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  constructor
  · intro hx
    rw [Function.not_injective_iff] at hx
    obtain ⟨i, j, hij, hne⟩ := hx
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨(i, j), mem_coordinatePairs _ |>.2 hlt, hij⟩
    · exact ⟨(j, i), mem_coordinatePairs _ |>.2 hgt, hij.symm⟩
  · rintro ⟨⟨i, j⟩, hp, hij⟩ h_inj
    exact (mem_coordinatePairs _ |>.1 hp).ne (h_inj hij)

/-- **Collision bound for uniform sampling.**  When the function space `ι → κ` is nonempty, a
uniform map from `ι` to `κ` fails to be injective with probability at most
`(Fintype.card ι).choose 2 / Fintype.card κ`.  When the function space is empty, `uniformOn` is the
zero measure and the inequality remains valid under that convention.

This is the union bound over the unordered pairs of coordinates.  It remains valid when the
right-hand side exceeds one, avoiding an unnecessary size assumption on the sample. -/
theorem uniformOn_not_injective_le [MeasurableSpace κ] [MeasurableSingletonClass κ] :
    uniformOn (Set.univ : Set (ι → κ)) {x | ¬Function.Injective x} ≤
      (Fintype.card ι).choose 2 / Fintype.card κ := by
  classical
  let _ : LinearOrder ι := (Fintype.equivFin ι).linearOrder
  cases isEmpty_or_nonempty κ with
  | inl hκ =>
      cases isEmpty_or_nonempty ι with
      | inl hι => simp [Function.Injective]
      | inr hι =>
          rw [Set.univ_eq_empty_iff.mpr (inferInstance : IsEmpty (ι → κ)),
            uniformOn_empty_meas]
          exact bot_le
  | inr hκ =>
      rw [not_injective_set_eq_iUnion]
      calc
        uniformOn (Set.univ : Set (ι → κ))
            (⋃ p ∈ coordinatePairs ι, {x | x p.1 = x p.2})
          ≤ ∑ p ∈ coordinatePairs ι,
              uniformOn (Set.univ : Set (ι → κ)) {x | x p.1 = x p.2} :=
            measure_biUnion_finset_le _ _
        _ = ∑ _p ∈ coordinatePairs ι, 1 / (Fintype.card κ : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact uniformOn_apply_eq_apply p.1 p.2 (mem_coordinatePairs p |>.1 hp).ne
        _ = (Fintype.card ι).choose 2 / Fintype.card κ := by
          rw [Finset.sum_const, nsmul_eq_mul, card_coordinatePairs]
          simp [div_eq_mul_inv]

/-- Conditioning a finite uniform sample on an event `E` can increase the probability of an event
`A` by at most the original probability of `Eᶜ`, provided `E` is nonempty.  When `E` is empty,
Mathlib's `uniformOn E` is the zero measure and the inequality remains valid under that convention.

This is the upper half of the elementary coupling bound between a uniform law and its
conditioning. -/
theorem uniformOn_le_univ_add_compl {Ω : Type*} [Finite Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (E A : Set Ω) :
    uniformOn E A ≤ uniformOn Set.univ A + uniformOn Set.univ Eᶜ := by
  cases isEmpty_or_nonempty Ω with
  | inl =>
      have hE : E = ∅ := by ext x; exact isEmptyElim x
      have hA : A = ∅ := by ext x; exact isEmptyElim x
      subst E
      subst A
      simp
  | inr =>
      have hfactor : uniformOn E A * uniformOn Set.univ E =
          uniformOn Set.univ (A ∩ E) := by
        rw [uniformOn_inter' Set.finite_univ, Set.univ_inter]
      calc
        uniformOn E A
          = uniformOn E A * (uniformOn Set.univ E + uniformOn Set.univ Eᶜ) := by
              rw [uniformOn_compl E Set.finite_univ Set.univ_nonempty, mul_one]
        _ = uniformOn Set.univ (A ∩ E) +
            uniformOn E A * uniformOn Set.univ Eᶜ := by rw [mul_add, hfactor]
        _ ≤ uniformOn Set.univ A + uniformOn Set.univ Eᶜ := by
          exact add_le_add (measure_mono Set.inter_subset_left)
            (mul_le_of_le_one_left bot_le prob_le_one)

/-- Conditioning a finite uniform sample on an event `E` can decrease the probability of an event
`A` by at most the original probability of `Eᶜ`, provided `E` is nonempty.  When `E` is empty,
Mathlib's `uniformOn E` is the zero measure and the inequality remains valid under that convention.

This is the lower half of the elementary coupling bound between a uniform law and its
conditioning. -/
theorem uniformOn_univ_le_add_compl {Ω : Type*} [Finite Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (E A : Set Ω) :
    uniformOn Set.univ A ≤ uniformOn E A + uniformOn Set.univ Eᶜ := by
  rw [← uniformOn_add_compl_eq E A Set.finite_univ]
  simp only [Set.univ_inter]
  exact add_le_add (mul_le_of_le_one_right bot_le prob_le_one)
    (mul_le_of_le_one_left bot_le prob_le_one)

omit [Fintype ι] [Fintype κ] in
/-- The uniform measure on injective maps differs from the uniform measure on all maps only on the
collision event: for every event `A`, the former is at most the latter plus the collision measure.

When an injective map `ι → κ` exists, these are the probabilities for uniform sampling without and
with replacement, respectively.  The inequality also holds when the set of injective maps is empty,
in which case its `uniformOn` measure is zero. -/
theorem uniformOn_injective_le_add [Finite ι] [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ]
    (A : Set (ι → κ)) :
    uniformOn {x : ι → κ | Function.Injective x} A ≤
      uniformOn Set.univ A + uniformOn Set.univ {x : ι → κ | ¬Function.Injective x} := by
  simpa only [Set.compl_ofPred] using
    uniformOn_le_univ_add_compl {x : ι → κ | Function.Injective x} A

omit [Fintype ι] [Fintype κ] in
/-- The uniform measure on all maps differs from the uniform measure on injective maps only on the
collision event: for every event `A`, the former is at most the latter plus the collision measure.

When an injective map `ι → κ` exists, these are the probabilities for uniform sampling with and
without replacement, respectively.  The inequality also holds when the set of injective maps is
empty, in which case its `uniformOn` measure is zero. -/
theorem uniformOn_univ_le_injective_add [Finite ι] [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ]
    (A : Set (ι → κ)) :
    uniformOn Set.univ A ≤ uniformOn {x : ι → κ | Function.Injective x} A +
      uniformOn Set.univ {x : ι → κ | ¬Function.Injective x} := by
  simpa only [Set.compl_ofPred] using
    uniformOn_univ_le_add_compl {x : ι → κ | Function.Injective x} A

/-- **Quantitative finite-sampling bound, injective maps to all maps.**  For every event `A`, its
uniform measure among injective maps is at most its uniform measure among all maps plus
`(Fintype.card ι).choose 2 / Fintype.card κ`.

When an injective map `ι → κ` exists, this compares uniform sampling without replacement to uniform
sampling with replacement.  The inequality also holds in the degenerate case. -/
theorem uniformOn_injective_le_add_choose_two_div [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (A : Set (ι → κ)) :
    uniformOn {x : ι → κ | Function.Injective x} A ≤
      uniformOn Set.univ A + (Fintype.card ι).choose 2 / Fintype.card κ :=
  (uniformOn_injective_le_add A).trans <|
    add_le_add le_rfl uniformOn_not_injective_le

/-- **Quantitative finite-sampling bound, all maps to injective maps.**  For every event `A`, its
uniform measure among all maps is at most its uniform measure among injective maps plus
`(Fintype.card ι).choose 2 / Fintype.card κ`.

When an injective map `ι → κ` exists, this compares uniform sampling with replacement to uniform
sampling without replacement.  The inequality also holds in the degenerate case. -/
theorem uniformOn_univ_le_injective_add_choose_two_div [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (A : Set (ι → κ)) :
    uniformOn Set.univ A ≤ uniformOn {x : ι → κ | Function.Injective x} A +
      (Fintype.card ι).choose 2 / Fintype.card κ :=
  (uniformOn_univ_le_injective_add A).trans <|
    add_le_add le_rfl uniformOn_not_injective_le

end Probability

end TauCeti
