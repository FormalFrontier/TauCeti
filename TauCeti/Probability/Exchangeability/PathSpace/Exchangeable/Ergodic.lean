/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.CountableAction
public import TauCeti.Probability.Exchangeability.PathSpace.HewittSavage

/-!
# Exchangeable laws and ergodicity of the finitely supported permutation action

An exchangeable path law is invariant under the group of finitely supported permutations of the
time index.  This file records the resulting **group action** on path space and identifies
ergodicity of that action with triviality of the exchangeable σ-algebra:

```text
(∀ s, MeasurableSet[exchangeableSigma α] s → ρ s = 0 ∨ ρ s = 1)  ↔  ErgodicSMul TimePerm (ℕ → α) ρ
```

(`exchangeableSigma_trivial_iff_ergodicSMul`).

The two sides are not the same statement.  `exchangeableSigma` collects the events that are
**exactly** fixed by every finitely supported reindexing, while Mathlib's `ErgodicSMul` quantifies
over the **almost** invariant events.  The bridge is the countability of the acting group: an
almost invariant event agrees almost everywhere with an exchangeable one
(`exists_measurableSet_exchangeableSigma_ae_eq`), by the saturation argument of
`TauCeti.MeasureTheory.exists_smul_invariant_ae_eq`.

⚠ The permutation action here is the one on the *time index*, and ergodicity for it is a different
statement from ergodicity of the one-sided shift, which concerns the smaller σ-algebra of
shift-invariant events.  For an i.i.d. product law both hold: `ergodic_shift_infinitePi_const` is
the shift form and `ergodicSMul_infinitePi_const` below is the permutation form.

## Main definitions

* `TimePerm` — the finitary symmetric group of the time index `ℕ`, acting on `ℕ → α` by
  `(g • x) n = x (g⁻¹ n)`.

## Main results

* `exists_measurableSet_exchangeableSigma_ae_eq` — an almost invariant event agrees almost
  everywhere with an `exchangeableSigma`-measurable one.
* `exchangeableSigma_trivial_iff_ergodicSMul` — the zero-one law for `exchangeableSigma` is
  ergodicity of the finitely supported permutation action.
* `ergodicSMul_infinitePi_const` — Hewitt–Savage in ergodic form: the finitely supported
  permutations act ergodically on an i.i.d. product law.

This discharges the `ErgodicSMul` interface, item (1) ⇔ (2) of the zero-one/ergodic/extreme
interfaces of Layer 6 of the `Exchangeability` roadmap.  No material is adapted from
`cameronfreer/exchangeability`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {α : Type*}

/-- The **finitary symmetric group of the time index**, the group of finitely supported
permutations of `ℕ` acting on one-sided path space by reindexing.

This is a type synonym for `↥(Equiv.Perm.finitary ℕ)`.  The synonym is deliberate: reindexing is
an action on the *domain* of a path `x : ℕ → α`, whereas `Pi.instSMul` would make a subgroup of
`Equiv.Perm ℕ` act on the *values* of a path whenever the state space `α` carries an action of it
— which it does for `α = ℕ`.  Wrapping the group keeps the two actions from ever competing.

The interface is `equivFinitary`, `toPerm`, `ofPerm` and `TimePerm.ext`; no proof outside this
section unfolds the synonym. -/
-- The group structure, and with it `toPerm_one`, `toPerm_mul` and `toPerm_inv`, is transported
-- along the synonym, so those lemmas hold definitionally and by nothing else; the module system
-- therefore requires this definition and `equivFinitary`, `toPerm`, `ofPerm` below to be
-- `@[expose]`d.
@[expose]
def TimePerm : Type := Equiv.Perm.finitary ℕ

namespace TimePerm

instance instGroup : Group TimePerm := inferInstanceAs (Group (Equiv.Perm.finitary ℕ))

instance instCountable : Countable TimePerm := inferInstanceAs (Countable (Equiv.Perm.finitary ℕ))

/-- The identification of `TimePerm` with the finitary symmetric group `Equiv.Perm.finitary ℕ`
that it abbreviates. -/
@[expose]
def equivFinitary : TimePerm ≃ Equiv.Perm.finitary ℕ := Equiv.refl _

/-- The finitely supported permutation of `ℕ` underlying an element of `TimePerm`. -/
@[expose]
def toPerm (g : TimePerm) : Equiv.Perm ℕ := (equivFinitary g).val

/-- The permutation underlying an element of `TimePerm` is finitely supported. -/
theorem finite_compl_fixedBy_toPerm (g : TimePerm) :
    (MulAction.fixedBy ℕ (toPerm g))ᶜ.Finite :=
  Equiv.Perm.mem_finitary.mp (equivFinitary g).2

/-- An element of `TimePerm` is determined by the permutation underlying it. -/
theorem toPerm_injective : Function.Injective toPerm := fun _ _ h =>
  equivFinitary.injective (Subtype.ext h)

@[ext]
theorem ext {g h : TimePerm} (hgh : toPerm g = toPerm h) : g = h := toPerm_injective hgh

/-- Package a finitely supported permutation of `ℕ` as an element of `TimePerm`. -/
@[expose]
def ofPerm (π : Equiv.Perm ℕ) (hπ : (MulAction.fixedBy ℕ π)ᶜ.Finite) : TimePerm :=
  equivFinitary.symm ⟨π, Equiv.Perm.mem_finitary.mpr hπ⟩

@[simp]
theorem toPerm_ofPerm (π : Equiv.Perm ℕ) (hπ : (MulAction.fixedBy ℕ π)ᶜ.Finite) :
    toPerm (ofPerm π hπ) = π :=
  rfl

@[simp]
theorem toPerm_one : toPerm 1 = 1 := rfl

@[simp]
theorem toPerm_mul (g h : TimePerm) : toPerm (g * h) = toPerm g * toPerm h := rfl

@[simp]
theorem toPerm_inv (g : TimePerm) : toPerm g⁻¹ = (toPerm g)⁻¹ := rfl

end TimePerm

/-- The finitely supported time permutations act on path space by reindexing along the inverse,
`(g • x) n = x (g⁻¹ n)`.  The inverse is what makes reindexing a *left* action. -/
instance instSMulTimePerm : SMul TimePerm (ℕ → α) :=
  ⟨fun g x => permReindex (TimePerm.toPerm g)⁻¹ x⟩

theorem timePerm_smul_def (g : TimePerm) (x : ℕ → α) :
    g • x = permReindex (TimePerm.toPerm g)⁻¹ x :=
  rfl

@[simp]
theorem timePerm_smul_apply (g : TimePerm) (x : ℕ → α) (n : ℕ) :
    (g • x) n = x ((TimePerm.toPerm g)⁻¹ n) :=
  rfl

instance instMulActionTimePerm : MulAction TimePerm (ℕ → α) where
  one_smul x := by ext n; simp
  mul_smul g h x := by ext n; simp [mul_inv_rev]

/-- Reindexing along a permutation is the same map whether it is read as an action of `TimePerm`
or written out with `permReindex`.  This is the form in which the exchangeable σ-algebra, which is
stated with `permReindex`, meets the action. -/
theorem preimage_timePerm_smul (g : TimePerm) (s : Set (ℕ → α)) :
    (fun x : ℕ → α => g • x) ⁻¹' s = permReindex (TimePerm.toPerm g)⁻¹ ⁻¹' s :=
  rfl

variable [MeasurableSpace α]

instance instMeasurableConstSMulTimePerm : MeasurableConstSMul TimePerm (ℕ → α) :=
  ⟨fun g => measurable_reindex (α := α) ⇑(TimePerm.toPerm g)⁻¹⟩

/-- An exchangeable path law is invariant under the finitely supported permutation action. -/
theorem ExchangeableLaw.smulInvariantMeasure {ρ : Measure (ℕ → α)} (hρ : ExchangeableLaw ρ) :
    SMulInvariantMeasure TimePerm (ℕ → α) ρ :=
  ⟨fun g _ hs =>
    (hρ.measurePreserving_permReindex (TimePerm.toPerm g)⁻¹).measure_preimage
      hs.nullMeasurableSet⟩

/-- **An almost invariant path event agrees almost everywhere with an exchangeable event.**

The exchangeable σ-algebra is defined by *exact* invariance under finitely supported reindexings,
while a.e. invariance is what Mathlib's ergodicity predicate supplies.  Because the group of
finitely supported permutations of `ℕ` is countable, the two agree modulo null sets: the
saturation of `s` under the whole group is an exchangeable event almost equal to `s`. -/
theorem exists_measurableSet_exchangeableSigma_ae_eq {ρ : Measure (ℕ → α)} {s : Set (ℕ → α)}
    (hs : MeasurableSet s)
    (hinv : ∀ π : Equiv.Perm ℕ, (MulAction.fixedBy ℕ π)ᶜ.Finite →
      permReindex (α := α) π ⁻¹' s =ᵐ[ρ] s) :
    ∃ t, MeasurableSet[exchangeableSigma α] t ∧ t =ᵐ[ρ] s := by
  obtain ⟨t, ht_meas, ht_inv, hts⟩ :=
    TauCeti.MeasureTheory.exists_smul_invariant_ae_eq (G := TimePerm) (μ := ρ) hs fun g =>
      hinv (TimePerm.toPerm g)⁻¹ <| by
        simpa only [MulAction.fixedBy_inv ℕ] using TimePerm.finite_compl_fixedBy_toPerm g
  refine ⟨t, measurableSet_exchangeableSigma_of_forall_permReindex ht_meas fun π hπ => ?_, hts⟩
  have hg := ht_inv (TimePerm.ofPerm π⁻¹ (by simpa only [MulAction.fixedBy_inv ℕ] using hπ))
  rwa [preimage_timePerm_smul, TimePerm.toPerm_ofPerm, inv_inv] at hg

/-- **Ergodicity of the permutation action makes every exchangeable event trivial.**

This is the easy direction: an `exchangeableSigma`-measurable event is exactly invariant, hence
almost invariant. -/
theorem measure_eq_zero_or_one_of_ergodicSMul {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ]
    [ErgodicSMul TimePerm (ℕ → α) ρ] {s : Set (ℕ → α)}
    (hs : MeasurableSet[exchangeableSigma α] s) :
    ρ s = 0 ∨ ρ s = 1 := by
  have hs_meas : MeasurableSet s := MeasurableSet.ambient_of_exchangeableSigma hs
  have hconst : EventuallyConst s (ae ρ) :=
    MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq TimePerm hs_meas.nullMeasurableSet
      fun g => by
        have hfix := MeasurableSet.preimage_permReindex_eq_of_exchangeableSigma hs
          (π := (TimePerm.toPerm g)⁻¹)
          (by simpa only [MulAction.fixedBy_inv ℕ] using TimePerm.finite_compl_fixedBy_toPerm g)
        rw [preimage_timePerm_smul, hfix]
        exact EventuallyEq.rfl
  rcases eventuallyConst_set'.mp hconst with h | h
  · exact Or.inl (by simpa using measure_congr h)
  · exact Or.inr (by simpa using measure_congr h)

/-- **Triviality of the exchangeable σ-algebra makes the permutation action ergodic.**

This is the substantive direction: the a.e.-invariant events Mathlib's predicate quantifies over
are handled through `exists_measurableSet_exchangeableSigma_ae_eq`, which is where countability of
the acting group is used. -/
theorem ergodicSMul_of_exchangeableSigma_trivial {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ]
    (hρ : ExchangeableLaw ρ)
    (htrivial : ∀ s, MeasurableSet[exchangeableSigma α] s → ρ s = 0 ∨ ρ s = 1) :
    ErgodicSMul TimePerm (ℕ → α) ρ := by
  have := hρ.smulInvariantMeasure
  refine TauCeti.MeasureTheory.ergodicSMul_of_forall_smul_invariant fun t ht ht_inv => ?_
  have ht_exch : MeasurableSet[exchangeableSigma α] t :=
    measurableSet_exchangeableSigma_of_forall_permReindex ht fun π hπ => by
      have hg := ht_inv (TimePerm.ofPerm π⁻¹ (by simpa only [MulAction.fixedBy_inv ℕ] using hπ))
      rwa [preimage_timePerm_smul, TimePerm.toPerm_ofPerm, inv_inv] at hg
  refine eventuallyConst_set'.mpr ?_
  rcases htrivial t ht_exch with h | h
  · exact Or.inl (ae_eq_empty.mpr h)
  · exact Or.inr (ae_eq_univ.mpr ((prob_compl_eq_zero_iff ht).mpr h))

/-- **The zero-one law for `exchangeableSigma` is ergodicity of the finitely supported permutation
action.**

Both sides say that an exchangeable path law admits no nontrivial permutation-invariant event; the
content of the equivalence is that it does not matter whether "invariant" is read exactly, as in
the σ-algebra `exchangeableSigma α`, or almost everywhere, as in Mathlib's `ErgodicSMul`.

⚠ The action is by finitely supported permutations of the time index.  This is *not* one-sided
shift ergodicity: the shift-invariant events form a smaller σ-algebra, so the two statements are
not interchangeable. -/
theorem exchangeableSigma_trivial_iff_ergodicSMul {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ]
    (hρ : ExchangeableLaw ρ) :
    (∀ s, MeasurableSet[exchangeableSigma α] s → ρ s = 0 ∨ ρ s = 1) ↔
      ErgodicSMul TimePerm (ℕ → α) ρ :=
  ⟨ergodicSMul_of_exchangeableSigma_trivial hρ,
    fun _ _ hs => measure_eq_zero_or_one_of_ergodicSMul hs⟩

/-- **Hewitt–Savage in ergodic form.**  The finitely supported permutations of the time index act
ergodically on an i.i.d. product law `P^{⊗ℕ}`.

This is the zero-one law `exchangeableSigma_trivial_of_infinitePi` read through
`exchangeableSigma_trivial_iff_ergodicSMul`.  It is the permutation-action counterpart of the
shift ergodicity recorded by `ergodic_shift_infinitePi_const`. -/
theorem ergodicSMul_infinitePi_const (P : ProbabilityMeasure α) :
    ErgodicSMul TimePerm (ℕ → α) (Measure.infinitePi fun _ : ℕ => (P : Measure α)) :=
  (exchangeableSigma_trivial_iff_ergodicSMul (exchangeableLaw_infinitePi_const P)).mp
    fun _ hs => exchangeableSigma_trivial_of_infinitePi P hs

end Probability

end TauCeti
