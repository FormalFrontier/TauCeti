/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Floor

/-!
# The equipartition of the unit interval into `m` cells

`unitInterval.cellIdx m x` is the index of the cell containing `x` when `[0, 1]` is cut into `m`
pieces of equal length,

`[0, 1/m), [1/m, 2/m), …, [(m-1)/m, 1]`.

The cells are the fibres of `cellIdx m`, and each has volume `1/m`. This is the measure-theoretic
content behind reading a finite object as an object on the canonical carrier `(I, volume)`: a
finite graph as a step graphon, a finite partition as a measurable one, an `m`-point law as a law
on the unit interval.

## The clipping at the top

`cellIdx m x = min ⌊m * x⌋₊ (m - 1)`. The `min` is what closes the top cell: without it `x = 1`
would be a fibre of its own and the fibres would no longer be `m` sets of equal measure. Clipping,
rather than special-casing `x = 1`, also keeps the definition total in `m`: at `m = 0` it returns
`0`, a value no statement below uses, since each carries `i < m`.

The top fibre is genuinely `Set.Ici ((m-1)/m)`, and `volume_preimage_cellIdx` computes it as such;
the argument does not quietly replace it by `Set.Ico ((m-1)/m) 1` and appeal to `{1}` being null.

## Main definitions

* `TauCeti.unitInterval.cellIdx` — the cell index.

## Main results

* `TauCeti.unitInterval.cellIdx_lt` — the index is a valid one: `cellIdx m x < m` when `0 < m`;
* `TauCeti.unitInterval.measurable_cellIdx` — the index depends measurably on the point;
* `TauCeti.unitInterval.measurableSet_preimage_cellIdx` — every cell is measurable;
* `TauCeti.unitInterval.volume_preimage_cellIdx` — every cell has volume `1/m`;
* `TauCeti.unitInterval.integral_pi_comp_cellIdx` — a function of the cell indices of finitely many
  independent uniform points integrates to the average of its values over `V → Fin m`.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md` — the `(I, volume)` carrier on which
  `finiteGraphGraphon` (Layer 1/7) and the Layer-2 step graphons are built. Nothing here mentions
  graphons.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal unitInterval

namespace TauCeti

namespace unitInterval

variable {m i : ℕ}

/-- The index of the cell containing `x` for the partition of `[0, 1]` into the `m` equal cells
`[0, 1/m), [1/m, 2/m), …, [(m-1)/m, 1]`.

The `min` closes the top cell, so that `x = 1` is not a fibre of its own; see the module docstring.
At `m = 0` the value is `0` and carries no meaning — every statement about it assumes `i < m`. -/
def cellIdx (m : ℕ) (x : I) : ℕ := min ⌊(m : ℝ) * (x : ℝ)⌋₊ (m - 1)

/-- The cell index is a valid index into `Fin m`. -/
theorem cellIdx_lt (hm : 0 < m) (x : I) : cellIdx m x < m :=
  lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm Nat.one_pos)

/-- The cell index depends measurably on the point: a floor of a continuous function, followed by
a map out of the countable discrete space `ℕ`. -/
@[fun_prop]
theorem measurable_cellIdx : Measurable (cellIdx m) :=
  (measurable_of_countable fun k => min k (m - 1)).comp
    (Nat.measurable_floor.comp (measurable_const.mul measurable_subtype_coe))

/-- Each cell is measurable. -/
@[measurability]
theorem measurableSet_preimage_cellIdx (m i : ℕ) : MeasurableSet (cellIdx m ⁻¹' {i}) :=
  measurable_cellIdx (measurableSet_singleton i)

/-- Every cell of the `m`-fold equipartition has volume `1/m`.

Two cases, and they are genuinely different sets: below the top the fibre is the half-open interval
`[i/m, (i+1)/m)`, while the top fibre is the closed `[(m-1)/m, 1]`. -/
theorem volume_preimage_cellIdx (hi : i < m) :
    volume (cellIdx m ⁻¹' {i}) = (m : ℝ≥0∞)⁻¹ := by
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le i) hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hα : (i : ℝ) / m ∈ I :=
    ⟨by positivity, (div_le_one hmR).2 (by exact_mod_cast hi.le)⟩
  -- the two cases contribute the same value, computed from different intervals
  have hgoal : volume (cellIdx m ⁻¹' {i}) = ENNReal.ofReal (1 / (m : ℝ)) := by
    rcases (Nat.succ_le_of_lt hi).lt_or_eq with hlt | heq
    · -- below the top: the fibre is `[i/m, (i+1)/m)`
      have hβ : ((i : ℝ) + 1) / m ∈ I :=
        ⟨by positivity, (div_le_one hmR).2 (by exact_mod_cast hlt.le)⟩
      have hset : cellIdx m ⁻¹' {i} = Ico (⟨(i : ℝ) / m, hα⟩ : I) ⟨((i : ℝ) + 1) / m, hβ⟩ := by
        ext x
        have h0 : (0 : ℝ) ≤ (m : ℝ) * (x : ℝ) := mul_nonneg hmR.le x.2.1
        have hcomm : (m : ℝ) * (x : ℝ) = (x : ℝ) * m := mul_comm _ _
        have hmin : cellIdx m x = i ↔ ⌊(m : ℝ) * (x : ℝ)⌋₊ = i := by
          simp only [cellIdx]; omega
        simp only [mem_preimage, mem_singleton_iff, mem_Ico, ← Subtype.coe_le_coe,
          ← Subtype.coe_lt_coe, hmin, Nat.floor_eq_iff h0]
        rw [div_le_iff₀ hmR, lt_div_iff₀ hmR]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      rw [hset, _root_.unitInterval.volume_Ico]
      congr 1
      field_simp
      ring
    · -- the top cell: the fibre is `[(m-1)/m, 1]`
      have hset : cellIdx m ⁻¹' {i} = Ici (⟨(i : ℝ) / m, hα⟩ : I) := by
        ext x
        have h0 : (0 : ℝ) ≤ (m : ℝ) * (x : ℝ) := mul_nonneg hmR.le x.2.1
        have hcomm : (m : ℝ) * (x : ℝ) = (x : ℝ) * m := mul_comm _ _
        have hmin : cellIdx m x = i ↔ i ≤ ⌊(m : ℝ) * (x : ℝ)⌋₊ := by
          simp only [cellIdx]; omega
        simp only [mem_preimage, mem_singleton_iff, mem_Ici, ← Subtype.coe_le_coe, hmin,
          Nat.le_floor_iff h0]
        rw [div_le_iff₀ hmR]
        constructor
        · intro h; linarith
        · intro h; linarith
      rw [hset, _root_.unitInterval.volume_Ici]
      congr 1
      have : (i : ℝ) + 1 = m := by exact_mod_cast heq
      field_simp
      linarith
  rw [hgoal, one_div, ENNReal.ofReal_inv_of_pos hmR, ENNReal.ofReal_natCast]

variable {V : Type*} [Fintype V]

open scoped Classical in
/-- **Independent uniform points, read through their cells.** The integral of a function of the
cell indices of `#V` independent uniform points on `[0, 1]` is the average of that function over
all `#V`-tuples of cells.

This is the transfer that turns an integral over the continuous carrier `(I, volume)` into a finite
sum, and it is where the equal volume of the cells is consumed. The integrand's argument is
`ℕ`-valued, so no `0 < m` hypothesis is hidden in a `Fin m`-valued cell map; the sum on the right
ranges over `V → Fin m`, which is where the finiteness lives. -/
theorem integral_pi_comp_cellIdx (hm : 0 < m) (f : (V → ℕ) → ℝ) :
    ∫ x : V → I, f (fun v => cellIdx m (x v)) ∂(Measure.pi fun _ : V => (volume : Measure I))
      = (∑ ψ : V → Fin m, f fun v => (ψ v : ℕ)) / (m : ℝ) ^ Fintype.card V := by
  classical
  set box : (V → Fin m) → Set (V → I) :=
    fun ψ => univ.pi fun v => cellIdx m ⁻¹' {((ψ v : ℕ))} with hbox
  have hboxMeas : ∀ ψ, MeasurableSet (box ψ) := fun ψ =>
    MeasurableSet.univ_pi fun v => measurableSet_preimage_cellIdx m _
  have hboxVol : ∀ ψ, (Measure.pi fun _ : V => (volume : Measure I)) (box ψ)
      = ((m : ℝ≥0∞)⁻¹) ^ Fintype.card V := by
    intro ψ
    rw [hbox, Measure.pi_pi]
    simp [volume_preimage_cellIdx (ψ _).isLt, Finset.prod_const]
  -- decompose the integrand into the cell boxes, exactly one of which contains a given point
  have key : ∀ x : V → I, f (fun v => cellIdx m (x v))
      = ∑ ψ : V → Fin m, (box ψ).indicator (fun _ => f fun v => (ψ v : ℕ)) x := by
    intro x
    set ψ₀ : V → Fin m := fun v => ⟨cellIdx m (x v), cellIdx_lt hm (x v)⟩ with hψ₀
    rw [Finset.sum_eq_single ψ₀]
    · rw [indicator_of_mem]
      intro v _
      exact rfl
    · intro ψ _ hne
      refine indicator_of_notMem (fun hmem => hne ?_) _
      funext v
      exact Fin.val_injective (hmem v (mem_univ v)).symm
    · intro h
      exact absurd (Finset.mem_univ ψ₀) h
  calc ∫ x : V → I, f (fun v => cellIdx m (x v)) ∂(Measure.pi fun _ : V => (volume : Measure I))
      = ∑ ψ : V → Fin m,
          ∫ x : V → I, (box ψ).indicator (fun _ => f fun v => (ψ v : ℕ)) x
            ∂(Measure.pi fun _ : V => (volume : Measure I)) := by
        rw [← integral_finsetSum _ fun ψ _ => (integrable_const _).indicator (hboxMeas ψ)]
        exact integral_congr_ae (Filter.Eventually.of_forall key)
    _ = ∑ ψ : V → Fin m, ((m : ℝ)⁻¹) ^ Fintype.card V * f fun v => (ψ v : ℕ) := by
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [integral_indicator_const _ (hboxMeas ψ), Measure.real, hboxVol ψ]
        simp [ENNReal.toReal_pow, smul_eq_mul]
    _ = (∑ ψ : V → Fin m, f fun v => (ψ v : ℕ)) / (m : ℝ) ^ Fintype.card V := by
        rw [← Finset.mul_sum, inv_pow, div_eq_inv_mul]

end unitInterval

end TauCeti
