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
`0`, but that value has no cell-index meaning; results that interpret it as a valid cell index or
compute a cell volume carry positivity or range hypotheses.

So the fibres are the half-open cells `[i/m, (i+1)/m)` for `i + 1 < m`, together with the closed
top cell `[(m-1)/m, 1] = Set.Ici ((m-1)/m)`.

## Main definitions

* `TauCeti.unitInterval.cellIdx` — the cell index.

## Main results

* `TauCeti.unitInterval.cellIdx_lt` — the index is a valid one: `cellIdx m x < m` when `0 < m`;
* `TauCeti.unitInterval.cellIdx_eq_iff_of_succ_lt` and
  `TauCeti.unitInterval.cellIdx_eq_sub_one_iff` — the fibres below the top cell, and the top
  fibre;
* `TauCeti.unitInterval.measurable_cellIdx` — the index depends measurably on the point;
* `TauCeti.unitInterval.measurableSet_preimage_cellIdx` — every cell is measurable;
* `TauCeti.unitInterval.volume_preimage_cellIdx` — every cell has volume `1/m`;
* `TauCeti.unitInterval.integral_pi_comp_cellIdx_eq_inv_smul_sum` — a function of the cell indices
  of finitely many independent uniform points integrates to the average of its values over
  `V → Fin m`.

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
At `m = 0` the value is `0` and carries no cell-index meaning; results that interpret the value as
a valid cell index or compute cell volume require positivity or range hypotheses. -/
def cellIdx (m : ℕ) (x : I) : ℕ := min ⌊(m : ℝ) * (x : ℝ)⌋₊ (m - 1)

/-- The cell index is a valid index into `Fin m`. -/
theorem cellIdx_lt (hm : 0 < m) (x : I) : cellIdx m x < m :=
  lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm Nat.one_pos)

/-- A cell below the top one has the half-open fibre: `cellIdx m x = i` exactly when
`i / m ≤ x < (i + 1) / m`. -/
@[simp]
theorem cellIdx_eq_iff_of_succ_lt (hi : i + 1 < m) (x : I) :
    cellIdx m x = i ↔ (i : ℝ) / m ≤ (x : ℝ) ∧ (x : ℝ) < ((i : ℝ) + 1) / m := by
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have h0 : (0 : ℝ) ≤ (m : ℝ) * (x : ℝ) := mul_nonneg hmR.le x.2.1
  have hmin : cellIdx m x = i ↔ ⌊(m : ℝ) * (x : ℝ)⌋₊ = i := by
    simp only [cellIdx]
    omega
  rw [hmin, Nat.floor_eq_iff h0, div_le_iff₀ hmR, lt_div_iff₀ hmR]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- The top cell is closed at `1`: `cellIdx m x = m - 1` exactly when
`(m - 1) / m ≤ x`. -/
@[simp]
theorem cellIdx_eq_sub_one_iff (hm : 0 < m) (x : I) :
    cellIdx m x = m - 1 ↔ ((m - 1 : ℕ) : ℝ) / m ≤ (x : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h0 : (0 : ℝ) ≤ (m : ℝ) * (x : ℝ) := mul_nonneg hmR.le x.2.1
  have hmin : cellIdx m x = m - 1 ↔ m - 1 ≤ ⌊(m : ℝ) * (x : ℝ)⌋₊ := by
    simp only [cellIdx]
    omega
  rw [hmin, Nat.le_floor_iff h0, div_le_iff₀ hmR]
  simp only [mul_comm]

/-- The cell index depends measurably on the point. -/
@[fun_prop]
theorem measurable_cellIdx : Measurable (cellIdx m) :=
  (measurable_of_countable fun k => min k (m - 1)).comp
    (Nat.measurable_floor.comp (measurable_const.mul measurable_subtype_coe))

/-- Each cell is measurable. -/
@[measurability]
theorem measurableSet_preimage_cellIdx (m i : ℕ) : MeasurableSet (cellIdx m ⁻¹' {i}) :=
  measurable_cellIdx (measurableSet_singleton i)

/-- Every cell of the `m`-fold equipartition has volume `1/m`: the half-open `[i/m, (i+1)/m)` below
the top cell, and the closed `[(m-1)/m, 1]` at the top. -/
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
        simp only [mem_preimage, mem_singleton_iff, mem_Ico, ← Subtype.coe_le_coe,
          ← Subtype.coe_lt_coe]
        exact cellIdx_eq_iff_of_succ_lt hlt x
      rw [hset, _root_.unitInterval.volume_Ico]
      congr 1
      field_simp
      ring
    · -- the top cell: the fibre is `[(m-1)/m, 1]`
      have hset : cellIdx m ⁻¹' {i} = Ici (⟨(i : ℝ) / m, hα⟩ : I) := by
        ext x
        simp only [mem_preimage, mem_singleton_iff, mem_Ici, ← Subtype.coe_le_coe]
        have hi_top : i = m - 1 := by omega
        simpa [hi_top] using cellIdx_eq_sub_one_iff hm0 x
      rw [hset, _root_.unitInterval.volume_Ici]
      congr 1
      have : (i : ℝ) + 1 = m := by exact_mod_cast heq
      field_simp
      linarith
  rw [hgoal, one_div, ENNReal.ofReal_inv_of_pos hmR, ENNReal.ofReal_natCast]

variable {V E : Type*} [Fintype V] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

open scoped Classical in
/-- **The cells cut the cube into products of fibres, exactly one of which holds a given point.**
Evaluating a function on the cell indices of `x` is the same as summing its indicator contributions
over the products `univ.pi fun v => cellIdx m ⁻¹' {ψ v}` indexed by all `#V`-tuples of cells.

Nothing measure-theoretic is involved: the boxes are just preimages of the cell map, and `E` needs
only the additive structure that `Set.indicator` and the sum require. -/
private theorem pi_comp_cellIdx_eq_sum_indicator {V E : Type*} [Fintype V] [AddCommMonoid E]
    (hm : 0 < m)
    (f : (V → ℕ) → E) (x : V → I) :
    f (fun v => cellIdx m (x v))
      = ∑ ψ : V → Fin m, (univ.pi fun v => cellIdx m ⁻¹' {((ψ v : ℕ))}).indicator
          (fun _ => f fun v => (ψ v : ℕ)) x := by
  set ψ₀ : V → Fin m := fun v => ⟨cellIdx m (x v), cellIdx_lt hm (x v)⟩ with hψ₀
  -- membership in the box of `ψ` pins `ψ` down to `ψ₀`, so the sum is an equality test on the
  -- index and `Finset.sum_ite_eq` collapses it
  have hψ : ∀ ψ : V → Fin m,
      x ∈ (univ.pi fun v => cellIdx m ⁻¹' {((ψ v : ℕ))}) ↔ ψ₀ = ψ := by
    intro ψ
    simp [hψ₀, Set.mem_pi, funext_iff, Fin.ext_iff, eq_comm]
  simp [Set.indicator_apply, hψ, hψ₀]

open scoped Classical in
/-- **Independent uniform points, read through their cells.** The integral of a function of the
cell indices of `#V` independent uniform points on `[0, 1]` is the average of that function over
all `#V`-tuples of cells.

This is the transfer that turns an integral over the continuous carrier `(I, volume)` into a finite
sum, and it is where the equal volume of the cells is consumed. The integrand's argument is
`ℕ`-valued, so no `0 < m` hypothesis is hidden in a `Fin m`-valued cell map; the sum on the right
ranges over `V → Fin m`, which is where the finiteness lives. -/
theorem integral_pi_comp_cellIdx_eq_inv_smul_sum (hm : 0 < m) (f : (V → ℕ) → E) :
    ∫ x : V → I, f (fun v => cellIdx m (x v)) ∂(Measure.pi fun _ : V => (volume : Measure I))
      = ((m : ℝ) ^ Fintype.card V)⁻¹ • ∑ ψ : V → Fin m, f fun v => (ψ v : ℕ) := by
  classical
  have hboxMeas : ∀ ψ : V → Fin m,
      MeasurableSet (univ.pi fun v => cellIdx m ⁻¹' {((ψ v : ℕ))}) := fun ψ =>
    MeasurableSet.univ_pi fun v => measurableSet_preimage_cellIdx m _
  have hboxVol : ∀ ψ : V → Fin m,
      (Measure.pi fun _ : V => (volume : Measure I))
          (univ.pi fun v => cellIdx m ⁻¹' {((ψ v : ℕ))})
        = ((m : ℝ≥0∞)⁻¹) ^ Fintype.card V := by
    intro ψ
    rw [Measure.pi_pi]
    simp [volume_preimage_cellIdx (ψ _).isLt, Finset.prod_const]
  calc ∫ x : V → I, f (fun v => cellIdx m (x v)) ∂(Measure.pi fun _ : V => (volume : Measure I))
      = ∑ ψ : V → Fin m,
          ∫ x : V → I, (univ.pi fun v => cellIdx m ⁻¹' {((ψ v : ℕ))}).indicator
              (fun _ => f fun v => (ψ v : ℕ)) x
            ∂(Measure.pi fun _ : V => (volume : Measure I)) := by
        rw [← integral_finsetSum _ fun ψ _ => (integrable_const _).indicator (hboxMeas ψ)]
        exact integral_congr_ae
          (Filter.Eventually.of_forall (pi_comp_cellIdx_eq_sum_indicator hm f))
    _ = ∑ ψ : V → Fin m, ((m : ℝ)⁻¹) ^ Fintype.card V • f fun v => (ψ v : ℕ) := by
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [integral_indicator_const _ (hboxMeas ψ), measureReal_def, hboxVol ψ]
        simp [ENNReal.toReal_pow]
    _ = ((m : ℝ) ^ Fintype.card V)⁻¹ • ∑ ψ : V → Fin m, f fun v => (ψ v : ℕ) := by
        rw [← Finset.smul_sum, inv_pow]

end unitInterval

end TauCeti
