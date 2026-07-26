/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.GeometryOfNumbers.Doubling

/-!
# A concrete rank-two lattice exercising the geometry-of-numbers engine

The Layer-0 engine in `TauCeti/NumberTheory/GeometryOfNumbers/Doubling.lean` proves its
packing and doubling bounds for an *arbitrary* additive subgroup `Λ ≤ (ι → ℂ)`. This file
is the roadmap's acceptance-criterion worked example for that engine: a concrete rank-two
lattice in the plane `ℂ ≅ ℝ²` (indexed by `ι = Fin 1`, so `Fin 1 → ℂ` is one copy of `ℂ`)
on which both bounds become explicit numbers.

The lattice is the Gaussian lattice `ℤ + ℤ·i`, packaged as
`TauCeti.GeometryOfNumbers.gaussianLattice : AddSubgroup (Fin 1 → ℂ)`. Its only nontrivial
input to the engine is the separation hypothesis: a *nonzero* Gaussian integer has norm at
least `1` (`one_le_norm_of_mem_gaussianLattice_of_ne_zero`), so the packing lemma applies
with separation scale `ρ = 1/2` and produces a finite intersection with the box.

## Main results

* `TauCeti.GeometryOfNumbers.one_le_norm_of_mem_gaussianLattice_of_ne_zero`: a nonzero
  point of the Gaussian lattice has norm at least `1` (the lattice's minimal distance).
* `TauCeti.GeometryOfNumbers.gaussianLattice_inter_box_two_finite`: the lattice points in
  the radius-two box form a finite set (the packing lemma discharges discreteness).
* `TauCeti.GeometryOfNumbers.gaussianLattice_inter_box_two_ncard_le`: at most `256` of
  them, the explicit packing count `(8/ρ)^(2·#ι)` at `ρ = 1/2`, `#ι = 1`.
* `gaussianLattice_ncard_inter_box_two_le_fortyNine_mul_ncard_inter_box_one`:
  the doubling instance `#(Λ ∩ box 2) ≤ 49 · #(Λ ∩ box 1)`, the engine's proved factor
  `49^{#ι} = 49` at `#ι = 1`; `…_le_sixtyFour_…` is the rounder `64`-factor corollary.

These exercise both halves of the engine — `addSubgroup_inter_box_finite_and_ncard_le_of_separated`
and `ncard_inter_box_two_le_pow_mul_ncard_inter_box_one` — on a genuine rank-two lattice,
with no new analytic input beyond the elementary minimal-distance bound.
-/

public section

namespace TauCeti.GeometryOfNumbers

open scoped Complex

/-- The Gaussian lattice `ℤ + ℤ·i`, realised as a rank-two additive subgroup of the plane
`Fin 1 → ℂ` (one copy of `ℂ ≅ ℝ²`): the points whose single coordinate is a Gaussian
integer. -/
def gaussianLattice : AddSubgroup (Fin 1 → ℂ) where
  carrier := {x | ∃ m n : ℤ, x 0 = (m : ℂ) + (n : ℂ) * Complex.I}
  add_mem' := by
    rintro a b ⟨m, n, ha⟩ ⟨m', n', hb⟩
    exact ⟨m + m', n + n', by rw [Pi.add_apply, ha, hb]; push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro a ⟨m, n, ha⟩
    exact ⟨-m, -n, by rw [Pi.neg_apply, ha]; push_cast; ring⟩

/-- Membership in the Gaussian lattice unfolds to the single coordinate being a Gaussian
integer. -/
@[simp]
theorem mem_gaussianLattice {x : Fin 1 → ℂ} :
    x ∈ gaussianLattice ↔ ∃ m n : ℤ, x 0 = (m : ℂ) + (n : ℂ) * Complex.I := Iff.rfl

/-- **Minimal distance of the Gaussian lattice.** A nonzero Gaussian integer has norm at
least `1`, since its squared norm `m² + n²` is a positive integer. This is the separation
input the packing lemma needs. -/
theorem one_le_norm_of_mem_gaussianLattice_of_ne_zero {x : Fin 1 → ℂ}
    (hx : x ∈ gaussianLattice) (hne : x ≠ 0) : 1 ≤ ‖x 0‖ := by
  obtain ⟨m, n, hmn⟩ := hx
  -- A point of `Fin 1 → ℂ` is determined by its coordinate, so `x ≠ 0` forces `x 0 ≠ 0`.
  have hx0 : x 0 ≠ 0 := by
    intro h
    refine hne (funext fun i => ?_)
    rw [Subsingleton.elim i 0, Pi.zero_apply]
    exact h
  -- Hence not both integer parts vanish.
  have hmn0 : m ≠ 0 ∨ n ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (by rw [hmn, h.1, h.2]; simp)
  -- A nonzero integer has square at least one.
  have key : ∀ k : ℤ, k ≠ 0 → 1 ≤ k * k := fun k hk => by
    nlinarith [Int.one_le_abs hk, abs_mul_abs_self k, abs_nonneg k]
  have hz : (1 : ℤ) ≤ m * m + n * n := by
    rcases hmn0 with hm | hn
    · nlinarith [key m hm, mul_self_nonneg n]
    · nlinarith [key n hn, mul_self_nonneg m]
  -- The squared norm is exactly `m² + n²`.
  have hre : (x 0).re = (m : ℝ) := by rw [hmn]; simp
  have him : (x 0).im = (n : ℝ) := by rw [hmn]; simp
  have hsq : 1 ≤ ‖x 0‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    exact_mod_cast hz
  by_contra hlt
  push Not at hlt
  nlinarith [hsq, hlt, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ‖x 0‖) (norm_nonneg (x 0))]

/-- The separation hypothesis the packing lemma consumes: every nonzero lattice point
escapes the box of scale `1/2`. -/
private theorem gaussianLattice_separated :
    ∀ x ∈ gaussianLattice, x ≠ 0 →
      ∃ i, (1 / 2 : ℝ) * (fun _ : Fin 1 => (1 : ℝ)) i < ‖x i‖ :=
  fun x hx hne => ⟨0, by
    have h1 := one_le_norm_of_mem_gaussianLattice_of_ne_zero hx hne
    rw [show (fun _ : Fin 1 => (1 : ℝ)) 0 = 1 by rfl]
    linarith⟩

/-- **Discreteness via packing.** The Gaussian lattice meets the radius-two box in a finite
set: the engine's packing lemma discharges the finiteness hypothesis directly from the
minimal-distance bound. -/
theorem gaussianLattice_inter_box_two_finite :
    ((gaussianLattice : Set (Fin 1 → ℂ)) ∩ box (fun _ => 1) 2).Finite :=
  (addSubgroup_inter_box_finite_and_ncard_le_of_separated (fun _ => 1) (fun _ => one_pos)
    gaussianLattice (ρ := 1 / 2) (by norm_num) (by norm_num) gaussianLattice_separated).1

/-- **Explicit packing count.** At most `256` Gaussian-lattice points lie in the radius-two
box, the engine's bound `(8/ρ)^(2·#ι)` evaluated at `ρ = 1/2` and `#ι = 1` (so `16² = 256`). -/
theorem gaussianLattice_inter_box_two_ncard_le :
    (((gaussianLattice : Set (Fin 1 → ℂ)) ∩ box (fun _ => 1) 2).ncard : ℝ) ≤ 256 := by
  refine (addSubgroup_inter_box_finite_and_ncard_le_of_separated (fun _ => 1) (fun _ => one_pos)
    gaussianLattice (ρ := 1 / 2) (by norm_num) (by norm_num) gaussianLattice_separated).2.trans ?_
  rw [Fintype.card_fin]
  norm_num

/-- **A concrete doubling instance.** Passing from the unit box to the double box multiplies the
Gaussian-lattice point count by at most the engine's proved factor `49^{#ι} = 49` at `#ι = 1`:
`#(Λ ∩ box 2) ≤ 49 · #(Λ ∩ box 1)`. -/
theorem gaussianLattice_ncard_inter_box_two_le_fortyNine_mul_ncard_inter_box_one :
    (((gaussianLattice : Set (Fin 1 → ℂ)) ∩ box (fun _ => 1) 2).ncard : ℝ) ≤
      49 * (((gaussianLattice : Set (Fin 1 → ℂ)) ∩ box (fun _ => 1) 1).ncard : ℝ) := by
  simpa [Fintype.card_fin, pow_one] using
    ncard_inter_box_two_le_pow_mul_ncard_inter_box_one (ι := Fin 1) (fun _ => 1)
      (fun _ => one_pos) gaussianLattice gaussianLattice_inter_box_two_finite

/-- The same doubling instance with the rounder factor `64` — a compatibility corollary of
`gaussianLattice_ncard_inter_box_two_le_fortyNine_mul_ncard_inter_box_one`, weakening `49 ≤ 64`:
`#(Λ ∩ box 2) ≤ 64 · #(Λ ∩ box 1)`. -/
theorem gaussianLattice_ncard_inter_box_two_le_sixtyFour_mul_ncard_inter_box_one :
    (((gaussianLattice : Set (Fin 1 → ℂ)) ∩ box (fun _ => 1) 2).ncard : ℝ) ≤
      64 * (((gaussianLattice : Set (Fin 1 → ℂ)) ∩ box (fun _ => 1) 1).ncard : ℝ) :=
  gaussianLattice_ncard_inter_box_two_le_fortyNine_mul_ncard_inter_box_one.trans
    (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))

end TauCeti.GeometryOfNumbers
