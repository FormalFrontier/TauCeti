/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Radial coordinates on the cube

Mathlib's generalized loops `Ω^ N X x` are continuous maps `I^N → X` that are constant on the
cube boundary `Cube.boundary N = {y | ∃ i, y i = 0 ∨ y i = 1}`. Arguments that shrink a
generalized loop into the middle of the cube and fill the resulting collar — the standard way
to move the base point of a higher homotopy group along a path — need a numerical grip on how
far a cube point is from the boundary. This file supplies it, for a finite index type.

The `sup` distance to the centre is the right measure: on `I^N` with `N` finite, the product
metric *is* the `sup` metric, so

* `TauCeti.cubeRadius z = 2 * dist z TauCeti.cubeCenter`

is continuous for free, takes values in `[0, 1]`, vanishes at the centre, and equals `1`
exactly on the boundary (`TauCeti.cubeRadius_eq_one_iff`). Radial rescaling by a factor `s` is
`TauCeti.cubeScale`, defined with `Set.projIcc` so that it is total and jointly continuous, and
it multiplies the radius by `s` as long as the result still fits in the cube
(`TauCeti.cubeRadius_cubeScale`). In particular a point of radius `r > 0` is scaled by `1 / r`
onto the boundary, which is what makes the collar constructions glue continuously.

## Main declarations

* `TauCeti.cubeCenter`, `TauCeti.cubeRadius`: the centre of `I^N` and the `sup` radius around
  it.
* `TauCeti.cubeRadius_le_one` and `TauCeti.cubeRadius_eq_one_iff`: the radius is at most one,
  with equality exactly on `Cube.boundary N`.
* `TauCeti.cubeScale`: radial rescaling of a cube point, and `TauCeti.cubeRadius_cubeScale`: it
  scales the radius.

## References

This supplies the cube geometry behind the base-point-change isomorphisms of higher homotopy
groups requested in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 3, item 9.
-/

public section
noncomputable section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy

variable {N : Type*}

/-! ### The centre of the cube and radial rescaling -/

/-- The centre of the cube `I^N`, all of whose coordinates are `1 / 2`. -/
def cubeCenter : I^N := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩

@[simp]
theorem cubeCenter_apply (i : N) : ((cubeCenter i : I) : ℝ) = 1 / 2 := by
  unfold cubeCenter
  rfl

/-- Radial rescaling of a cube point about the centre by a factor `s`, clamped back into the
cube so that it is total and jointly continuous. It agrees with the honest rescaling whenever
the rescaled point still lies in the cube; see `TauCeti.cubeScale_apply_coe`. -/
def cubeScale (s : ℝ) (z : I^N) : I^N :=
  fun i => Set.projIcc (0 : ℝ) 1 zero_le_one (1 / 2 + ((z i : ℝ) - 1 / 2) * s)

theorem continuous_cubeScale : Continuous fun p : ℝ × (I^N) => cubeScale p.1 p.2 :=
  continuous_pi fun _ => continuous_projIcc.comp' (by fun_prop)

@[simp]
theorem cubeScale_one (z : I^N) : cubeScale 1 z = z := by
  funext i
  apply Subtype.ext
  have h0 := (z i).2.1
  have h1 := (z i).2.2
  simp only [cubeScale]
  rw [Set.coe_projIcc, max_eq_right (by simp; linarith), min_eq_right (by linarith)]
  ring

variable [Fintype N]

/-- The `sup` radius of a cube point around the centre of the cube, normalised so that the
boundary has radius one. -/
def cubeRadius (z : I^N) : ℝ := 2 * dist z (cubeCenter : I^N)

theorem cubeRadius_def (z : I^N) : cubeRadius z = 2 * dist z (cubeCenter : I^N) := by
  unfold cubeRadius
  rfl

theorem continuous_cubeRadius : Continuous (cubeRadius : (I^N) → ℝ) := by
  unfold cubeRadius; fun_prop

theorem cubeRadius_nonneg (z : I^N) : 0 ≤ cubeRadius z := by
  rw [cubeRadius_def]; positivity

omit [Fintype N] in
theorem dist_apply_cubeCenter (z : I^N) (i : N) :
    dist (z i) ((cubeCenter : I^N) i) = |(z i : ℝ) - 1 / 2| := by
  rw [Subtype.dist_eq, Real.dist_eq]; rfl

theorem abs_sub_half_le_cubeRadius (z : I^N) (i : N) :
    |(z i : ℝ) - 1 / 2| ≤ cubeRadius z / 2 := by
  rw [cubeRadius_def, ← dist_apply_cubeCenter]
  have := dist_le_pi_dist z (cubeCenter : I^N) i
  linarith

theorem cubeRadius_le_one (z : I^N) : cubeRadius z ≤ 1 := by
  have h_one : (1 : ℝ) = 2 * (1 / 2) := by norm_num
  rw [cubeRadius_def, h_one]
  gcongr
  rw [dist_pi_le_iff (by norm_num)]
  intro i
  rw [dist_apply_cubeCenter, abs_le]
  have h0 := (z i).2.1
  have h1 := (z i).2.2
  constructor <;> linarith

/-- A cube point has radius one exactly when it lies on the boundary of the cube. -/
theorem cubeRadius_eq_one_iff (z : I^N) : cubeRadius z = 1 ↔ z ∈ Cube.boundary N := by
  constructor
  · intro h
    by_contra hz
    simp only [Cube.boundary, Set.mem_ofPred_eq, not_exists, not_or] at hz
    have hlt : dist z (cubeCenter : I^N) < 1 / 2 := by
      rw [dist_pi_lt_iff (by norm_num)]
      intro i
      rw [dist_apply_cubeCenter, abs_lt]
      have h0 := (z i).2.1
      have h1 := (z i).2.2
      have e0 : (z i : ℝ) ≠ 0 := fun hc => (hz i).1 (Subtype.ext hc)
      have e1 : (z i : ℝ) ≠ 1 := fun hc => (hz i).2 (Subtype.ext hc)
      constructor <;> [rcases h0.lt_or_eq with h | h; rcases h1.lt_or_eq with h | h] <;>
        first
          | linarith
          | exact absurd h.symm e0
          | exact absurd h e1
    rw [cubeRadius_def] at h
    linarith
  · rintro ⟨i, hi⟩
    refine le_antisymm (cubeRadius_le_one z) ?_
    have h_one : (1 : ℝ) = 2 * (1 / 2) := by norm_num
    rw [cubeRadius_def, h_one]
    gcongr
    refine le_trans ?_ (dist_le_pi_dist z (cubeCenter : I^N) i)
    rw [dist_apply_cubeCenter]
    rcases hi with hi | hi <;> rw [hi] <;> norm_num

/-- Radial rescaling is honest, that is, the clamping in `TauCeti.cubeScale` is inactive, as
soon as the rescaled radius still fits inside the cube. -/
theorem cubeScale_apply_coe {s : ℝ} (hs : 0 ≤ s) {z : I^N} (h : s * cubeRadius z ≤ 1) (i : N) :
    ((cubeScale s z i : I) : ℝ) = 1 / 2 + ((z i : ℝ) - 1 / 2) * s := by
  have hb := abs_sub_half_le_cubeRadius z i
  have habs : |((z i : ℝ) - 1 / 2) * s| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hs]
    nlinarith [abs_nonneg ((z i : ℝ) - 1 / 2)]
  rw [abs_le] at habs
  simp only [cubeScale]
  rw [Set.coe_projIcc, max_eq_right (by simp; linarith), min_eq_right (by linarith)]

/-- Rescaling radially by `s` multiplies the radius by `s`, provided the rescaled point still
fits in the cube. -/
theorem cubeRadius_cubeScale {s : ℝ} (hs : 0 ≤ s) {z : I^N} (h : s * cubeRadius z ≤ 1) :
    cubeRadius (cubeScale s z) = s * cubeRadius z := by
  have key : ∀ i : N, |((cubeScale s z i : I) : ℝ) - 1 / 2| = s * |(z i : ℝ) - 1 / 2| := by
    intro i
    have h_sub : (1 : ℝ) / 2 + ((z i : ℝ) - 1 / 2) * s - 1 / 2 =
        ((z i : ℝ) - 1 / 2) * s := by ring
    rw [cubeScale_apply_coe hs h i, h_sub, abs_mul, abs_of_nonneg hs, mul_comm]
  have hr := cubeRadius_nonneg z
  refine le_antisymm ?_ ?_
  · have h_mul : s * cubeRadius z = 2 * (s * cubeRadius z / 2) := by ring
    rw [cubeRadius_def, h_mul]
    gcongr
    rw [dist_pi_le_iff (by positivity)]
    intro i
    rw [dist_apply_cubeCenter, key i]
    have := abs_sub_half_le_cubeRadius z i
    nlinarith
  · rcases eq_or_lt_of_le hs with hs0 | hs0
    · rw [← hs0, zero_mul]; exact cubeRadius_nonneg _
    have h_mul : s * (2 * dist z (cubeCenter : I^N)) =
        2 * (s * dist z (cubeCenter : I^N)) := by ring
    rw [cubeRadius_def, cubeRadius_def, h_mul]
    gcongr 2 * ?_
    rw [← le_div_iff₀' hs0, dist_pi_le_iff (by positivity)]
    intro i
    rw [dist_apply_cubeCenter, le_div_iff₀' hs0, ← key i, ← dist_apply_cubeCenter]
    exact dist_le_pi_dist _ _ i

end TauCeti
