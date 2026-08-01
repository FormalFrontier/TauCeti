/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Totally positive elements of a number field

An element `x` of a number field `K` is **totally positive** when it is strictly positive under
every real embedding `K →+* ℝ` — equivalently, at every real infinite place. This is the
archimedean positivity condition that distinguishes the *narrow* class group from the ordinary one:
the narrow class group of the multiquadratic roadmap (Layer 3) is the quotient of the fractional
ideals by the principal ideals with a totally positive generator, and its `2`-rank is what the
`t - 1` genus-theory formula computes in the real case.

This file introduces the predicate and its multiplicative structure. The totally positive elements
are closed under multiplication and inversion and contain every nonzero square, so the totally
positive units form a subgroup of `Kˣ` containing the squares — the subgroup by which the narrow
class group refines the ordinary one. The statements are made at the level of a field with its
infinite places (`[Field K]`); for a totally complex field the condition is vacuous.

## Main definitions and results

* `TauCeti.NumberField.IsTotallyPositive`: strict positivity at every real place.
* `TauCeti.NumberField.IsTotallyPositive.mul`, `isTotallyPositive_one`, `IsTotallyPositive.inv`,
  `isTotallyPositive_sq`: the multiplicative structure, including that nonzero squares are totally
  positive.
* `TauCeti.NumberField.totallyPositiveUnits`: the subgroup of totally positive units of `Kˣ`, with
  `sq_mem_totallyPositiveUnits` recording that it contains every square.
-/

public section

open NumberField InfinitePlace

namespace TauCeti.NumberField

variable {K : Type*} [Field K]

/-- An element of a number field is **totally positive** when it is strictly positive under every
real embedding `K →+* ℝ` (equivalently, at every real infinite place `w`). For a totally complex
field the condition is vacuous; the content is at the real places. -/
def IsTotallyPositive (x : K) : Prop :=
  ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < embedding_of_isReal hw x

@[simp]
theorem isTotallyPositive_one : IsTotallyPositive (1 : K) := fun _ _ => by
  rw [map_one]; exact one_pos

theorem IsTotallyPositive.mul {x y : K} (hx : IsTotallyPositive x) (hy : IsTotallyPositive y) :
    IsTotallyPositive (x * y) := fun w hw => by
  rw [map_mul]; exact mul_pos (hx w hw) (hy w hw)

/-- A totally positive element has a totally positive inverse: real embeddings send inverses to
inverses, and the reciprocal of a positive real is positive. -/
theorem IsTotallyPositive.inv {x : K} (hx : IsTotallyPositive x) : IsTotallyPositive x⁻¹ :=
  fun w hw => by rw [map_inv₀]; exact inv_pos.mpr (hx w hw)

/-- Every nonzero square is totally positive: at each real place its value is the square of a
nonzero real. -/
theorem isTotallyPositive_sq {x : K} (hx : x ≠ 0) : IsTotallyPositive (x ^ 2) := fun w hw => by
  rw [map_pow]
  exact sq_pos_iff.mpr fun h => hx ((embedding_of_isReal hw).injective (h.trans (map_zero _).symm))

/-- The subgroup of **totally positive units** of `Kˣ`: those units whose underlying element is
totally positive. The narrow class group is the quotient of the class group of ideals by the image
of this subgroup. -/
def totallyPositiveUnits : Subgroup Kˣ where
  carrier := {u | IsTotallyPositive (u : K)}
  one_mem' := by
    change IsTotallyPositive ((1 : Kˣ) : K)
    rw [Units.val_one]; exact isTotallyPositive_one
  mul_mem' {x y} hx hy := by
    change IsTotallyPositive ((x * y : Kˣ) : K)
    rw [Units.val_mul]; exact IsTotallyPositive.mul hx hy
  inv_mem' {x} hx := by
    change IsTotallyPositive ((x⁻¹ : Kˣ) : K)
    rw [Units.val_inv_eq_inv_val]; exact hx.inv

@[simp]
theorem mem_totallyPositiveUnits {u : Kˣ} :
    u ∈ totallyPositiveUnits ↔ IsTotallyPositive (u : K) := Iff.rfl

/-- The subgroup of totally positive units contains every square, so the narrow class group
receives the squares of the ordinary class group. -/
theorem sq_mem_totallyPositiveUnits (u : Kˣ) : u ^ 2 ∈ totallyPositiveUnits := by
  rw [mem_totallyPositiveUnits, Units.val_pow_eq_pow_val]
  exact isTotallyPositive_sq (Units.ne_zero u)

end TauCeti.NumberField
