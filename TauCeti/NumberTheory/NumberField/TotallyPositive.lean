/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Ring.Units
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Totally positive elements of a number field

An element `x` of a number field `K` is **totally positive** when it is strictly positive under
every real embedding `K →+* ℝ` — equivalently, at every real infinite place. This is the archimedean
positivity condition underlying the *narrow* class group of the multiquadratic roadmap (Layer 3):
the narrow class group `Cl⁺(K)` is the quotient of the fractional ideals by the principal ideals
admitting a totally positive generator. It surjects onto the ordinary class group `Cl(K)`
(forgetting the positivity condition), and the `2`-rank of `Cl⁺(K)` is what the genus-theory
`t - 1` formula (with `t` the number of ramified primes) computes for a **real quadratic** field
in the multiquadratic roadmap.

This file introduces the predicate and its multiplicative structure. The totally positive elements
are closed under multiplication and inversion and contain every nonzero square, so the totally
positive units form a subgroup of `Kˣ`. That subgroup is the kernel of the sign (signature) map on
units; the signs *not* realized by units measure the difference between `Cl⁺(K)` and `Cl(K)`.

## Main definitions and results

* `TauCeti.NumberField.IsTotallyPositive`: strict positivity at every real place, with
  `isTotallyPositive_iff` its introduction/elimination form.
* `TauCeti.NumberField.isTotallyPositive_one`, `IsTotallyPositive.mul`, `IsTotallyPositive.inv`,
  `isTotallyPositive_sq`: the multiplicative structure, including that nonzero squares are totally
  positive.
* `TauCeti.NumberField.totallyPositiveUnits`: the subgroup of totally positive units of `Kˣ` (the
  kernel of the unit signature map), with `sq_mem_totallyPositiveUnits`.
* `TauCeti.NumberField.totallyPositiveIntegerUnits`: the corresponding subgroup of the arithmetic
  units `(𝓞 K)ˣ`, the preimage of `totallyPositiveUnits` under `(𝓞 K)ˣ → Kˣ`, with
  `mem_totallyPositiveIntegerUnits` and `sq_mem_totallyPositiveIntegerUnits`.
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

/-- Introduction and elimination form of `IsTotallyPositive`: total positivity is exactly strict
positivity at every real infinite place. -/
@[simp, grind =] theorem isTotallyPositive_iff {x : K} :
    IsTotallyPositive x ↔ ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < embedding_of_isReal hw x :=
  Iff.rfl

/-- The element `1` is totally positive: every real embedding sends it to `1 > 0`. -/
theorem isTotallyPositive_one : IsTotallyPositive (1 : K) :=
  isTotallyPositive_iff.mpr fun _ _ => by rw [map_one]; exact one_pos

/-- Totally positive elements are closed under multiplication: a product of positives is positive at
each real place. -/
theorem IsTotallyPositive.mul {x y : K} (hx : IsTotallyPositive x) (hy : IsTotallyPositive y) :
    IsTotallyPositive (x * y) :=
  isTotallyPositive_iff.mpr fun w hw => by rw [map_mul]; exact mul_pos (hx w hw) (hy w hw)

/-- A totally positive element has a totally positive inverse: real embeddings send inverses to
inverses, and the reciprocal of a positive real is positive. -/
theorem IsTotallyPositive.inv {x : K} (hx : IsTotallyPositive x) : IsTotallyPositive x⁻¹ :=
  isTotallyPositive_iff.mpr fun w hw => by rw [map_inv₀]; exact inv_pos.mpr (hx w hw)

/-- Every nonzero square is totally positive: at each real place its value is the square of a
nonzero real. -/
theorem isTotallyPositive_sq {x : K} (hx : x ≠ 0) : IsTotallyPositive (x ^ 2) :=
  isTotallyPositive_iff.mpr fun w hw => by
    rw [map_pow]; exact sq_pos_iff.mpr ((map_ne_zero _).mpr hx)

/-- The subgroup of **totally positive units** of `Kˣ`: the intersection, over the real infinite
places `w`, of the preimages of the positive units of `ℝ` under the real embedding `w`. It is the
kernel of the sign (signature) map on units, and controls the comparison between the narrow class
group `Cl⁺(K)` and the ordinary class group `Cl(K)`. -/
noncomputable def totallyPositiveUnits : Subgroup Kˣ :=
  ⨅ (w : InfinitePlace K) (hw : w.IsReal),
    (Units.posSubgroup ℝ).comap (Units.map (embedding_of_isReal hw).toMonoidHom)

/-- A unit lies in `totallyPositiveUnits` exactly when its underlying field element is totally
positive. -/
@[simp]
theorem mem_totallyPositiveUnits {u : Kˣ} :
    u ∈ totallyPositiveUnits ↔ IsTotallyPositive (u : K) := by
  simp only [totallyPositiveUnits, Subgroup.mem_iInf, Subgroup.mem_comap,
    Units.mem_posSubgroup, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    isTotallyPositive_iff]

/-- Every square of a unit is a totally positive unit. -/
theorem sq_mem_totallyPositiveUnits (u : Kˣ) : u ^ 2 ∈ totallyPositiveUnits := by
  rw [mem_totallyPositiveUnits, Units.val_pow_eq_pow_val]
  exact isTotallyPositive_sq (Units.ne_zero u)

variable [NumberField K]

/-- The subgroup of **totally positive integer units** of `(𝓞 K)ˣ`: the preimage of
`totallyPositiveUnits` under the inclusion `(𝓞 K)ˣ → Kˣ`, i.e. the integer units whose image in `K`
is totally positive. It is the kernel of the integer-unit signature map; the signatures realized by
units — the quotient of `(𝓞 K)ˣ` by this subgroup — are the archimedean input to the comparison
between the narrow and ordinary class groups. -/
noncomputable def totallyPositiveIntegerUnits : Subgroup (𝓞 K)ˣ :=
  totallyPositiveUnits.comap (Units.map (algebraMap (𝓞 K) K).toMonoidHom)

omit [NumberField K] in
/-- Membership in `totallyPositiveIntegerUnits` is total positivity of the image in `K`. -/
@[simp] theorem mem_totallyPositiveIntegerUnits {u : (𝓞 K)ˣ} :
    u ∈ totallyPositiveIntegerUnits ↔ IsTotallyPositive (algebraMap (𝓞 K) K (u : 𝓞 K)) := by
  simp only [totallyPositiveIntegerUnits, Subgroup.mem_comap, mem_totallyPositiveUnits,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]

omit [NumberField K] in
/-- Every square of an integer unit is a totally positive integer unit. -/
theorem sq_mem_totallyPositiveIntegerUnits (u : (𝓞 K)ˣ) :
    u ^ 2 ∈ totallyPositiveIntegerUnits := by
  rw [totallyPositiveIntegerUnits, Subgroup.mem_comap, map_pow]
  exact sq_mem_totallyPositiveUnits _

instance : (Units.posSubgroup ℝ).FiniteIndex :=
  ⟨by rw [Units.index_posSubgroup]; norm_num⟩

/-- The preimage of the positive units of `ℝ` under any homomorphism `Kˣ →* ℝˣ` has finite index:
it is the kernel of the composite into the two-element group `ℝˣ ⧸ Units.posSubgroup ℝ`. -/
instance instFiniteIndexComapPosSubgroup (f : Kˣ →* ℝˣ) :
    ((Units.posSubgroup ℝ).comap f).FiniteIndex := by
  rw [← QuotientGroup.ker_mk' (Units.posSubgroup ℝ), MonoidHom.comap_ker]
  infer_instance

/-- `totallyPositiveUnits` has **finite index** in `Kˣ`: it is a finite intersection, over the real
infinite places, of the finite-index preimages of the positive units of `ℝ`. -/
theorem finiteIndex_totallyPositiveUnits : (totallyPositiveUnits (K := K)).FiniteIndex := by
  rw [totallyPositiveUnits, iInf_subtype']
  exact Subgroup.finiteIndex_iInf fun _ => inferInstance

end TauCeti.NumberField
