/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Rescaling generators by the base field

Multiplying each generator of an intermediate field by a nonzero scalar from the base field does
not change the field it generates: the base scalars and their inverses are already there. This is
the field-theoretic content of "generators matter only up to their square class" arguments, where
a generator `√(a c²)` is replaced by `√a = c⁻¹ · √(a c²)`.

## Main results

* `TauCeti.IntermediateField.adjoin_range_algebraMap_mul`: for nonzero `u : ι → K`,
  `K(u i · x i : i) = K(x i : i)`.
-/

public section

open IntermediateField

namespace TauCeti.IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Rescaling generators by nonzero base scalars.** If every `u i` is a nonzero element of the
base field `K`, then the family `(u i) · x i` generates the same intermediate field of `L / K` as
the family `x`. -/
theorem adjoin_range_algebraMap_mul {ι : Type*} {u : ι → K} (hu : ∀ i, u i ≠ 0) (x : ι → L) :
    adjoin K (Set.range fun i => algebraMap K L (u i) * x i) = adjoin K (Set.range x) := by
  refine le_antisymm (adjoin_le_iff.mpr ?_) (adjoin_le_iff.mpr ?_)
  · rintro _ ⟨i, rfl⟩
    exact mul_mem (_root_.algebraMap_mem _ _) (subset_adjoin K _ ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    have hx : x i = algebraMap K L (u i)⁻¹ * (algebraMap K L (u i) * x i) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hu i), map_one, one_mul]
    rw [hx]
    exact mul_mem (_root_.algebraMap_mem _ _) (subset_adjoin K _ ⟨i, rfl⟩)

end TauCeti.IntermediateField
