/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.ExactSequence

/-!
# The narrow class group of a number field is finite

The narrow class group `Cl⁺(K)` is finite. It surjects onto the finite ordinary class group `Cl(K)`
(`NarrowClassGroup.toClassGroup`), and by exactness (`toClassGroup_ker`) the kernel of that
surjection is the image of the principal-class map `mkPrincipal`, which factors through
`Kˣ ⧸ totallyPositiveUnits` — finite because `totallyPositiveUnits` has finite index
(`finiteIndex_totallyPositiveUnits`).

## Main results

* `TauCeti.NumberField.NarrowClassGroup.instFinite`: `Cl⁺(K)` is finite.
-/

public section

open NumberField
open scoped nonZeroDivisors

namespace TauCeti.NumberField.NarrowClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- The narrow class group is **finite**. -/
instance instFinite : Finite (NarrowClassGroup K) := by
  haveI : Finite (ClassGroup (𝓞 K)) := Finite.of_fintype _
  refine (MonoidHom.finite_iff_finite_ker_range (toClassGroup (K := K))).mpr ⟨?_, inferInstance⟩
  -- By exactness `ker toClassGroup = mkPrincipal.range`, a quotient of `Kˣ ⧸ totallyPositiveUnits`.
  rw [toClassGroup_ker]
  have htp : totallyPositiveUnits (K := K) ≤ (mkPrincipal (K := K)).ker := fun x hx => by
    rw [MonoidHom.mem_ker, mkPrincipal_apply, mk_eq_one_iff, mem_narrowPrincipalSubgroup]
    exact ⟨x, mem_totallyPositiveUnits.mp hx, rfl⟩
  haveI : (mkPrincipal (K := K)).ker.FiniteIndex := Subgroup.finiteIndex_of_le htp
  exact (QuotientGroup.quotientKerEquivRange (mkPrincipal (K := K))).finite_iff.mp inferInstance

end TauCeti.NumberField.NarrowClassGroup
