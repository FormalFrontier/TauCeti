/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic

/-!
# The narrow class group of a number field is finite

The narrow class group `Cl⁺(K)` is finite. It surjects onto the finite ordinary class group `Cl(K)`
(`NarrowClassGroup.toClassGroup`), and by exactness (`toClassGroup_ker`) the kernel of that
surjection is the image of the principal-class map `mkPrincipal`, which factors through
`Kˣ ⧸ totallyPositiveUnits` — finite because `totallyPositiveUnits` has finite index
(`finiteIndex_totallyPositiveUnits`).

## Main results

* `TauCeti.NumberField.NarrowClassGroup.instFinite`: `Cl⁺(K)` is finite.
* `TauCeti.NumberField.NarrowClassGroup.exists_card_eq_card_classGroup_mul_two_pow`: the narrow
  class number is the ordinary class number times a power of `2`.
-/

public section

open NumberField
open scoped nonZeroDivisors

namespace TauCeti.NumberField.NarrowClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- The narrow class group is **finite**. -/
instance instFinite : Finite (NarrowClassGroup K) := by
  have : Finite (ClassGroup (𝓞 K)) := Finite.of_fintype _
  refine (MonoidHom.finite_iff_finite_ker_range (toClassGroup (K := K))).mpr ⟨?_, inferInstance⟩
  -- By exactness `ker toClassGroup = mkPrincipal.range`, a quotient of `Kˣ ⧸ totallyPositiveUnits`.
  rw [toClassGroup_ker]
  have htp : totallyPositiveUnits (K := K) ≤ (mkPrincipal (K := K)).ker := fun x hx => by
    rw [MonoidHom.mem_ker, mkPrincipal_apply, mk_eq_one_iff, mem_narrowPrincipalSubgroup]
    exact ⟨x, mem_totallyPositiveUnits.mp hx, rfl⟩
  have : (mkPrincipal (K := K)).ker.FiniteIndex := Subgroup.finiteIndex_of_le htp
  exact (QuotientGroup.quotientKerEquivRange (mkPrincipal (K := K))).finite_iff.mp inferInstance

/-- The kernel of the forgetful map `Cl⁺(K) → Cl(K)` is a `2`-group: it is `2`-torsion
(`sq_eq_one_of_mem_ker_toClassGroup`). -/
theorem isPGroup_two_ker_toClassGroup :
    IsPGroup 2 (MonoidHom.ker (toClassGroup (K := K))) := fun g =>
  ⟨1, Subtype.ext <| by
    rw [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact sq_eq_one_of_mem_ker_toClassGroup g.2⟩

/-- The narrow class number is the ordinary class number times the order of the kernel of the
forgetful map `Cl⁺(K) → Cl(K)`. -/
theorem card_eq_card_classGroup_mul_card_ker :
    Nat.card (NarrowClassGroup K) =
      Nat.card (ClassGroup (𝓞 K)) * Nat.card (MonoidHom.ker (toClassGroup (K := K))) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker (toClassGroup (K := K))),
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (toClassGroup (K := K))
      toClassGroup_surjective).toEquiv]

/-- **The narrow class number is the ordinary class number times a power of `2`.** The extra factor
is the order of the elementary abelian `2`-group `ker(Cl⁺(K) → Cl(K))`. -/
theorem exists_card_eq_card_classGroup_mul_two_pow :
    ∃ k, Nat.card (NarrowClassGroup K) = Nat.card (ClassGroup (𝓞 K)) * 2 ^ k := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_two_ker_toClassGroup (K := K))
  exact ⟨k, by rw [card_eq_card_classGroup_mul_card_ker, hk]⟩

end TauCeti.NumberField.NarrowClassGroup
