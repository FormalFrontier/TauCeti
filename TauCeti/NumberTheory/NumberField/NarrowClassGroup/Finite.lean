/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup

/-!
# The narrow class group of a number field is finite

The narrow class group `Cl⁺(K)` is finite. It surjects onto the finite ordinary class group `Cl(K)`
(`NarrowClassGroup.toClassGroup`), and the kernel of that surjection is covered by the classes of
principal ideals, which factor through the finite quotient `Kˣ ⧸ totallyPositiveUnits`
(`finite_quotient_totallyPositiveUnits`).

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
  haveI := finite_quotient_totallyPositiveUnits (K := K)
  haveI : Finite (ClassGroup (𝓞 K)) := Finite.of_fintype _
  refine (MonoidHom.finite_iff_finite_ker_range (toClassGroup (K := K))).mpr ⟨?_, inferInstance⟩
  -- `ker toClassGroup` is covered by the classes of principal ideals, i.e. the range of
  -- `g = mk ∘ toPrincipalIdeal`, which is a quotient of the finite `Kˣ ⧸ totallyPositiveUnits`.
  set g : Kˣ →* NarrowClassGroup K := (mk).comp (toPrincipalIdeal (𝓞 K) K) with hg
  have htp : totallyPositiveUnits (K := K) ≤ g.ker := fun x hx => by
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, mk_eq_one_iff, mem_narrowPrincipalSubgroup]
    exact ⟨x, mem_totallyPositiveUnits.mp hx, rfl⟩
  have hgfin : Finite g.range := by
    have hsurj : Function.Surjective
        (QuotientGroup.map totallyPositiveUnits g.ker (MonoidHom.id Kˣ)
          (by rw [Subgroup.comap_id]; exact htp)) := fun q =>
      QuotientGroup.induction_on q fun y => ⟨QuotientGroup.mk y, by simp⟩
    exact (QuotientGroup.quotientKerEquivRange g).finite_iff.mp (Finite.of_surjective _ hsurj)
  have hle : (toClassGroup (K := K)).ker ≤ g.range := by
    intro z hz
    obtain ⟨I, rfl⟩ := mk_surjective z
    rw [MonoidHom.mem_ker, toClassGroup_mk] at hz
    have hmem : I ∈ (toPrincipalIdeal (𝓞 K) K).range := by
      rw [mem_principal_ideals_iff]
      obtain ⟨a, ha⟩ := (ClassGroup.mk_eq_one_iff.mp hz).principal
      exact ⟨a, FractionalIdeal.coeToSubmodule_injective
        (by simp only [FractionalIdeal.coe_spanSingleton]; exact ha.symm)⟩
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, by rw [hg, MonoidHom.comp_apply, hx]⟩
  exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end TauCeti.NumberField.NarrowClassGroup
