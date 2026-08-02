/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic

/-!
# The narrow class group of a totally complex field

For a **totally complex** number field `K` (no real infinite places) the positivity condition is
vacuous: every unit is totally positive (`totallyPositiveUnits_eq_top`), so the forgetful surjection
`Cl⁺(K) → Cl(K)` is also injective. Hence the narrow and ordinary class groups **coincide** — as the
multiquadratic roadmap notes, for imaginary fields narrow = ordinary. (The `t - 1` genus-theory rank
formula concerns the *real* case, where the two can differ.)

## Main results

* `TauCeti.NumberField.NarrowClassGroup.toClassGroup_injective`: for a totally complex field the
  forgetful map `Cl⁺(K) → Cl(K)` is injective.
* `TauCeti.NumberField.NarrowClassGroup.toClassGroupEquiv`: the isomorphism `Cl⁺(K) ≃* Cl(K)`.
-/

public section

open NumberField
open scoped nonZeroDivisors

namespace TauCeti.NumberField.NarrowClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- For a totally complex field the forgetful map `Cl⁺(K) → Cl(K)` is injective: by exactness its
kernel is `mkPrincipal.range`, and every principal class is already trivial because principal ideals
have a (vacuously totally positive) generator. -/
theorem toClassGroup_injective [IsTotallyComplex K] :
    Function.Injective (toClassGroup (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, toClassGroup_ker, Subgroup.eq_bot_iff_forall]
  rintro _ ⟨x, rfl⟩
  rw [mkPrincipal_apply, mk_eq_one_iff, mem_narrowPrincipalSubgroup]
  exact ⟨x, by simp, rfl⟩

/-- For a **totally complex** number field the narrow and ordinary class groups coincide:
`Cl⁺(K) ≃* Cl(K)`, forgetting positivity. -/
noncomputable def toClassGroupEquiv [IsTotallyComplex K] :
    NarrowClassGroup K ≃* ClassGroup (𝓞 K) :=
  MulEquiv.ofBijective (toClassGroup (K := K)) ⟨toClassGroup_injective, toClassGroup_surjective⟩

@[simp] theorem toClassGroupEquiv_apply [IsTotallyComplex K] (z : NarrowClassGroup K) :
    toClassGroupEquiv z = toClassGroup z := by
  simp only [toClassGroupEquiv]
  exact MulEquiv.ofBijective_apply (toClassGroup (K := K)) _ z

end TauCeti.NumberField.NarrowClassGroup
