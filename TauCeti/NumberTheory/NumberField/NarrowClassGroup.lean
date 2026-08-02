/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# The narrow class group of a number field

The **narrow class group** `Cl⁺(K)` of a number field `K` is the group of invertible fractional
ideals of `𝓞 K` modulo the principal ones admitting a **totally positive** generator. It refines the
ordinary class group `Cl(K)`, which quotients by *all* principal ideals: forgetting the positivity
condition on generators gives a surjection `Cl⁺(K) → Cl(K)`.

The narrow class group is the object whose `2`-rank the genus-theory `t - 1` formula computes for a
real quadratic field (Layer 3 of the multiquadratic roadmap); for imaginary fields, where every unit
is totally positive (there are no real places), `Cl⁺(K)` and `Cl(K)` coincide.

## Main definitions and results

* `TauCeti.NumberField.narrowPrincipalSubgroup`: the subgroup of principal fractional ideals with a
  totally positive generator.
* `TauCeti.NumberField.narrowClassGroup`: the quotient `Cl⁺(K)`, a `CommGroup`.
* `TauCeti.NumberField.narrowClassGroup.mk`: the class of an invertible fractional ideal.
* `TauCeti.NumberField.narrowClassGroup.toClassGroup`: the surjection `Cl⁺(K) → Cl(K)` forgetting
  positivity, with `toClassGroup_surjective`.
-/

public section

open NumberField FractionalIdeal
open scoped nonZeroDivisors

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The subgroup of `(FractionalIdeal (𝓞 K)⁰ K)ˣ` of **principal fractional ideals with a totally
positive generator**: the image of `totallyPositiveUnits` under `toPrincipalIdeal`. The narrow class
group quotients by this subgroup. -/
noncomputable def narrowPrincipalSubgroup : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Subgroup.map (toPrincipalIdeal (𝓞 K) K) totallyPositiveUnits

/-- The **narrow class group** `Cl⁺(K)`: invertible fractional ideals of `𝓞 K` modulo the principal
ones with a totally positive generator. -/
def narrowClassGroup : Type _ :=
  (FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ narrowPrincipalSubgroup K

noncomputable instance : CommGroup (narrowClassGroup K) :=
  inferInstanceAs (CommGroup ((FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ narrowPrincipalSubgroup K))

noncomputable instance : Inhabited (narrowClassGroup K) := ⟨1⟩

namespace narrowClassGroup

variable {K}

/-- The class of an invertible fractional ideal in the narrow class group. -/
noncomputable def mk : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* narrowClassGroup K :=
  QuotientGroup.mk' (narrowPrincipalSubgroup K)

/-- Principal fractional ideals with a totally positive generator have the same class as the whole
ring: they map to `1` in the ordinary class group. -/
theorem narrowPrincipalSubgroup_le_ker :
    narrowPrincipalSubgroup K ≤ MonoidHom.ker (ClassGroup.mk (R := 𝓞 K) K) := by
  rintro _ ⟨x, -, rfl⟩
  rw [MonoidHom.mem_ker, ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal]
  exact ⟨⟨(x : K), coe_spanSingleton _ _⟩⟩

/-- The **surjection `Cl⁺(K) → Cl(K)`** onto the ordinary class group, forgetting the positivity
condition on generators. -/
noncomputable def toClassGroup : narrowClassGroup K →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift (narrowPrincipalSubgroup K) (ClassGroup.mk (R := 𝓞 K) K)
    narrowPrincipalSubgroup_le_ker

@[simp] theorem toClassGroup_mk (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    toClassGroup (mk I) = ClassGroup.mk K I :=
  QuotientGroup.lift_mk' _ narrowPrincipalSubgroup_le_ker I

theorem toClassGroup_surjective : Function.Surjective (toClassGroup (K := K)) :=
  fun C => ClassGroup.induction (K := K)
    (P := fun C => ∃ D, toClassGroup D = C) (fun I => ⟨mk I, rfl⟩) C

end narrowClassGroup

end TauCeti.NumberField
