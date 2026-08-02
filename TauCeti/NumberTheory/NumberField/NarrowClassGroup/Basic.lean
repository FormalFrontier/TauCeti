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

This construction adapts Mathlib's `ClassGroup` (`Mathlib.RingTheory.ClassGroup.Basic`): where
`ClassGroup R` is `(FractionalIdeal R⁰ (FractionRing R))ˣ ⧸ (toPrincipalIdeal R _).range`, the
narrow class group quotients the invertible fractional ideals over `K` by the *smaller* subgroup
`narrowPrincipalSubgroup` of principal ideals with a totally positive generator.

The narrow class group is the object whose `2`-rank the genus-theory `t - 1` formula computes for a
real quadratic field (Layer 3 of the multiquadratic roadmap); for imaginary fields, where every unit
is totally positive (there are no real places), `Cl⁺(K)` and `Cl(K)` coincide.

## Main definitions and results

* `TauCeti.NumberField.narrowPrincipalSubgroup`: the subgroup of principal fractional ideals with a
  totally positive generator, with `mem_narrowPrincipalSubgroup`.
* `TauCeti.NumberField.NarrowClassGroup`: the quotient `Cl⁺(K)`, a `CommGroup`.
* `TauCeti.NumberField.NarrowClassGroup.mk`: the class of an invertible fractional ideal, with
  `mk_surjective`, `mk_eq_one_iff`, `mk_eq_mk_iff`, and the eliminator `induction`.
* `TauCeti.NumberField.NarrowClassGroup.lift`: the universal property — a homomorphism trivial on
  `narrowPrincipalSubgroup` descends to `Cl⁺(K)`, with `lift_mk` and `lift_unique`.
* `TauCeti.NumberField.NarrowClassGroup.toClassGroup`: the surjection `Cl⁺(K) → Cl(K)` forgetting
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

variable {K}

/-- A fractional ideal lies in `narrowPrincipalSubgroup` exactly when it is `toPrincipalIdeal` of a
totally positive unit. -/
@[simp] theorem mem_narrowPrincipalSubgroup {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    I ∈ narrowPrincipalSubgroup K ↔
      ∃ x : Kˣ, IsTotallyPositive (x : K) ∧ toPrincipalIdeal (𝓞 K) K x = I := by
  simp only [narrowPrincipalSubgroup, Subgroup.mem_map, mem_totallyPositiveUnits]

variable (K)

/-- The **narrow class group** `Cl⁺(K)`: invertible fractional ideals of `𝓞 K` modulo the principal
ones with a totally positive generator. -/
def NarrowClassGroup : Type _ :=
  (FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ narrowPrincipalSubgroup K

noncomputable instance : CommGroup (NarrowClassGroup K) :=
  inferInstanceAs (CommGroup ((FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ narrowPrincipalSubgroup K))

noncomputable instance : Inhabited (NarrowClassGroup K) := ⟨1⟩

namespace NarrowClassGroup

variable {K}

/-- The class of an invertible fractional ideal in the narrow class group. -/
noncomputable def mk : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* NarrowClassGroup K :=
  QuotientGroup.mk' (narrowPrincipalSubgroup K)

/-- Induction on the narrow class group: to prove a property of every class it suffices to prove it
for the class `mk I` of every invertible fractional ideal. -/
@[elab_as_elim] theorem induction {P : NarrowClassGroup K → Prop}
    (h : ∀ I, P (mk I)) (x : NarrowClassGroup K) : P x :=
  QuotientGroup.induction_on x h

/-- Every narrow ideal class is represented by an invertible fractional ideal. -/
theorem mk_surjective : Function.Surjective (mk : _ → NarrowClassGroup K) :=
  QuotientGroup.mk'_surjective _

/-- A fractional ideal has trivial narrow class exactly when it has a totally positive generator. -/
@[simp] theorem mk_eq_one_iff {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    mk I = 1 ↔ I ∈ narrowPrincipalSubgroup K :=
  QuotientGroup.eq_one_iff I

/-- Two fractional ideals have the same narrow class exactly when they differ by a principal ideal
with a totally positive generator. -/
@[simp] theorem mk_eq_mk_iff {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    mk I = mk J ↔ ∃ z ∈ narrowPrincipalSubgroup K, I * z = J :=
  QuotientGroup.mk'_eq_mk' (narrowPrincipalSubgroup K)

variable {M : Type*} [Monoid M]

/-- **Universal property of the narrow class group.** A homomorphism `φ` out of the invertible
fractional ideals whose kernel contains `narrowPrincipalSubgroup` (i.e. `φ` is trivial on principal
ideals with a totally positive generator) descends to a homomorphism `Cl⁺(K) → M`. -/
noncomputable def lift (φ : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* M)
    (h : narrowPrincipalSubgroup K ≤ MonoidHom.ker φ) : NarrowClassGroup K →* M :=
  QuotientGroup.lift (narrowPrincipalSubgroup K) φ h

/-- The descended homomorphism `lift φ h` agrees with `φ` on the class of each representative. -/
@[simp] theorem lift_mk (φ : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* M)
    (h : narrowPrincipalSubgroup K ≤ MonoidHom.ker φ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    lift φ h (mk I) = φ I :=
  QuotientGroup.lift_mk' _ h I

/-- The lift is the unique homomorphism `Cl⁺(K) → M` factoring `φ` through `mk`. -/
theorem lift_unique (φ : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* M)
    (h : narrowPrincipalSubgroup K ≤ MonoidHom.ker φ) (ψ : NarrowClassGroup K →* M)
    (hψ : ∀ I, ψ (mk I) = φ I) : ψ = lift φ h :=
  MonoidHom.ext fun x => induction (fun I => (hψ I).trans (lift_mk φ h I).symm) x

/-- Principal fractional ideals with a totally positive generator have the same class as the whole
ring: they map to `1` in the ordinary class group. -/
private theorem narrowPrincipalSubgroup_le_ker :
    narrowPrincipalSubgroup K ≤ MonoidHom.ker (ClassGroup.mk (R := 𝓞 K) K) := by
  rintro _ ⟨x, -, rfl⟩
  rw [MonoidHom.mem_ker, ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal]
  exact ⟨⟨(x : K), coe_spanSingleton _ _⟩⟩

/-- The **surjection `Cl⁺(K) → Cl(K)`** onto the ordinary class group, forgetting the positivity
condition on generators. -/
noncomputable def toClassGroup : NarrowClassGroup K →* ClassGroup (𝓞 K) :=
  lift (ClassGroup.mk (R := 𝓞 K) K) narrowPrincipalSubgroup_le_ker

/-- Forgetting positivity sends the narrow class of `I` to its ordinary ideal class. -/
@[simp] theorem toClassGroup_mk (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    toClassGroup (mk I) = ClassGroup.mk K I :=
  lift_mk _ _ I

/-- The forgetful homomorphism `Cl⁺(K) → Cl(K)` onto the ordinary class group is surjective. -/
theorem toClassGroup_surjective : Function.Surjective (toClassGroup (K := K)) :=
  fun C => ClassGroup.induction (K := K)
    (P := fun C => ∃ D, toClassGroup D = C) (fun I => ⟨mk I, toClassGroup_mk I⟩) C

/-- The kernel of `toClassGroup` is the image under `mk` of the kernel of the ordinary class-group
map `ClassGroup.mk`. This is `QuotientGroup.ker_lift` specialised to the defining quotient. -/
theorem toClassGroup_ker_eq_map :
    MonoidHom.ker (toClassGroup (K := K)) =
      Subgroup.map mk (MonoidHom.ker (ClassGroup.mk (R := 𝓞 K) K)) :=
  QuotientGroup.ker_lift (narrowPrincipalSubgroup K) (ClassGroup.mk (R := 𝓞 K) K)
    narrowPrincipalSubgroup_le_ker

end NarrowClassGroup

end TauCeti.NumberField
