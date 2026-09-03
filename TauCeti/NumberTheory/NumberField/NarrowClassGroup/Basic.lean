/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.TotallyPositive
public import TauCeti.RingTheory.ClassGroup.Basic

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

* `NumberField.narrowPrincipalSubgroup`: the subgroup of principal fractional ideals with a
  totally positive generator, with `mem_narrowPrincipalSubgroup`.
* `NumberField.NarrowClassGroup`: the quotient `Cl⁺(K)`, a `CommGroup`.
* `NumberField.NarrowClassGroup.mk`: the class of an invertible fractional ideal, with
  `mk_surjective`, `mk_eq_one_iff`, `mk_eq_mk_iff`, and the eliminator `induction`.
* `NumberField.NarrowClassGroup.lift`: the universal property — a homomorphism trivial on
  `narrowPrincipalSubgroup` descends to `Cl⁺(K)`, with `lift_mk` and `lift_unique`.
* `NumberField.NarrowClassGroup.toClassGroup`: the surjection `Cl⁺(K) → Cl(K)` forgetting
  positivity, with `toClassGroup_surjective`.
* `NumberField.NarrowClassGroup.mkPrincipal` and `toClassGroup_ker`: the principal-class map
  `Kˣ → Cl⁺(K)` and exactness at `Cl⁺(K)` of `Kˣ → Cl⁺(K) → Cl(K) → 1`
  (`ker toClassGroup = mkPrincipal.range`).
* `NumberField.NarrowClassGroup.mkPrincipal_sq` and `sq_eq_one_of_mem_ker_toClassGroup`:
  `mkPrincipal` is `2`-torsion, so `ker(Cl⁺ → Cl)` is an elementary abelian `2`-group.
* `NumberField.NarrowClassGroup.mk0`: the narrow class of a nonzero integral ideal, with
  `toClassGroup_mk0`, `mk0_surjective`, the triviality criterion `mk0_eq_one_iff`,
  the `2`-torsion of principal classes
  `mk0_sq_eq_one_of_eq_span_singleton`, `mkPrincipal_coe_eq_mk0`, and the comparison
  `mk0_eq_mk0_iff`.
-/

public section

open NumberField FractionalIdeal
open scoped nonZeroDivisors

namespace NumberField

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
  exact ClassGroup.mk_toPrincipalIdeal x

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

/-- The narrow ideal class of the principal fractional ideal `(x)` generated by a unit `x : Kˣ`. -/
noncomputable def mkPrincipal : Kˣ →* NarrowClassGroup K :=
  mk.comp (toPrincipalIdeal (𝓞 K) K)

theorem mkPrincipal_apply (x : Kˣ) :
    mkPrincipal x = mk (toPrincipalIdeal (𝓞 K) K x) := by
  simp only [mkPrincipal, MonoidHom.comp_apply]

/-- The composition `Cl⁺(K) → Cl(K)` after `mkPrincipal` is trivial: forgetting positivity kills the
class of a principal ideal. This is the "composition is one" half of exactness at `Cl⁺(K)`. -/
@[simp] theorem toClassGroup_comp_mkPrincipal :
    (toClassGroup (K := K)).comp mkPrincipal = 1 := by
  ext x
  rw [MonoidHom.comp_apply, MonoidHom.one_apply, mkPrincipal_apply, toClassGroup_mk]
  exact ClassGroup.mk_toPrincipalIdeal x

@[simp] theorem toClassGroup_mkPrincipal (x : Kˣ) : toClassGroup (mkPrincipal (K := K) x) = 1 := by
  rw [← MonoidHom.comp_apply, toClassGroup_comp_mkPrincipal, MonoidHom.one_apply]

/-- **Exactness at `Cl⁺(K)`** of `Kˣ → Cl⁺(K) → Cl(K) → 1`: the kernel of the forgetful map to the
ordinary class group is exactly the image of the principal-class map. Together with
`toClassGroup_surjective` this expresses exactness of the whole sequence. -/
theorem toClassGroup_ker :
    MonoidHom.ker (toClassGroup (K := K)) = (mkPrincipal (K := K)).range := by
  -- `QuotientGroup.ker_lift` for the defining quotient: the kernel is the image under `mk` of the
  -- ordinary class-group kernel, which is exactly the principal ideals `toPrincipalIdeal.range`.
  have hker : MonoidHom.ker (toClassGroup (K := K)) =
      Subgroup.map mk (MonoidHom.ker (ClassGroup.mk (R := 𝓞 K) K)) :=
    QuotientGroup.ker_lift (narrowPrincipalSubgroup K) (ClassGroup.mk (R := 𝓞 K) K)
      narrowPrincipalSubgroup_le_ker
  have hcg : MonoidHom.ker (ClassGroup.mk (R := 𝓞 K) K) = (toPrincipalIdeal (𝓞 K) K).range := by
    ext I
    rw [MonoidHom.mem_ker, ClassGroup.mk_eq_one_iff, mem_principal_ideals_iff, isPrincipal_iff]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
  have hdef : mkPrincipal (K := K) = mk.comp (toPrincipalIdeal (𝓞 K) K) :=
    MonoidHom.ext fun x => by rw [mkPrincipal_apply, MonoidHom.comp_apply]
  rw [hker, hcg, hdef, MonoidHom.range_comp]

/-- The principal-class map is `2`-torsion: `mkPrincipal x ^ 2 = 1`, since `x ^ 2` is totally
positive and so `(x ^ 2)` is a principal ideal with a totally positive generator. -/
@[simp] theorem mkPrincipal_sq (x : Kˣ) : mkPrincipal x ^ 2 = 1 := by
  rw [← map_pow, mkPrincipal_apply, mk_eq_one_iff, mem_narrowPrincipalSubgroup]
  exact ⟨x ^ 2, mem_totallyPositiveUnits.mp (sq_mem_totallyPositiveUnits x), rfl⟩

/-- The kernel of the forgetful map `Cl⁺(K) → Cl(K)` is killed by `2`: by exactness it is the image
of `mkPrincipal`, which is `2`-torsion. So the narrow-vs-ordinary defect is an elementary abelian
`2`-group. -/
@[grind →] theorem sq_eq_one_of_mem_ker_toClassGroup {C : NarrowClassGroup K}
    (hC : C ∈ MonoidHom.ker (toClassGroup (K := K))) : C ^ 2 = 1 := by
  rw [toClassGroup_ker] at hC
  obtain ⟨x, rfl⟩ := hC
  exact mkPrincipal_sq x

/-! ### Classes of integral ideals -/

/-- The **narrow class of a nonzero integral ideal** of `𝓞 K`, the narrow counterpart of
`ClassGroup.mk0`. -/
noncomputable def mk0 : (Ideal (𝓞 K))⁰ →* NarrowClassGroup K :=
  mk.comp (FractionalIdeal.mk0 K)

@[simp] theorem mk_mk0 (I : (Ideal (𝓞 K))⁰) : mk (FractionalIdeal.mk0 K I) = mk0 I := (rfl)

/-- Forgetting positivity sends the narrow class of an integral ideal to its ordinary class. -/
@[simp] theorem toClassGroup_mk0 (I : (Ideal (𝓞 K))⁰) :
    toClassGroup (mk0 I) = ClassGroup.mk0 I := by
  rw [← mk_mk0, toClassGroup_mk, ClassGroup.mk_mk0]

/-- An integral ideal has trivial narrow class exactly when it has a nonzero totally positive
generator. -/
@[simp] theorem mk0_eq_one_iff {I : (Ideal (RingOfIntegers K))⁰} :
    mk0 I = 1 ↔ ∃ a : RingOfIntegers K, a ≠ 0 ∧ IsTotallyPositive (a : K) ∧
      (I : Ideal (RingOfIntegers K)) = Ideal.span {a} := by
  constructor
  · intro h
    rw [← mk_mk0, mk_eq_one_iff, mem_narrowPrincipalSubgroup] at h
    obtain ⟨x, hxpos, hx⟩ := h
    have hxmem : (x : K) ∈
        ((I : Ideal (RingOfIntegers K)) : FractionalIdeal (RingOfIntegers K)⁰ K) := by
      rw [← FractionalIdeal.coe_mk0, ← hx, coe_toPrincipalIdeal]
      exact mem_spanSingleton_self (RingOfIntegers K)⁰ (x : K)
    obtain ⟨a, _haI, ha⟩ :=
      (FractionalIdeal.mem_coeIdeal (RingOfIntegers K)⁰).mp hxmem
    have ha' : (a : K) = (x : K) := ha
    have ha0 : a ≠ 0 := fun ha0 ↦ x.ne_zero (by rw [← ha, ha0, map_zero])
    refine ⟨a, ha0, ?_, ?_⟩
    · rw [ha']
      exact hxpos
    · have hcoe :
          ((I : Ideal (RingOfIntegers K)) : FractionalIdeal (RingOfIntegers K)⁰ K) =
            ((Ideal.span {a} : Ideal (RingOfIntegers K)) :
              FractionalIdeal (RingOfIntegers K)⁰ K) := by
        rw [FractionalIdeal.coeIdeal_span_singleton, ha]
        have hxval := congrArg Units.val hx
        simpa only [coe_toPrincipalIdeal, FractionalIdeal.coe_mk0] using hxval.symm
      exact FractionalIdeal.coeIdeal_injective hcoe
  · rintro ⟨a, ha, hpos, hI⟩
    rw [← mk_mk0, mk_eq_one_iff, mem_narrowPrincipalSubgroup]
    refine ⟨Units.mk0 (a : K) (RingOfIntegers.coe_ne_zero_iff.mpr ha), hpos, Units.ext ?_⟩
    rw [coe_toPrincipalIdeal, FractionalIdeal.coe_mk0, hI,
      FractionalIdeal.coeIdeal_span_singleton]
    rfl

/-- **A principal ideal with a totally positive generator has trivial narrow class.** -/
theorem mk0_eq_one_of_isTotallyPositive {a : 𝓞 K} (ha : a ≠ 0)
    (hpos : IsTotallyPositive (a : K)) {I : (Ideal (𝓞 K))⁰}
    (hI : (I : Ideal (𝓞 K)) = Ideal.span {a}) : mk0 I = 1 := by
  exact mk0_eq_one_iff.mpr ⟨a, ha, hpos, hI⟩

/-- **The narrow class of a principal ideal is `2`-torsion**, since the square of any generator is
totally positive. -/
theorem mk0_sq_eq_one_of_eq_span_singleton {a : 𝓞 K} (ha : a ≠ 0) {I : (Ideal (𝓞 K))⁰}
    (hI : (I : Ideal (𝓞 K)) = Ideal.span {a}) : mk0 I ^ 2 = 1 := by
  rw [← map_pow]
  refine mk0_eq_one_of_isTotallyPositive (a := a ^ 2) (pow_ne_zero 2 ha) ?_ ?_
  · push_cast
    exact isTotallyPositive_sq (RingOfIntegers.coe_ne_zero_iff.mpr ha)
  · rw [SubmonoidClass.coe_pow, hI, ← Ideal.span_singleton_pow]

/-- The narrow class of the principal ideal generated by a nonzero algebraic integer is the
principal narrow class of that integer. -/
theorem mkPrincipal_coe_eq_mk0 {a : 𝓞 K} (ha : a ≠ 0) {I : (Ideal (𝓞 K))⁰}
    (hI : (I : Ideal (𝓞 K)) = Ideal.span {a}) :
    mkPrincipal (Units.mk0 (a : K) (RingOfIntegers.coe_ne_zero_iff.mpr ha)) = mk0 I := by
  rw [mkPrincipal_apply, ← mk_mk0]
  refine congrArg mk (Units.ext ?_)
  rw [coe_toPrincipalIdeal, FractionalIdeal.coe_mk0, hI, coeIdeal_span_singleton]
  rfl

/-- **Every narrow ideal class is the class of an integral ideal.** An ordinary integral
representative differs from the given class by a principal class, and a principal class is the class
of an integral ideal because it is its own inverse. -/
theorem mk0_surjective : Function.Surjective (mk0 : (Ideal (𝓞 K))⁰ → NarrowClassGroup K) := by
  intro C
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective (toClassGroup C)
  have hker : C * (mk0 J)⁻¹ ∈ MonoidHom.ker (toClassGroup (K := K)) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, toClassGroup_mk0, hJ, mul_inv_cancel]
  rw [toClassGroup_ker] at hker
  obtain ⟨u, hu⟩ := hker
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (u : K)
  replace hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha : a ≠ 0 := fun h => by
    rw [h, map_zero, zero_div] at hab
    exact u.ne_zero hab.symm
  have hspa : Ideal.span {a} ∈ (Ideal (𝓞 K))⁰ :=
    Ideal.span_singleton_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
  have hspb : Ideal.span {b} ∈ (Ideal (𝓞 K))⁰ :=
    Ideal.span_singleton_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hb)
  -- Write the unit `u = a / b` as a ratio, so its principal class splits into two integral ones.
  have hsplit : u = Units.mk0 (a : K) (RingOfIntegers.coe_ne_zero_iff.mpr ha) *
      (Units.mk0 (b : K) (RingOfIntegers.coe_ne_zero_iff.mpr hb))⁻¹ := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, ← div_eq_mul_inv]
    exact hab.symm
  have hb2 : (mk0 ⟨Ideal.span {b}, hspb⟩)⁻¹ = mk0 ⟨Ideal.span {b}, hspb⟩ := by
    rw [inv_eq_iff_mul_eq_one, ← sq]
    exact mk0_sq_eq_one_of_eq_span_singleton hb rfl
  have hprin : mk0 ⟨Ideal.span {a}, hspa⟩ * mk0 ⟨Ideal.span {b}, hspb⟩ = mkPrincipal u := by
    rw [hsplit, map_mul, map_inv,
      mkPrincipal_coe_eq_mk0 (I := ⟨Ideal.span {a}, hspa⟩) ha rfl,
      mkPrincipal_coe_eq_mk0 (I := ⟨Ideal.span {b}, hspb⟩) hb rfl, hb2]
  refine ⟨(⟨Ideal.span {a}, hspa⟩ * ⟨Ideal.span {b}, hspb⟩) * J, ?_⟩
  rw [map_mul, map_mul, hprin, hu]
  group

/-- **When two integral ideals have the same narrow class.** They do exactly when they differ by a
principal ideal with a totally positive generator, written as a ratio `x / y` of algebraic integers;
the ratio is totally positive precisely when the product `x * y` is. -/
theorem mk0_eq_mk0_iff {I J : (Ideal (𝓞 K))⁰} :
    mk0 I = mk0 J ↔ ∃ (x y : 𝓞 K) (_hx : x ≠ 0) (_hy : y ≠ 0),
      IsTotallyPositive ((x : K) * (y : K)) ∧
        Ideal.span {x} * (I : Ideal (𝓞 K)) = Ideal.span {y} * (J : Ideal (𝓞 K)) := by
  constructor
  · intro h
    rw [← mk_mk0, ← mk_mk0, mk_eq_mk_iff] at h
    obtain ⟨z, hz, hzeq⟩ := h
    obtain ⟨α, hαpos, rfl⟩ := mem_narrowPrincipalSubgroup.mp hz
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (α : K)
    replace hy : y ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
    have hyK : (y : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hy
    have hx : x ≠ 0 := fun h0 => by
      rw [h0, map_zero, zero_div] at hxy
      exact α.ne_zero hxy.symm
    have hxK : (x : K) = (α : K) * (y : K) := by
      rw [← hxy]; field_simp
    refine ⟨x, y, hx, hy, ?_, ?_⟩
    · rw [hxK, mul_assoc, ← sq]
      exact hαpos.mul (isTotallyPositive_sq hyK)
    · -- Clear the denominator in the fractional-ideal identity, then descend to integral ideals.
      have hcoe : ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * spanSingleton (𝓞 K)⁰ (α : K) =
          ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
        have hval := congrArg Units.val hzeq
        rwa [Units.val_mul, FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0,
          coe_toPrincipalIdeal] at hval
      have hmul := congrArg (fun T => T * spanSingleton (𝓞 K)⁰ (y : K)) hcoe
      simp only [mul_assoc, spanSingleton_mul_spanSingleton, ← hxK] at hmul
      refine FractionalIdeal.coeIdeal_injective (K := K) ?_
      simp only [FractionalIdeal.coeIdeal_mul, coeIdeal_span_singleton]
      rw [mul_comm _ ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K),
        mul_comm _ ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)]
      exact hmul
  · rintro ⟨x, y, hx, hy, hpos, heq⟩
    have hspx : Ideal.span {x} ∈ (Ideal (𝓞 K))⁰ :=
      Ideal.span_singleton_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
    have hspy : Ideal.span {y} ∈ (Ideal (𝓞 K))⁰ :=
      Ideal.span_singleton_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hy)
    have hxy : mk0 ⟨Ideal.span {x}, hspx⟩ = mk0 ⟨Ideal.span {y}, hspy⟩ := by
      have hone : mk0 ⟨Ideal.span {x}, hspx⟩ * mk0 ⟨Ideal.span {y}, hspy⟩ = 1 := by
        rw [← map_mul]
        refine mk0_eq_one_of_isTotallyPositive (a := x * y) (mul_ne_zero hx hy) ?_ ?_
        · push_cast
          exact hpos
        · rw [Submonoid.coe_mul, Ideal.span_singleton_mul_span_singleton]
      have hyinv : (mk0 ⟨Ideal.span {y}, hspy⟩)⁻¹ = mk0 ⟨Ideal.span {y}, hspy⟩ := by
        rw [inv_eq_iff_mul_eq_one, ← sq]
        exact mk0_sq_eq_one_of_eq_span_singleton hy rfl
      rw [← hyinv, eq_inv_iff_mul_eq_one]
      exact hone
    have hprod := congrArg mk0 (Subtype.ext heq :
      (⟨Ideal.span {x}, hspx⟩ * I : (Ideal (𝓞 K))⁰) = ⟨Ideal.span {y}, hspy⟩ * J)
    rw [map_mul, map_mul, hxy] at hprod
    exact mul_left_cancel hprod

end NarrowClassGroup

end NumberField
