/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Ideal.Away
public import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# Moduli of a number field and multiplicative congruence

A **modulus** of a number field `K` is a pair consisting of a nonzero integral ideal of `𝓞 K` (the
finite part) and a finite set of real infinite places (the infinite part).  Moduli are the data
against which the congruence conditions defining ray classes are imposed: an element `x` of `Kˣ` is
*congruent to one modulo `𝔪`* when the finite part divides `x - 1` locally at each of its prime
divisors, and `x` is positive at each real place selected by the infinite part.

This file builds that vocabulary:

* the carrier `Modulus K`, its divisibility relation, its finite support and exponent function, the
  trivial modulus and the modulus with unit finite part and every real place;
* the predicate `IsCongrOne` and the subgroup `congruenceSubgroup` of `Kˣ` it cuts out, together
  with the larger subgroup `primeToSubgroup` of elements that are units at the primes dividing the
  finite part, and the subgroup `unitsCongruenceSubgroup` of `(𝓞 K)ˣ` obtained by restriction;
* the group `idealsPrimeTo 𝔪` of invertible fractional ideals and the monoid
  `integralIdealsPrimeTo 𝔪` of nonzero integral ideals that are prime to the finite part.

The last two are *abbreviations* for `TauCeti.NumberFieldArithmetic.idealsAway 𝔪.support` and
`TauCeti.NumberFieldArithmetic.integralIdealsAway 𝔪.support`: there is exactly one group of
prime-to fractional ideals and one monoid of prime-to integral ideals, and both are the ones built
away from a finite set of primes.

## Main definitions

* `TauCeti.GlobalNumberFields.Modulus`: the carrier, with `Modulus.support`, `Modulus.exponent`,
  `Modulus.one` and `TauCeti.GlobalNumberFields.narrowModulus`.
* `TauCeti.GlobalNumberFields.IsCongrOne`: multiplicative congruence to one modulo a modulus.
* `TauCeti.GlobalNumberFields.congruenceSubgroup`, `TauCeti.GlobalNumberFields.primeToSubgroup`,
  `TauCeti.GlobalNumberFields.unitsCongruenceSubgroup`: the subgroups of `Kˣ` and `(𝓞 K)ˣ` these
  conditions define.
* `TauCeti.GlobalNumberFields.idealsPrimeTo`,
  `TauCeti.GlobalNumberFields.integralIdealsPrimeTo`: ideals prime to the finite part, with the
  inclusion `TauCeti.GlobalNumberFields.integralIdealsPrimeToInclusion` along divisibility.

## Main results

* `TauCeti.GlobalNumberFields.Modulus.mem_support_iff`: membership in the support is divisibility
  of the finite part.  `Modulus.support_one` and `Modulus.support_mono` are consequences.
* `TauCeti.GlobalNumberFields.congruenceSubgroup_le_primeToSubgroup`: an element congruent to one
  is a unit at every prime dividing the finite part.  This is what makes the ray a subgroup of the
  prime-to ideals.
* `TauCeti.GlobalNumberFields.IsCongrOne.mono` and
  `TauCeti.GlobalNumberFields.congruenceSubgroup_antitone`: congruence to one is antitone in the
  modulus, which is what makes the transition maps between ray class groups run from a larger
  modulus to a smaller one.
* `TauCeti.GlobalNumberFields.isCongrOne_narrowModulus_iff`: congruence to one modulo the modulus
  with unit finite part and every real place is total positivity.
* `TauCeti.GlobalNumberFields.Modulus.isCoprimeTo_iff_sup_eq_top`: being prime to the support is
  comaximality with the finite part.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

-- Provenance: the declaration names and signatures formalized here follow the interface file
-- `GlobalNumberFields/Suggested.lean`, and its accompanying `README.md`, of the TauCetiRoadmap
-- repository, which specify this API.
namespace TauCeti.GlobalNumberFields

/-- A **modulus** of a number field `K`: a nonzero integral ideal of `𝓞 K` together with a finite
set of real infinite places.  Complex places never divide a modulus, which is why the infinite part
is a `Finset` of the subtype `{w : InfinitePlace K // w.IsReal}` rather than of all infinite
places. -/
structure Modulus (K : Type*) [Field K] [NumberField K] where
  /-- The finite part of the modulus: a nonzero integral ideal of `𝓞 K`. -/
  finitePart : Ideal (𝓞 K)
  /-- The finite part of a modulus is nonzero. -/
  finitePart_ne_bot : finitePart ≠ ⊥
  /-- The infinite part of the modulus: a finite set of real places of `K`. -/
  infinitePart : Finset {w : InfinitePlace K // w.IsReal}

variable {K : Type*} [Field K] [NumberField K]

namespace Modulus

omit [NumberField K] in
/-- A height-one prime never divides the unit ideal. -/
private theorem not_dvd_top (v : HeightOneSpectrum (𝓞 K)) :
    ¬ v.asIdeal ∣ (⊤ : Ideal (𝓞 K)) :=
  fun hv ↦ v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd hv))

theorem finitePart_ne_zero (𝔪 : Modulus K) : 𝔪.finitePart ≠ 0 := fun h ↦
  𝔪.finitePart_ne_bot (by rwa [Ideal.zero_eq_bot] at h)

/-- **Divisibility of moduli**: `𝔪 ∣ 𝔫` when the finite part of `𝔪` divides that of `𝔫` and the
infinite part of `𝔪` is contained in that of `𝔫`, so that the congruence conditions imposed by
`𝔫` are the stronger ones. -/
instance : Dvd (Modulus K) :=
  ⟨fun 𝔪 𝔫 ↦ 𝔪.finitePart ∣ 𝔫.finitePart ∧ 𝔪.infinitePart ⊆ 𝔫.infinitePart⟩

@[refl]
theorem dvd_refl (𝔪 : Modulus K) : 𝔪 ∣ 𝔪 := ⟨_root_.dvd_refl _, Finset.Subset.refl _⟩

theorem dvd_trans {𝔪 𝔫 𝔭 : Modulus K} (h₁ : 𝔪 ∣ 𝔫) (h₂ : 𝔫 ∣ 𝔭) : 𝔪 ∣ 𝔭 :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- The **support** of a modulus: the finite set of height-one primes dividing its finite part. -/
noncomputable def support (𝔪 : Modulus K) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors 𝔪.finitePart_ne_zero).toFinset

/-- **Membership in the support is divisibility of the finite part.**  This is the characterizing
theorem of `Modulus.support`; `Modulus.support_one` and `Modulus.support_mono` are derived from
it. -/
@[simp]
theorem mem_support_iff (𝔪 : Modulus K) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ 𝔪.support ↔ v.asIdeal ∣ 𝔪.finitePart :=
  Set.Finite.mem_toFinset _

theorem dvd_finitePart_of_mem_support {𝔪 : Modulus K} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ 𝔪.support) : v.asIdeal ∣ 𝔪.finitePart :=
  (mem_support_iff 𝔪 v).mp hv

/-- The support grows with the modulus. -/
theorem support_mono {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) : 𝔪.support ⊆ 𝔫.support := fun v hv ↦
  (mem_support_iff 𝔫 v).mpr (((mem_support_iff 𝔪 v).mp hv).trans h.1)

/-- The **exponent** of a finite place in a modulus: the multiplicity of `v` in the factorization
of the finite part. -/
noncomputable def exponent (𝔪 : Modulus K) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk 𝔪.finitePart).factors

/-- A prime lies in the support of a modulus exactly when it occurs in the finite part with a
positive exponent. -/
theorem mem_support_iff_exponent_ne_zero (𝔪 : Modulus K) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ 𝔪.support ↔ 𝔪.exponent v ≠ 0 := by
  rw [mem_support_iff, exponent,
    Associates.count_ne_zero_iff_dvd 𝔪.finitePart_ne_zero v.irreducible]

theorem exponent_pos_of_mem_support {𝔪 : Modulus K} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ 𝔪.support) : 0 < 𝔪.exponent v :=
  Nat.pos_of_ne_zero ((mem_support_iff_exponent_ne_zero 𝔪 v).mp hv)

/-- Exponents grow with the modulus. -/
theorem exponent_mono {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) (v : HeightOneSpectrum (𝓞 K)) :
    𝔪.exponent v ≤ 𝔫.exponent v :=
  Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr 𝔫.finitePart_ne_zero)
    (Associates.irreducible_mk.mpr v.irreducible) (Associates.mk_le_mk_of_dvd h.1)

/-- The **trivial modulus**: unit finite part and no real places.  It imposes no condition, so its
ray class group is the ordinary class group. -/
def one (K : Type*) [Field K] [NumberField K] : Modulus K where
  finitePart := ⊤
  finitePart_ne_bot := top_ne_bot
  infinitePart := ∅

@[simp] theorem one_finitePart : (one K).finitePart = ⊤ := (rfl)

@[simp] theorem one_infinitePart : (one K).infinitePart = ∅ := (rfl)

/-- The trivial modulus has empty support: no height-one prime divides the unit ideal. -/
@[simp] theorem support_one : (one K).support = ∅ := by
  ext v
  rw [mem_support_iff, one_finitePart]
  simpa only [Finset.notMem_empty, iff_false] using not_dvd_top v

theorem one_dvd (𝔪 : Modulus K) : one K ∣ 𝔪 :=
  ⟨by rw [one_finitePart, ← Ideal.one_eq_top]; exact _root_.one_dvd _, by simp⟩

end Modulus

/-- The modulus with unit finite part and **every** real place.  Its ray class group is the narrow
class group. -/
noncomputable def narrowModulus (K : Type*) [Field K] [NumberField K] : Modulus K :=
  { Modulus.one K with
    infinitePart := (Set.finite_univ (α := {w : InfinitePlace K // w.IsReal})).toFinset }

@[simp] theorem narrowModulus_finitePart : (narrowModulus K).finitePart = ⊤ := (rfl)

@[simp] theorem mem_narrowModulus_infinitePart (w : {w : InfinitePlace K // w.IsReal}) :
    w ∈ (narrowModulus K).infinitePart :=
  (Set.Finite.mem_toFinset _).mpr (Set.mem_univ w)

/-- The narrow modulus has the same finite part as the trivial one, hence the same support. -/
@[simp] theorem narrowModulus_support : (narrowModulus K).support = ∅ := by
  refine Eq.trans ?_ Modulus.support_one
  ext v
  rw [Modulus.mem_support_iff, Modulus.mem_support_iff, narrowModulus_finitePart,
    Modulus.one_finitePart]

/-! ### Multiplicative congruence -/

/-- **Multiplicative congruence to one modulo a modulus.**  An element `x` of `Kˣ` satisfies
`IsCongrOne 𝔪 x` when, at every prime `v` dividing the finite part of `𝔪`, the element `x - 1` is
divisible by `v ^ (𝔪.exponent v)` locally — equivalently `v.valuation K (x - 1)` is at most
`exp (-𝔪.exponent v)` — and `x` is positive at every real place selected by the infinite part.

This is a condition on `Kˣ`, not on `K`: writing it on `K` would let `0` meet a request for
negative signs.  It is also not unqualified membership in `1 + 𝔪.finitePart`, since `x` need not
be an algebraic integer. -/
def IsCongrOne (𝔪 : Modulus K) (x : Kˣ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.finitePart →
      v.valuation K ((x : K) - 1) ≤ WithZero.exp (-(𝔪.exponent v : ℤ))) ∧
    ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.2 (x : K)

theorem isCongrOne_iff {𝔪 : Modulus K} {x : Kˣ} :
    IsCongrOne 𝔪 x ↔
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.finitePart →
          v.valuation K ((x : K) - 1) ≤ WithZero.exp (-(𝔪.exponent v : ℤ))) ∧
        ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.2 (x : K) :=
  Iff.rfl

namespace IsCongrOne

variable {𝔪 : Modulus K} {x : Kˣ}

theorem valuation_sub_one_le (hx : IsCongrOne 𝔪 x) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∣ 𝔪.finitePart) :
    v.valuation K ((x : K) - 1) ≤ WithZero.exp (-(𝔪.exponent v : ℤ)) := hx.1 v hv

theorem pos (hx : IsCongrOne 𝔪 x) {w : {w : InfinitePlace K // w.IsReal}}
    (hw : w ∈ 𝔪.infinitePart) : 0 < InfinitePlace.embedding_of_isReal w.2 (x : K) := hx.2 w hw

/-- An element congruent to one modulo `𝔪` has `v`-adic valuation strictly less than one at
`x - 1`, for every prime `v` dividing the finite part: the exponent there is positive. -/
theorem valuation_sub_one_lt_one (hx : IsCongrOne 𝔪 x) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∣ 𝔪.finitePart) : v.valuation K ((x : K) - 1) < 1 := by
  refine lt_of_le_of_lt (hx.valuation_sub_one_le hv) ?_
  have hpos : 0 < 𝔪.exponent v :=
    Modulus.exponent_pos_of_mem_support ((Modulus.mem_support_iff 𝔪 v).mpr hv)
  exact WithZero.exp_lt_one_iff.mpr (neg_neg_iff_pos.mpr (Int.natCast_pos.mpr hpos))

/-- **An element congruent to one is a unit at the primes dividing the finite part.** -/
theorem valuation_eq_one (hx : IsCongrOne 𝔪 x) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∣ 𝔪.finitePart) : v.valuation K (x : K) = 1 := by
  have h := Valuation.map_one_add_of_lt (v.valuation K) (hx.valuation_sub_one_lt_one hv)
  rwa [add_sub_cancel] at h

/-- **Congruence is antitone in the modulus.**  An element congruent to one modulo the larger
modulus `𝔫` is congruent to one modulo every divisor `𝔪` of `𝔫`: the exponents can only have
shrunk and fewer real places are constrained. -/
theorem mono {𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) (hx : IsCongrOne 𝔫 x) : IsCongrOne 𝔪 x := by
  refine ⟨fun v hv ↦ ?_, fun w hw ↦ hx.pos (h.2 hw)⟩
  refine (hx.valuation_sub_one_le (hv.trans h.1)).trans (WithZero.exp_le_exp.mpr ?_)
  exact neg_le_neg (Int.ofNat_le.mpr (Modulus.exponent_mono h v))

end IsCongrOne

/-- The subgroup of `Kˣ` of elements congruent to one modulo `𝔪`.  The ray of principal ideals is
generated by its image in the fractional ideals. -/
def congruenceSubgroup (𝔪 : Modulus K) : Subgroup Kˣ where
  carrier := {x | IsCongrOne 𝔪 x}
  one_mem' := by
    refine ⟨fun v _ ↦ ?_, fun w _ ↦ ?_⟩
    · simp
    · simp
  mul_mem' := by
    rintro x y hx hy
    refine ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩
    · -- `xy - 1 = x (y - 1) + (x - 1)`, and `x` is a unit at `v`.
      have hxy : ((x * y : Kˣ) : K) - 1 = (x : K) * ((y : K) - 1) + ((x : K) - 1) := by
        push_cast; ring
      refine le_trans (hxy ▸ Valuation.map_add (v.valuation K) _ _) (max_le ?_ ?_)
      · rw [map_mul, hx.valuation_eq_one hv, one_mul]
        exact hy.valuation_sub_one_le hv
      · exact hx.valuation_sub_one_le hv
    · have := mul_pos (hx.pos hw) (hy.pos hw)
      rwa [← map_mul, ← Units.val_mul] at this
  inv_mem' := by
    rintro x hx
    refine ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩
    · have hne : (x : K) ≠ 0 := x.ne_zero
      have hxy : ((x⁻¹ : Kˣ) : K) - 1 = -(((x : K) - 1) * (x : K)⁻¹) := by
        rw [Units.val_inv_eq_inv_val]
        field_simp
        ring
      rw [hxy, Valuation.map_neg, map_mul, map_inv₀, hx.valuation_eq_one hv, inv_one, mul_one]
      exact hx.valuation_sub_one_le hv
    · have := inv_pos.mpr (hx.pos hw)
      rwa [← map_inv₀, ← Units.val_inv_eq_inv_val] at this

@[simp] theorem mem_congruenceSubgroup {𝔪 : Modulus K} {x : Kˣ} :
    x ∈ congruenceSubgroup 𝔪 ↔ IsCongrOne 𝔪 x := Iff.rfl

/-- **The congruence subgroups decrease as the modulus grows.** -/
theorem congruenceSubgroup_antitone {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) :
    congruenceSubgroup 𝔫 ≤ congruenceSubgroup 𝔪 :=
  fun _ hx ↦ mem_congruenceSubgroup.mpr (IsCongrOne.mono h (mem_congruenceSubgroup.mp hx))

/-- The subgroup of `Kˣ` of elements that are units at every prime dividing the finite part of the
modulus.  This is the domain of reduction to the residue units. -/
def primeToSubgroup (𝔪 : Modulus K) : Subgroup Kˣ where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.finitePart →
    v.valuation K (x : K) = 1}
  one_mem' := by simp
  mul_mem' := fun hx hy v hv ↦ by
    rw [Units.val_mul, map_mul, hx v hv, hy v hv, one_mul]
  inv_mem' := fun hx v hv ↦ by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx v hv, inv_one]

@[simp] theorem mem_primeToSubgroup {𝔪 : Modulus K} {x : Kˣ} :
    x ∈ primeToSubgroup 𝔪 ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.finitePart → v.valuation K (x : K) = 1 :=
  Iff.rfl

/-- **Congruence to one implies being a unit at the finite part.**  This inclusion is what makes
the principal ideal of an element congruent to one prime to the modulus. -/
theorem congruenceSubgroup_le_primeToSubgroup (𝔪 : Modulus K) :
    congruenceSubgroup 𝔪 ≤ primeToSubgroup 𝔪 :=
  fun _ hx v hv ↦ hx.valuation_eq_one (v := v) hv

/-- The units of `𝓞 K` congruent to one modulo `𝔪`.  Its index in `(𝓞 K)ˣ` is the unit correction
in the ray class number formula. -/
def unitsCongruenceSubgroup (𝔪 : Modulus K) : Subgroup (𝓞 K)ˣ :=
  (congruenceSubgroup 𝔪).comap (Units.map (algebraMap (𝓞 K) K).toMonoidHom)

@[simp] theorem mem_unitsCongruenceSubgroup {𝔪 : Modulus K} {u : (𝓞 K)ˣ} :
    u ∈ unitsCongruenceSubgroup 𝔪 ↔
      IsCongrOne 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) := Iff.rfl

/-- **The trivial modulus imposes no condition.**  Its finite part is the unit ideal, which no
prime divides, and its infinite part is empty. -/
@[simp] theorem isCongrOne_one (x : Kˣ) : IsCongrOne (Modulus.one K) x :=
  ⟨fun v hv ↦ absurd (Modulus.one_finitePart (K := K) ▸ hv) (Modulus.not_dvd_top v),
    fun w hw ↦ absurd hw (by simp)⟩

theorem congruenceSubgroup_one : congruenceSubgroup (Modulus.one K) = ⊤ :=
  Subgroup.eq_top_iff' _ |>.mpr fun x ↦ isCongrOne_one x

/-- **Congruence to one modulo the narrow modulus is total positivity.**  The finite part of
`narrowModulus K` is the unit ideal, so only the sign conditions survive, and they are imposed at
every real place. -/
theorem isCongrOne_narrowModulus_iff {x : Kˣ} :
    IsCongrOne (narrowModulus K) x ↔ IsTotallyPositive (x : K) := by
  refine ⟨fun hx ↦ isTotallyPositive_iff.mpr fun w hw ↦ hx.pos (w := ⟨w, hw⟩) (by simp),
    fun hx ↦ ⟨fun v hv ↦ ?_, fun w _ ↦ isTotallyPositive_iff.mp hx w w.2⟩⟩
  exact absurd ((Modulus.mem_support_iff _ v).mpr hv) (by simp)

/-! ### Ideals prime to a modulus -/

/-- **The group of fractional ideals prime to a modulus**: the invertible fractional ideals whose
multiplicity vanishes at every prime dividing the finite part.  There is one such group, the one
built away from a finite set of primes. -/
noncomputable abbrev idealsPrimeTo (𝔪 : Modulus K) :
    Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  NumberFieldArithmetic.idealsAway (K := K) 𝔪.support

/-- Coprimality of a nonzero integral ideal to a modulus: it is prime to the support, that is, to
the finite part.  This is the membership predicate of `integralIdealsPrimeTo`. -/
def Modulus.IsCoprimeTo (𝔪 : Modulus K) (I : Ideal (𝓞 K)) : Prop :=
  Ideal.IsPrimeTo I (𝔪.support : Set (HeightOneSpectrum (𝓞 K)))

theorem Modulus.isCoprimeTo_iff {𝔪 : Modulus K} {I : Ideal (𝓞 K)} :
    𝔪.IsCoprimeTo I ↔ I ≠ ⊥ ∧ ∀ v ∈ 𝔪.support, ¬ v.asIdeal ∣ I := Ideal.isPrimeTo_iff

/-- **Being prime to the modulus is comaximality with its finite part.**  A prime dividing both `I`
and the finite part is exactly a prime of the support dividing `I`, and such a prime exists as soon
as `I` and the finite part fail to generate the unit ideal. -/
theorem Modulus.isCoprimeTo_iff_sup_eq_top {𝔪 : Modulus K} {I : Ideal (𝓞 K)} :
    𝔪.IsCoprimeTo I ↔ I ≠ ⊥ ∧ I ⊔ 𝔪.finitePart = ⊤ := by
  rw [isCoprimeTo_iff]
  refine and_congr_right fun hI ↦ ⟨fun h ↦ ?_, fun h v hv hdvd ↦ ?_⟩
  · by_contra hne
    obtain ⟨𝔭, h𝔭max, h𝔭le⟩ := Ideal.exists_le_maximal _ hne
    have h𝔭bot : 𝔭 ≠ ⊥ := fun hbot ↦ 𝔪.finitePart_ne_bot
      (le_bot_iff.mp (hbot ▸ le_sup_right.trans h𝔭le))
    refine h ⟨𝔭, h𝔭max.isPrime, h𝔭bot⟩ ?_ ?_
    · exact (mem_support_iff _ _).mpr (Ideal.dvd_iff_le.mpr (le_sup_right.trans h𝔭le))
    · exact Ideal.dvd_iff_le.mpr (le_sup_left.trans h𝔭le)
  · refine v.isPrime.ne_top (top_le_iff.mp ?_)
    rw [← h]
    exact sup_le (Ideal.le_of_dvd hdvd) (Ideal.le_of_dvd (dvd_finitePart_of_mem_support hv))

/-- **The monoid of nonzero integral ideals prime to a modulus.**  There is one such monoid, the
one built away from a finite set of primes; its membership predicate is `Modulus.IsCoprimeTo`. -/
noncomputable abbrev integralIdealsPrimeTo (𝔪 : Modulus K) : Submonoid (Ideal (𝓞 K)) :=
  NumberFieldArithmetic.integralIdealsAway (K := K) 𝔪.support

theorem Modulus.mem_integralIdealsPrimeTo {𝔪 : Modulus K} {I : Ideal (𝓞 K)} :
    I ∈ integralIdealsPrimeTo 𝔪 ↔ 𝔪.IsCoprimeTo I :=
  NumberFieldArithmetic.mem_integralIdealsAway_iff.trans Modulus.isCoprimeTo_iff.symm

/-- **The integral prime-to monoid is antitone in the modulus**: the support of a divisor `𝔪` of
`𝔫` is contained in that of `𝔫`, so an ideal prime to `𝔫` is prime to `𝔪`. -/
theorem integralIdealsPrimeTo_antitone {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) :
    integralIdealsPrimeTo 𝔫 ≤ integralIdealsPrimeTo 𝔪 := by
  intro I hI
  rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff] at hI ⊢
  exact ⟨hI.1, fun v hv ↦ hI.2 v (Modulus.support_mono h hv)⟩

/-- The inclusion of the integral ideals prime to `𝔫` into those prime to `𝔪`, for a divisor `𝔪`
of `𝔫`.  It is the literal inclusion, matching `NumberFieldArithmetic.idealsAwayInclusion` on the
fractional side. -/
noncomputable def integralIdealsPrimeToInclusion {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) :
    integralIdealsPrimeTo 𝔫 →* integralIdealsPrimeTo 𝔪 :=
  Submonoid.inclusion (integralIdealsPrimeTo_antitone h)

/-- The inclusion between integral prime-to monoids does not change the underlying ideal. -/
@[simp] theorem coe_integralIdealsPrimeToInclusion {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    (I : integralIdealsPrimeTo 𝔫) :
    ((integralIdealsPrimeToInclusion h I : integralIdealsPrimeTo 𝔪) : Ideal (𝓞 K)) =
      (I : Ideal (𝓞 K)) := (rfl)

end TauCeti.GlobalNumberFields
