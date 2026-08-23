/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.FractionalIdealDivisor.Basic
public import TauCeti.RingTheory.ClassGroup.Basic

/-!
# `n`-th roots of invertible fractional ideals, and the `n`-th root class map

Let `R` be a Dedekind domain with fraction field `K`. `FractionalIdealDivisor.Basic` identifies the
group of invertible fractional ideals of `R` with the free Weil-divisor group on the height-one
primes, by `fractionalIdealDivisorAddEquiv`. In a free abelian group, an element all of whose
coefficients are divisible by `n` is `n` times an element, and for `n ≠ 0` that element is unique.
This file transports that division back to fractional ideals and records what it says about the
ideal class group.

Everything below is stated for all `n : ℕ`, including the degenerate `n = 0`. There `nDivisible R K
0` is the trivial subgroup (divisibility by `0` is vanishing), `nthRootHom R K 0` is constantly `1`,
and the results remain true but say nothing: `1 ^ 0 = 1` is the only instance of `nthRootHom_pow`.

## Main definitions

* `nDivisible R K n`: the subgroup of invertible fractional ideals all of whose multiplicities
  `FractionalIdeal.count K v` are divisible by `n`.
* `nthRootHom R K n`: the **`n`-th root homomorphism** from `nDivisible R K n` to the group of
  invertible fractional ideals. It is built from a private helper performing coefficientwise
  integer division of the Weil divisor by `n`; that helper is deliberately not public, since off
  `nDivisible R K n` integer division rounds and the value obeys no law worth depending on.
  Restricting to the subgroup is what makes it multiplicative for `n ≠ 0`, integer division being
  additive on multiples of `n`; for `n = 0` it is constant.
* `unitsNDivisible R K n`: the subgroup of `x : Kˣ` whose principal fractional ideal `(x)` lies in
  `nDivisible R K n`.
* `nthRootClass R K n`: the **`n`-th root class map** `unitsNDivisible R K n →* ClassGroup R`,
  sending `u` to the ideal class of the `n`-th root of `(u)`. Its codomain is taken to be the whole
  class group, with `nthRootClass_pow` recording that the image lands in the `n`-torsion.

## Main results

* `nthRootHom_pow`: the `n`-th root homomorphism is a genuine `n`-th root — its value raised to the
  `n`-th power is the original ideal.
* `mem_nDivisible_iff_exists_pow`: `nDivisible R K n` is exactly the subgroup of `n`-th powers.
  The forward direction is `exists_pow_eq_of_nDivisible` — an invertible fractional ideal whose
  multiplicities are all divisible by `n` is an `n`-th power — and the converse is
  `pow_mem_nDivisible`, with `pow_mem_unitsNDivisible` the corresponding statement for `Kˣ`.
* `nthRootClass_pow`: every value of the `n`-th root class map is `n`-torsion.
* `nthRootClass_eq_one_iff`: the `n`-th root class of `u` is trivial exactly when `u` is a unit of
  `R` times an `n`-th power in `Kˣ`.

The last two are the torsion and kernel statements that will become exactness at the middle term of
the fundamental sequence `1 → Rˣ/(Rˣ)ⁿ → K(∅, n) → Cl(R)[n] → 1` once the quotients are formed and
the codomain is restricted along `nthRootClass_pow`. Neither step is taken here: this file supplies
the `n`-th root map, the torsion bound and the kernel description, and states no exactness or
finiteness result.

These are ingredients for `TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (Mordell–Weil), whose
weak Mordell–Weil argument needs the Selmer group `K(S, n)` of
`Mathlib.RingTheory.DedekindDomain.SelmerGroup` to be finite; Mathlib leaves that finiteness as a
`TODO` and the roadmap assigns it to this repository. The finiteness proof is not in this file.

None of the definitions here is `@[expose]`: the interface is the membership, coefficient and
coercion lemmas, not the construction bodies. The characteristic lemmas that hold by
definition are therefore written `:= (rfl)`, `:= (Iff.rfl)` and `:= (proof)` rather than bare — the
parentheses keep the proof elaborating where the definition is still available, which is what lets
the bodies stay unexposed. Do not "simplify" them back.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/FractionalIdeal.lean`
at the roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll). Following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header. The `n`-th root is built here by dividing the coefficients of a Weil divisor and
transporting along `fractionalIdealDivisorAddEquiv`, where the source builds it from its own
`ofFinsupp`/`toFinsupp` pair; that pair duplicates the isomorphism this repository already has, so
it is not ported.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### The `n`-th root homomorphism -/

/-- The subgroup of invertible fractional ideals all of whose multiplicities are divisible by `n`,
equivalently those whose Weil divisor is `n` times a divisor. -/
def nDivisible (n : ℕ) : Subgroup (FractionalIdeal R⁰ K)ˣ where
  carrier := {I | ∀ v : HeightOneSpectrum R, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K)}
  one_mem' v := by rw [Units.val_one, count_one]; exact dvd_zero _
  mul_mem' {I J} hI hJ v := by
    rw [Units.val_mul, count_mul K v (Units.ne_zero I) (Units.ne_zero J)]
    exact dvd_add (hI v) (hJ v)
  inv_mem' {I} hI v := by
    rw [Units.val_inv_eq_inv_val, count_inv]
    exact (hI v).neg_right

variable {R K} in
/-- Membership in `nDivisible R K n` is divisibility of every multiplicity by `n`. -/
@[simp]
lemma mem_nDivisible {n : ℕ} {I : (FractionalIdeal R⁰ K)ˣ} :
    I ∈ nDivisible R K n ↔
      ∀ v : HeightOneSpectrum R, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K) :=
  (Iff.rfl)

/-- An `n`-th power is `n`-divisible: every multiplicity of `J ^ n` is `n` times one of `J`. This
is the introduction rule for `nDivisible R K n`, converse to `exists_pow_eq_of_nDivisible`. -/
lemma pow_mem_nDivisible (n : ℕ) (J : (FractionalIdeal R⁰ K)ˣ) : J ^ n ∈ nDivisible R K n :=
  mem_nDivisible.mpr fun v ↦ by
    rw [Units.val_pow_eq_pow_val, count_pow]
    exact dvd_mul_right _ _

/-- Coefficientwise integer division of the Weil divisor of an invertible fractional ideal by `n`,
transported back along `fractionalIdealDivisorAddEquiv`. Since integer division rounds, this is a
genuine `n`-th root exactly on `nDivisible R K n`, where `nthRootHom` bundles it as a group
homomorphism; off that subgroup it is only a candidate. -/
private noncomputable def nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) :
    (FractionalIdeal R⁰ K)ˣ :=
  Additive.toMul ((fractionalIdealDivisorAddEquiv R K).symm
    (Finsupp.mapRange (· / (n : ℤ)) (Int.zero_ediv _)
      (fractionalIdealDivisor R K (Additive.ofMul I))))

/-- The Weil divisor of the `n`-th root is the Weil divisor of `I` with every coefficient divided
by `n`: `nthRootFun` read back through the isomorphism defining it. -/
private lemma fractionalIdealDivisor_nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) :
    fractionalIdealDivisor R K (Additive.ofMul (nthRootFun R K n I)) =
      Finsupp.mapRange (· / (n : ℤ)) (Int.zero_ediv _)
        (fractionalIdealDivisor R K (Additive.ofMul I)) := by
  conv_lhs => rw [nthRootFun]
  simp only [ofMul_toMul, ← fractionalIdealDivisorAddEquiv_apply, AddEquiv.apply_symm_apply]

/-- The multiplicities of the `n`-th root are those of `I`, divided by `n`. -/
private lemma count_nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    count K v (nthRootFun R K n I : FractionalIdeal R⁰ K) =
      count K v (I : FractionalIdeal R⁰ K) / n := by
  have key : ∀ J : (FractionalIdeal R⁰ K)ˣ, count K v (J : FractionalIdeal R⁰ K) =
      coeff (fractionalIdealDivisor R K (Additive.ofMul J)) v :=
    fun J ↦ (coeff_fractionalIdealDivisor R K (Additive.ofMul J) v).symm
  rw [key, key I, fractionalIdealDivisor_nthRootFun]
  simp only [coeff, Finsupp.mapRange_apply]

/-- The **`n`-th root homomorphism**: on the subgroup of ideals whose multiplicities are all
divisible by `n`, dividing every multiplicity by `n` is a group homomorphism. For `n ≠ 0` the
restriction is what makes this multiplicative, integer division being additive on multiples of `n`
and not in general; for `n = 0` the map is constantly `1` and the subgroup is trivial. -/
noncomputable def nthRootHom (n : ℕ) : nDivisible R K n →* (FractionalIdeal R⁰ K)ˣ where
  toFun I := nthRootFun R K n (I : (FractionalIdeal R⁰ K)ˣ)
  map_one' := units_eq_of_forall_count_eq R K fun v ↦ by
    simp only [count_nthRootFun, Subgroup.coe_one, Units.val_one, count_one, Int.zero_ediv]
  map_mul' I J := units_eq_of_forall_count_eq R K fun v ↦ by
    rw [count_nthRootFun, Units.val_mul, count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      count_nthRootFun, count_nthRootFun, Subgroup.coe_mul, Units.val_mul,
      count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      Int.add_ediv_of_dvd_left (mem_nDivisible.mp I.2 v)]

variable {R K} in
/-- The multiplicities of the `n`-th root are those of `I`, divided by `n`. Together with
`units_eq_of_forall_count_eq` this determines `nthRootHom` completely, so no lemma below needs to
unfold it. -/
@[simp]
lemma count_nthRootHom (n : ℕ) (I : nDivisible R K n) (v : HeightOneSpectrum R) :
    count K v (nthRootHom R K n I : FractionalIdeal R⁰ K) =
      count K v ((I : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) / n :=
  (count_nthRootFun R K n _ v)

/-- The `n`-th root homomorphism is a genuine `n`-th root: raising its value to the `n`-th power
returns the original ideal. -/
lemma nthRootHom_pow (n : ℕ) (I : nDivisible R K n) :
    nthRootHom R K n I ^ n = (I : (FractionalIdeal R⁰ K)ˣ) :=
  units_eq_of_forall_count_eq R K fun v ↦ by
    rw [Units.val_pow_eq_pow_val, count_pow, count_nthRootHom,
      Int.mul_ediv_cancel' (mem_nDivisible.mp I.2 v)]

/-- **`n`-th roots of invertible fractional ideals.** An invertible fractional ideal all of whose
multiplicities are divisible by `n` is an `n`-th power. -/
lemma exists_pow_eq_of_nDivisible (n : ℕ) {I : (FractionalIdeal R⁰ K)ˣ}
    (hI : I ∈ nDivisible R K n) : ∃ J : (FractionalIdeal R⁰ K)ˣ, J ^ n = I :=
  ⟨nthRootHom R K n ⟨I, hI⟩, nthRootHom_pow R K n ⟨I, hI⟩⟩

variable {R K} in
/-- **`nDivisible R K n` is exactly the subgroup of `n`-th powers.** Combining
`exists_pow_eq_of_nDivisible` with its converse `pow_mem_nDivisible`. -/
lemma mem_nDivisible_iff_exists_pow {n : ℕ} {I : (FractionalIdeal R⁰ K)ˣ} :
    I ∈ nDivisible R K n ↔ ∃ J : (FractionalIdeal R⁰ K)ˣ, J ^ n = I :=
  ⟨exists_pow_eq_of_nDivisible R K n, by rintro ⟨J, rfl⟩; exact pow_mem_nDivisible R K n J⟩

/-! ### The `n`-th root class map -/

/-- The subgroup of those `x : Kˣ` whose principal fractional ideal `(x)` has all multiplicities
divisible by `n`. These are exactly the elements for which an `n`-th root of `(x)` exists, so they
are exactly the elements the `n`-th root class map is defined on. -/
def unitsNDivisible (n : ℕ) : Subgroup Kˣ :=
  Subgroup.comap (toPrincipalIdeal R K) (nDivisible R K n)

variable {R K} in
/-- Membership in `unitsNDivisible R K n` is divisibility by `n` of every multiplicity of the
principal fractional ideal generated by `u`. -/
@[simp]
lemma mem_unitsNDivisible {n : ℕ} {u : Kˣ} :
    u ∈ unitsNDivisible R K n ↔
      ∀ v : HeightOneSpectrum R, (n : ℤ) ∣ count K v (spanSingleton R⁰ (u : K)) := by
  rw [unitsNDivisible, Subgroup.mem_comap, mem_nDivisible]
  simp only [coe_toPrincipalIdeal]

/-- An `n`-th power of a unit of `K` lies in `unitsNDivisible R K n`: the introduction rule, and
the reason the subgroup contains the `n`-th powers that the quotient `Kˣ/(Kˣ)ⁿ` divides out. -/
lemma pow_mem_unitsNDivisible (n : ℕ) (w : Kˣ) : w ^ n ∈ unitsNDivisible R K n := by
  rw [unitsNDivisible, Subgroup.mem_comap, map_pow]
  exact pow_mem_nDivisible R K n _

/-- The principal-ideal map restricted to `unitsNDivisible R K n`, with codomain cut down to the
subgroup `nDivisible R K n` that it lands in by definition. -/
noncomputable def unitsNDivisibleToNDivisible (n : ℕ) :
    unitsNDivisible R K n →* nDivisible R K n :=
  ((toPrincipalIdeal R K).comp (unitsNDivisible R K n).subtype).codRestrict _ fun x ↦ x.2

/-- Underneath the codomain restriction, `unitsNDivisibleToNDivisible` is `toPrincipalIdeal`. -/
@[simp]
lemma coe_unitsNDivisibleToNDivisible (n : ℕ) (u : unitsNDivisible R K n) :
    (unitsNDivisibleToNDivisible R K n u : (FractionalIdeal R⁰ K)ˣ) =
      toPrincipalIdeal R K (u : Kˣ) :=
  (rfl)

/-- The **`n`-th root class map**: send `u : Kˣ` whose principal ideal `(u)` is `n`-divisible to the
ideal class of the `n`-th root of `(u)`. This is the map that becomes the right-hand map of
`1 → Rˣ/(Rˣ)ⁿ → K(∅, n) → Cl(R)[n] → 1` once quotients are formed and the codomain is cut down to
the `n`-torsion; here it is taken with its full codomain `ClassGroup R`. -/
noncomputable def nthRootClass (n : ℕ) : unitsNDivisible R K n →* ClassGroup R :=
  (ClassGroup.mk K).comp ((nthRootHom R K n).comp (unitsNDivisibleToNDivisible R K n))

/-- The `n`-th root class map is the class of the `n`-th root of the principal ideal, by
definition. -/
@[simp]
lemma nthRootClass_apply (n : ℕ) (u : unitsNDivisible R K n) :
    nthRootClass R K n u =
      ClassGroup.mk K (nthRootHom R K n (unitsNDivisibleToNDivisible R K n u)) :=
  (rfl)

/-- **Every value of the `n`-th root class map is `n`-torsion.** The `n`-th power of the class of
the `n`-th root of `(u)` is the class of `(u)` itself, which is trivial because `(u)` is principal.
This is what lets a consumer cut the codomain down to the `n`-torsion of `ClassGroup R`. -/
-- Deliberately not `@[simp]`: `nthRootClass_apply` is already `simp`, so `simp` rewrites this
-- left-hand side before this lemma could fire, exactly as for `nthRootClass_eq_one_iff` below.
lemma nthRootClass_pow (n : ℕ) (u : unitsNDivisible R K n) : nthRootClass R K n u ^ n = 1 := by
  rw [nthRootClass_apply, ← map_pow, nthRootHom_pow, coe_unitsNDivisibleToNDivisible,
    ClassGroup.mk_toPrincipalIdeal]

/-- **The kernel of the `n`-th root class map.** The `n`-th root class of `u` is trivial exactly
when `u` is a unit of `R` times an `n`-th power in `Kˣ`. Passing to quotients, this is what will
give exactness at the middle term of `1 → Rˣ/(Rˣ)ⁿ → K(∅, n) → Cl(R)[n] → 1`; the quotients are not
formed here. -/
-- Deliberately not `@[simp]`: `nthRootClass_apply`, `nthRootHom_apply` and
-- `coe_unitsNDivisibleToNDivisible` are already `simp` lemmas, so `simp` rewrites this left-hand
-- side to `ClassGroup.mk K (nthRootFun R K n (toPrincipalIdeal R K ↑u)) = 1` before this lemma
-- could fire. Tagging it is a `simpNF` violation for exactly that reason.
lemma nthRootClass_eq_one_iff {n : ℕ} (u : unitsNDivisible R K n) :
    nthRootClass R K n u = 1 ↔
      ∃ (a : Rˣ) (w : Kˣ), Units.map (algebraMap R K : R →* K) a * w ^ n = (u : Kˣ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · -- Every multiplicity of `(u)` is divisible by `0`, hence zero, so `(u)` is already trivial and
    -- both sides hold.
    have hu1 : toPrincipalIdeal R K (u : Kˣ) = 1 :=
      units_eq_of_forall_count_eq R K fun v ↦ by
        rw [coe_toPrincipalIdeal, Units.val_one, count_one]
        exact zero_dvd_iff.mp (by simpa using mem_unitsNDivisible.mp u.2 v)
    obtain ⟨a, ha⟩ := (toPrincipalIdeal_eq_one_iff _).mp hu1
    have hroot : nthRootHom R K 0 (unitsNDivisibleToNDivisible R K 0 u) = 1 :=
      units_eq_of_forall_count_eq R K fun v ↦ by
        rw [count_nthRootHom, Nat.cast_zero, Int.ediv_zero, Units.val_one, count_one]
    exact iff_of_true (by rw [nthRootClass_apply, hroot, map_one])
      ⟨a, 1, by rw [pow_zero, mul_one, ha]⟩
  rw [nthRootClass_apply, ClassGroup.mk_eq_one_iff_exists]
  constructor
  · rintro ⟨w, hw⟩
    -- The `n`-th power of the generator `w` of the root generates `(u)`, so `u / wⁿ` is a unit.
    have hpow : toPrincipalIdeal R K (w ^ n) = toPrincipalIdeal R K (u : Kˣ) := by
      rw [map_pow, hw, nthRootHom_pow, coe_unitsNDivisibleToNDivisible]
    have h1 : toPrincipalIdeal R K ((u : Kˣ) * (w ^ n)⁻¹) = 1 := by
      rw [map_mul, map_inv, hpow, mul_inv_cancel]
    obtain ⟨a, ha⟩ := (toPrincipalIdeal_eq_one_iff _).mp h1
    exact ⟨a, w, by rw [ha]; group⟩
  · rintro ⟨a, w, hw⟩
    -- Conversely `w` generates the `n`-th root: its multiplicities are those of `(u)` over `n`.
    refine ⟨w, units_eq_of_forall_count_eq R K fun v ↦ ?_⟩
    have hcu : count K v ((toPrincipalIdeal R K (u : Kˣ) : (FractionalIdeal R⁰ K)ˣ) :
        FractionalIdeal R⁰ K) = n * count K v
          ((toPrincipalIdeal R K w : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) := by
      rw [← hw, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val,
        count_mul K v (Units.ne_zero _) (pow_ne_zero _ (Units.ne_zero _)), count_pow,
        (toPrincipalIdeal_eq_one_iff _).mpr ⟨a, rfl⟩, Units.val_one, count_one, zero_add]
    rw [count_nthRootHom, coe_unitsNDivisibleToNDivisible, hcu,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hn)]

end WeilDivisor

end AlgebraicGeometry

end TauCeti
