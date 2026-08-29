/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Ramification and inertia counting criteria

This file records Galois consequences of the fundamental identity for primes in finite
extensions of domains. First, in a Galois extension the number of primes above a prime ideal is
maximal exactly when the common ramification index and inertia degree are both `1`. Second, the
cardinality of the inertia subgroup of a prime `P` upstairs is the ramification index of `P`
itself over the base, rather than the `Ideal.ramificationIdxIn` of the prime below it.

The rest of the file is about how inertia subgroups vary with the prime. Translating a prime by
`σ` conjugates its inertia subgroup by `σ`, since `τ • x - x ∈ σ • P` says exactly
`(σ⁻¹ τ σ) • y - y ∈ P` after the substitution `x = σ • y`. Because the Galois group acts
transitively on the primes above a fixed prime of the base, a *commutative* Galois group therefore
has one inertia subgroup per prime of the base, not one per prime upstairs. That uniformity is
what lets a statement about ramification in an intermediate field be tested at a single prime
upstairs.

## Main results

* `TauCeti.RamificationInertia.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup`:
  the domain/flat Galois counting criterion.
* `Ideal.card_inertia_eq_ramificationIdx`: the un-`In` form of the inertia count.
* `Ideal.mem_inertia_pointwise_smul_iff`: translation conjugates inertia subgroups.
* `Ideal.inertia_pointwise_smul`: for a commutative Galois group, translation leaves the inertia
  subgroup unchanged.
* `Ideal.inertia_eq_of_liesOver`: for a commutative Galois group, all the primes above a fixed
  prime of the base have the same inertia subgroup.

## Provenance

Built directly on Mathlib's Galois fundamental identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`), on its inertia count
(`Ideal.card_inertia_eq_ramificationIdxIn`), and on its transitivity statement
(`Ideal.exists_smul_eq_of_isGaloisGroup`).
-/

public section

open Ideal Module

namespace Ideal

/-- The cardinality of the inertia subgroup of `P` is the ramification index of `P` over `R`.
This is `Ideal.card_inertia_eq_ramificationIdxIn` stated with the ramification index of `P`
itself rather than with `Ideal.ramificationIdxIn` of the ideal below it. -/
theorem card_inertia_eq_ramificationIdx (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S] (G : Type*)
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S] (P : Ideal S) [P.IsPrime]
    [PerfectField (P.under R).ResidueField] :
    Nat.card (P.inertia G) = P.ramificationIdx R :=
  (card_inertia_eq_ramificationIdxIn (G := G) (P.under R) P).trans
    (ramificationIdxIn_eq_ramificationIdx (P.under R) P G)

end Ideal

namespace TauCeti.RamificationInertia

/-- In a finite flat Galois extension of domains, the number of primes over a prime ideal
equals the order of the Galois group iff the common ramification index and inertia degree are
both `1`. -/
theorem ncard_primesOver_eq_natCard_iff_of_isGaloisGroup {A B : Type*}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [Module.Flat A B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (P : Ideal A) [P.IsPrime] : (primesOver P B).ncard = Nat.card G ↔
      P.ramificationIdxIn B = 1 ∧ P.inertiaDegIn B = 1 := by
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn P B G
  have hG : 0 < Nat.card G := Nat.card_pos
  constructor
  · intro hn
    rw [hn] at h_main
    have hef : P.ramificationIdxIn B * P.inertiaDegIn B = 1 :=
      Nat.eq_of_mul_eq_mul_left hG (by rw [mul_one]; exact h_main)
    exact mul_eq_one.mp hef
  · rintro ⟨he, hf⟩
    simpa [he, hf] using h_main

end TauCeti.RamificationInertia

namespace Ideal

section Inertia

open scoped Pointwise

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]

/-- **Inertia is conjugated by the Galois action.** An element `τ` lies in the inertia subgroup of
the translated ideal `σ • P` exactly when its conjugate `σ⁻¹ τ σ` lies in the inertia subgroup
of `P`. -/
theorem mem_inertia_pointwise_smul_iff {σ τ : G} {P : Ideal S} :
    τ ∈ (σ • P).inertia G ↔ σ⁻¹ * τ * σ ∈ P.inertia G := by
  simp only [AddSubgroup.mem_inertia, Submodule.mem_toAddSubgroup]
  constructor
  · intro h y
    have hy := h (σ • y)
    rw [mem_pointwise_smul_iff_inv_smul_mem, smul_sub] at hy
    simpa only [mul_smul, inv_smul_smul] using hy
  · intro h x
    rw [mem_pointwise_smul_iff_inv_smul_mem, smul_sub]
    simpa only [mul_smul, smul_inv_smul] using h (σ⁻¹ • x)

variable (σ : G) (P : Ideal S)

open scoped IsMulCommutative in
/-- **A commutative Galois group has translation-invariant inertia subgroups.** -/
@[simp]
theorem inertia_pointwise_smul [IsMulCommutative G] :
    (σ • P).inertia G = P.inertia G := by
  ext τ
  rw [mem_inertia_pointwise_smul_iff]
  refine iff_of_eq (congrArg (· ∈ P.inertia G) ?_)
  rw [mul_comm σ⁻¹ τ, mul_assoc, inv_mul_cancel, mul_one]

end Inertia

section InertiaOver

open scoped Pointwise

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) (P Q : Ideal B)
  [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p] (G : Type*) [Group G] [Finite G]
  [IsMulCommutative G] [MulSemiringAction G B] [IsGaloisGroup G A B]

include p in
/-- **All the inertia subgroups over a fixed prime coincide, for a commutative Galois group.**
The Galois group acts transitively on the primes above `p`
(`Ideal.exists_smul_eq_of_isGaloisGroup`), and translation conjugates inertia subgroups
(`Ideal.mem_inertia_pointwise_smul_iff`), so commutativity makes them all equal. -/
theorem inertia_eq_of_liesOver : P.inertia G = Q.inertia G := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup p P Q G
  exact (inertia_pointwise_smul σ P).symm

end InertiaOver

end Ideal
