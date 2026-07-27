/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.Int
import TauCeti.RingTheory.Ideal.LiesOver

/-!
# The Frobenius acts on square roots by the Legendre symbol

Let `S` be a commutative domain, `Q` an ideal of `S` lying over the rational prime `p ≠ 2`, and
`φ` an arithmetic Frobenius at `Q` (`AlgHom.IsArithFrobAt`, so `φ y ≡ y ^ p (mod Q)` for all
`y`). If `x ∈ S` is a square root of an integer `d` with `p ∤ d`, then

`φ x = legendreSym p d • x`.

Indeed `φ x ≡ x ^ p = (x²)^((p-1)/2) · x = d^((p-1)/2) · x ≡ (d/p) · x (mod Q)` by Euler's
criterion, while `(φ x)² = x²` forces `φ x = ± x` on the nose; the two signs are separated
modulo `Q` because `2x ∈ Q` would force `p ∣ 4d`. This is the local input for the Frobenius
form of the multiquadratic splitting law (Layer 1 of the multiquadratic roadmap): the Frobenius
of `ℚ(√d₁, …, √dₙ)` at `p` acts on each generator by the sign `(dᵢ/p)`.
`TauCeti.NumberTheory.NumberField.Frobenius` transports this computation to the Galois group of
a number field, and `TauCeti.NumberTheory.Multiquadratic.Frobenius` applies it to the
multiquadratic generators.

## Main results

* `TauCeti.AlgHom.IsArithFrobAt.apply_sqrt`: `φ x = legendreSym p d • x` for an arithmetic
  Frobenius `φ : S →ₐ[ℤ] S` at `Q` and `x² = d`.
* `TauCeti.IsArithFrobAt.smul_sqrt`: the same for a Frobenius element `σ` of a monoid acting
  on `S`.
-/

public section

open Ideal

namespace TauCeti

variable {S : Type*} [CommRing S] {p : ℕ} [Fact p.Prime] {d : ℤ}

omit [Fact p.Prime] in
/-- The residue cardinality entering `AlgHom.IsArithFrobAt` over the rational prime `p` is `p`
itself: for `Q` lying over `(p)`, `Nat.card (ℤ ⧸ Q ∩ ℤ) = p`. Internal plumbing for
`apply_sqrt`. -/
private theorem natCard_quotient_under (Q : Ideal S) [Q.LiesOver (span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  rw [← Ideal.LiesOver.over (P := Q) (p := span {(p : ℤ)})]
  exact Int.card_ideal_quot p

omit [Fact p.Prime] in
/-- The base Frobenius congruence over a rational prime: for an arithmetic Frobenius
`φ : S →ₐ[ℤ] S` at an ideal `Q` lying over `(p)`, `φ y ≡ y ^ p (mod Q)`, the exponent being `p`,
the cardinality of the base residue ring `ℤ ⧸ Q ∩ ℤ`. Internal plumbing for `apply_sqrt`. -/
private theorem AlgHom.IsArithFrobAt.sub_pow_mem {φ : S →ₐ[ℤ] S} (H : φ.IsArithFrobAt Q)
    [Q.LiesOver (span {(p : ℤ)})] (y : S) : φ y - y ^ p ∈ Q := by
  have h := H y
  rwa [natCard_quotient_under (p := p) Q] at h

variable [IsDomain S] {Q : Ideal S} {x : S}

omit [IsDomain S] in
/-- The **Frobenius congruence for a square root, refined by Euler's criterion**: for an
arithmetic Frobenius `φ : S →ₐ[ℤ] S` at `Q` lying over the odd rational prime `p`, if
`x² = d` then `φ x ≡ legendreSym p d • x (mod Q)`. Internal step of `apply_sqrt`. -/
private theorem AlgHom.IsArithFrobAt.sub_legendreSym_smul_mem {φ : S →ₐ[ℤ] S}
    (H : φ.IsArithFrobAt Q) [Q.LiesOver (span {(p : ℤ)})] (hodd : p ≠ 2)
    (hx : x ^ 2 = algebraMap ℤ S d) : φ x - legendreSym p d • x ∈ Q := by
  -- `p` is odd, so `p = 2·(p/2) + 1`; hence `x ^ p = (x²)^(p/2) · x = d^(p/2) · x`.
  have hp : p = 2 * (p / 2) + 1 := by
    have := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hodd); omega
  have hxp : x ^ p = algebraMap ℤ S (d ^ (p / 2)) * x := by
    conv_lhs => rw [hp]
    rw [pow_succ, pow_mul, hx, ← map_pow]
  -- Euler's criterion: `p ∣ d ^ (p / 2) - legendreSym p d`.
  have heuler : (p : ℤ) ∣ d ^ (p / 2) - legendreSym p d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero.mpr (legendreSym.eq_pow p d).symm
  -- Scaling Euler by `x`: `d^(p/2) · x ≡ legendreSym p d • x (mod Q)`.
  have hstep : algebraMap ℤ S (d ^ (p / 2)) * x - legendreSym p d • x ∈ Q := by
    have hfactor : algebraMap ℤ S (d ^ (p / 2)) * x - legendreSym p d • x =
        algebraMap ℤ S (d ^ (p / 2) - legendreSym p d) * x := by
      simp only [map_sub, sub_mul, zsmul_eq_mul, eq_intCast]
    rw [hfactor]
    exact Q.mul_mem_right x ((algebraMap_int_mem_iff_dvd_of_liesOver Q _).mpr heuler)
  -- Combine with the base congruence `φ x ≡ x ^ p (mod Q)`.
  have hsum := Q.add_mem (AlgHom.IsArithFrobAt.sub_pow_mem (p := p) H x) hstep
  rw [hxp] at hsum
  rwa [sub_add_sub_cancel] at hsum

omit [IsDomain S] in
/-- The two square roots of `d` are **distinct modulo `Q`**: if `x² = d`, the prime `p` is odd
and `p ∤ d`, and `Q` lies over `(p)`, then `x + x ∉ Q`. (Otherwise `(x + x)² = 4d ∈ Q` would
give `p ∣ 4d`, forcing `p = 2` or `p ∣ d`.) Internal step of `apply_sqrt`. -/
private theorem add_self_notMem (hodd : p ≠ 2) (hd : ¬ (p : ℤ) ∣ d)
    [Q.LiesOver (span {(p : ℤ)})] (hx : x ^ 2 = algebraMap ℤ S d) : x + x ∉ Q := by
  intro hmem
  -- `(x + x)² = 4d`, so `4d ∈ Q`, whence `p ∣ 4d` since `Q ∩ ℤ = (p)`.
  have h4d : algebraMap ℤ S (4 * d) ∈ Q := by
    have hsq4 : algebraMap ℤ S (4 * d) = (x + x) * (x + x) := by
      rw [map_mul, ← hx, eq_intCast]; push_cast; ring
    rw [hsq4]; exact Q.mul_mem_right _ hmem
  rcases (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_mul.mp
      ((algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp h4d) with h4 | hdd
  · -- `p ∣ 4 = 2²` forces `p = 2`, excluded.
    have h22 : p ∣ 2 ^ 2 := by simpa using (by exact_mod_cast h4 : p ∣ 4)
    exact hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow h22))
  · exact hd hdd

/-- **An arithmetic Frobenius acts on square roots by the Legendre symbol.** Let `S` be a
domain, `Q` an ideal of `S` over the odd rational prime `p`, and `φ : S →ₐ[ℤ] S` an arithmetic
Frobenius at `Q`. If `x² = d` for an integer `d` not divisible by `p`, then
`φ x = legendreSym p d • x`: the Frobenius fixes `√d` when `d` is a quadratic residue mod `p`
and negates it otherwise. (Primality of `Q` is not needed: the sign separation comes from `S`
being a domain and `Q ∩ ℤ = (p)`.) -/
theorem AlgHom.IsArithFrobAt.apply_sqrt {φ : S →ₐ[ℤ] S} (H : φ.IsArithFrobAt Q)
    [Q.LiesOver (span {(p : ℤ)})] (hodd : p ≠ 2) (hd : ¬ (p : ℤ) ∣ d)
    (hx : x ^ 2 = algebraMap ℤ S d) :
    φ x = legendreSym p d • x := by
  -- `φ x ≡ legendreSym p d • x (mod Q)` by the Frobenius congruence refined via Euler.
  have hkey : φ x - legendreSym p d • x ∈ Q :=
    AlgHom.IsArithFrobAt.sub_legendreSym_smul_mem H hodd hx
  -- `(φ x)² = x²`, so in the domain `S` the value `φ x` is `x` or `-x` on the nose.
  have hpm : φ x = x ∨ φ x = -x :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [← map_pow, hx, AlgHom.commutes])
  -- The target `legendreSym p d • x` is likewise `x` or `-x`, since the symbol is `±1`.
  have hgoal : legendreSym p d • x = x ∨ legendreSym p d • x = -x :=
    (legendreSym.eq_one_or_neg_one p (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd])).imp
      (fun h ↦ by rw [h, one_smul]) (fun h ↦ by rw [h, neg_smul, one_smul])
  -- When both signs agree the goal is immediate; when they disagree `x + x ∈ Q`, excluded.
  have hsep : x + x ∉ Q := add_self_notMem hodd hd hx
  rcases hpm with hx' | hx' <;> rcases hgoal with hg | hg
  · rw [hx', hg]
  · rw [hx', hg, sub_neg_eq_add] at hkey; exact absurd hkey hsep
  · rw [hx', hg] at hkey
    have hmem := Q.neg_mem hkey
    rw [neg_sub, sub_neg_eq_add] at hmem
    exact absurd hmem hsep
  · rw [hx', hg]

/-- **A Frobenius element acts on square roots by the Legendre symbol**, action form: if `σ : M`
is an arithmetic Frobenius at an ideal `Q` over the odd prime `p` and `x² = d` with `p ∤ d`,
then `σ • x = legendreSym p d • x`. Only a monoid action is needed. -/
theorem IsArithFrobAt.smul_sqrt {M : Type*} [Monoid M] [MulSemiringAction M S]
    [SMulCommClass M ℤ S] {σ : M} (H : _root_.IsArithFrobAt ℤ σ Q)
    [Q.LiesOver (span {(p : ℤ)})] (hodd : p ≠ 2) (hd : ¬ (p : ℤ) ∣ d)
    (hx : x ^ 2 = algebraMap ℤ S d) :
    σ • x = legendreSym p d • x := by
  simpa only [MulSemiringAction.toAlgHom_apply] using
    TauCeti.AlgHom.IsArithFrobAt.apply_sqrt H hodd hd hx

end TauCeti
