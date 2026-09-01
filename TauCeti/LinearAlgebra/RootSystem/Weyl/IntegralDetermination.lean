/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Alternating

public section

/-!
# An alternating element below a weight is determined by its dominant integral coefficients

An element of the integral group algebra `ℤ[M]` of the weight space of a root system is
*alternating* for the dot action (`TauCeti.IsDotAlternating`) when its coefficients transform by
the sign character. Such an element is determined by its coefficients on a fundamental domain of
the dot action, and `TauCeti.IsDotAlternating.eq_of_coeff_openDotDominantChamber_eq` says so with
the fundamental domain taken to be the open dominant chamber of the dot action. That statement
needs a `[LinearOrder R]` on the coefficient ring compatible with its ring structure
(`[IsStrictOrderedRing R]`), because a chamber is cut out by inequalities.

This file proves the same determination without any order on `R`, for an alternating element whose
support is **integral** — every simple coroot takes an integer value on it — and lies **below** a
fixed weight `lam`, in the sense that `lam - x` is a nonnegative integer combination of the simple
roots. The fundamental domain is then described arithmetically rather than by inequalities: a
weight `x` is taken to be *dominant integral* when every simple coroot takes a **natural** value
on it. Since `⟨ρ, αᵢ^∨⟩ = 1`, that is exactly the condition `⟨x + ρ, αᵢ^∨⟩ > 0` cutting out the
open dominant chamber of the dot action, read off arithmetically.

Both hypotheses are met by the object the Weyl character formula is about: for a finite-dimensional
highest weight module of weight `lam`, the product of the formal character with the Weyl
denominator is alternating and supported in `lam - Q⁺`, while the coefficient ring there is an
algebraically closed field, which carries no linear order making it a strictly ordered ring, so
that the chamber statement does not apply to it.

## Main results

* `TauCeti.IsDotAlternating.eq_zero_of_forall_coeff_dominantIntegral_eq_zero`: **an alternating
  element below `lam` whose dominant integral coefficients all vanish is zero.**
* `TauCeti.IsDotAlternating.eq_of_forall_coeff_dominantIntegral_eq`: **two alternating elements
  below `lam` agreeing at every dominant integral weight are equal.**

## The argument

Suppose `f.coeff x ≠ 0` and `x` is not dominant integral, so that some simple coroot takes a
negative integer value `z` on `x`.

* If `z = -1` then `x` lies on the wall of the simple reflection `sᵢ` for the dot action, and an
  alternating element vanishes there
  (`TauCeti.IsDotAlternating.coeff_eq_zero_of_coroot'_eq_neg_one`).
* Otherwise `z ≤ -2` and the dot reflection `sᵢ ⬝ x = x - (z + 1) αᵢ` *raises* `x` by the positive
  multiple `-(z+1)` of `αᵢ`. Its coefficient is `-f.coeff x`, again nonzero, so it too lies below
  `lam`, and the height of `lam - sᵢ ⬝ x` is smaller by `-(z+1) ≥ 1`.

Induction on that height — a natural number, because `lam - x` lies in the positive root cone
(`TauCeti.exists_natCast_eq_heightLinearMap_of_mem_posRootCone`) — therefore reaches a dominant
integral weight, where the hypothesis applies. No Weyl-group orbit and no finiteness of the Weyl
group enters: the raising is by a single simple reflection at a time.

## References

This supplies the order-free replacement, named as missing in
`TauCeti/Algebra/Lie/HighestWeight/Character.lean`, for the chamber step of the Weyl character
formula of Layer 6 of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

The raising induction is the one of `TauCeti/LinearAlgebra/RootSystem/DominantCone.lean`, run for
the dot action instead of the linear one.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §13.2 and
  §24.2.
-/

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : _root_.RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R] [Invertible (2 : R)]
  [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] {b : P.Base}
  {lam : M} {f g : AddMonoidAlgebra ℤ M}

namespace IsDotAlternating

/-- The raising induction behind
`TauCeti.IsDotAlternating.eq_zero_of_forall_coeff_dominantIntegral_eq_zero`, run on the height of
`lam - x`: a weight on which some simple coroot takes a value below `-1` is moved by the dot
reflection in that root to a weight of strictly smaller height and opposite coefficient. -/
private theorem coeff_eq_zero_of_heightLinearMap_eq (hf : IsDotAlternating P b f)
    (hcone : ∀ x : M, f.coeff x ≠ 0 → lam - x ∈ posRootCone P b)
    (hint : ∀ x : M, f.coeff x ≠ 0 → ∀ i ∈ b.support, ∃ z : ℤ, P.coroot' i x = (z : R))
    (hdom : ∀ x : M, (∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i x = (n : R)) → f.coeff x = 0) :
    ∀ n : ℕ, ∀ x : M, heightLinearMap P b (lam - x) = (n : R) → f.coeff x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx
    by_contra hne
    by_cases hd : ∀ i ∈ b.support, ∃ m : ℕ, P.coroot' i x = (m : R)
    · exact hne (hdom x hd)
    push Not at hd
    obtain ⟨i, hi, hnotnat⟩ := hd
    obtain ⟨z, hz⟩ := hint x hne i hi
    have hzneg : z < 0 := by
      by_contra hc
      push Not at hc
      exact hnotnat z.toNat
        (by rw [hz, ← Int.cast_natCast (R := R) z.toNat, Int.toNat_of_nonneg hc])
    rcases eq_or_lt_of_le (by omega : z ≤ -1) with hwall | hlt
    · refine hne (hf.coeff_eq_zero_of_coroot'_eq_neg_one hi ?_)
      rw [hz, hwall]
      norm_num
    -- Below the wall the dot reflection raises `x` strictly.
    set y := dotAction P b (_root_.RootPairing.weylGroup.ofIdx P i) x with hy
    have hyx : y = x - ((z : R) + 1) • P.root i := by
      rw [hy, dotAction_ofIdx P b hi, hz]
    have hyc : f.coeff y ≠ 0 := by
      rw [hy, hf.coeff_dotAction, weylSign_ofIdx]
      simpa using hne
    obtain ⟨m, hm⟩ := exists_natCast_eq_heightLinearMap_of_mem_posRootCone P b (hcone y hyc)
    -- The height drops by `-(z+1) ≥ 1`.
    have hheight : (m : R) = (n : R) + ((z : R) + 1) := by
      have hsub : lam - y = (lam - x) + ((z : R) + 1) • P.root i := by
        rw [hyx]; abel
      rw [← hm, hsub, map_add, map_smul, heightLinearMap_simpleRoot P b ⟨i, hi⟩, hx,
        smul_eq_mul, mul_one]
    have hcast : ((m : ℤ) : R) = (((n : ℤ) + z + 1 : ℤ) : R) := by push_cast; rw [hheight]; ring
    have hmn : (m : ℤ) < (n : ℤ) := by
      have := Int.cast_injective (α := R) hcast
      omega
    exact hyc (ih m (by exact_mod_cast hmn) y hm)

/-- **An alternating element below `lam` whose dominant integral coefficients all vanish is zero.**

The support is assumed to lie in `lam - Q⁺` and to be integral on the simple coroots; the
conclusion is that a coefficient at a weight with a negative simple coroot value is forced to
vanish as well, either because the weight lies on a wall of the dot action or because the dot
reflection carries it to a weight strictly closer to `lam`. -/
theorem eq_zero_of_forall_coeff_dominantIntegral_eq_zero (hf : IsDotAlternating P b f)
    (hcone : ∀ x : M, f.coeff x ≠ 0 → lam - x ∈ posRootCone P b)
    (hint : ∀ x : M, f.coeff x ≠ 0 → ∀ i ∈ b.support, ∃ z : ℤ, P.coroot' i x = (z : R))
    (hdom : ∀ x : M, (∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i x = (n : R)) → f.coeff x = 0) :
    f = 0 := by
  rw [← AddMonoidAlgebra.coeff_eq_zero]
  refine Finsupp.ext fun x ↦ ?_
  by_cases hne : f.coeff x = 0
  · simpa using hne
  obtain ⟨n, hn⟩ := exists_natCast_eq_heightLinearMap_of_mem_posRootCone P b (hcone x hne)
  exact absurd (hf.coeff_eq_zero_of_heightLinearMap_eq hcone hint hdom n x hn) hne

/-- **Two alternating elements below `lam` agreeing at every dominant integral weight are equal.**

This is the order-free counterpart of
`TauCeti.IsDotAlternating.eq_of_coeff_openDotDominantChamber_eq`: the dominant integral weights
replace the open dominant chamber of the dot action, at the cost of the two support hypotheses,
which the character of a highest weight module satisfies. -/
theorem eq_of_forall_coeff_dominantIntegral_eq (hf : IsDotAlternating P b f)
    (hg : IsDotAlternating P b g)
    (hconef : ∀ x : M, f.coeff x ≠ 0 → lam - x ∈ posRootCone P b)
    (hconeg : ∀ x : M, g.coeff x ≠ 0 → lam - x ∈ posRootCone P b)
    (hintf : ∀ x : M, f.coeff x ≠ 0 → ∀ i ∈ b.support, ∃ z : ℤ, P.coroot' i x = (z : R))
    (hintg : ∀ x : M, g.coeff x ≠ 0 → ∀ i ∈ b.support, ∃ z : ℤ, P.coroot' i x = (z : R))
    (hagree : ∀ x : M, (∀ i ∈ b.support, ∃ n : ℕ, P.coroot' i x = (n : R)) →
      f.coeff x = g.coeff x) :
    f = g := by
  have hsplit : ∀ x : M, (f - g).coeff x ≠ 0 → f.coeff x ≠ 0 ∨ g.coeff x ≠ 0 := by
    intro x hxne
    by_contra hc
    push Not at hc
    exact hxne (by simp [AddMonoidAlgebra.coeff_sub, hc.1, hc.2])
  rw [← sub_eq_zero]
  refine (hf.sub hg).eq_zero_of_forall_coeff_dominantIntegral_eq_zero (lam := lam)
    (fun x hx ↦ (hsplit x hx).elim (hconef x) (hconeg x))
    (fun x hx ↦ (hsplit x hx).elim (hintf x) (hintg x)) fun x hx ↦ ?_
  simp [AddMonoidAlgebra.coeff_sub, hagree x hx]

end IsDotAlternating

end TauCeti
