/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Orthogonality of the sine system on `[0, π]`

The functions `θ ↦ sin (k θ)`, for `k` a positive natural number, are pairwise orthogonal on the
interval `[0, π]`, each of square norm `π / 2`:

`∫₀^π sin (m θ) · sin (n θ) dθ = (π / 2) · δ_{mn}`.

This file proves that identity and its normalized form, in which the system `√(2/π) · sin (k ·)` is
orthonormal.

The proof is the product-to-sum identity `2 sin x sin y = cos (x - y) - cos (x + y)` followed by
the single computation `∫₀^π cos (k θ) dθ = 0` for a nonzero integer `k`, which is
`TauCeti.integral_cos_int_mul` below. That computation is elementary — the antiderivative
`sin (k θ) / k` vanishes at both endpoints because `sin` vanishes at every integer multiple of `π`
— and is obtained here from `intervalIntegral.mul_integral_comp_mul_left` and `integral_cos`.

The cosine counterpart of the orthogonality relation is already available in this repository, in
the Chebyshev vocabulary: `TauCeti.integral_chebyshevCosine_mul_chebyshevCosine_eq_ite`
(`TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Cosine/Transfer.lean`) records
`∫₀^π cos (m θ) cos (n θ) dθ` through the Chebyshev `T` measure. Nothing there covers the sine
system, whose square norm is `π / 2` in *every* degree — the cosine system is the one whose
degree-`0` mode has square norm `π` instead — so the two families are stated separately, and this
file is deliberately independent of the Chebyshev measure-theoretic development. In the other
direction the single-mode integral does serve that development: the two cosine-side single-mode
integrals `TauCeti.integral_chebyshevCosine_zero` and
`TauCeti.integral_chebyshevCosine_of_ne_zero` are read off `TauCeti.integral_cos_int_mul` below,
so the computation is performed once.

## Main results

* `TauCeti.integral_cos_int_mul`: `∫₀^π cos (k θ) dθ` is `π` when the integer `k` is zero and `0`
  otherwise.
* `TauCeti.integral_sin_nat_mul_mul_sin_nat_mul`: the orthogonality relation
  `∫₀^π sin (m θ) sin (n θ) dθ = (π / 2) · δ_{mn}` for all natural `m` and `n`, the degenerate
  mode `m = n = 0` — where the integrand vanishes identically — absorbed into the right-hand side
  rather than hypothesised away.
* `TauCeti.integral_sin_succ_mul_sin_succ`: the same relation indexed by the positive frequencies
  `m + 1`, where the degenerate mode is out of range and the right-hand side is a plain
  Kronecker delta, and
  `TauCeti.two_div_pi_mul_integral_sin_succ_mul_sin_succ`, its normalized restatement
  `(2/π) ∫₀^π sin ((m+1) θ) sin ((n+1) θ) dθ = δ_{mn}`.

## References

The sine system on `[0, π]` is the classical Fourier sine basis; see for instance
E. M. Stein, R. Shakarchi, *Fourier Analysis: An Introduction*, Princeton (2003), Chapter 2.

The normalized form is the identity that the engine case of
`TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md` reduces the character
orthonormality of `SU(2)` to; see
`TauCeti/RepresentationTheory/SU2/Weyl/Orthogonality.lean`.
-/

public section

namespace TauCeti

/-- `∫₀^π cos (k θ) dθ` for an integer `k`: it is `π` in degree `0`, and vanishes otherwise,
because the antiderivative `sin (k θ) / k` vanishes at both endpoints. -/
theorem integral_cos_int_mul (k : ℤ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos ((k : ℝ) * θ) = if k = 0 then Real.pi else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have h := intervalIntegral.mul_integral_comp_mul_left
      (f := Real.cos) (a := (0 : ℝ)) (b := Real.pi) (k : ℝ)
    rw [integral_cos, mul_zero, Real.sin_zero, sub_zero, Real.sin_int_mul_pi] at h
    rw [ite_eq_right hk]
    exact (mul_eq_zero.mp h).resolve_left hk'

/-- **Orthogonality of the sine system on `[0, π]`.** For natural numbers `m` and `n`,
`∫₀^π sin (m θ) sin (n θ) dθ` is `π / 2` when `m = n` is nonzero, and `0` otherwise.

The degenerate mode `m = n = 0` is absorbed into the right-hand side rather than hypothesised
away: there the integrand vanishes identically, so the integral is `0`, not `π / 2`. The condition
`m = n ∧ m ≠ 0` is symmetric in `m` and `n` up to logical equivalence, since under `m = n` the
requirements `m ≠ 0` and `n ≠ 0` coincide. -/
theorem integral_sin_nat_mul_mul_sin_nat_mul (m n : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin ((m : ℝ) * θ) * Real.sin ((n : ℝ) * θ)
      = if m = n ∧ m ≠ 0 then Real.pi / 2 else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · -- The degenerate mode: the integrand is identically `0`.
    simp
  rw [if_congr (and_iff_left hm) rfl rfl]
  -- Product to sum: `2 sin (m θ) sin (n θ) = cos ((m - n) θ) - cos ((m + n) θ)`.
  have hprod : ∀ θ : ℝ, Real.sin ((m : ℝ) * θ) * Real.sin ((n : ℝ) * θ)
      = Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ) / 2
        - Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * θ) / 2 := by
    intro θ
    have hsub : (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * θ = (m : ℝ) * θ - (n : ℝ) * θ := by
      push_cast; ring
    have hadd : (((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * θ = (m : ℝ) * θ + (n : ℝ) * θ := by
      push_cast; ring
    rw [hsub, hadd, Real.cos_sub, Real.cos_add]
    ring
  have hint : ∀ k : ℤ, IntervalIntegrable (fun θ : ℝ => Real.cos ((k : ℝ) * θ) / 2)
      MeasureTheory.volume 0 Real.pi := fun k =>
    (by fun_prop : Continuous fun θ : ℝ => Real.cos ((k : ℝ) * θ) / 2).intervalIntegrable _ _
  have hne : (m : ℤ) + (n : ℤ) ≠ 0 := by omega
  simp only [hprod]
  rw [intervalIntegral.integral_sub (hint _) (hint _), intervalIntegral.integral_div,
    intervalIntegral.integral_div, integral_cos_int_mul, integral_cos_int_mul, ite_eq_right hne]
  rcases eq_or_ne m n with rfl | hmn
  · rw [ite_eq_left (by omega : (m : ℤ) - (m : ℤ) = 0), ite_eq_left rfl]
    ring
  · rw [ite_eq_right (by omega : ¬((m : ℤ) - (n : ℤ) = 0)), ite_eq_right hmn]
    ring

/-- The sine system indexed by its positive frequencies `m + 1`, so that the degenerate mode of
`TauCeti.integral_sin_nat_mul_mul_sin_nat_mul` is out of range and the right-hand side is a plain
Kronecker delta: `∫₀^π sin ((m+1) θ) sin ((n+1) θ) dθ = (π / 2) · δ_{mn}`. -/
theorem integral_sin_succ_mul_sin_succ (m n : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)
      = if m = n then Real.pi / 2 else 0 := by
  have hshift : ∀ θ : ℝ, Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)
      = Real.sin (((m + 1 : ℕ) : ℝ) * θ) * Real.sin (((n + 1 : ℕ) : ℝ) * θ) := by
    intro θ; push_cast; ring
  simp only [hshift]
  rw [integral_sin_nat_mul_mul_sin_nat_mul (m + 1) (n + 1),
    if_congr (by omega : (m + 1 = n + 1 ∧ m + 1 ≠ 0) ↔ m = n) rfl rfl]

/-- **The sine system, normalized.** With the `2/π` normalization the family
`√(2/π) · sin ((m+1) ·)` is orthonormal on `[0, π]`:
`(2/π) ∫₀^π sin ((m+1) θ) sin ((n+1) θ) dθ = δ_{mn}`.

This is the form the character orthonormality of `SU(2)` reduces to, and
`TauCeti.SU2.character_symPower_orthonormal_torusExp`
(`TauCeti/RepresentationTheory/SU2/Weyl/Orthogonality.lean`) is proved by rewriting with it. -/
theorem two_div_pi_mul_integral_sin_succ_mul_sin_succ (m n : ℕ) :
    2 / Real.pi * ∫ θ in (0 : ℝ)..Real.pi,
        Real.sin (((m : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * θ)
      = if m = n then 1 else 0 := by
  rw [integral_sin_succ_mul_sin_succ]
  rcases eq_or_ne m n with rfl | hmn
  · rw [ite_eq_left rfl, ite_eq_left rfl]
    field_simp
  · rw [ite_eq_right hmn, ite_eq_right hmn]
    ring

end TauCeti
