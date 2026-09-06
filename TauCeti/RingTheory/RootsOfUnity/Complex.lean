/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import TauCeti.RingTheory.RootsOfUnity.Adjoin

/-!
# The average of a multiset of complex roots of unity

A sum of `d` complex roots of unity has absolute value at most `d`. This file proves an arithmetic
sharpening: if the **average** of the summands happens to be an algebraic integer, then the sum is
either `0` or of absolute value exactly `d`, with nothing in between possible.

The proof is Kronecker's theorem. Fix a primitive `n`-th root of unity `ζ`; the number field
`ℚ(ζ)` contains every `n`-th root of unity, hence the sum `x` and its average `α = x / d`. A field
embedding of `ℚ(ζ)` into `ℂ` sends each summand to an `n`-th root of unity, so it sends `x` to a
sum of `d` complex numbers of modulus one; therefore `‖α‖ ≤ 1` at *every* embedding, not just the
inclusion we started with. A nonzero algebraic integer with that property is a root of unity
(`NumberField.Embeddings.pow_eq_one_of_norm_le_one`), so `‖α‖ = 1`.

The hypothesis on the average is what makes the statement bite: without it the bound `‖x‖ ≤ d` is
all there is, and intermediate absolute values really do occur, `1 + i` being a sum of two fourth
roots of unity of absolute value `√2`.

## Main statements

* `TauCeti.sum_eq_zero_or_norm_sum_eq_card_of_isIntegral`: a multiset of `n`-th roots of unity
  whose average is integral over `ℤ` has sum `0`, or a sum whose absolute value is its
  cardinality.
* `TauCeti.norm_map_multiset_sum_le_card`: the image in `ℂ` of a sum of `n`-th roots of unity has
  absolute value at most the number of summands, under any ring homomorphism.

## References

* Kronecker's theorem on algebraic integers in the closed unit disc, in Mathlib as
  `NumberField.Embeddings.pow_eq_one_of_norm_le_one`.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Theorem 3.8, where this is the
  Kronecker half of Burnside's vanishing theorem for character values, applied to the average once
  the arithmetic half has shown that average to be an algebraic integer.
-/

public section

namespace TauCeti

/-- A ring homomorphism into `ℂ` sends a multiset of `n`-th roots of unity to complex numbers of
modulus one, so it sends their sum to a complex number of modulus at most the cardinality. -/
theorem norm_map_multiset_sum_le_card {K : Type*} [Semiring K] {n : ℕ} (hn : n ≠ 0)
    {t : Multiset K} (ht : ∀ ν ∈ t, ν ^ n = 1) (φ : K →+* ℂ) :
    ‖φ t.sum‖ ≤ Multiset.card t := by
  have hmap : (t.map φ).map (‖·‖) = t.map fun _ => (1 : ℝ) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun ν hν =>
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, ht ν hν, map_one]) hn
  calc ‖φ t.sum‖ = ‖(t.map φ).sum‖ := by rw [map_multiset_sum]
    _ ≤ ((t.map φ).map (‖·‖)).sum := norm_multiset_sum_le _
    _ = Multiset.card t := by rw [hmap]; simp

/-- **The average of a multiset of roots of unity is `0` or of modulus one, once it is an
algebraic integer.** If every element of a multiset `s` of complex numbers is an `n`-th root of
unity and the average `s.sum / #s` is integral over `ℤ`, then either `s.sum = 0` or
`‖s.sum‖ = #s`.

This is Kronecker's theorem applied inside `ℚ(ζ)` for `ζ` a primitive `n`-th root of unity: the
average is an algebraic integer all of whose conjugates lie in the closed unit disc, because each
conjugate is again an average of `#s` complex numbers of modulus one. -/
theorem sum_eq_zero_or_norm_sum_eq_card_of_isIntegral {n : ℕ} (hn : n ≠ 0) {s : Multiset ℂ}
    (hs : ∀ μ ∈ s, μ ^ n = 1) (hint : IsIntegral ℤ (s.sum / (Multiset.card s : ℂ))) :
    s.sum = 0 ∨ ‖s.sum‖ = Multiset.card s := by
  have : NeZero n := ⟨hn⟩
  rcases Nat.eq_zero_or_pos (Multiset.card s) with hcard | hcard
  · exact Or.inl (by rw [Multiset.card_eq_zero.mp hcard, Multiset.sum_zero])
  have hd : ((Multiset.card s : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hcard.ne'
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ n := ⟨_, Complex.isPrimitiveRoot_exp n hn⟩
  set K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional
      ((hζ.isIntegral (Nat.pos_of_ne_zero hn)).tower_top (A := ℚ))
  have : NumberField K := ⟨⟩
  -- `s`, read inside `K`
  set t : Multiset K :=
    s.attach.map fun p => (⟨p.1, hζ.mem_adjoin_of_pow_eq_one (hs p.1 p.2)⟩ : K) with htdef
  have hcoe : t.map (algebraMap K ℂ) = s := by
    rw [htdef, Multiset.map_map]
    exact Multiset.attach_map_val s
  have hcardt : Multiset.card t = Multiset.card s := by
    rw [htdef, Multiset.card_map, Multiset.card_attach]
  have hroot : ∀ ν ∈ t, ν ^ n = 1 := by
    intro ν hν
    rw [htdef, Multiset.mem_map] at hν
    obtain ⟨p, -, rfl⟩ := hν
    exact Subtype.ext (by simpa using hs p.1 p.2)
  have hsum : algebraMap K ℂ t.sum = s.sum := by rw [map_multiset_sum, hcoe]
  -- the average, read inside `K`
  set α : K := t.sum / (Multiset.card s : K) with hαdef
  have hαcoe : algebraMap K ℂ α = s.sum / (Multiset.card s : ℂ) := by
    rw [hαdef, map_div₀, hsum, map_natCast]
  have hαint : IsIntegral ℤ α :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := K) (B := ℂ)).1 (hαcoe ▸ hint)
  have hbound : ∀ φ : K →+* ℂ, ‖φ α‖ ≤ 1 := by
    intro φ
    rw [hαdef, map_div₀, map_natCast, norm_div, Complex.norm_natCast,
      div_le_one (by positivity)]
    exact hcardt ▸ norm_map_multiset_sum_le_card hn hroot φ
  rcases eq_or_ne α 0 with hα0 | hα0
  · refine Or.inl ?_
    rw [hα0, map_zero, eq_comm, div_eq_zero_iff] at hαcoe
    exact hαcoe.resolve_right hd
  · refine Or.inr ?_
    obtain ⟨m, hm, hpow⟩ :=
      NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hα0 hαint hbound
    have hnorm : ‖algebraMap K ℂ α‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hpow, map_one]) hm.ne'
    rw [hαcoe, norm_div, Complex.norm_natCast, div_eq_one_iff_eq (by positivity)] at hnorm
    exact hnorm

end TauCeti
