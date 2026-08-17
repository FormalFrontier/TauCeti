/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Basic
public import TauCeti.NumberTheory.NumberField.Internal.QuadraticIntegralBasis
public import TauCeti.NumberTheory.NumberField.Discriminant.OfIntegralBasis
public import Mathlib.NumberTheory.NumberField.Norm
import TauCeti.RingTheory.Norm.Quadratic

/-!
# The ring of integers of a quadratic field

For a quadratic number field `K = ℚ(√d)` — presented by an algebraic integer `θ : 𝓞 K` with
`minpoly ℤ θ = X² - d` and `Algebra.adjoin ℚ {θ} = ⊤` — with `d` squarefree, the ring of integers
depends on `d mod 4`:

* `d ≢ 1 (mod 4)`: `𝓞 K = ℤ[θ]` and `NumberField.discr K = 4 * d`;
* `d ≡ 1 (mod 4)`: `𝓞 K = ℤ[ω]` with `ω = (1+θ)/2 = NumberField.halfGen`, and
  `NumberField.discr K = d`.

The content is the "no more integers" step: an algebraic integer `z` with `(z : K) = a + b·θ`
(`a, b : ℚ`) has `2a ∈ ℤ` and `a² - d·b² ∈ ℤ` (its trace and norm), whence `2a, 2b ∈ ℤ` (using that
`d` is squarefree), and the residue `a² ≡ d·b² (mod 4)` fixes the coordinates: `2a, 2b` are both
even when `d % 4 ≠ 1`, and are equal mod `2` (so `z ∈ ℤ + ℤ·ω`) when `d ≡ 1 (mod 4)`.

## Main results

* `NumberField.adjoin_gen_eq_top_of_mod_four_ne_one`: `𝓞 K = ℤ[θ]` for `d % 4 ≠ 1`.
* `NumberField.discr_eq_four_mul_of_mod_four_ne_one`: `discr K = 4d` for `d % 4 ≠ 1`.
* `NumberField.adjoin_halfGen_eq_top_of_mod_four_eq_one`: `𝓞 K = ℤ[(1+θ)/2]` for `d ≡ 1`.
* `NumberField.discr_eq_of_squarefree_of_mod_four_eq_one`: `discr K = d` for `d ≡ 1`.
-/

public section

open Polynomial NumberField Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- A rational number whose image in a number field is an algebraic integer is an integer. -/
private theorem exists_intCast_eq_of_algebraMap_mem_range {q : ℚ}
    (h : algebraMap ℚ K q ∈ (algebraMap (𝓞 K) K).range) : ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨w, hw⟩ := h
  have hint : IsIntegral ℤ q := by
    have hwint : IsIntegral ℤ (algebraMap ℚ K q) := by
      rw [← hw]; exact (IsIntegralClosure.isIntegral ℤ K w).algebraMap
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ K)
      (FaithfulSMul.algebraMap_injective ℚ K)).mp hwint
  exact (IsIntegrallyClosed.isIntegral_iff).mp hint

/-- If `d` is squarefree and `d · B²` is an integer for a rational `B`, then `B` is an integer:
the reduced denominator squared divides `d`, so is a unit. -/
private theorem den_eq_one_of_squarefree_mul_sq_isInt {d : ℤ} (hd : Squarefree d) {B : ℚ} {m : ℤ}
    (h : (d : ℚ) * B ^ 2 = (m : ℚ)) : B.den = 1 := by
  have hden : (B.den : ℚ) ≠ 0 := by exact_mod_cast B.den_ne_zero
  -- Clear denominators: `d * B.num² = m * B.den²` in `ℤ`.
  have hnumden : (B.num : ℚ) = B * (B.den : ℚ) := (div_eq_iff hden).mp (Rat.num_div_den B)
  have key : (d : ℚ) * (B.num : ℚ) ^ 2 = (m : ℚ) * (B.den : ℚ) ^ 2 := by
    have hsq : (B.num : ℚ) ^ 2 = B ^ 2 * (B.den : ℚ) ^ 2 := by rw [hnumden]; ring
    rw [hsq, ← mul_assoc, h]
  have keyZ : d * B.num ^ 2 = m * (B.den : ℤ) ^ 2 := by exact_mod_cast key
  -- `B.den² ∣ d`, using `gcd(B.num, B.den) = 1`.
  have hdvd : ((B.den : ℤ)) ^ 2 ∣ d * B.num ^ 2 := ⟨m, by rw [keyZ]; ring⟩
  have hcop : IsCoprime (B.num) ((B.den : ℤ)) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using B.reduced)
  have hcop2 : IsCoprime ((B.den : ℤ) ^ 2) (B.num ^ 2) := hcop.symm.pow
  have hdvdd : ((B.den : ℤ)) ^ 2 ∣ d := hcop2.dvd_of_dvd_mul_right hdvd
  have hunit : IsUnit ((B.den : ℤ)) := hd _ (by rw [← pow_two]; exact hdvdd)
  have hb1 : (B.den : ℤ) = 1 := by
    rcases Int.isUnit_iff.mp hunit with h1 | h1
    · exact h1
    · have hpos : (0 : ℤ) < (B.den : ℤ) := by exact_mod_cast B.pos
      omega
  exact_mod_cast hb1

variable {θ : 𝓞 K} {d : ℤ}

/-- **Trace and norm of a quadratic algebraic integer are integers.** For `z : 𝓞 K` with
`(z : K) = a + c·θ`, both `2a` (the trace) and `a² - d·c²` (the norm) are integers. -/
private theorem exists_intCast_coords (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {z : 𝓞 K} {a c : ℚ}
    (hz : (z : K) = algebraMap ℚ K a + algebraMap ℚ K c * (θ : K)) :
    (∃ A : ℤ, (A : ℚ) = 2 * a) ∧ (∃ N : ℤ, (N : ℚ) = a ^ 2 - (d : ℚ) * c ^ 2) := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨finrank_rat_eq_two hmin hgen⟩
  -- Trace: `Tr z = 2a` since `Tr θ = 0`.
  have htr : Algebra.trace ℚ K (z : K) = 2 * a := by
    rw [hz, Algebra.IsQuadraticExtension.trace_algebraMap_add_algebraMap_mul ℚ K c a (θ : K),
      trace_gen_eq_zero hmin]
    ring
  have hAex : ∃ A : ℤ, (A : ℚ) = 2 * a :=
    ⟨Algebra.trace ℤ (𝓞 K) z, by rw [Algebra.coe_trace_int, htr]⟩
  refine ⟨hAex, ?_⟩
  obtain ⟨A, hA⟩ := hAex
  -- Norm: `z` satisfies `z² - (2a)·z + (a²-dc²) = 0`, so `a²-dc² = (2a)·z - z² ∈ 𝓞 K ∩ ℚ = ℤ`.
  have hroot : (z : K) ^ 2 - algebraMap ℚ K (2 * a) * (z : K)
      + algebraMap ℚ K (a ^ 2 - (d : ℚ) * c ^ 2) = 0 := by
    have hθ : (θ : K) ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := coe_gen_sq_ratCast hmin
    rw [hz]
    simp only [map_mul, map_sub, map_pow, map_ofNat]
    linear_combination (algebraMap ℚ K c) ^ 2 * hθ
  have hmem : algebraMap ℚ K (a ^ 2 - (d : ℚ) * c ^ 2) ∈ (algebraMap (𝓞 K) K).range := by
    refine ⟨algebraMap ℤ (𝓞 K) A * z - z ^ 2, ?_⟩
    have heq : algebraMap ℚ K (a ^ 2 - (d : ℚ) * c ^ 2)
        = algebraMap ℤ K A * (z : K) - (z : K) ^ 2 := by
      have : algebraMap ℚ K (2 * a) = algebraMap ℤ K A := by
        rw [← hA, IsScalarTower.algebraMap_apply ℤ ℚ K]; norm_num
      rw [this] at hroot; linear_combination hroot
    rw [heq, map_sub, map_mul, map_pow, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K,
      RingOfIntegers.coe_eq_algebraMap]
  obtain ⟨N, hN⟩ := exists_intCast_eq_of_algebraMap_mem_range hmem
  exact ⟨N, hN⟩

/-- **Parity from the norm residue.** If `A² - d·B² = 4N` with `d ≡ 2, 3 (mod 4)`, then `A` and
`B` are both even: squares are `0, 1 (mod 4)`, so `A² ≡ d·B² (mod 4)` is impossible unless `B`
(hence `A`) is even. -/
private theorem two_dvd_of_sq_sub_mul_sq {A B N : ℤ} (hd4 : d % 4 = 2 ∨ d % 4 = 3)
    (h : A ^ 2 - d * B ^ 2 = 4 * N) : 2 ∣ A ∧ 2 ∣ B := by
  have key : ∀ x y w : ZMod 4, (w = 2 ∨ w = 3) → x ^ 2 - w * y ^ 2 = 0 →
      (x = 0 ∨ x = 2) ∧ (y = 0 ∨ y = 2) := by decide
  have hw : (d : ZMod 4) = 2 ∨ (d : ZMod 4) = 3 := by
    rcases hd4 with h1 | h1
    · left
      have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (d - 2) 4).mpr (by omega)
      push_cast at h0; exact sub_eq_zero.mp h0
    · right
      have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (d - 3) 4).mpr (by omega)
      push_cast at h0; exact sub_eq_zero.mp h0
  have heq0 : (A : ZMod 4) ^ 2 - (d : ZMod 4) * (B : ZMod 4) ^ 2 = 0 := by
    have hc : ((A ^ 2 - d * B ^ 2 : ℤ) : ZMod 4) = ((4 * N : ℤ) : ZMod 4) := by rw [h]
    push_cast at hc
    rw [hc, (by decide : (4 : ZMod 4) = 0)]; ring
  obtain ⟨hA, hB⟩ := key _ _ _ hw heq0
  refine ⟨?_, ?_⟩
  · rcases hA with h0 | h2
    · exact dvd_trans (by norm_num) ((ZMod.intCast_zmod_eq_zero_iff_dvd A 4).mp h0)
    · have h0 : ((A - 2 : ℤ) : ZMod 4) = 0 := by push_cast; rw [h2]; ring
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (A - 2) 4).mp h0; omega
  · rcases hB with h0 | h2
    · exact dvd_trans (by norm_num) ((ZMod.intCast_zmod_eq_zero_iff_dvd B 4).mp h0)
    · have h0 : ((B - 2 : ℤ) : ZMod 4) = 0 := by push_cast; rw [h2]; ring
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (B - 2) 4).mp h0; omega

/-- **Parity from the norm residue, `d ≡ 1 (mod 4)`.** If `A² - d·B² = 4N` then `A ≡ B (mod 2)`:
in `ZMod 4`, `A² = B²` forces `A - B ∈ {0, 2}`. -/
private theorem two_dvd_sub_of_sq_sub_mul_sq {A B N : ℤ} (hd4 : d % 4 = 1)
    (h : A ^ 2 - d * B ^ 2 = 4 * N) : 2 ∣ (A - B) := by
  have key : ∀ x y : ZMod 4, x ^ 2 - (1 : ZMod 4) * y ^ 2 = 0 → x - y = 0 ∨ x - y = 2 := by decide
  have hd1 : (d : ZMod 4) = 1 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (d - 1) 4).mpr (by omega)
    push_cast at h0; exact sub_eq_zero.mp h0
  have heq0 : (A : ZMod 4) ^ 2 - (1 : ZMod 4) * (B : ZMod 4) ^ 2 = 0 := by
    have hc : ((A ^ 2 - d * B ^ 2 : ℤ) : ZMod 4) = ((4 * N : ℤ) : ZMod 4) := by rw [h]
    push_cast at hc
    rw [← hd1, hc, (by decide : (4 : ZMod 4) = 0)]; ring
  rcases key _ _ heq0 with h0 | h2
  · have h0' : ((A - B : ℤ) : ZMod 4) = 0 := by push_cast; exact h0
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (A - B) 4).mp h0'; omega
  · have h0' : ((A - B - 2 : ℤ) : ZMod 4) = 0 := by push_cast; rw [h2]; ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (A - B - 2) 4).mp h0'; omega

/-- For `d ≡ 1 (mod 4)`, `ω = (1 + θ)/2` is an algebraic integer: it is a root of the monic
integer polynomial `X² - X - (d-1)/4`. -/
private theorem isIntegral_halfGen (hmin : minpoly ℤ θ = X ^ 2 - C d) (hd4 : d % 4 = 1) :
    IsIntegral ℤ ((1 + (θ : K)) / 2) := by
  obtain ⟨e, he⟩ : ∃ e : ℤ, d = 4 * e + 1 := ⟨d / 4, by omega⟩
  have ht : (θ : K) ^ 2 = algebraMap ℤ K d := coe_gen_sq hmin
  have hde : algebraMap ℤ K d = 4 * algebraMap ℤ K e + 1 := by
    rw [he]; simp only [map_add, map_mul, map_ofNat, map_one]
  refine ⟨X ^ 2 - X - C e, ?_, ?_⟩
  · monicity!
  · simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    field_simp
    linear_combination ht + hde
/-- **Shared half-integer coordinate/norm data.** For squarefree `d` and any `z : 𝓞 K`, the
`{1, θ}`-coordinates of `z` are half-integers: `z = (A/2)·1 + (B/2)·θ` with `A` its trace and `B`
twice its second coordinate, and the norm relation `A² - d·B² = 4N` holds for some `N : ℤ`. Both
congruence branches read off their integral basis from this by the appropriate parity argument
(`two_dvd_of_sq_sub_mul_sq` for `d ≢ 1`, `two_dvd_sub_of_sq_sub_mul_sq` for `d ≡ 1 (mod 4)`). -/
private theorem exists_half_int_coords (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) (z : 𝓞 K) :
    ∃ A B N : ℤ, (z : K) = algebraMap ℚ K ((A : ℚ) / 2) + algebraMap ℚ K ((B : ℚ) / 2) * (θ : K)
      ∧ A ^ 2 - d * B ^ 2 = 4 * N := by
  have hfr := finrank_rat_eq_two hmin hgen
  obtain ⟨bs, hbs, hb⟩ := Internal.exists_basis_eq_one_self_of_notMem_range_of_isIntegral
    hfr (gen_notMem_range hmin) θ.isIntegral_coe
  set a := bs.repr (z : K) 0 with ha
  set c := bs.repr (z : K) 1 with hc
  have hz : (z : K) = algebraMap ℚ K a + algebraMap ℚ K c * (θ : K) := by
    have hsum := bs.sum_repr (z : K)
    rw [Fin.sum_univ_two, hbs] at hsum
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hsum
    rw [← hsum, Algebra.smul_def, Algebra.smul_def, mul_one]
  obtain ⟨⟨A, hA⟩, ⟨N, hN⟩⟩ := exists_intCast_coords hmin hgen hz
  -- `2c ∈ ℤ` from squarefreeness (`d·(2c)² = A² - 4N ∈ ℤ`).
  have h2c : (d : ℚ) * (2 * c) ^ 2 = ((A ^ 2 - 4 * N : ℤ) : ℚ) := by push_cast; rw [hA, hN]; ring
  have hcden : (2 * c).den = 1 := den_eq_one_of_squarefree_mul_sq_isInt hsf h2c
  obtain ⟨B, hB⟩ : ∃ B : ℤ, (B : ℚ) = 2 * c :=
    ⟨(2 * c).num, by rw [← Rat.num_div_den (2 * c), hcden]; simp⟩
  have hABN : A ^ 2 - d * B ^ 2 = 4 * N := by
    have : ((A ^ 2 - d * B ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by push_cast; rw [hA, hB, hN]; ring
    exact_mod_cast this
  refine ⟨A, B, N, ?_, hABN⟩
  have hAa : (A : ℚ) / 2 = a := by rw [hA]; ring
  have hBc : (B : ℚ) / 2 = c := by rw [hB]; ring
  rw [hz, hAa, hBc]

/-- **`𝓞 K = ℤ[θ]` for `d ≢ 1 (mod 4)`: coordinates.** Every algebraic integer of `ℚ(√d)` is a
`ℤ`-combination `k + l·θ` — the "no more integers" step (see the module docstring). -/
private theorem exists_int_repr (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d)
    (hd4 : d % 4 = 2 ∨ d % 4 = 3) (z : 𝓞 K) : ∃ k l : ℤ, z = k • (1 : 𝓞 K) + l • θ := by
  obtain ⟨A, B, N, hz, hABN⟩ := exists_half_int_coords hmin hgen hsf z
  -- Parity: `A, B` both even, so the half-integer coordinates `A/2, B/2` are the integers `k, l`.
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := two_dvd_of_sq_sub_mul_sq hd4 hABN
  have hAk : (A : ℚ) / 2 = (k : ℚ) := by rw [hk]; push_cast; ring
  have hBl : (B : ℚ) / 2 = (l : ℚ) := by rw [hl]; push_cast; ring
  -- The coercion `𝓞 K → K` is injective, so compare in `K`, where `algebraMap ℚ K` of an integer
  -- cast and the `ℤ`-scalar action both reduce to the integer cast `↑· : ℤ → K`.
  refine ⟨k, l, RingOfIntegers.coe_injective ?_⟩
  change (z : K) = ((k • (1 : 𝓞 K) + l • θ) : K)
  rw [hz, hAk, hBl]
  push_cast [zsmul_eq_mul, map_intCast]
  ring

/-- For `d ≡ 1 (mod 4)`, the half-integer generator `ω = (1 + θ)/2 ∈ 𝓞 K`. -/
noncomputable def halfGen (hmin : minpoly ℤ θ = X ^ 2 - C d) (hd4 : d % 4 = 1) : 𝓞 K :=
  ⟨(1 + (θ : K)) / 2, isIntegral_halfGen hmin hd4⟩

/-- The half-integer generator coerces to `(1 + θ)/2` in `K`. -/
@[simp] theorem coe_halfGen (hmin : minpoly ℤ θ = X ^ 2 - C d) (hd4 : d % 4 = 1) :
    (halfGen hmin hd4 : K) = (1 + (θ : K)) / 2 := by
  unfold halfGen; rfl

/-- **`𝓞 K = ℤ[ω]` for `d ≡ 1 (mod 4)`: coordinates.** Every algebraic integer is a `ℤ`-combination
`k + l·ω` with `ω = (1+θ)/2`. Since `θ = 2ω - 1`, the half-integer coordinates `A/2, B/2` give
`z = (A-B)/2 · 1 + B · ω`, and `A ≡ B (mod 2)` (`d ≡ 1`) makes `(A-B)/2` an integer. -/
private theorem exists_int_repr_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) (hd4 : d % 4 = 1) (z : 𝓞 K) :
    ∃ k l : ℤ, z = k • (1 : 𝓞 K) + l • halfGen hmin hd4 := by
  obtain ⟨A, B, N, hz, hABN⟩ := exists_half_int_coords hmin hgen hsf z
  obtain ⟨m, hm⟩ := two_dvd_sub_of_sq_sub_mul_sq hd4 hABN
  have hmABK : (A : K) - (B : K) = 2 * (m : K) := by exact_mod_cast hm
  -- Compare in `K` (the coercion `𝓞 K → K` is injective); `ω = (1+θ)/2`, so `θ = 2ω - 1` and the
  -- half-integer coordinates combine to `(A-B)/2 · 1 + B · ω = m · 1 + B · ω`.
  refine ⟨m, B, RingOfIntegers.coe_injective ?_⟩
  change (z : K) = ((m • (1 : 𝓞 K) + B • halfGen hmin hd4) : K)
  rw [hz]
  push_cast [zsmul_eq_mul, map_intCast, map_div₀, map_ofNat, coe_halfGen]
  field_simp
  linear_combination hmABK

/-- **Spanning from a coordinate representation.** If `bs = ![1, g]` is a `ℚ`-basis of `K` whose
entries are algebraic integers and every `z : 𝓞 K` is an integer combination `k·1 + l·g`, then the
integral lifts `⟨bs i, _⟩` span `𝓞 K` over `ℤ`. -/
private theorem span_eq_top_of_int_repr {g : 𝓞 K} {bs : Basis (Fin 2) ℚ K}
    (hbs : (bs : Fin 2 → K) = ![1, (g : K)]) (hb : ∀ i, IsIntegral ℤ (bs i))
    (hrepr : ∀ z : 𝓞 K, ∃ k l : ℤ, z = k • (1 : 𝓞 K) + l • g) :
    Submodule.span ℤ (Set.range fun i => (⟨bs i, hb i⟩ : 𝓞 K)) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨k, l, hkl⟩ := hrepr z
  -- The integral lifts `⟨bs 0, _⟩, ⟨bs 1, _⟩` are `1` and `g`; check on the injective coercion to
  -- `K`, where `⟨bs i, _⟩` reduces definitionally to `bs i`.
  have e0 : (⟨bs 0, hb 0⟩ : 𝓞 K) = 1 := by
    apply RingOfIntegers.coe_injective; change bs 0 = (1 : K); rw [hbs]; rfl
  have e1 : (⟨bs 1, hb 1⟩ : 𝓞 K) = g := by
    apply RingOfIntegers.coe_injective; change bs 1 = (g : K); rw [hbs]; rfl
  have h1 : (1 : 𝓞 K) ∈ Submodule.span ℤ (Set.range fun i => (⟨bs i, hb i⟩ : 𝓞 K)) :=
    e0 ▸ Submodule.subset_span (Set.mem_range_self 0)
  have hg : g ∈ Submodule.span ℤ (Set.range fun i => (⟨bs i, hb i⟩ : 𝓞 K)) :=
    e1 ▸ Submodule.subset_span (Set.mem_range_self 1)
  rw [hkl]
  exact add_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ hg)

/-- **The ring of integers is `ℤ[(1+θ)/2]` when `d ≡ 1 (mod 4)`.** For squarefree `d` with
`d % 4 = 1`, the ring of integers of `ℚ(√d)` is generated over `ℤ` by `ω = (1+θ)/2`. -/
theorem adjoin_halfGen_eq_top_of_mod_four_eq_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) (hd4 : d % 4 = 1) :
    Algebra.adjoin ℤ {halfGen hmin hd4} = (⊤ : Subalgebra ℤ (𝓞 K)) := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨k, l, hkl⟩ := exists_int_repr_one hmin hgen hsf hd4 z
  rw [hkl]
  exact add_mem (zsmul_mem (one_mem _) k)
    (zsmul_mem (Algebra.subset_adjoin (Set.mem_singleton _)) l)

/-- **The discriminant of `ℚ(√d)` when `d ≡ 1 (mod 4)`.** For squarefree `d` with `d % 4 = 1`, the
field discriminant is `disc K = d` (the ring of integers is `ℤ[(1+θ)/2]`, whose `{1, ω}` basis has
discriminant `d`). -/
theorem discr_eq_of_squarefree_of_mod_four_eq_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) (hd4 : d % 4 = 1) :
    NumberField.discr K = d := by
  have hfr := finrank_rat_eq_two hmin hgen
  have hωnotmem : ((1 + (θ : K)) / 2) ∉ (algebraMap ℚ K).range := by
    rintro ⟨q, hq⟩
    exact gen_notMem_range hmin ⟨2 * q - 1, by rw [map_sub, map_mul, map_one, map_ofNat, hq]; ring⟩
  obtain ⟨bs, hbs, hb⟩ := Internal.exists_basis_eq_one_self_of_notMem_range_of_isIntegral
    hfr hωnotmem (isIntegral_halfGen hmin hd4)
  have hdd : Algebra.discr ℚ (bs : Fin 2 → K) = ((d : ℤ) : ℚ) := by
    rw [hbs]; exact discr_one_halfGen hmin hgen
  have hbs' : (bs : Fin 2 → K) = ![1, (halfGen hmin hd4 : K)] := by rw [coe_halfGen]; exact hbs
  have hspan := span_eq_top_of_int_repr hbs' hb (exists_int_repr_one hmin hgen hsf hd4)
  exact_mod_cast discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int bs hb hspan hdd

variable (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
  (hsf : Squarefree d) (hd4 : d % 4 ≠ 1)

include hsf hd4 in
/-- From squarefreeness and `d % 4 ≠ 1`, the residue is `2` or `3` (it is never `0`, as `4 ∤ d`). -/
private theorem mod_four_eq_two_or_three : d % 4 = 2 ∨ d % 4 = 3 := by
  have hnd4 : ¬ (4 : ℤ) ∣ d := fun h => by
    have h2 : IsUnit (2 : ℤ) := hsf 2 (by rw [(by norm_num : (2 : ℤ) * 2 = 4)]; exact h)
    rw [Int.isUnit_iff] at h2; omega
  omega

include hmin hgen hsf hd4 in
/-- **The ring of integers is `ℤ[θ]` when `d ≢ 1 (mod 4)`.** For squarefree `d` with `d % 4 ≠ 1`,
the ring of integers of `ℚ(√d)` is generated over `ℤ` by `θ`. -/
theorem adjoin_gen_eq_top_of_mod_four_ne_one :
    Algebra.adjoin ℤ {θ} = (⊤ : Subalgebra ℤ (𝓞 K)) := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨k, l, hkl⟩ := exists_int_repr hmin hgen hsf (mod_four_eq_two_or_three hsf hd4) z
  rw [hkl]
  exact add_mem (zsmul_mem (one_mem _) k)
    (zsmul_mem (Algebra.subset_adjoin (Set.mem_singleton θ)) l)

include hmin hgen hsf hd4 in
/-- **The discriminant of `ℚ(√d)` when `d ≢ 1 (mod 4)`.** For squarefree `d` with `d % 4 ≠ 1`
(equivalently `d ≡ 2, 3 (mod 4)`), the field discriminant is `disc K = 4d`. The ring of integers is
`ℤ[θ]` — see `adjoin_gen_eq_top_of_mod_four_ne_one`. -/
theorem discr_eq_four_mul_of_mod_four_ne_one : NumberField.discr K = 4 * d := by
  have hfr := finrank_rat_eq_two hmin hgen
  have hd4' := mod_four_eq_two_or_three hsf hd4
  obtain ⟨bs, hbs, hb⟩ := Internal.exists_basis_eq_one_self_of_notMem_range_of_isIntegral
    hfr (gen_notMem_range hmin) θ.isIntegral_coe
  -- Discriminant of `{1, θ}` is `4d` (`discr_one_gen`); `{1, θ}` spans `𝓞 K` over `ℤ`.
  have hdd : Algebra.discr ℚ (bs : Fin 2 → K) = ((4 * d : ℤ) : ℚ) := by
    rw [hbs]; exact discr_one_gen hmin hgen
  have hspan := span_eq_top_of_int_repr hbs hb (exists_int_repr hmin hgen hsf hd4')
  exact discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int bs hb hspan hdd

end NumberField
