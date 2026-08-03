/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Basic
public import TauCeti.NumberTheory.NumberField.Internal.QuadraticIntegralBasis
public import TauCeti.NumberTheory.EffectiveBounds.Discriminant.Equality
public import Mathlib.NumberTheory.NumberField.Norm

/-!
# The ring of integers and discriminant of a quadratic field, non-`1 mod 4` case

For a quadratic number field `K = ℚ(√d)` — presented by an algebraic integer `θ : 𝓞 K` with
`minpoly ℤ θ = X² - d` and `Algebra.adjoin ℚ {θ} = ⊤` — with `d` squarefree and `d % 4 ≠ 1`, the
ring of integers is `ℤ[θ]` (`Algebra.adjoin ℤ {θ} = ⊤`) and `NumberField.discr K = 4 * d`.

The content is the "no more integers" step: an algebraic integer `z` with `(z : K) = a + b·θ`
(`a, b : ℚ`) has `2a ∈ ℤ` and `a² - d·b² ∈ ℤ` (its trace and norm), whence `2a, 2b ∈ ℤ` (using that
`d` is squarefree), and the residue `a² ≡ d·b² (mod 4)` forces `2a, 2b` both even when `d % 4 ≠ 1`
(equivalently `d ≡ 2, 3 (mod 4)`), i.e. `a, b ∈ ℤ`.

## Main results

* `TauCeti.NumberField.adjoin_gen_eq_top_of_emod_four_ne_one`: the ring of integers is `ℤ[θ]`.
* `TauCeti.NumberField.discr_eq_four_mul_of_emod_four_ne_one`: `discr K = 4d`.
-/

public section

open Polynomial NumberField Module

namespace TauCeti.NumberField

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
  have hfr := finrank_rat_eq_two hmin hgen
  -- Trace: `Tr z = 2a` since `Tr θ = 0`.
  have htr : Algebra.trace ℚ K (z : K) = 2 * a := by
    rw [hz, map_add, Algebra.trace_algebraMap, hfr, ← Algebra.smul_def, map_smul,
      trace_coe_eq_zero hmin hgen]
    simp
  have hAex : ∃ A : ℤ, (A : ℚ) = 2 * a :=
    ⟨Algebra.trace ℤ (𝓞 K) z, by rw [Algebra.coe_trace_int, htr]⟩
  refine ⟨hAex, ?_⟩
  obtain ⟨A, hA⟩ := hAex
  -- Norm: `z` satisfies `z² - (2a)·z + (a²-dc²) = 0`, so `a²-dc² = (2a)·z - z² ∈ 𝓞 K ∩ ℚ = ℤ`.
  have hroot : (z : K) ^ 2 - algebraMap ℚ K (2 * a) * (z : K)
      + algebraMap ℚ K (a ^ 2 - (d : ℚ) * c ^ 2) = 0 := by
    have hθ : (θ : K) ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := by
      rw [coe_gen_sq hmin, IsScalarTower.algebraMap_apply ℤ ℚ K]; norm_num
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
    rw [hc, show (4 : ZMod 4) = 0 from by decide]; ring
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

/-- The generator `θ` is not rational (`minpoly` has degree `2`), so `{1, θ}` is a `ℚ`-basis. -/
private theorem coe_notMem_range (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    (θ : K) ∉ (algebraMap ℚ K).range := by
  rintro ⟨q, hq⟩
  have hdvd : minpoly ℚ (algebraMap ℚ K q) ∣ (X - C q) := minpoly.dvd ℚ _ (by simp)
  have h1 : (minpoly ℚ (algebraMap ℚ K q)).natDegree ≤ 1 := by
    simpa [natDegree_X_sub_C] using Polynomial.natDegree_le_of_dvd hdvd (X_sub_C_ne_zero q)
  rw [hq, minpoly_rat_quadratic hmin, natDegree_X_pow_sub_C] at h1
  norm_num at h1

/-- **`𝓞 K = ℤ[θ]` for `d ≢ 1 (mod 4)`: coordinates.** Every algebraic integer of `ℚ(√d)` is a
`ℤ`-combination `k + l·θ` — the "no more integers" step (see the module docstring). -/
private theorem exists_int_repr (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d)
    (hd4 : d % 4 = 2 ∨ d % 4 = 3) (z : 𝓞 K) : ∃ k l : ℤ, z = k • (1 : 𝓞 K) + l • θ := by
  have hfr := finrank_rat_eq_two hmin hgen
  obtain ⟨bs, hbs, hb⟩ := Internal.exists_basis_eq_one_self_of_notMem_range_of_isIntegral
    hfr (coe_notMem_range hmin) θ.isIntegral_coe
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
  -- Parity: `A, B` both even, so `a = A/2`, `c = B/2` are integers.
  have hABN : A ^ 2 - d * B ^ 2 = 4 * N := by
    have : ((A ^ 2 - d * B ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by push_cast; rw [hA, hB, hN]; ring
    exact_mod_cast this
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := two_dvd_of_sq_sub_mul_sq hd4 hABN
  have hak : a = (k : ℚ) := by rw [hk] at hA; push_cast at hA; linarith
  have hcl : c = (l : ℚ) := by rw [hl] at hB; push_cast at hB; linarith
  -- The coercion `𝓞 K → K` is injective; the identity holds on coordinates, where `algebraMap ℚ K`
  -- of an integer cast and the `ℤ`-scalar action both reduce to the integer cast `↑· : ℤ → K`.
  refine ⟨k, l, RingOfIntegers.coe_injective ?_⟩
  change (z : K) = ((k • (1 : 𝓞 K) + l • θ) : K)
  rw [hz, hak, hcl]
  push_cast [zsmul_eq_mul, map_intCast]
  ring

variable (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
  (hsf : Squarefree d) (hd4 : d % 4 ≠ 1)

include hsf hd4 in
/-- From squarefreeness and `d % 4 ≠ 1`, the residue is `2` or `3` (it is never `0`, as `4 ∤ d`). -/
private theorem emod_four_eq_two_or_three : d % 4 = 2 ∨ d % 4 = 3 := by
  have hnd4 : ¬ (4 : ℤ) ∣ d := fun h => by
    have h2 : IsUnit (2 : ℤ) := hsf 2 (by rw [show (2 : ℤ) * 2 = 4 from by norm_num]; exact h)
    rw [Int.isUnit_iff] at h2; omega
  omega

include hmin hgen hsf hd4 in
/-- **The ring of integers is `ℤ[θ]` when `d ≢ 1 (mod 4)`.** For squarefree `d` with `d % 4 ≠ 1`,
the ring of integers of `ℚ(√d)` is generated over `ℤ` by `θ`. -/
theorem adjoin_gen_eq_top_of_emod_four_ne_one :
    Algebra.adjoin ℤ {θ} = (⊤ : Subalgebra ℤ (𝓞 K)) := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨k, l, hkl⟩ := exists_int_repr hmin hgen hsf (emod_four_eq_two_or_three hsf hd4) z
  rw [hkl]
  exact add_mem (zsmul_mem (one_mem _) k)
    (zsmul_mem (Algebra.subset_adjoin (Set.mem_singleton θ)) l)

include hmin hgen hsf hd4 in
/-- **The discriminant of `ℚ(√d)` when `d ≢ 1 (mod 4)`.** For squarefree `d` with `d % 4 ≠ 1`
(equivalently `d ≡ 2, 3 (mod 4)`), the field discriminant is `disc K = 4d`. The ring of integers is
`ℤ[θ]` — see `adjoin_gen_eq_top_of_emod_four_ne_one`. -/
theorem discr_eq_four_mul_of_emod_four_ne_one : NumberField.discr K = 4 * d := by
  have hfr := finrank_rat_eq_two hmin hgen
  have hd4' := emod_four_eq_two_or_three hsf hd4
  obtain ⟨bs, hbs, hb⟩ := Internal.exists_basis_eq_one_self_of_notMem_range_of_isIntegral
    hfr (coe_notMem_range hmin) θ.isIntegral_coe
  -- Discriminant of `{1, θ}` is `4d` (`discr_coe_one_gen`).
  have hdd : Algebra.discr ℚ (bs : Fin 2 → K) = ((4 * d : ℤ) : ℚ) := by
    rw [hbs]; exact discr_coe_one_gen hmin hgen
  -- Spanning: `{1, θ}` spans `𝓞 K` over `ℤ` (`exists_int_repr`).
  have hspan : Submodule.span ℤ (Set.range fun i => (⟨bs i, hb i⟩ : 𝓞 K)) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨k, l, hkl⟩ := exists_int_repr hmin hgen hsf hd4' z
    have hval0 : bs 0 = (1 : K) := by rw [hbs]; rfl
    have hval1 : bs 1 = (θ : K) := by rw [hbs]; rfl
    -- The basis vectors `⟨bs 0, _⟩`, `⟨bs 1, _⟩` of `𝓞 K` are `1` and `θ`; check on the coercion
    -- to `K` (injective), where `⟨bs i, _⟩` reduces definitionally to `bs i`.
    have e0 : (⟨bs 0, hb 0⟩ : 𝓞 K) = 1 := by
      apply RingOfIntegers.coe_injective; change bs 0 = (1 : K); exact hval0
    have e1 : (⟨bs 1, hb 1⟩ : 𝓞 K) = θ := by
      apply RingOfIntegers.coe_injective; change bs 1 = (θ : K); exact hval1
    have h1 : (1 : 𝓞 K) ∈ Submodule.span ℤ (Set.range fun i => (⟨bs i, hb i⟩ : 𝓞 K)) :=
      e0 ▸ Submodule.subset_span (Set.mem_range_self 0)
    have hθ : θ ∈ Submodule.span ℤ (Set.range fun i => (⟨bs i, hb i⟩ : 𝓞 K)) :=
      e1 ▸ Submodule.subset_span (Set.mem_range_self 1)
    rw [hkl]
    exact add_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ hθ)
  exact discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int bs hb hspan hdd

end TauCeti.NumberField
