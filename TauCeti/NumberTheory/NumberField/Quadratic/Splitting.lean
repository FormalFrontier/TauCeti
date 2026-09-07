/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.RingTheory.Discriminant
public import TauCeti.NumberTheory.NumberField.SplitsCompletely
import Mathlib.Algebra.CharP.Two
import TauCeti.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.Algebra.Polynomial.SpecificDegree
public import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers

/-!
# The prime-splitting law for a quadratic field

For a quadratic number field `K = ℚ(√d)` — given as `K` generated over `ℚ` by an algebraic
integer `θ` whose minimal polynomial over `ℤ` is `X² - d` — and an odd prime `p` not dividing
`d`, the prime `p` splits completely in `K` (there are `[K:ℚ] = 2` primes of `𝓞 K` above it) if
and only if `d` is a quadratic residue mod `p`, i.e. `legendreSym p d = 1`.

The proof routes through Mathlib's number-field Kummer–Dedekind theorem
(`primesOverSpanEquivMonicFactorsMod`): the primes above `p` biject with the monic irreducible
factors of `X² - d` mod `p`, of which there are two exactly when `d` is a square mod `p`. The
required conductor hypothesis `p ∤ exponent θ` follows because the conductor exponent divides the
power-basis discriminant `4d`, which is coprime to the odd prime `p ∤ d`.

This is the base case (`n = 1`) of the multiquadratic prime-splitting law (Layer 1 of the
multiquadratic roadmap).

The splitting law is then read off at the level of ideals: a completely split rational prime is
the absolute norm of a prime of `𝓞 K`
(`Ideal.absNorm_eq_of_ncard_primesOver_eq_finrank`). That is the shape in which the
splitting law enters genus theory, where an ideal of norm `p` is what carries the prescribed
values of the genus characters.

The prime `2` is handled separately, for squarefree `d ≡ 1 (mod 4)`, where `2` is unramified: the
number of primes of `𝓞 K` above `2` is `2` when `d ≡ 1 (mod 8)` and `1` when `d ≡ 5 (mod 8)`. The
generator `θ` with `θ² = d` is useless here, since `2` divides its conductor exponent; the law is
read off instead from the half-integer generator `ω = (1 + θ)/2`, which for squarefree `d` generates
`𝓞 K` over `ℤ` (`adjoin_halfGen_eq_top_of_mod_four_eq_one`) and has minimal polynomial
`X² - X - (d - 1)/4` (`minpoly_halfGen`).

## Main results

* `NumberField.ncard_primesOver_quadratic_iff`: the quadratic splitting law at an odd prime.
* `NumberField.exists_isPrime_and_absNorm_eq_of_legendreSym_eq_one`: an odd prime `p` with
  `legendreSym p d = 1` is the absolute norm of a prime ideal of `𝓞 K`.
* `NumberField.ncard_primesOver_two_of_mod_four_eq_one`: for squarefree `d ≡ 1 (mod 4)`, the
  number of primes above `2` is `if d % 8 = 1 then 2 else 1`, and
  `NumberField.ncard_primesOver_two_of_minpoly_eq_X_sq_sub_X_add` is the same count for the field
  presented by the half-integer generator `(1 + √d)/2`; with the corollaries
  `NumberField.ncard_primesOver_two_eq_finrank_iff_of_mod_four_eq_one` (`2` splits iff
  `d ≡ 1 (mod 8)`) and `NumberField.ncard_primesOver_two_eq_one_iff_of_mod_four_eq_one` (`2` is
  inert iff `d ≡ 5 (mod 8)`).

## Provenance

The conductor/discriminant and Kummer–Dedekind toolchain is from Mathlib; this assembly is new,
prepared for the multiquadratic roadmap of the Tau Ceti library. The dyadic case, stated for the
half-integer generator with minimal polynomial `X² − X + C ((1 − d)/4)`, follows the presentation
in `TauCetiRoadmap/NumberFieldArithmetic/README.md`.
-/

public section

open Polynomial NumberField Ideal Module RingOfIntegers UniqueFactorizationMonoid

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]


/-- The power-basis discriminant `4d` lies in the conductor: for `θ` generating `K` over `ℚ`
with minimal polynomial `X² - d` over `ℤ`, the image of `4 * d` in `𝓞 K` belongs to
`conductor ℤ θ`. This is the crux of the conductor bound, since it forces the conductor
exponent of `θ` to divide `4d`. -/
private theorem algebraMap_four_mul_mem_conductor {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (algebraMap ℤ (𝓞 K)) (4 * d) ∈ conductor ℤ θ := by
  rw [mem_conductor_iff]
  intro b
  have hintθℤ : IsIntegral ℤ (θ : K) := θ.isIntegral_coe
  have hintθℚ : IsIntegral ℚ (θ : K) := hintθℤ.tower_top
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop' hintθℚ hgen
  have hgenθ : pb.gen = (θ : K) := PowerBasis.ofAdjoinEqTop'_gen hintθℚ hgen
  have hmin' : minpoly ℚ pb.gen = X ^ 2 - C ((d : ℤ) : ℚ) := by
    rw [hgenθ]; exact minpoly_rat_quadratic hmin
  have hdim : pb.dim = 2 := by
    rw [← pb.natDegree_minpoly, hmin', natDegree_X_pow_sub_C]
  have hdiscr : Algebra.discr ℚ pb.basis = ((4 * d : ℤ) : ℚ) := by
    -- `pb.basis` is `{1, θ}` reindexed along `pb.dim = 2`, so its discriminant is `discr_one_gen`.
    have hb2 : ⇑pb.basis ∘ ⇑(finCongr hdim).symm = ![(1 : K), (θ : K)] := by
      funext j; fin_cases j <;> simp [hgenθ]
    rw [← Algebra.discr_reindex ℚ pb.basis (finCongr hdim), hb2, discr_one_gen hmin hgen]
  have hgenint : IsIntegral ℤ pb.gen := hgenθ ▸ hintθℤ
  have key := Algebra.discr_mul_isIntegral_mem_adjoin (R := ℤ) (K := ℚ) (L := K) (B := pb)
    hgenint (z := (b : K)) (b.isIntegral_coe)
  rw [hdiscr, hgenθ] at key
  -- `key : ((4d:ℤ):ℚ) • (b:K) ∈ adjoin ℤ {(θ:K)}`; bridge back into `𝓞 K`.
  let f : (𝓞 K) →ₐ[ℤ] K := IsScalarTower.toAlgHom ℤ (𝓞 K) K
  have hfθ : f θ = (θ : K) := by rw [IsScalarTower.coe_toAlgHom']
  have hAmap : (Algebra.adjoin ℤ {θ}).map f = Algebra.adjoin ℤ {(θ : K)} := by
    rw [← Algebra.adjoin_image, Set.image_singleton, hfθ]
  have himg : ((4 * d : ℤ) : ℚ) • (b : K) = f (algebraMap ℤ (𝓞 K) (4 * d) * b) := by
    have key1 : f (algebraMap ℤ (𝓞 K) (4 * d) * b) = algebraMap ℤ K (4 * d) * (b : K) := by
      rw [map_mul, IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
    rw [key1, Algebra.smul_def]
    simp
  rw [himg, ← hAmap] at key
  obtain ⟨y, hyA, hyeq⟩ := key
  rwa [(FaithfulSMul.algebraMap_injective (𝓞 K) K) hyeq] at hyA

/-- **Conductor bound.** If `θ` generates `K` and has minimal polynomial `X² - d`, then an odd
prime not dividing `d` does not divide the conductor exponent of `θ`. -/
private theorem not_dvd_exponent_of_minpoly_quadratic {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (hcop : ¬ (p : ℤ) ∣ d) : ¬ p ∣ exponent θ := by
  -- Key bound: `4d ∈ conductor ℤ θ`, hence the conductor exponent divides `4d`.
  have hmem := algebraMap_four_mul_mem_conductor hmin hgen
  have hdvd : exponent θ ∣ (4 * d).natAbs := by
    have hmem' : (4 * d : ℤ) ∈ under ℤ (conductor ℤ θ) := Ideal.mem_comap.mpr hmem
    rw [← Int.ideal_span_absNorm_eq_self (under ℤ (conductor ℤ θ)),
      Ideal.mem_span_singleton] at hmem'
    have h : absNorm (under ℤ (conductor ℤ θ)) ∣ (4 * d).natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hmem'
    exact h
  -- `p` odd and `p ∤ d` ⟹ `p ∤ 4d` ⟹ `p ∤ exponent`.
  intro hp
  have hp4d : (p : ℤ) ∣ 4 * d := by
    have h := Int.natCast_dvd_natCast.mpr (hp.trans hdvd)
    rwa [Int.dvd_natAbs] at h
  rcases (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_mul.mp hp4d with h4 | hd
  · have hp4 : p ∣ 4 := by exact_mod_cast h4
    have hp2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow (by simpa using hp4 : p ∣ 2 ^ 2)
    exact hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hp2)
  · exact hcop hd

omit [NumberField K] in
/-- **Factor count mod p.** `X² - d` has two monic irreducible factors mod `p` (for `p` odd,
`p ∤ d`) iff `d` is a square mod `p`. -/
private theorem card_monicFactorsMod_quadratic_iff {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (hcop : ¬ (p : ℤ) ∣ d) : (monicFactorsMod θ p).card = 2 ↔ legendreSym p d = 1 := by
  classical
  have hc0 : (d : ZMod p) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hcop
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hnd : ¬ (p ∣ 2) := fun h => hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
    intro h0
    exact hnd ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by exact_mod_cast h0))
  have hmap : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) = X ^ 2 - C (d : ZMod p) := by
    rw [hmin]; simp [Polynomial.map_sub, Polynomial.map_pow]
  rw [legendreSym.eq_one_iff p hc0]
  simp only [monicFactorsMod, hmap]
  constructor
  · intro hcard
    by_contra hns
    have hirr : Irreducible (X ^ 2 - C (d : ZMod p)) :=
      (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
        (fun b hb => hns ⟨b, by rw [← hb]; ring⟩)
    rw [normalizedFactors_irreducible hirr] at hcard
    simp at hcard
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := fun h => hc0 (by rw [ha, h]; ring)
    have hane : a ≠ -a := by
      intro h
      have h2a : (2 : ZMod p) * a = 0 := by linear_combination h
      exact ha0 ((mul_eq_zero.mp h2a).resolve_left h2)
    have hfac : X ^ 2 - C (d : ZMod p) = (X - C a) * (X - C (-a)) := by
      rw [ha]; simp only [map_mul, map_neg]; ring
    rw [hfac, normalizedFactors_mul (X_sub_C_ne_zero a) (X_sub_C_ne_zero (-a)),
      normalizedFactors_irreducible (irreducible_X_sub_C a),
      normalizedFactors_irreducible (irreducible_X_sub_C (-a)),
      (monic_X_sub_C a).normalize_eq_self, (monic_X_sub_C (-a)).normalize_eq_self,
      Multiset.toFinset_add, Multiset.toFinset_singleton, Multiset.toFinset_singleton,
      Finset.card_union_of_disjoint (Finset.disjoint_singleton.mpr (by
        rw [Ne, sub_right_inj, C_inj]; exact hane))]
    simp

/-- **The quadratic splitting law.** For `K = ℚ(√d)` (`θ` a square root of the integer `d`
generating `K`) and an odd prime `p ∤ d`, `p` splits completely in `K` iff `d` is a quadratic
residue mod `p`. This is the `n = 1` case of the multiquadratic prime-splitting law. -/
theorem ncard_primesOver_quadratic_iff {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hcop : ¬ (p : ℤ) ∣ d) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K ↔ legendreSym p d = 1 := by
  have hp := not_dvd_exponent_of_minpoly_quadratic hmin hgen hodd hcop
  rw [ncard_primesOver_eq_card_monicFactorsMod θ hp, finrank_rat_eq_two hmin hgen]
  exact card_monicFactorsMod_quadratic_iff hmin hodd hcop

/-- **A split prime is an ideal norm.** For `K = ℚ(√d)` and an odd prime `p` for which `d` is a
quadratic residue mod `p` — that is, one which splits in `K` by
`ncard_primesOver_quadratic_iff` — there is a prime ideal of `𝓞 K` of absolute norm `p`. This is the
form in which the splitting law feeds genus theory: the genus characters are computed on ideals
through their absolute norms. -/
theorem exists_isPrime_and_absNorm_eq_of_legendreSym_eq_one {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hleg : legendreSym p d = 1) :
    ∃ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime ∧ 𝔭.LiesOver (span {(p : ℤ)}) ∧ Ideal.absNorm 𝔭 = p := by
  -- A nonzero value of the Legendre symbol already records that `p ∤ d`.
  have hcop : ¬ (p : ℤ) ∣ d := by
    intro hdvd
    rw [(legendreSym.eq_zero_iff p d).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr hdvd)]
      at hleg
    exact zero_ne_one hleg
  have hsplit : ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)).ncard = finrank ℚ K :=
    (ncard_primesOver_quadratic_iff hmin hgen hodd hcop).mpr hleg
  obtain ⟨⟨𝔮, h𝔮, hlo⟩⟩ :=
    (inferInstance : Nonempty ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)))
  -- `h𝔮` and `hlo` are the prime and lies-over hypotheses of the norm computation; pass them
  -- explicitly rather than installing them as anonymous local instances.
  exact ⟨𝔮, h𝔮, hlo,
    @Ideal.absNorm_eq_of_ncard_primesOver_eq_finrank K _ _ p _ 𝔮 h𝔮 hlo hsplit⟩

/-! ### The prime `2` for `d ≡ 1 (mod 4)` -/

/-- **Factor count mod `2`.** The minimal polynomial `X² - X - c` of the half-integer generator
has two monic irreducible factors mod `2` when `c = (d - 1)/4` is even, i.e. `d ≡ 1 (mod 8)`, and
one when `c` is odd. -/
private theorem card_monicFactorsMod_halfGen_two {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hd4 : d % 4 = 1) :
    (monicFactorsMod (halfGen hmin hd4) 2).card = if d % 8 = 1 then 2 else 1 := by
  classical
  set c : ℤ := (d - 1) / 4 with hc
  have h4 : 4 * c = d - 1 := by omega
  have hmap : (minpoly ℤ (halfGen hmin hd4)).map (Int.castRingHom (ZMod 2)) =
      X ^ 2 + X + C (c : ZMod 2) := by
    rw [minpoly_halfGen hmin hd4, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, eq_intCast, sub_eq_add_neg, sub_eq_add_neg,
      CharTwo.neg_eq, CharTwo.neg_eq]
  simp only [monicFactorsMod, hmap]
  by_cases hd8 : d % 8 = 1
  · -- `c` is even: `X² + X = (X - 0)(X - 1)`, two distinct linear factors.
    have hc0 : (c : ZMod 2) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
    have hfac : (X ^ 2 + X + C (c : ZMod 2) : (ZMod 2)[X]) = (X - C 0) * (X - C 1) := by
      rw [hc0, C_0, add_zero, sub_zero, C_1, CharTwo.sub_eq_add]; ring
    have h0 : normalizedFactors (X - C (0 : ZMod 2)) = {X - C 0} := by
      rw [normalizedFactors_irreducible (irreducible_X_sub_C _),
        (monic_X_sub_C _).normalize_eq_self]
    have h1 : normalizedFactors (X - C (1 : ZMod 2)) = {X - C 1} := by
      rw [normalizedFactors_irreducible (irreducible_X_sub_C _),
        (monic_X_sub_C _).normalize_eq_self]
    have hne : (X - C (0 : ZMod 2) : (ZMod 2)[X]) ≠ X - C 1 := by
      rw [Ne, sub_right_inj, C_inj]; exact zero_ne_one
    rw [ite_eq_left hd8, hfac, normalizedFactors_mul (X_sub_C_ne_zero 0) (X_sub_C_ne_zero 1),
      h0, h1]
    simp only [Multiset.toFinset_add, Multiset.toFinset_singleton, Finset.singleton_union]
    exact Finset.card_pair hne
  · -- `c` is odd: `X² + X + 1` has no root in `𝔽₂`, hence is irreducible.
    have hc1 : (c : ZMod 2) = 1 := by
      rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff']; omega
    rw [ite_eq_right hd8, hc1, C_1]
    have hq : (X ^ 2 + X + 1 : (ZMod 2)[X]) = X ^ 2 + (X + C 1) := by rw [C_1]; ring
    have hlt : (X + C 1 : (ZMod 2)[X]).natDegree < (X ^ 2 : (ZMod 2)[X]).natDegree := by
      rw [natDegree_X_add_C, natDegree_X_pow]; norm_num
    have hdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by
      rw [hq, natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_X_pow]
    have hirr : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
      refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun x hx => ?_
      rw [IsRoot.def, eval_add, eval_add, eval_pow, eval_X, eval_one, ZMod.pow_card] at hx
      have h2 : (x + x + 1 : ZMod 2) = 1 := by
        have : (2 : ZMod 2) = 0 := by decide
        linear_combination x * this
      rw [h2] at hx
      exact one_ne_zero hx
    rw [normalizedFactors_irreducible hirr, Multiset.toFinset_singleton, Finset.card_singleton]

/-- **The number of primes above `2` for `d ≡ 1 (mod 4)`.** For `K = ℚ(√d)` with `d` squarefree
and `d ≡ 1 (mod 4)`, there are two primes of `𝓞 K` above `2` when `d ≡ 1 (mod 8)` and one when
`d ≡ 5 (mod 8)`. -/
theorem ncard_primesOver_two_of_mod_four_eq_one {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd4 : d % 4 = 1) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = if d % 8 = 1 then 2 else 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hexp : exponent (halfGen hmin hd4) = 1 :=
    exponent_eq_one_iff.mpr (adjoin_halfGen_eq_top_of_mod_four_eq_one hmin hgen hsf hd4)
  have hp : ¬ (2 : ℕ) ∣ exponent (halfGen hmin hd4) := by rw [hexp]; norm_num
  have h := ncard_primesOver_eq_card_monicFactorsMod (halfGen hmin hd4) hp
  rw [Nat.cast_ofNat] at h
  rw [h, card_monicFactorsMod_halfGen_two hmin hd4]

/-- **The number of primes above `2`, in the half-integer presentation.** Let `K` be generated over
`ℚ` by an algebraic integer `ω` with minimal polynomial `X² - X + (1 - d)/4` over `ℤ`, where `d` is
squarefree with `d ≡ 1 (mod 4)` — the presentation of `ℚ(√d)` by `ω = (1 + √d)/2`. Then there are
two primes of `𝓞 K` above `2` when `d ≡ 1 (mod 8)` and one when `d ≡ 5 (mod 8)`. -/
theorem ncard_primesOver_two_of_minpoly_eq_X_sq_sub_X_add {ω : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ ω = X ^ 2 - X + C ((1 - d) / 4)) (hgen : Algebra.adjoin ℚ {(ω : K)} = ⊤)
    (hsf : Squarefree d) (hd4 : d % 4 = 1) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = if d % 8 = 1 then 2 else 1 := by
  set c : ℤ := (1 - d) / 4 with hc
  have h4 : 4 * c = 1 - d := by omega
  -- `θ = 2ω - 1` is a square root of `d` generating `K`, and `ω` is its half-integer generator.
  set θ : 𝓞 K := ω + ω - 1 with hθ
  have hθK : algebraMap (𝓞 K) K θ = algebraMap (𝓞 K) K ω + algebraMap (𝓞 K) K ω - 1 := by
    rw [hθ, map_sub, map_add, map_one]
  have hωroot : aeval ω (X ^ 2 - X + C c : ℤ[X]) = 0 := by rw [← hmin]; exact minpoly.aeval ℤ ω
  have hωsq : ω ^ 2 - ω + (c : 𝓞 K) = 0 := by
    rwa [map_add, map_sub, map_pow, aeval_X, aeval_C, algebraMap_int_eq, eq_intCast] at hωroot
  have hθsq : θ ^ 2 = (d : 𝓞 K) := by
    have h4' : (4 : 𝓞 K) * (c : 𝓞 K) = 1 - (d : 𝓞 K) := by exact_mod_cast h4
    rw [hθ]
    linear_combination 4 * hωsq - h4'
  have hgenθ : Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
    rw [eq_top_iff, ← hgen, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    have hmem : (θ : K) ∈ Algebra.adjoin ℚ {(θ : K)} := Algebra.subset_adjoin rfl
    have hω : algebraMap (𝓞 K) K ω = (1 / 2 : ℚ) • (algebraMap (𝓞 K) K θ + 1) := by
      rw [hθK, Algebra.smul_def, map_div₀, map_one, map_ofNat]; ring
    rw [show (ω : K) = (1 / 2 : ℚ) • ((θ : K) + 1) from hω]
    exact Subalgebra.smul_mem _ (add_mem hmem (one_mem _)) _
  -- `ω` is not a rational integer, so neither is `θ`, and `X² - d` is its minimal polynomial.
  have hωnot : ω ∉ (algebraMap ℤ (𝓞 K)).range := by
    rw [← minpoly.two_le_natDegree_iff (Algebra.IsIntegral.isIntegral ω), hmin]
    have hq : (X ^ 2 - X + C c : ℤ[X]) = X ^ 2 + (C (-1) * X + C c) := by
      rw [map_neg, C_1]; ring
    have hlt : (C (-1) * X + C c : ℤ[X]).natDegree < (X ^ 2 : ℤ[X]).natDegree := by
      rw [natDegree_X_pow]
      exact lt_of_le_of_lt natDegree_linear_le (by norm_num)
    rw [hq, natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_X_pow]
  have hθnot : θ ∉ (algebraMap ℤ (𝓞 K)).range := by
    rintro ⟨n, hn⟩
    apply hωnot
    -- `ω = (n + 1)/2` is a rational algebraic integer, hence a rational integer.
    have hθn : algebraMap (𝓞 K) K θ = algebraMap ℤ K n := by
      rw [← hn, IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
    have hωq : algebraMap (𝓞 K) K ω = algebraMap ℚ K ((((n : ℤ) : ℚ) + 1) / 2) := by
      rw [map_div₀, map_add, map_one, map_ofNat, ← eq_intCast (algebraMap ℤ ℚ) n,
        ← IsScalarTower.algebraMap_apply ℤ ℚ K, ← hθn, hθK]
      ring
    have hint : IsIntegral ℤ ((((n : ℤ) : ℚ) + 1) / 2) := by
      rw [← isIntegral_algebraMap_iff (A := ℚ) (B := K) (R := ℤ), ← hωq]
      exact ω.isIntegral_coe
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨m, RingOfIntegers.coe_injective ?_⟩
    rw [hωq, ← hm, ← IsScalarTower.algebraMap_apply ℤ ℚ K,
      ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
  have hminθ : minpoly ℤ θ = X ^ 2 - C d := by
    have hintθ : IsIntegral ℤ θ := Algebra.IsIntegral.isIntegral θ
    have hroot : aeval θ (X ^ 2 - C d : ℤ[X]) = 0 := by
      rw [map_sub, map_pow, aeval_X, aeval_C, algebraMap_int_eq, eq_intCast, hθsq, sub_self]
    obtain ⟨r, hr⟩ := minpoly.isIntegrallyClosed_dvd hintθ hroot
    have hmonic : (X ^ 2 - C d : ℤ[X]).Monic := monic_X_pow_sub_C d two_ne_zero
    have hrmonic : r.Monic := (minpoly.monic hintθ).of_mul_monic_left (hr ▸ hmonic)
    have h2le : 2 ≤ (minpoly ℤ θ).natDegree := (minpoly.two_le_natDegree_iff hintθ).mpr hθnot
    have hsum : (minpoly ℤ θ).natDegree + r.natDegree = 2 := by
      rw [← (minpoly.monic hintθ).natDegree_mul hrmonic, ← hr, natDegree_X_pow_sub_C]
    have hr1 : r = 1 := Polynomial.eq_one_of_monic_natDegree_zero hrmonic (by omega)
    rw [hr, hr1, mul_one]
  exact ncard_primesOver_two_of_mod_four_eq_one hminθ hgenθ hsf hd4

/-- **The splitting law at `2` for `d ≡ 1 (mod 4)`.** For `K = ℚ(√d)` with `d` squarefree and
`d ≡ 1 (mod 4)`, the prime `2` splits completely in `K` if and only if `d ≡ 1 (mod 8)`. -/
theorem ncard_primesOver_two_eq_finrank_iff_of_mod_four_eq_one {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd4 : d % 4 = 1) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = finrank ℚ K ↔ d % 8 = 1 := by
  rw [ncard_primesOver_two_of_mod_four_eq_one hmin hgen hsf hd4, finrank_rat_eq_two hmin hgen]
  split_ifs with h <;> simp [h]

/-- **The inert case at `2` for `d ≡ 1 (mod 4)`.** For `K = ℚ(√d)` with `d` squarefree and
`d ≡ 1 (mod 4)`, the prime `2` is inert in `K` (there is a single prime above it) if and only if
`d ≡ 5 (mod 8)`. -/
theorem ncard_primesOver_two_eq_one_iff_of_mod_four_eq_one {θ : 𝓞 K} {d : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd4 : d % 4 = 1) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = 1 ↔ d % 8 = 5 := by
  rw [ncard_primesOver_two_of_mod_four_eq_one hmin hgen hsf hd4]
  split_ifs with h
  · simp only [OfNat.ofNat_ne_one, false_iff]; omega
  · simp only [true_iff]; omega

end NumberField
