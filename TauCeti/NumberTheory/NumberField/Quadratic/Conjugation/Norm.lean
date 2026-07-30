/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Basic

/-!
# Norm-principality for quadratic conjugation

For a quadratic number field `K = ℚ(√d)` with quadratic conjugation
`σ = TauCeti.NumberField.ringOfIntegersQuadraticConj`, this file proves the genus-theoretic
key fact that `I · σI` is principal for every ideal `I` of `𝓞 K`.  This is the hypothesis
consumed by `TauCeti.NumberField.mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv`.

The proof idea, for `I ≠ 0`, runs through the relative ideal norm: `I · σI` has the same relative
norm as `(Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 K))` and contains it, hence equals it, and that
extension of a principal `ℤ`-ideal is principal.  (The zero ideal is trivially principal.)

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*, for the
classical genus theory this norm-principality underlies.
-/

public section

open Polynomial NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- The quadratic field `K` has degree `2` over `ℚ`: its power basis has dimension
`natDegree (X² - d) = 2`. -/
private theorem finrank_rat_eq_two (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Module.finrank ℚ K = 2 := by
  have hint : IsIntegral ℚ (θ : K) := θ.isIntegral_coe.tower_top
  rw [(PowerBasis.ofAdjoinEqTop' hint hgen).finrank,
    PowerBasis.ofAdjoinEqTop'_dim hint hgen, minpoly_rat_quadratic hmin, natDegree_X_pow_sub_C]

/-- The generator `θ` of the quadratic field is nonzero (its minimal polynomial has degree `2`,
not `1`). -/
private theorem coe_gen_ne_zero (hmin : minpoly ℤ θ = X ^ 2 - C d) : (θ : K) ≠ 0 := by
  intro h0
  have hh : minpoly ℚ (θ : K) = X ^ 2 - C ((d : ℤ) : ℚ) := minpoly_rat_quadratic hmin
  rw [h0, minpoly.zero] at hh
  have := congrArg natDegree hh
  rw [natDegree_X, natDegree_X_pow_sub_C] at this
  exact absurd this (by norm_num)

/-- Quadratic conjugation is a nontrivial automorphism: it does not equal the identity, since it
sends the nonzero generator `θ` to its negative `-θ`. -/
private theorem quadraticConj_ne_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (1 : K ≃ₐ[ℚ] K) ≠ quadraticConj hmin hgen := by
  intro h
  have hθ : (θ : K) = -(θ : K) := by
    have := DFunLike.congr_fun h (θ : K)
    rwa [AlgEquiv.one_apply, quadraticConj_gen] at this
  have h2 : (θ : K) + (θ : K) = 0 := by nth_rewrite 2 [hθ]; ring
  exact coe_gen_ne_zero hmin (add_self_eq_zero.mp h2)

/-- The automorphism group of the quadratic field `K/ℚ` has exactly `2` elements. -/
private theorem card_aut_eq_two (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
  refine le_antisymm ?_ ?_
  · exact (AlgEquiv.card_le).trans (finrank_rat_eq_two hmin hgen).le
  · exact Fintype.one_lt_card_iff.mpr
      ⟨1, quadraticConj hmin hgen, quadraticConj_ne_one hmin hgen⟩

/-- The quadratic field `K` is Galois over `ℚ`: it has `finrank = 2` automorphisms
(the identity and the conjugation). -/
private theorem isGalois_rat (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : IsGalois ℚ K :=
  IsGalois.of_card_aut_eq_finrank ℚ K
    (by rw [Nat.card_eq_fintype_card, card_aut_eq_two hmin hgen, finrank_rat_eq_two hmin hgen])

/-- The product of an element over the Galois group `{1, σ}` of `K/ℚ` is `y · σy`. -/
private theorem prod_aut_eq (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (y : K) :
    ∏ g : K ≃ₐ[ℚ] K, g y = y * quadraticConj hmin hgen y := by
  classical
  have hu : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, quadraticConj hmin hgen} := by
    refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
    rw [Finset.card_univ, card_aut_eq_two hmin hgen,
      Finset.card_pair (quadraticConj_ne_one hmin hgen)]
  rw [hu, Finset.prod_pair (quadraticConj_ne_one hmin hgen), AlgEquiv.one_apply]

/-- The relative-norm generator `N(y) = y · σy`: applying `Algebra.norm ℚ` to `y` and coercing to
`K` gives the product with its conjugate. -/
private theorem norm_eq_mul_conj (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (y : K) :
    algebraMap ℚ K (Algebra.norm ℚ y) = y * quadraticConj hmin hgen y := by
  haveI := isGalois_rat hmin hgen
  rw [Algebra.norm_eq_prod_automorphisms, prod_aut_eq hmin hgen]

/-- **Key norm identity.** For `x : 𝓞 K`, the extension of its integral norm equals `x · σx`, the
product of `x` with its quadratic conjugate. -/
private theorem algebraMap_intNorm_eq (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (x : 𝓞 K) :
    algebraMap ℤ (𝓞 K) (Algebra.intNorm ℤ (𝓞 K) x)
      = x * ringOfIntegersQuadraticConj hmin hgen x := by
  have hσ : algebraMap (𝓞 K) K (ringOfIntegersQuadraticConj hmin hgen x)
      = quadraticConj hmin hgen (algebraMap (𝓞 K) K x) := by
    simpa only [RingOfIntegers.coe_eq_algebraMap] using coe_ringOfIntegersQuadraticConj hmin hgen x
  apply RingOfIntegers.coe_injective
  rw [map_mul, hσ, ← norm_eq_mul_conj hmin hgen, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K,
    IsScalarTower.algebraMap_apply ℤ ℚ K]
  congr 1
  rw [Algebra.intNorm_eq_norm, algebraMap_int_eq, eq_intCast]
  exact Algebra.coe_norm_int x

attribute [local instance] FractionRing.liftAlgebra

/-- The degree of `Frac(𝓞 K)/Frac(ℤ)` is `2`, matching `finrank ℚ K`. -/
private theorem finrank_frac_eq_two (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Module.finrank (FractionRing ℤ) (FractionRing (𝓞 K)) = 2 := by
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing ℤ (FractionRing ℤ) (𝓞 K) (FractionRing (𝓞 K)),
    RingOfIntegers.rank, finrank_rat_eq_two hmin hgen]

/-- Quadratic conjugation packaged as a `ℤ`-algebra automorphism of `𝓞 K` (every ring
automorphism is automatically `ℤ`-linear). -/
private noncomputable def ringOfIntegersQuadraticConjₐ (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : 𝓞 K ≃ₐ[ℤ] 𝓞 K :=
  AlgEquiv.ofRingEquiv (f := ringOfIntegersQuadraticConj hmin hgen)
    (fun z => by rw [algebraMap_int_eq]; exact map_intCast _ z)

/-- The relative norm is invariant under pushforward by quadratic conjugation. -/
private theorem relNorm_map_eq (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (J : Ideal (𝓞 K)) :
    Ideal.relNorm ℤ (Ideal.map (ringOfIntegersQuadraticConj hmin hgen) J)
      = Ideal.relNorm ℤ J :=
  Ideal.relNorm_map_algEquiv (ringOfIntegersQuadraticConjₐ hmin hgen) J

/-- **Norm-principality (Lemma A).** For quadratic conjugation `σ = ringOfIntegersQuadraticConj`,
the product `I · σI` is a principal ideal, for every ideal `I` of `𝓞 K`. This is the
genus-theoretic hypothesis fed to `mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv`. -/
theorem isPrincipal_mul_map_ringOfIntegersQuadraticConj
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (I : Ideal (𝓞 K)) :
    (I * Ideal.map (ringOfIntegersQuadraticConj hmin hgen) I).IsPrincipal := by
  -- For `I ≠ 0`, `I · σI = (Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 K))`, the extension of a
  -- principal `ℤ`-ideal; the equality is obtained by matching relative norms and divisibility.
  rcases eq_or_ne I 0 with rfl | hJne
  · exact ⟨0, by simp⟩
  set σ := ringOfIntegersQuadraticConj hmin hgen with hσdef
  set J : Ideal (𝓞 K) := I with hJ
  set A : Ideal (𝓞 K) := Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.relNorm ℤ J) with hA
  set B : Ideal (𝓞 K) := J * Ideal.map σ J with hB
  have hmapne : Ideal.map σ J ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective σ.injective, ← Ideal.zero_eq_bot]
    exact hJne
  have hBne : B ≠ 0 := by rw [hB]; exact mul_ne_zero hJne hmapne
  -- (1) `A` is principal (extension of a principal `ℤ`-ideal).
  have hAprin : A.IsPrincipal := by
    obtain ⟨m, hm⟩ := (IsPrincipalIdealRing.principal (Ideal.relNorm ℤ J)).principal
    exact ⟨algebraMap ℤ (𝓞 K) m, by
      rw [hA, hm, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]⟩
  -- (2) `A ≤ B`: each generator `N(x) = x·σx` lies in `J · σJ`.
  have hAB : A ≤ B := by
    rw [hA, Ideal.map_relNorm, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [Function.comp_apply, algebraMap_intNorm_eq hmin hgen, hB]
    exact Ideal.mul_mem_mul hx (Ideal.mem_map_of_mem σ hx)
  -- (3) `relNorm A = relNorm B = (relNorm J)²`.
  have hnorm : Ideal.relNorm ℤ A = Ideal.relNorm ℤ B := by
    rw [hB, map_mul (Ideal.relNorm ℤ), relNorm_map_eq hmin hgen, ← sq, hA,
      Ideal.relNorm_algebraMap, finrank_frac_eq_two hmin hgen]
  -- (4) `A = B`, from `B ∣ A` together with the equal norms.
  have hAeqB : A = B := by
    obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hAB
    have hBnorm_ne : Ideal.relNorm ℤ B ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.relNorm_eq_bot_iff, ← Ideal.zero_eq_bot]; exact hBne
    have hC1 : Ideal.relNorm ℤ C = 1 := by
      apply mul_left_cancel₀ hBnorm_ne
      rw [mul_one, ← map_mul (Ideal.relNorm ℤ), ← hC, hnorm]
    have hCtop : C = ⊤ := by
      have hle : (⊤ : Ideal ℤ) ≤ Ideal.comap (algebraMap ℤ (𝓞 K)) C := by
        rw [← Ideal.one_eq_top, ← hC1]; exact Ideal.relNorm_le_comap ℤ C
      rw [Ideal.eq_top_iff_one]
      have := hle (Submodule.mem_top (x := (1 : ℤ)))
      rwa [Ideal.mem_comap, map_one] at this
    rw [hC, hCtop, Ideal.mul_top]
  rw [← hAeqB]; exact hAprin

end TauCeti.NumberField
