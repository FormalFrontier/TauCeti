/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Norm
public import TauCeti.NumberTheory.DedekindDomain.RelNorm
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Basic

/-!
# Norm-principality for quadratic conjugation

For a quadratic number field `K = ℚ(√d)` with quadratic conjugation
`σ = TauCeti.NumberField.ringOfIntegersQuadraticConj`, this file proves the genus-theoretic
key fact that `I · σI` is principal for every ideal `I` of `𝓞 K`.  This is the hypothesis
consumed by `TauCeti.NumberField.mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv`.

The proof runs through the relative ideal norm: `I · σI` has the same relative norm as
`(Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 K))` and contains it, hence equals it, and that
extension of a principal `ℤ`-ideal is principal.  The zero ideal needs no separate treatment.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*, for the
classical genus theory this norm-principality underlies.
-/

public section

open Polynomial NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

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
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : (1 : K ≃ₐ[ℚ] K) ≠ quadraticConj hmin hgen := by
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
  have := isGalois_rat hmin hgen
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

/-- The degree of `𝓞 K` over `ℤ` is `2`, matching `finrank ℚ K`. -/
private theorem finrank_int_eq_two (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Module.finrank ℤ (𝓞 K) = 2 := by
  rw [RingOfIntegers.rank, finrank_rat_eq_two hmin hgen]

/-- Quadratic conjugation packaged as a `ℤ`-algebra automorphism of `𝓞 K` (every ring
automorphism is automatically `ℤ`-linear). -/
private noncomputable def ringOfIntegersQuadraticConjₐ (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : 𝓞 K ≃ₐ[ℤ] 𝓞 K :=
  AlgEquiv.ofRingEquiv (f := ringOfIntegersQuadraticConj hmin hgen)
    (fun z => by rw [algebraMap_int_eq]; exact map_intCast _ z)

/-- Pushing an ideal forward along quadratic conjugation and along its `ℤ`-algebra form
`ringOfIntegersQuadraticConjₐ` give the same ideal: the two wrappers carry the same underlying
ring homomorphism. -/
private theorem map_ringOfIntegersQuadraticConjₐ (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (J : Ideal (𝓞 K)) :
    Ideal.map (ringOfIntegersQuadraticConjₐ hmin hgen) J =
      Ideal.map (ringOfIntegersQuadraticConj hmin hgen) J :=
  rfl

/-- The extension of the norm ideal of `J` is contained in `J · σJ`. -/
private theorem map_relNorm_le_mul_map_ringOfIntegersQuadraticConj
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (J : Ideal (𝓞 K)) :
    Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.relNorm ℤ J) ≤
      J * Ideal.map (ringOfIntegersQuadraticConj hmin hgen) J := by
  -- Each generator of the extension is `N(x) = x · σx` for some `x ∈ J`.
  rw [Ideal.map_relNorm, Ideal.span_le]
  rintro _ ⟨x, hx, rfl⟩
  rw [Function.comp_apply, algebraMap_intNorm_eq hmin hgen]
  exact Ideal.mul_mem_mul hx (Ideal.mem_map_of_mem _ hx)

/-- **Norm-principality (Lemma A).** For quadratic conjugation `σ = ringOfIntegersQuadraticConj`,
the product `I · σI` is a principal ideal, for every ideal `I` of `𝓞 K`. This is the
genus-theoretic hypothesis fed to `mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv`. -/
theorem isPrincipal_mul_map_ringOfIntegersQuadraticConj
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (I : Ideal (𝓞 K)) :
    (I * Ideal.map (ringOfIntegersQuadraticConj hmin hgen) I).IsPrincipal := by
  -- `I · σI = (Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 K))`, the extension of a principal
  -- `ℤ`-ideal; the equality is obtained by matching relative norms and divisibility.
  -- Conjugation preserves the relative norm: rewrite to the `ℤ`-algebra form, which is what
  -- Mathlib's lemma takes.
  have hreln : Ideal.relNorm ℤ (Ideal.map (ringOfIntegersQuadraticConj hmin hgen) I) =
      Ideal.relNorm ℤ I := by
    rw [← map_ringOfIntegersQuadraticConjₐ hmin hgen I,
      Ideal.relNorm_map_algEquiv (ringOfIntegersQuadraticConjₐ hmin hgen) I]
  -- So both ideals have relative norm `(relNorm I)²`.
  have hnorm : Ideal.relNorm ℤ (Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.relNorm ℤ I)) =
      Ideal.relNorm ℤ (I * Ideal.map (ringOfIntegersQuadraticConj hmin hgen) I) := by
    rw [Ideal.relNorm_algebraMap, finrank_int_eq_two hmin hgen,
      map_mul (Ideal.relNorm ℤ), hreln, ← sq]
  -- So the containment is an equality, and the left side is principal, being the extension of the
  -- principal `ℤ`-ideal `relNorm I`.
  rw [← Ideal.eq_of_le_of_relNorm_eq
    (map_relNorm_le_mul_map_ringOfIntegersQuadraticConj hmin hgen I) hnorm]
  have : (Ideal.relNorm ℤ I).IsPrincipal := IsPrincipalIdealRing.principal _
  infer_instance

end TauCeti.NumberField
