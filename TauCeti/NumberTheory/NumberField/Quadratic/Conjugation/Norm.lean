/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Norm
public import TauCeti.NumberTheory.DedekindDomain.RelNorm
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Basic
import TauCeti.RingTheory.Norm.Quadratic

/-!
# Norm-principality for quadratic conjugation

For a quadratic number field `K = ℚ(√d)` with quadratic conjugation
`σ = NumberField.ringOfIntegersQuadraticConj`, this file proves the genus-theoretic
key fact that `I · σI` is principal for every ideal `I` of `𝓞 K`.  This is the hypothesis
consumed by `NumberField.mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv`.

The proof runs through the relative ideal norm: `I · σI` has the same relative norm as
`(Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 K))` and contains it, hence equals it, and that
extension of a principal `ℤ`-ideal is principal.  The zero ideal needs no separate treatment.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*, for the
classical genus theory this norm-principality underlies.
-/

public section

open Polynomial NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- The generator `θ` of the quadratic field is nonzero: it is irrational (`gen_notMem_range`),
whereas `0` is rational. -/
private theorem coe_gen_ne_zero (hmin : minpoly ℤ θ = X ^ 2 - C d) : (θ : K) ≠ 0 := fun h0 =>
  gen_notMem_range hmin ⟨0, by rw [map_zero, h0]⟩

/-- Quadratic conjugation is a nontrivial automorphism: it does not equal the identity, since it
sends the nonzero generator `θ` to its negative `-θ`. -/
private theorem quadraticConj_ne_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : quadraticConj hmin hgen ≠ 1 := by
  intro h
  have hθ : (θ : K) = -(θ : K) := by
    have := DFunLike.congr_fun h (θ : K)
    rw [quadraticConj_gen, AlgEquiv.one_apply] at this
    exact this.symm
  have h2 : (θ : K) + (θ : K) = 0 := by nth_rewrite 2 [hθ]; ring
  exact coe_gen_ne_zero hmin (add_self_eq_zero.mp h2)

/-- The relative-norm generator `N(y) = y · σy`: applying `Algebra.norm ℚ` to `y` and coercing to
`K` gives the product with its conjugate. -/
private theorem norm_eq_mul_conj (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (y : K) :
    algebraMap ℚ K (Algebra.norm ℚ y) = y * quadraticConj hmin hgen y := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨finrank_rat_eq_two hmin hgen⟩
  exact Algebra.IsQuadraticExtension.algebraMap_norm_eq_mul ℚ K
    (quadraticConj_ne_one hmin hgen) y

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

/-- **The norm-ideal identity.** For quadratic conjugation `σ = ringOfIntegersQuadraticConj`, the
product `I · σI` is the extension to `𝓞 K` of the relative norm ideal `relNorm ℤ I`. -/
@[simp] theorem mul_map_ringOfIntegersQuadraticConj_eq_map_relNorm
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (I : Ideal (𝓞 K)) :
    I * Ideal.map (ringOfIntegersQuadraticConj hmin hgen) I
      = Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.relNorm ℤ I) := by
  -- Conjugation preserves the relative norm, so `σI` and `I` have equal relative norm.
  have hreln : Ideal.relNorm ℤ (Ideal.map (ringOfIntegersQuadraticConj hmin hgen) I) =
      Ideal.relNorm ℤ I := by
    rw [← map_ringOfIntegersQuadraticConjₐ hmin hgen I,
      Ideal.relNorm_map_algEquiv (ringOfIntegersQuadraticConjₐ hmin hgen) I]
  -- Hence both `(relNorm I) 𝓞 K` and `I · σI` have relative norm `(relNorm I)²`.
  have hnorm : Ideal.relNorm ℤ (Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.relNorm ℤ I)) =
      Ideal.relNorm ℤ (I * Ideal.map (ringOfIntegersQuadraticConj hmin hgen) I) := by
    rw [Ideal.relNorm_algebraMap, finrank_int_eq_two hmin hgen,
      map_mul (Ideal.relNorm ℤ), hreln, ← sq]
  -- With the containment `(relNorm I) 𝓞 K ≤ I · σI`, equal relative norms force equality.
  exact (Ideal.eq_of_le_of_relNorm_eq
    (map_relNorm_le_mul_map_ringOfIntegersQuadraticConj hmin hgen I) hnorm).symm

/-- **Norm-principality (Lemma A).** For quadratic conjugation `σ = ringOfIntegersQuadraticConj`,
the product `I · σI` is a principal ideal, for every ideal `I` of `𝓞 K`. This is the
genus-theoretic hypothesis fed to `mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv`. -/
theorem isPrincipal_mul_map_ringOfIntegersQuadraticConj
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (I : Ideal (𝓞 K)) :
    (I * Ideal.map (ringOfIntegersQuadraticConj hmin hgen) I).IsPrincipal := by
  -- `I · σI` is the extension of the principal `ℤ`-ideal `relNorm ℤ I`, hence principal.
  rw [mul_map_ringOfIntegersQuadraticConj_eq_map_relNorm hmin hgen I]
  have : (Ideal.relNorm ℤ I).IsPrincipal := IsPrincipalIdealRing.principal _
  infer_instance

end NumberField
