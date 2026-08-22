/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.TotallyPositive
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.ClassGroup
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Hilbert90

/-!
# Ambiguous ideals of an imaginary quadratic field

An ideal of `𝓞 K` is *ambiguous* when quadratic conjugation `σ` fixes it, `σI = I`; an ideal class
is *ambiguous* when `σ` fixes it, which for a quadratic field means exactly that the class is
`2`-torsion (`NumberField.mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff`, since `σ` acts by
inversion). Every ambiguous ideal obviously has an ambiguous class. This file proves the converse
for an **imaginary** quadratic field: every ambiguous class is the class of an ambiguous ideal, so
the two notions of "ambiguous" match up:

`C ^ 2 = 1 ↔ ∃ I, σI = I ∧ [I] = C`.

This is the descent step of the classical *ambiguous class number formula*, which counts the
`2`-torsion of `Cl(𝓞 K)`: it replaces a count of ambiguous **classes** by a count of ambiguous
**ideals**. The remaining step of that count — that the class of an ambiguous ideal is a product of
classes of ramified primes, which in turn satisfy the relation `∏ 𝔭 = (θ)` of
`TauCeti.Multiquadratic.span_singleton_eq_prod_primeFactors` — is
`NumberField.classGroupMk0_mem_closure_of_map_eq_self` in
`Quadratic/Conjugation/Ambiguous/Ideal.lean`; the two together give the genus-theoretic bound
`2-rank ≤ t - 1` of the Multiquadratic roadmap.

The proof is Hilbert's Theorem 90 for the quadratic extension `K/ℚ`, in the elementary form
available for a degree-two extension. If `[σJ] = [J]` then `(x) σJ = (y) J` for nonzero
`x y : 𝓞 K`; conjugating and cancelling gives `(x σx) = (y σy)`, so `x σx` and `y σy` are
associates. The unit relating them has norm the square of the rational `N(y) / N(x)`, and in a
**totally complex** field total positivity is vacuous, so the norm of a nonzero element is strictly
positive (`NumberField.norm_pos_of_isTotallyPositive`), which forces `x σx = y σy` on the nose.
Hilbert 90 then produces `ε ≠ 0` with `x ε = y σε`, and `I = (ε) J` is an ambiguous ideal in `J`'s
class. For a *real* quadratic field the positivity fails — that is exactly where the classical
unit index `[E : E ∩ N K^×]` enters the ambiguous class number formula — so the hypothesis
`IsTotallyComplex K` is essential rather than technical. The repair is to pass to the **narrow**
class group, where total positivity restores the sign for every quadratic field; see
`Quadratic/Conjugation/Ambiguous/Narrow.lean`.

The integral Hilbert 90 result used below is proved in `Quadratic.Conjugation.Hilbert90`.

See F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2, whose Proposition 2.9 is
the statement proved here, and D. A. Cox, *Primes of the Form x² + ny²*, §6.A, for the classical
ambiguous class number formula.

## Main results

* `NumberField.mul_ringOfIntegersQuadraticConj_eq_mul_ringOfIntegersQuadraticConj_of_associated`:
  associated norms with a positive norm product are equal, the archimedean input to the descent.
* `NumberField.exists_map_ringOfIntegersQuadraticConj_eq_self_of_sq_eq_one`: a `2`-torsion ideal
  class of an imaginary quadratic field is the class of an ambiguous ideal.
* `NumberField.classGroupMk0_sq_eq_one_of_map_ringOfIntegersQuadraticConj_eq_self`: conversely, the
  class of an ambiguous ideal is `2`-torsion.
* `NumberField.sq_eq_one_iff_exists_map_ringOfIntegersQuadraticConj_eq_self`: the ambiguous classes
  are exactly the classes of ambiguous ideals.
* `Ideal.map_map_of_involutive`: pushing an ideal forward twice along an involutive ring
  automorphism returns it.
-/

public section

open Polynomial NumberField
open scoped NumberField nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- Pushing an ideal forward twice along an involutive ring automorphism returns it. -/
theorem _root_.Ideal.map_map_of_involutive {R : Type*} [CommSemiring R] {f : R ≃+* R}
    (hf : Function.Involutive f) (I : Ideal R) : Ideal.map f (Ideal.map f I) = I := by
  have hcomp : (f : R →+* R).comp (f : R →+* R) = RingHom.id R := RingHom.ext hf
  rw [← Ideal.map_coe (f := f) I, ← Ideal.map_coe (f := f) (Ideal.map (f : R →+* R) I),
    Ideal.map_map, hcomp, Ideal.map_id]

/-- **Two elements with associated norms and positive norm product have equal norms.** If
`x σx` and `y σy` are associates in `𝓞 K` and the norm of `x y` is positive, then `x σx = y σy`:
their ratio is a unit whose norm is the square of the rational `N(y) / N(x)`, so `N(x) = ± N(y)`,
and the sign is fixed by `0 < N(x) N(y)`.

This is where the archimedean input enters the ambiguous class number formula. For a totally complex
field the norm of a nonzero element is automatically positive; for a real quadratic field the
positivity has to come from total positivity of `x y`, which is what the *narrow* class group
supplies. -/
theorem mul_ringOfIntegersQuadraticConj_eq_mul_ringOfIntegersQuadraticConj_of_associated
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {x y : 𝓞 K}
    (hnorm : 0 < Algebra.norm ℚ ((x : K) * (y : K)))
    (hassoc : Associated (x * ringOfIntegersQuadraticConj hmin hgen x)
      (y * ringOfIntegersQuadraticConj hmin hgen y)) :
    x * ringOfIntegersQuadraticConj hmin hgen x =
      y * ringOfIntegersQuadraticConj hmin hgen y := by
  obtain ⟨u, hu⟩ := hassoc
  set nx := Algebra.norm ℚ (algebraMap (𝓞 K) K x) with hnx
  set ny := Algebra.norm ℚ (algebraMap (𝓞 K) K y) with hny
  have hprod : 0 < nx * ny := by rw [hnx, hny, ← map_mul]; exact hnorm
  -- Passing to `K`, the associating unit satisfies `nx · u = ny`.
  have hK : algebraMap ℚ K nx * algebraMap (𝓞 K) K (u : 𝓞 K) = algebraMap ℚ K ny := by
    have h := congrArg (algebraMap (𝓞 K) K) hu
    rw [map_mul, ← algebraMap_norm_eq_mul_ringOfIntegersQuadraticConj hmin hgen x,
      ← algebraMap_norm_eq_mul_ringOfIntegersQuadraticConj hmin hgen y] at h
    rw [hnx, hny]
    exact h
  -- The norm of a unit of `𝓞 K` is `±1`.
  have hnormu : Algebra.norm ℚ (algebraMap (𝓞 K) K (u : 𝓞 K)) = 1 ∨
      Algebra.norm ℚ (algebraMap (𝓞 K) K (u : 𝓞 K)) = -1 := by
    have hcast : ((Algebra.norm ℤ (u : 𝓞 K) : ℤ) : ℚ)
        = Algebra.norm ℚ (algebraMap (𝓞 K) K (u : 𝓞 K)) := Algebra.coe_norm_int _
    rcases Int.isUnit_iff.mp (IsUnit.map (Algebra.norm ℤ (S := 𝓞 K)) u.isUnit) with h | h
    · exact Or.inl (by rw [← hcast, h]; norm_num)
    · exact Or.inr (by rw [← hcast, h]; norm_num)
  -- Taking norms of `hK` gives `nx² · N(u) = ny²`, which pins `nx = ny`.
  have hsq : nx ^ 2 * Algebra.norm ℚ (algebraMap (𝓞 K) K (u : 𝓞 K)) = ny ^ 2 := by
    have h := congrArg (Algebra.norm ℚ) hK
    rwa [map_mul, Algebra.norm_algebraMap, Algebra.norm_algebraMap,
      finrank_rat_eq_two hmin hgen] at h
  have hnxny : nx = ny := by
    rcases hnormu with h | h
    · rw [h, mul_one] at hsq
      have hfac : (nx - ny) * (nx + ny) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hfac with h' | h' <;> nlinarith [hprod, sq_nonneg nx]
    · rw [h] at hsq
      nlinarith [hprod, sq_nonneg nx, sq_nonneg ny]
  apply RingOfIntegers.coe_injective
  rw [← algebraMap_norm_eq_mul_ringOfIntegersQuadraticConj hmin hgen x,
    ← algebraMap_norm_eq_mul_ringOfIntegersQuadraticConj hmin hgen y, ← hnx, ← hny, hnxny]

/-- **Every ambiguous ideal class of an imaginary quadratic field is the class of an ambiguous
ideal.** Let `K` be a totally complex quadratic number field with quadratic conjugation `σ`. A
`2`-torsion ideal class — equivalently, by
`mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff`, a class fixed by `σ` — is the class of an
ideal `I` with `σI = I`. This is the Hilbert-90 descent step of the ambiguous class number
formula. -/
theorem exists_map_ringOfIntegersQuadraticConj_eq_self_of_sq_eq_one [IsTotallyComplex K]
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {C : ClassGroup (𝓞 K)} (hC : C ^ 2 = 1) :
    ∃ I : (Ideal (𝓞 K))⁰,
      Ideal.map (ringOfIntegersQuadraticConj hmin hgen) (I : Ideal (𝓞 K)) = (I : Ideal (𝓞 K)) ∧
        ClassGroup.mk0 I = C := by
  classical
  obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective C
  -- The class is fixed by conjugation, so `(x) σJ = (y) J` for some nonzero `x`, `y`.
  have hfix := (mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff hmin hgen
    (ClassGroup.mk0 J)).mpr hC
  rw [ClassGroup.mulEquiv_mk0] at hfix
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp hfix
  set σ := ringOfIntegersQuadraticConj hmin hgen
  have hinv : Function.Involutive σ := ringOfIntegersQuadraticConj_involutive hmin hgen
  -- Restate the pushforward in `hxy` along the equivalence rather than its underlying hom.
  simp only [Ideal.map_coe] at hxy
  have hJ0 : (J : Ideal (𝓞 K)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp J.2
  have hJm0 : Ideal.map σ (J : Ideal (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective σ.injective,
      ← Ideal.zero_eq_bot]
    exact hJ0
  have hspanx : Ideal.span ({x} : Set (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  -- Conjugating that identity gives the companion identity.
  have hxy2 : Ideal.span {σ x} * (J : Ideal (𝓞 K)) =
      Ideal.span {σ y} * Ideal.map σ (J : Ideal (𝓞 K)) := by
    have h := congrArg (Ideal.map σ) hxy
    rwa [Ideal.map_mul, Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_singleton, Ideal.map_map_of_involutive hinv] at h
  -- Multiplying the two identities and cancelling `σJ` leaves `(x σx) = (y σy)`.
  have hspan : Ideal.span {x * σ x} = Ideal.span ({y * σ y} : Set (𝓞 K)) := by
    refine mul_right_cancel₀ hJm0 ?_
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
    calc Ideal.span {x} * Ideal.span {σ x} * Ideal.map σ (J : Ideal (𝓞 K))
        = Ideal.span {σ x} * (Ideal.span {x} * Ideal.map σ (J : Ideal (𝓞 K))) := by ring
      _ = Ideal.span {σ x} * (Ideal.span {y} * (J : Ideal (𝓞 K))) := by rw [hxy]
      _ = Ideal.span {y} * (Ideal.span {σ x} * (J : Ideal (𝓞 K))) := by ring
      _ = Ideal.span {y} * (Ideal.span {σ y} * Ideal.map σ (J : Ideal (𝓞 K))) := by rw [hxy2]
      _ = Ideal.span {y} * Ideal.span {σ y} * Ideal.map σ (J : Ideal (𝓞 K)) := by ring
  have hnorm : x * σ x = y * σ y :=
    mul_ringOfIntegersQuadraticConj_eq_mul_ringOfIntegersQuadraticConj_of_associated hmin hgen
      (norm_pos_of_isTotallyPositive (by
        simpa using mul_ne_zero (RingOfIntegers.coe_ne_zero_iff.mpr hx)
          (RingOfIntegers.coe_ne_zero_iff.mpr hy)) (by simp))
      (Ideal.span_singleton_eq_span_singleton.mp hspan)
  -- Hilbert 90 produces the twisting element.
  obtain ⟨ε, hε0, hε⟩ := exists_ne_zero_mul_eq_mul_ringOfIntegersQuadraticConj hmin hgen hx hnorm
  have hspanε : Ideal.span ({ε} : Set (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hε0
  have hI0 : Ideal.span {ε} * (J : Ideal (𝓞 K)) ≠ 0 := mul_ne_zero hspanε hJ0
  refine ⟨⟨Ideal.span {ε} * (J : Ideal (𝓞 K)), mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩, ?_, ?_⟩
  · -- `(x) · σ((ε) J) = (x) · (ε) J`, and `(x) ≠ 0` cancels.
    refine mul_left_cancel₀ hspanx ?_
    rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
    calc Ideal.span {x} * (Ideal.span {σ ε} * Ideal.map σ (J : Ideal (𝓞 K)))
        = Ideal.span {σ ε} * (Ideal.span {x} * Ideal.map σ (J : Ideal (𝓞 K))) := by ring
      _ = Ideal.span {σ ε} * (Ideal.span {y} * (J : Ideal (𝓞 K))) := by rw [hxy]
      _ = Ideal.span {y * σ ε} * (J : Ideal (𝓞 K)) := by
            rw [← Ideal.span_singleton_mul_span_singleton]; ring
      _ = Ideal.span {x * ε} * (J : Ideal (𝓞 K)) := by rw [hε]
      _ = Ideal.span {x} * (Ideal.span {ε} * (J : Ideal (𝓞 K))) := by
            rw [← Ideal.span_singleton_mul_span_singleton]; ring
  · exact ClassGroup.mk0_eq_mk0_iff.mpr ⟨1, ε, one_ne_zero, hε0, by simp⟩

/-- **The class of an ambiguous ideal is `2`-torsion.** An ideal fixed by quadratic conjugation has
a class fixed by the induced action on `Cl(𝓞 K)`, which is `2`-torsion because that action is
inversion (`mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff`). This is the easy direction of
`sq_eq_one_iff_exists_map_ringOfIntegersQuadraticConj_eq_self`, and needs no hypothesis on the
signature of `K`. -/
theorem classGroupMk0_sq_eq_one_of_map_ringOfIntegersQuadraticConj_eq_self
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {I : (Ideal (𝓞 K))⁰}
    (hI : Ideal.map (ringOfIntegersQuadraticConj hmin hgen) (I : Ideal (𝓞 K)) =
      (I : Ideal (𝓞 K))) :
    ClassGroup.mk0 I ^ 2 = 1 :=
  (mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff hmin hgen (ClassGroup.mk0 I)).mp <| by
    rw [ClassGroup.mulEquiv_mk0]
    congr 1
    exact Subtype.ext ((Ideal.map_coe (f := ringOfIntegersQuadraticConj hmin hgen)
      (I : Ideal (𝓞 K))).trans hI)

/-- **The ambiguous classes of an imaginary quadratic field are exactly the classes of ambiguous
ideals.** For a totally complex quadratic number field, an ideal class is `2`-torsion — equivalently
fixed by quadratic conjugation — precisely when it is represented by an ideal that conjugation
fixes. This is the descent step of the ambiguous class number formula: it turns the count of
`2`-torsion classes into a count of ambiguous ideals. Classifying those ideals — their classes are
products of classes of ramified primes — is `classGroupMk0_mem_closure_of_map_eq_self`. -/
theorem sq_eq_one_iff_exists_map_ringOfIntegersQuadraticConj_eq_self [IsTotallyComplex K]
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (C : ClassGroup (𝓞 K)) :
    C ^ 2 = 1 ↔ ∃ I : (Ideal (𝓞 K))⁰,
      Ideal.map (ringOfIntegersQuadraticConj hmin hgen) (I : Ideal (𝓞 K)) = (I : Ideal (𝓞 K)) ∧
        ClassGroup.mk0 I = C :=
  ⟨exists_map_ringOfIntegersQuadraticConj_eq_self_of_sq_eq_one hmin hgen, by
    rintro ⟨I, hI, rfl⟩
    exact classGroupMk0_sq_eq_one_of_map_ringOfIntegersQuadraticConj_eq_self hmin hgen hI⟩

end NumberField
