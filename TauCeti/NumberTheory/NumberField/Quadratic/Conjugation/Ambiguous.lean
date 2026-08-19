/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.ClassGroup
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.TotallyComplex

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
**ideals**. The remaining step of that count — that an ambiguous ideal is, up to an extended
rational ideal, a product of the ramified primes, whose classes already satisfy the relation
`∏ 𝔭 = (θ)` of `TauCeti.Multiquadratic.prod_classGroupMk0_eq_one` — is not proved here; with it the
genus-theoretic bound `2-rank ≤ t - 1` of the Multiquadratic roadmap follows.

The proof is Hilbert's Theorem 90 for the quadratic extension `K/ℚ`, in the elementary form
available for a degree-two extension. If `[σJ] = [J]` then `(x) σJ = (y) J` for nonzero
`x y : 𝓞 K`; conjugating and cancelling gives `(x σx) = (y σy)`, so `x σx` and `y σy` are
associates. The unit relating them has norm the square of the rational `N(y) / N(x)`, and in an
**imaginary** quadratic field the norm of a nonzero element is strictly positive
(`NumberField.norm_pos_of_isTotallyComplex`), which forces `x σx = y σy` on the nose. Hilbert 90
then produces `ε ≠ 0` with `x ε = y σε`, and `I = (ε) J` is an ambiguous ideal in `J`'s class. For a
*real* quadratic field the positivity fails — that is exactly where the classical unit index
`[E : E ∩ N K^×]` enters the ambiguous class number formula — so the hypothesis
`IsTotallyComplex K` is essential rather than technical.

Hilbert 90 is available in Mathlib as `groupCohomology.exists_div_of_norm_eq_one`; for a quadratic
extension the two-line construction below (`ε = σx (x + y)`, or `ε = σx θ x` in the degenerate case)
is elementary, and gives an element of `𝓞 K` rather than of `K`, which is what the ideal
manipulation wants.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*, Chapter 6, for
the classical ambiguous class number formula.

## Main results

* `NumberField.exists_ne_zero_mul_eq_mul_ringOfIntegersQuadraticConj`: Hilbert's Theorem 90 for
  quadratic conjugation, in the integral form `x ε = y σε`.
* `NumberField.exists_map_ringOfIntegersQuadraticConj_eq_self_of_sq_eq_one`: a `2`-torsion ideal
  class of an imaginary quadratic field is the class of an ambiguous ideal.
* `NumberField.sq_eq_one_iff_exists_map_ringOfIntegersQuadraticConj_eq_self`: the ambiguous classes
  are exactly the classes of ambiguous ideals.
-/

public section

open Polynomial NumberField
open scoped NumberField nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **Hilbert's Theorem 90 for quadratic conjugation.** Let `σ` be the quadratic conjugation of a
quadratic number field and let `x y : 𝓞 K` with `x ≠ 0` have equal norms, `x σx = y σy`. Then there
is a nonzero `ε : 𝓞 K` with `x ε = y σε`; equivalently `y / x = ε / σε` is a "coboundary". The
construction is explicit: `ε = σx (x + y)` works unless `x + y = 0`, and then `ε = σx θ x` does. -/
theorem exists_ne_zero_mul_eq_mul_ringOfIntegersQuadraticConj
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {x y : 𝓞 K}
    (hx : x ≠ 0)
    (hnorm : x * ringOfIntegersQuadraticConj hmin hgen x =
      y * ringOfIntegersQuadraticConj hmin hgen y) :
    ∃ ε : 𝓞 K, ε ≠ 0 ∧ x * ε = y * ringOfIntegersQuadraticConj hmin hgen ε := by
  set σ := ringOfIntegersQuadraticConj hmin hgen
  have hinv : ∀ z : 𝓞 K, σ (σ z) = z := ringOfIntegersQuadraticConj_involutive hmin hgen
  have hgenσ : σ θ = -θ := ringOfIntegersQuadraticConj_gen hmin hgen
  have hσx : σ x ≠ 0 := fun h0 => hx (by simpa [hinv] using congrArg σ h0)
  have hθ : (θ : 𝓞 K) ≠ 0 := fun h0 => coe_gen_ne_zero hmin (by rw [h0]; simp)
  by_cases hxy : x + y = 0
  · refine ⟨σ x * θ * x, by simp [hσx, hθ, hx], ?_⟩
    simp only [map_mul, hinv, hgenσ]
    linear_combination (θ * x * σ x) * hxy
  · refine ⟨σ x * (x + y), by simp [hσx, hxy], ?_⟩
    simp only [map_mul, map_add, hinv]
    linear_combination x * hnorm

/-- Pushing an ideal forward twice along an involutive ring automorphism returns it. -/
private theorem map_map_of_involutive {R : Type*} [CommRing R] {f : R ≃+* R}
    (hf : Function.Involutive f) (I : Ideal R) : Ideal.map f (Ideal.map f I) = I :=
  have hcomp : (f : R →+* R).comp (f : R →+* R) = RingHom.id R := RingHom.ext hf
  have h : Ideal.map (f : R →+* R) (Ideal.map (f : R →+* R) I) = I := by
    rw [Ideal.map_map, hcomp, Ideal.map_id]
  h

/-- An involutive ring automorphism preserves nonvanishing of ideals. -/
private theorem map_ne_zero_of_involutive {R : Type*} [CommRing R] {f : R ≃+* R}
    (hf : Function.Involutive f) {I : Ideal R} (hI : I ≠ 0) : Ideal.map f I ≠ 0 := fun h0 =>
  hI <| by simpa [map_map_of_involutive hf] using congrArg (Ideal.map f) h0

/-- **Two elements of an imaginary quadratic field with associated norms have equal norms.** If
`x σx` and `y σy` are associates in `𝓞 K` then they are equal: their ratio is a unit whose norm is
the square of a positive rational, hence `1`. This is the step where total complexity of `K` enters;
over a real quadratic field the unit could have norm `-1`. -/
private theorem mul_conj_eq_mul_conj_of_associated [IsTotallyComplex K]
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {x y : 𝓞 K}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hassoc : Associated (x * ringOfIntegersQuadraticConj hmin hgen x)
      (y * ringOfIntegersQuadraticConj hmin hgen y)) :
    x * ringOfIntegersQuadraticConj hmin hgen x =
      y * ringOfIntegersQuadraticConj hmin hgen y := by
  obtain ⟨u, hu⟩ := hassoc
  have hσalg : ∀ z : 𝓞 K, algebraMap (𝓞 K) K (ringOfIntegersQuadraticConj hmin hgen z)
      = quadraticConj hmin hgen (algebraMap (𝓞 K) K z) := fun z => by
    simpa only [RingOfIntegers.coe_eq_algebraMap] using coe_ringOfIntegersQuadraticConj hmin hgen z
  -- Both products are the image of the field norm.
  have hcoe : ∀ z : 𝓞 K, algebraMap (𝓞 K) K (z * ringOfIntegersQuadraticConj hmin hgen z) =
      algebraMap ℚ K (Algebra.norm ℚ (algebraMap (𝓞 K) K z)) := fun z => by
    rw [map_mul, hσalg, algebraMap_norm_eq_mul_quadraticConj hmin hgen]
  set nx := Algebra.norm ℚ (algebraMap (𝓞 K) K x) with hnx
  set ny := Algebra.norm ℚ (algebraMap (𝓞 K) K y) with hny
  have hxpos : 0 < nx :=
    norm_pos_of_isTotallyComplex hmin hgen (RingOfIntegers.coe_ne_zero_iff.mpr hx)
  have hypos : 0 < ny :=
    norm_pos_of_isTotallyComplex hmin hgen (RingOfIntegers.coe_ne_zero_iff.mpr hy)
  -- Passing to `K`, the associating unit satisfies `nx · u = ny`.
  have hK : algebraMap ℚ K nx * algebraMap (𝓞 K) K (u : 𝓞 K) = algebraMap ℚ K ny := by
    have h := congrArg (algebraMap (𝓞 K) K) hu
    rwa [map_mul, hcoe x, hcoe y] at h
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
      rcases mul_eq_zero.mp hfac with h' | h' <;> linarith
    · rw [h] at hsq
      nlinarith
  apply RingOfIntegers.coe_injective
  rw [hcoe x, hcoe y, ← hnx, ← hny, hnxny]

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
  -- `Ideal.map` along the ring equivalence and along its underlying ring hom agree definitionally.
  replace hxy : Ideal.span {x} * Ideal.map σ (J : Ideal (𝓞 K)) =
    Ideal.span {y} * (J : Ideal (𝓞 K)) := hxy
  have hJ0 : (J : Ideal (𝓞 K)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp J.2
  have hJm0 : Ideal.map σ (J : Ideal (𝓞 K)) ≠ 0 := map_ne_zero_of_involutive hinv hJ0
  have hspanx : Ideal.span ({x} : Set (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  -- Conjugating that identity gives the companion identity.
  have hxy2 : Ideal.span {σ x} * (J : Ideal (𝓞 K)) =
      Ideal.span {σ y} * Ideal.map σ (J : Ideal (𝓞 K)) := by
    have h := congrArg (Ideal.map σ) hxy
    rwa [Ideal.map_mul, Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_singleton, map_map_of_involutive hinv] at h
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
    mul_conj_eq_mul_conj_of_associated hmin hgen hx hy
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

/-- **The class of an ambiguous ideal is `2`-torsion.** If quadratic conjugation fixes the ideal `I`
then `I · σI = I²` is principal, so `[I]² = 1`. This is the easy direction of
`sq_eq_one_iff_exists_map_ringOfIntegersQuadraticConj_eq_self`, and needs no hypothesis on the
signature of `K`. -/
theorem sq_classGroupMk0_eq_one_of_map_ringOfIntegersQuadraticConj_eq_self
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {I : (Ideal (𝓞 K))⁰}
    (hI : Ideal.map (ringOfIntegersQuadraticConj hmin hgen) (I : Ideal (𝓞 K)) =
      (I : Ideal (𝓞 K))) :
    ClassGroup.mk0 I ^ 2 = 1 := by
  obtain ⟨I, hI0⟩ := I
  have hprin := isPrincipal_mul_map_ringOfIntegersQuadraticConj hmin hgen I
  rw [hI, ← sq] at hprin
  rw [← map_pow, SubmonoidClass.mk_pow I hI0 2, ClassGroup.mk0_eq_one_iff]
  exact hprin

/-- **The ambiguous classes of an imaginary quadratic field are exactly the classes of ambiguous
ideals.** For a totally complex quadratic number field, an ideal class is `2`-torsion — equivalently
fixed by quadratic conjugation — precisely when it is represented by an ideal that conjugation
fixes. This is the descent step of the ambiguous class number formula: it turns the count of
`2`-torsion classes into a count of ambiguous ideals, which are the products of ramified primes. -/
theorem sq_eq_one_iff_exists_map_ringOfIntegersQuadraticConj_eq_self [IsTotallyComplex K]
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (C : ClassGroup (𝓞 K)) :
    C ^ 2 = 1 ↔ ∃ I : (Ideal (𝓞 K))⁰,
      Ideal.map (ringOfIntegersQuadraticConj hmin hgen) (I : Ideal (𝓞 K)) = (I : Ideal (𝓞 K)) ∧
        ClassGroup.mk0 I = C :=
  ⟨exists_map_ringOfIntegersQuadraticConj_eq_self_of_sq_eq_one hmin hgen, by
    rintro ⟨I, hI, rfl⟩
    exact sq_classGroupMk0_eq_one_of_map_ringOfIntegersQuadraticConj_eq_self hmin hgen hI⟩

end NumberField
