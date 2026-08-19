/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Norm

/-!
# Quadratic conjugation of an imaginary quadratic field is complex conjugation

For a quadratic number field `K = ℚ(√d)` that is totally complex — an *imaginary* quadratic field —
every complex embedding `φ : K →+* ℂ` intertwines the quadratic conjugation
`σ = NumberField.quadraticConj` with complex conjugation: `φ (σ x) = conj (φ x)`. Consequently the
field norm `Algebra.norm ℚ x = x · σx` is sent to `‖φ x‖²`, so it is **strictly positive** on
nonzero elements.

The intertwining is a counting argument. A number field of degree `2` has exactly two complex
embeddings (`NumberField.Embeddings.card`), and `φ ∘ σ` and `conj ∘ φ` are both different from `φ`:
the first because `σ` moves the nonzero generator `θ` to `-θ`, the second because a totally complex
field has no real embedding. Two elements of a two-element type that both differ from a third are
equal.

Positivity of the norm is the input that upgrades a norm-`±1` element of an imaginary quadratic
field to a norm-`1` one, which is what Hilbert's Theorem 90 consumes in
`Quadratic/Conjugation/Ambiguous.lean`; it is where the genus-theoretic `2`-rank formula for
imaginary quadratic fields parts company with the real case, whose extra unit index is exactly the
failure of this positivity.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*, for the
classical genus theory this supports.

## Main results

* `NumberField.apply_quadraticConj_eq_conj`: for a totally complex quadratic field, every complex
  embedding turns quadratic conjugation into complex conjugation.
* `NumberField.norm_pos_of_isTotallyComplex`: the field norm of a nonzero element of a totally
  complex quadratic field is strictly positive.
-/

public section

open Polynomial NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- In a type with exactly two elements, two elements that both differ from a third are equal. -/
private theorem eq_of_natCard_eq_two {α : Type*} (hcard : Nat.card α = 2) {u v w : α}
    (hu : u ≠ w) (hv : v ≠ w) : u = v := by
  obtain ⟨a, b, _, huniv⟩ := Nat.card_eq_two_iff.mp hcard
  have hmem : ∀ z : α, z = a ∨ z = b := fun z => by
    have hz : z ∈ ({a, b} : Set α) := huniv ▸ Set.mem_univ z
    simpa using hz
  rcases hmem u with rfl | rfl <;> rcases hmem v with rfl | rfl <;> rcases hmem w with rfl | rfl <;>
    simp_all

/-- **Quadratic conjugation is complex conjugation.** For a totally complex quadratic field `K` and
any complex embedding `φ : K →+* ℂ`, precomposing with quadratic conjugation is the same as
postcomposing with complex conjugation. -/
theorem comp_quadraticConj_eq_conjugate [IsTotallyComplex K] (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (φ : K →+* ℂ) :
    φ.comp (quadraticConj hmin hgen).toAlgHom.toRingHom = ComplexEmbedding.conjugate φ := by
  have hcard : Nat.card (K →+* ℂ) = 2 := by
    rw [Nat.card_eq_fintype_card, NumberField.Embeddings.card K ℂ, finrank_rat_eq_two hmin hgen]
  refine eq_of_natCard_eq_two hcard (w := φ) (fun h => ?_) (fun h => ?_)
  · -- `φ ∘ σ = φ` would force `φ θ = -φ θ`, hence `θ = 0`.
    have hθ : φ (θ : K) = -φ (θ : K) := by
      have := RingHom.congr_fun h (θ : K)
      simpa [quadraticConj_gen hmin hgen] using this.symm
    have h0 : φ (θ : K) = 0 := by linear_combination hθ / 2
    exact coe_gen_ne_zero (θ := θ) hmin ((map_eq_zero_iff φ φ.injective).mp h0)
  · exact IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.mpr h)

/-- **Quadratic conjugation is complex conjugation**, elementwise: for a totally complex quadratic
field, every complex embedding `φ` satisfies `φ (σ x) = conj (φ x)`. -/
@[simp] theorem apply_quadraticConj_eq_conj [IsTotallyComplex K] (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (φ : K →+* ℂ) (x : K) :
    φ (quadraticConj hmin hgen x) = (starRingEnd ℂ) (φ x) :=
  RingHom.congr_fun (comp_quadraticConj_eq_conjugate hmin hgen φ) x

/-- **The norm of an imaginary quadratic field is positive.** For a totally complex quadratic field
`K` and `x ≠ 0`, the field norm `Algebra.norm ℚ x` is strictly positive: under any complex embedding
`φ` it becomes `φ x · conj (φ x) = ‖φ x‖²`. This is what forbids a norm-`(-1)` element, the
difference between the imaginary and the real quadratic case in genus theory. -/
theorem norm_pos_of_isTotallyComplex [IsTotallyComplex K] (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {x : K} (hx : x ≠ 0) : 0 < Algebra.norm ℚ x := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hφx : φ x ≠ 0 := fun h => hx ((map_eq_zero_iff φ φ.injective).mp h)
  have key : ((Algebra.norm ℚ x : ℚ) : ℂ) = ((Complex.normSq (φ x) : ℝ) : ℂ) := by
    have h1 : algebraMap ℚ K (Algebra.norm ℚ x) = x * quadraticConj hmin hgen x :=
      algebraMap_norm_eq_mul_quadraticConj hmin hgen x
    have h2 : φ (algebraMap ℚ K (Algebra.norm ℚ x)) = ((Algebra.norm ℚ x : ℚ) : ℂ) := by
      rw [eq_ratCast (algebraMap ℚ K), map_ratCast]
    rw [← h2, h1, map_mul, apply_quadraticConj_eq_conj hmin hgen, Complex.mul_conj]
  have hreal : ((Algebra.norm ℚ x : ℚ) : ℝ) = Complex.normSq (φ x) := by
    exact_mod_cast key
  have hpos : (0 : ℝ) < ((Algebra.norm ℚ x : ℚ) : ℝ) := by
    rw [hreal]; exact Complex.normSq_pos.mpr hφx
  exact_mod_cast hpos

end NumberField
