/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Totally complex fields and their infinite places

A field containing an element whose square is a negative rational is totally complex: a real
embedding would send that element to a real square root of a negative number. A totally complex
field, having only complex infinite places, is then unramified at every infinite place in any
extension. Its complex embeddings come in conjugate pairs, so the field norm of a nonzero element
is a product of squares `(w x)²` over the infinite places, hence **strictly positive** — the
feature separating imaginary quadratic fields from real ones in genus theory.

## Main results

* `NumberField.isTotallyComplex_of_sq_ratCast_of_neg`: a negative square forces total
  complexity.
* `NumberField.IsUnramifiedAtInfinitePlaces_of_isTotallyComplex`: a totally complex base is
  unramified at all infinite places of any extension.
* `NumberField.norm_pos_of_isTotallyComplex`: the field norm of a nonzero element of a totally
  complex field is strictly positive.
-/

public section

open NumberField NumberField.InfinitePlace

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **A field with a negative square is totally complex.** If some `x : K` has `x² = r` for a
negative rational `r`, then every infinite place of `K` is complex. -/
theorem isTotallyComplex_of_sq_ratCast_of_neg {x : K} {r : ℚ} (hx2 : x ^ 2 = algebraMap ℚ K r)
    (hr : r < 0) : IsTotallyComplex K := by
  -- A real embedding would carry `x` to a real square root of `r < 0`, which is impossible.
  rw [isTotallyComplex_iff]
  intro w
  rw [isComplex_iff]
  intro hφ
  have hφsq : (embedding w) x ^ 2 = (r : ℂ) := by
    rw [← map_pow, hx2]; simp [map_ratCast]
  have hψsq : (hφ.embedding x) ^ 2 = (r : ℝ) := by
    have h : (((hφ.embedding x) ^ 2 : ℝ) : ℂ) = (r : ℂ) := by
      push_cast [hφ.coe_embedding_apply]; rw [hφsq]
    exact_mod_cast h
  have hrR : (r : ℝ) < 0 := by exact_mod_cast hr
  nlinarith [sq_nonneg (hφ.embedding x), hψsq, hrR]

/-- **A totally complex base is unramified at all infinite places.** Since a totally complex field
has only complex infinite places and a complex place never ramifies, every infinite place is
unramified in any extension `K` of a totally complex field `k`. -/
lemma IsUnramifiedAtInfinitePlaces_of_isTotallyComplex {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsTotallyComplex k] : IsUnramifiedAtInfinitePlaces k K where
  isUnramified w := by
    rw [InfinitePlace.isUnramified_iff]
    exact Or.inr (IsTotallyComplex.isComplex _)

/-- **The norm of a nonzero element of a totally complex field is positive.** The complex embeddings
of `K` come in conjugate pairs `φ, conj ∘ φ` — no embedding is real — and the pair over an infinite
place `w` contributes `φ x · conj (φ x) = (w x)²` to `Algebra.norm ℚ x`, so the norm is a product of
positive reals. This fails for a real field, where a real embedding can contribute a negative
factor. -/
theorem norm_pos_of_isTotallyComplex [IsTotallyComplex K] {x : K} (hx : x ≠ 0) :
    0 < Algebra.norm ℚ x := by
  classical
  -- The product of all complex embeddings, grouped by infinite place, is a product of squares.
  have key : ((Algebra.norm ℚ x : ℚ) : ℂ) = ((∏ w : InfinitePlace K, w x ^ 2 : ℝ) : ℂ) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ) (Algebra.norm ℚ x), Algebra.norm_eq_prod_embeddings ℚ ℂ x,
      ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ x)
        (fun σ : K →ₐ[ℚ] ℂ => σ x) (fun φ => by simp [RingHom.equivRatAlgHom]),
      ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ x)]
    push_cast
    refine Finset.prod_congr rfl fun w _ => ?_
    -- The embeddings above `w` are `embedding w` and its conjugate, which are distinct.
    have hne : embedding w ≠ ComplexEmbedding.conjugate (embedding w) := fun h =>
      IsTotallyComplex.complexEmbedding_not_isReal (embedding w)
        (ComplexEmbedding.isReal_iff.mpr h.symm)
    have hsub : ({embedding w, ComplexEmbedding.conjugate (embedding w)} : Finset (K →+* ℂ)) ⊆
        Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w) := by
      intro φ hφ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hφ with rfl | rfl
      · exact mk_embedding w
      · rw [mk_conjugate_eq]; exact mk_embedding w
    have hcard : (Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w)).card = 2 := by
      rw [InfinitePlace.card_filter_mk_eq, IsTotallyComplex.mult_eq]
    have heq : Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w) =
        {embedding w, ComplexEmbedding.conjugate (embedding w)} :=
      (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_pair hne])).symm
    rw [heq, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, norm_embedding_eq]
    push_cast
    ring
  have hreal : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ w : InfinitePlace K, w x ^ 2 := by
    exact_mod_cast key
  have hpos : (0 : ℝ) < ∏ w : InfinitePlace K, w x ^ 2 :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.mpr hx) 2
  rw [← hreal] at hpos
  exact_mod_cast hpos

end NumberField
