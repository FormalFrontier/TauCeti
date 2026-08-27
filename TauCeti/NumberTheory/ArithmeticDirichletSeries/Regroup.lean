/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NormCoeff

/-!
# Regrouping an ideal-indexed Dirichlet series by absolute norm

An `TauCeti.IdealArithmeticFunction K` has two Dirichlet series attached to it: the series indexed
by the nonzero integral ideals of `𝓞 K`, whose terms are `TauCeti.idealTerm`, and the Mathlib
`LSeries` of the regrouped coefficients `TauCeti.normCoeff`. This file proves that the second is
obtained from the first by summing over the finite absolute-norm fibres, so that absolute
convergence of the ideal-indexed series transfers to the `LSeries` together with the value of the
sum.

## Main definitions

* `TauCeti.idealTerm f s I` is the term `f I / N(I) ^ s` of the ideal-indexed Dirichlet series.
* `TauCeti.idealAbscissaOfAbsConv f` is the abscissa of absolute convergence of that series, the
  ideal-indexed analogue of Mathlib's `LSeries.abscissaOfAbsConv`.

## Main results

* `TauCeti.regroupByNorm`: if the ideal-indexed series has sum `L` at `s`, then so does the
  `LSeries` of `TauCeti.normCoeff f`; `TauCeti.LSeriesSummable_normCoeff` and
  `TauCeti.LSeries_normCoeff` are the summability and value statements it packages.
* `TauCeti.abscissaOfAbsConv_normCoeff_le`: consequently the grouped abscissa of absolute
  convergence is at most the ideal-indexed one.
* `TauCeti.summable_idealTerm_of_norm_normCoeff_eq_sum_norm`: the converse holds whenever no
  cancellation occurs inside a norm fibre. `TauCeti.summable_idealTerm_of_nonneg` and
  `TauCeti.idealAbscissaOfAbsConv_eq_abscissaOfAbsConv` specialize it to the case where every
  *individual ideal summand* is nonnegative, where moreover the two abscissae agree.

## Implementation notes

The regrouping is an instance of Mathlib's `HasSum.tsum_fiberwise` along the absolute norm
`fun I ↦ Ideal.absNorm (I : Ideal (𝓞 K))`, whose fibres are the finite sets
`TauCeti.normFiber K n`. Absolute convergence of the ideal-indexed series is expressed as plain
`Summable`, which for a complex-valued family is unconditional convergence and hence absolute
convergence; no rearrangement hypothesis is therefore needed for the transfer.

The converse is proved through `summable_partition` applied to the norms of the terms. All it
needs about `f` is that the norm of each grouped coefficient is the sum of the norms over its
fibre — the absence of cancellation inside the fibre. Nonnegativity of every ideal summand is one
way to secure that, through `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg`; it is the step that
fails under cancellation, as the rejection test
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` records. That test is a statement about
`TauCeti.normCoeff` alone, so it lives with that definition rather than here.

## Roadmap role

This is Layer **1.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`; the required worked
example 9 accompanies it in `TauCeti/NumberTheory/ArithmeticDirichletSeries/NormCoeff.lean`. The
exact value of the abscissa for the trivial weight is deliberately not proved here: its divergence
input is the Layer 5 ideal count of
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Estimates.lean`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-! ### The ideal-indexed term -/

/-- The term of the ideal-indexed Dirichlet series of `f` at the nonzero integral ideal `I`: the
value `f I` divided by the `s`-th complex power of the absolute norm of `I`. The zero ideal is
absent from the carrier `(Ideal (𝓞 K))⁰`, so no `n = 0` convention is needed here, in contrast
with Mathlib's `LSeries.term`. -/
noncomputable def idealTerm (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) : ℂ :=
  f I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s

/-- Defining equation of `TauCeti.idealTerm`. -/
theorem idealTerm_def (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    idealTerm K f s I = f I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s :=
  (rfl)

/-- The absolute value of an ideal term depends on `s` only through its real part. -/
@[simp]
theorem norm_idealTerm (f : IdealArithmeticFunction K) (s : ℂ) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm K f s I‖ = ‖f I‖ / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re := by
  rw [idealTerm_def, norm_div,
    Complex.norm_natCast_cpow_of_pos (Ideal.absNorm_pos_of_nonZeroDivisors I)]

/-- Ideal terms decrease in absolute value as the real part of `s` grows, because every nonzero
integral ideal has absolute norm at least one. -/
theorem norm_idealTerm_le_of_re_le_re (f : IdealArithmeticFunction K) {s s' : ℂ}
    (h : s.re ≤ s'.re) (I : (Ideal (𝓞 K))⁰) :
    ‖idealTerm K f s' I‖ ≤ ‖idealTerm K f s I‖ := by
  have h₁ : (1 : ℝ) ≤ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
  have h₀ : (0 : ℝ) < (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s.re :=
    Real.rpow_pos_of_pos (by linarith) _
  simp only [norm_idealTerm]
  gcongr

/-- Absolute convergence of the ideal-indexed series propagates to the right. -/
theorem summable_idealTerm_of_re_le_re {f : IdealArithmeticFunction K} {s s' : ℂ}
    (h : s.re ≤ s'.re) (hf : Summable (idealTerm K f s)) : Summable (idealTerm K f s') := by
  rw [← summable_norm_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_idealTerm_le_of_re_le_re K f h)

/-- Absolute convergence of the ideal-indexed series depends on `s` only through its real part. -/
theorem summable_idealTerm_iff_of_re_eq_re {f : IdealArithmeticFunction K} {s s' : ℂ}
    (h : s.re = s'.re) : Summable (idealTerm K f s) ↔ Summable (idealTerm K f s') :=
  ⟨summable_idealTerm_of_re_le_re K h.le, summable_idealTerm_of_re_le_re K h.ge⟩

/-! ### Regrouping -/

/-- The `n`-th term of the regrouped `LSeries` is the finite sum of the ideal terms over the
absolute-norm fibre of `n`. -/
theorem term_normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (s : ℂ) (n : ℕ) :
    LSeries.term (normCoeff K f) s n = ∑ I ∈ normFiber K n, idealTerm K f s I := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, normCoeff_eq_sum_normFiber, Finset.sum_div]
  refine Finset.sum_congr rfl fun I hI ↦ ?_
  rw [idealTerm_def, (mem_normFiber K).mp hI]

/-- The regrouped `LSeries` terms as the fibrewise sums of the ideal terms along the absolute
norm. This is the form consumed by `HasSum.tsum_fiberwise`; `term_normCoeff_eq_sum_normFiber` is
the usable finite-fibre formula. -/
private theorem term_normCoeff (f : IdealArithmeticFunction K) (s : ℂ) :
    LSeries.term (normCoeff K f) s = fun n ↦
      ∑' I : (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n},
        idealTerm K f s I := by
  funext n
  rw [← coe_normFiber, Finset.tsum_subtype' (normFiber K n) (idealTerm K f s)]
  exact term_normCoeff_eq_sum_normFiber K f s n

/-- **Regrouping by absolute norm.** If the Dirichlet series indexed by the nonzero integral ideals
converges absolutely at `s` with sum `L`, then the Mathlib `LSeries` of the regrouped coefficients
`TauCeti.normCoeff f` converges absolutely at `s` with the same sum.

Absolute convergence of the ideal-indexed series is the hypothesis `HasSum`, which for a
complex-valued family is unconditional. No hypothesis on the individual ideal summands is needed;
compare `TauCeti.summable_idealTerm_of_nonneg` for the converse, which does need one. -/
theorem regroupByNorm {f : IdealArithmeticFunction K} {s L : ℂ} (h : HasSum (idealTerm K f s) L) :
    LSeriesHasSum (normCoeff K f) s L := by
  simpa only [LSeriesHasSum, term_normCoeff] using
    h.tsum_fiberwise fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))

/-- Absolute convergence of the ideal-indexed Dirichlet series implies that of the regrouped
`LSeries`. -/
theorem LSeriesSummable_normCoeff {f : IdealArithmeticFunction K} {s : ℂ}
    (h : Summable (idealTerm K f s)) : LSeriesSummable (normCoeff K f) s :=
  LSeriesHasSum.LSeriesSummable (regroupByNorm K h.hasSum)

/-- Where the ideal-indexed Dirichlet series converges absolutely, the regrouped `LSeries` has the
same value. -/
theorem LSeries_normCoeff {f : IdealArithmeticFunction K} {s : ℂ}
    (h : Summable (idealTerm K f s)) :
    LSeries (normCoeff K f) s = ∑' I, idealTerm K f s I :=
  LSeriesHasSum.LSeries_eq (regroupByNorm K h.hasSum)

/-! ### The ideal-indexed abscissa of absolute convergence -/

/-- The abscissa of absolute convergence of the Dirichlet series indexed by the nonzero integral
ideals: the ideal-indexed analogue of Mathlib's `LSeries.abscissaOfAbsConv`. -/
noncomputable def idealAbscissaOfAbsConv (f : IdealArithmeticFunction K) : EReal :=
  sInf <| Real.toEReal '' {x : ℝ | Summable (idealTerm K f x)}

/-- Defining equation of `TauCeti.idealAbscissaOfAbsConv`. -/
theorem idealAbscissaOfAbsConv_def (f : IdealArithmeticFunction K) :
    idealAbscissaOfAbsConv K f = sInf (Real.toEReal '' {x : ℝ | Summable (idealTerm K f x)}) :=
  (rfl)

/-- The ideal-indexed series converges absolutely strictly to the right of its abscissa. -/
theorem summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re {f : IdealArithmeticFunction K} {s : ℂ}
    (hs : idealAbscissaOfAbsConv K f < s.re) : Summable (idealTerm K f s) := by
  obtain ⟨y, hy, hys⟩ : ∃ y : ℝ, Summable (idealTerm K f y) ∧ y < s.re := by
    simpa [idealAbscissaOfAbsConv, sInf_lt_iff] using hs
  exact summable_idealTerm_of_re_le_re K (Complex.ofReal_re y ▸ hys.le) hy

/-- A point of absolute convergence bounds the ideal-indexed abscissa. -/
theorem idealAbscissaOfAbsConv_le {f : IdealArithmeticFunction K} {s : ℂ}
    (h : Summable (idealTerm K f s)) : idealAbscissaOfAbsConv K f ≤ s.re :=
  sInf_le ⟨s.re, summable_idealTerm_of_re_le_re K (by simp) h, rfl⟩

/-- **The grouped abscissa is at most the ideal-indexed one.** Regrouping can only improve
convergence, since cancellation inside a norm fibre is never undone. -/
theorem abscissaOfAbsConv_normCoeff_le (f : IdealArithmeticFunction K) :
    LSeries.abscissaOfAbsConv (normCoeff K f) ≤ idealAbscissaOfAbsConv K f :=
  sInf_le_sInf <| Set.image_mono fun _ hx ↦ LSeriesSummable_normCoeff K hx

/-! ### The converse, in the absence of cancellation inside norm fibres -/

/-- At a real point, an ideal term of a nonnegative ideal arithmetic function is nonnegative. -/
theorem idealTerm_nonneg {f : IdealArithmeticFunction K} {I : (Ideal (𝓞 K))⁰} (h : 0 ≤ f I)
    (x : ℝ) : 0 ≤ idealTerm K f x I := by
  rw [idealTerm_def, div_eq_mul_inv]
  exact mul_nonneg h
    (Complex.inv_natCast_cpow_ofReal_pos (Ideal.absNorm_ne_zero_of_nonZeroDivisors I) x).le

/-- In the absence of cancellation inside norm fibres, the sum over an absolute-norm fibre of the
absolute values of the ideal terms at a real `x` is the absolute value of the corresponding
`LSeries` term. This is the step of the converse regrouping that cancellation destroys. -/
private theorem tsum_norm_idealTerm_fiber (f : IdealArithmeticFunction K)
    (hf : ∀ n, ‖normCoeff K f n‖ = ∑ I ∈ normFiber K n, ‖f I‖) (x : ℝ) (n : ℕ) :
    ∑' I : (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n},
        ‖idealTerm K f x I‖ = ‖LSeries.term (normCoeff K f) x n‖ := by
  rw [← coe_normFiber, Finset.tsum_subtype' (normFiber K n) fun I ↦ ‖idealTerm K f x I‖]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, norm_div,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), hf n, Finset.sum_div]
  refine Finset.sum_congr rfl fun I hI ↦ ?_
  rw [norm_idealTerm, (mem_normFiber K).mp hI]

/-- **The converse regrouping, in the absence of cancellation inside norm fibres.** If the
absolute value of every grouped coefficient is the sum of the absolute values of `f` over the
corresponding fibre — that is, if adding up a fibre loses no absolute value — then absolute
convergence of the regrouped `LSeries` implies absolute convergence of the ideal-indexed series.

This is the hypothesis the proof actually uses: it holds for a nonnegative `f`, by
`TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg`, but equally for a uniformly negative one or, more
generally, whenever the values of `f` over each fibre share a common phase. Nonnegativity of the
*grouped* coefficients `TauCeti.normCoeff f` does not suffice; see
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg`. -/
theorem summable_idealTerm_of_norm_normCoeff_eq_sum_norm (f : IdealArithmeticFunction K)
    (hf : ∀ n, ‖normCoeff K f n‖ = ∑ I ∈ normFiber K n, ‖f I‖) {s : ℂ}
    (h : LSeriesSummable (normCoeff K f) s) : Summable (idealTerm K f s) := by
  rw [summable_idealTerm_iff_of_re_eq_re K (s' := (s.re : ℂ)) (by simp)]
  replace h : LSeriesSummable (normCoeff K f) (s.re : ℂ) := h.of_re_le_re (by simp)
  refine Summable.of_norm ?_
  rw [summable_partition (f := fun I ↦ ‖idealTerm K f (s.re : ℂ) I‖) (fun _ ↦ norm_nonneg _)
    (s := fun n ↦ (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n})
    fun I ↦ ⟨Ideal.absNorm (I : Ideal (𝓞 K)), rfl, fun _ hn ↦ hn.symm⟩]
  refine ⟨fun n ↦ ?_, ?_⟩
  · have : Finite ((fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n}) :=
      (finite_normFiber K n).to_subtype
    exact Summable.of_finite
  · exact (summable_norm_iff.mpr h).congr fun n ↦
      (tsum_norm_idealTerm_fiber K f hf s.re n).symm

/-- **The converse regrouping, under nonnegativity of every ideal summand.** If every value of `f`
is a nonnegative real number, then absolute convergence of the regrouped `LSeries` implies absolute
convergence of the ideal-indexed series.

This is the special case of `TauCeti.summable_idealTerm_of_norm_normCoeff_eq_sum_norm` in which
nonnegativity rules out cancellation. Nonnegativity of the *grouped* coefficients
`TauCeti.normCoeff f` does not suffice; see
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg`. -/
theorem summable_idealTerm_of_nonneg (f : IdealArithmeticFunction K) (hf : ∀ I, 0 ≤ f I) {s : ℂ}
    (h : LSeriesSummable (normCoeff K f) s) : Summable (idealTerm K f s) :=
  summable_idealTerm_of_norm_normCoeff_eq_sum_norm K f
    (norm_normCoeff_eq_sum_norm_of_nonneg K f hf) h

/-- For a nonnegative ideal arithmetic function the two abscissae of absolute convergence agree:
there is no cancellation inside a norm fibre to exploit. -/
theorem idealAbscissaOfAbsConv_eq_abscissaOfAbsConv (f : IdealArithmeticFunction K)
    (hf : ∀ I, 0 ≤ f I) :
    idealAbscissaOfAbsConv K f = LSeries.abscissaOfAbsConv (normCoeff K f) :=
  le_antisymm (sInf_le_sInf <| Set.image_mono fun _ hx ↦ summable_idealTerm_of_nonneg K f hf hx)
    (abscissaOfAbsConv_normCoeff_le K f)

end TauCeti
