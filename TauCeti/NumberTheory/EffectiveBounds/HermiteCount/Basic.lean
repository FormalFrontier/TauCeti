/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.EffectiveBounds.SimpleGenerators

/-!
# An explicit count of number fields of bounded discriminant

Mathlib's `NumberField.finite_of_discr_bdd` is the qualitative summit of geometry of numbers:
inside a fixed extension `A / ℚ`, the number fields `K` with `|discr K| ≤ N` form a *finite* set.
Its proof bounds the degree of such a `K` (`rank_le_rankOfDiscrBdd`), bounds the conjugates of a
primitive integral generator (`minkowskiBound_lt_boundOfDiscBdd`, the convex-body input), and so
exhibits each `K` as `ℚ⟮x⟯` for `x` a root of an integer polynomial of bounded degree and
coefficient height; finiteness follows because there are finitely many such polynomials. The proof
extracts the *finiteness* of that generating set but discards the *count*.

This file is the **effective Hermite--Minkowski count** (the Layer-2 summit of the effective-bounds
roadmap): an explicit upper bound on the number of such fields. We re-run the generating-set step of
Mathlib's argument to expose the explicit polynomial bounds, then feed them to the elementary
field-counting lemma assembled in `TauCeti.IntermediateField` (built on the bounded-polynomial root
count of `TauCeti.Algebra.Polynomial`). The result is

`#{K : |discr K| ≤ N} ≤ (2 * C + 1) ^ (D + 1) * D`,

with `D = rankOfDiscrBdd N` Mathlib's explicit degree bound and `C = coeffBoundOfDiscrBdd N` an
explicit coefficient bound derived from Mathlib's Minkowski bound `boundOfDiscBdd N`.

## Main results

* `coeffBoundOfDiscrBdd`: an explicit height bound for the integer minimal polynomials of primitive
  generators of number fields of discriminant `≤ N`, uniform over real and complex generators.
* `TauCeti.NumberField.exists_mem_rootSet_eq_adjoin_of_abs_discr_le`: each such field is generated
  by a root of an integer polynomial of degree `≤ rankOfDiscrBdd N` and height
  `≤ coeffBoundOfDiscrBdd N`.
* `TauCeti.NumberField.ncard_setOf_finiteDimensional_abs_discr_le_le`: the explicit count.

The remainder of the file is the consumer-facing API layer over that count, packaging the exact
constants and recording the monotonicities that later effective estimates need:

* `hermiteCountBound` and `hermiteCountBound_mono`: the polynomial-count expression `(2C+1)^(D+1)·D`
  as a function of the degree and coefficient-height bounds, monotone in both.
* `ncard_setOf_finiteDimensional_abs_discr_le_le_of_bounds`: the count using any larger degree and
  coefficient-height bounds for the same threshold.
* `ncard_setOf_finiteDimensional_abs_discr_le_le_of_threshold_le` /
  `..._of_threshold_bounds`: counting the fields with `|d_K| ≤ N` using the constants attached to
  any larger threshold `M`, optionally coarsened further.
* `ncard_setOf_finiteDimensional_natAbs_discr_le_le_*`: the same family restated for the
  natural-number discriminant inequality `(discr K).natAbs ≤ N` that later estimates carry.

## Provenance

The generating-set construction (the case split on a real or complex infinite place, the use of
`exists_primitive_element_lt_of_isReal` / `exists_primitive_element_lt_of_isComplex` and
`Embeddings.coeff_bdd_of_norm_le`, and the final `IntermediateField.lift` identification) follows
the proofs of `NumberField.hermiteTheorem.finite_of_discr_bdd_of_isReal` and `..._of_isComplex` in
Mathlib's `Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean`; here those proofs are recast
to return the explicit generating set rather than only its finiteness. No formal code is vendored
verbatim.
-/

public section

open Module Polynomial NumberField NumberField.InfinitePlace
open NumberField.mixedEmbedding NumberField.hermiteTheorem TauCeti.IntermediateField
open scoped IntermediateField

namespace TauCeti.NumberField

/-- An explicit height bound for the integer minimal polynomial of a primitive generator of a number
field of discriminant `≤ N`. It is `⌈M ^ D * (D.choose (D / 2))⌉₊` where `D = rankOfDiscrBdd N` is
Mathlib's degree bound and `M = max √(1 + boundOfDiscBdd N ^ 2) 1` dominates the per-conjugate bound
of both the real and complex primitive elements of `finite_of_discr_bdd`. -/
noncomputable def coeffBoundOfDiscrBdd (N : ℕ) : ℕ :=
  ⌈(max (Real.sqrt (1 + (boundOfDiscBdd N : ℝ) ^ 2)) 1) ^ rankOfDiscrBdd N
      * ((rankOfDiscrBdd N).choose (rankOfDiscrBdd N / 2) : ℝ)⌉₊

/-- **Effective Hermite--Minkowski, generating element.** A number field `K` with `|discr K| ≤ N`
has a primitive integral generator `a` all of whose infinite places are at most
`max √(1 + boundOfDiscBdd N ^ 2) 1`. -/
private theorem exists_primitive_element_infinitePlace_le {K : Type*} [Field K] [NumberField K]
    {N : ℕ} (hK : |discr K| ≤ (N : ℤ)) :
    ∃ a : 𝓞 K, ℚ⟮(a : K)⟯ = ⊤ ∧
      ∀ w : InfinitePlace K, w (a : K) ≤ max (Real.sqrt (1 + (boundOfDiscBdd N : ℝ) ^ 2)) 1 := by
  classical
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have hBM : (boundOfDiscBdd N : ℝ) ≤ Real.sqrt (1 + (boundOfDiscBdd N : ℝ) ^ 2) :=
    Real.le_sqrt_of_sq_le (by linarith)
  -- The generator comes from the real or the complex convex-body input according to the type of
  -- an infinite place of `K`; both conjugate bounds fit under the single quantity above.
  by_cases hw₀ : IsReal w₀
  · have hlt : minkowskiBound K 1 < convexBodyLTFactor K * boundOfDiscBdd N := by
      calc minkowskiBound K 1 < boundOfDiscBdd N := minkowskiBound_lt_boundOfDiscBdd hK
        _ = 1 * boundOfDiscBdd N := (one_mul _).symm
        _ ≤ convexBodyLTFactor K * boundOfDiscBdd N := by
            gcongr; exact mod_cast one_le_convexBodyLTFactor K
    obtain ⟨a, ha₁, ha₂⟩ := exists_primitive_element_lt_of_isReal K hw₀ hlt
    refine ⟨a, ha₁, fun w => ?_⟩
    have hw : w (a : K) < max (boundOfDiscBdd N : ℝ) 1 := by
      have := ha₂ w; rwa [NNReal.coe_max, NNReal.coe_one] at this
    exact hw.le.trans (max_le_max hBM le_rfl)
  · rw [not_isReal_iff_isComplex] at hw₀
    have hlt : minkowskiBound K 1 < convexBodyLT'Factor K * boundOfDiscBdd N := by
      calc minkowskiBound K 1 < boundOfDiscBdd N := minkowskiBound_lt_boundOfDiscBdd hK
        _ = 1 * boundOfDiscBdd N := (one_mul _).symm
        _ ≤ convexBodyLT'Factor K * boundOfDiscBdd N := by
            gcongr; exact mod_cast one_le_convexBodyLT'Factor K
    obtain ⟨a, ha₁, ha₂⟩ := exists_primitive_element_lt_of_isComplex K hw₀ hlt
    exact ⟨a, ha₁, fun w => (ha₂ w).le.trans (le_max_left _ _)⟩

/-- The `ℤ`-minimal polynomial of an algebraic integer `a` of a number field `K` with
`finrank ℚ K ≤ rankOfDiscrBdd N`, all of whose conjugates have norm at most
`max √(1 + boundOfDiscBdd N ^ 2) 1`, has every coefficient bounded in absolute value by
`coeffBoundOfDiscrBdd N`. -/
private theorem abs_coeff_minpoly_le_coeffBoundOfDiscrBdd {K : Type*} [Field K] [NumberField K]
    {N : ℕ} {a : 𝓞 K} (hrank : finrank ℚ K ≤ rankOfDiscrBdd N)
    (hnorm : ∀ φ : K →+* ℂ, ‖φ (a : K)‖ ≤ max (Real.sqrt (1 + (boundOfDiscBdd N : ℝ) ^ 2)) 1)
    (i : ℕ) : |(minpoly ℤ (a : K)).coeff i| ≤ (coeffBoundOfDiscrBdd N : ℤ) := by
  rw [← @Int.cast_le ℝ]
  refine (Eq.trans_le ?_ (Embeddings.coeff_bdd_of_norm_le hnorm i)).trans ?_
  · simp only [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe, coeff_map,
      eq_intCast, Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]
  · rw [max_eq_left (le_max_right _ _)]
    refine le_trans (mul_le_mul (pow_le_pow_right₀ (le_max_right _ _) hrank) ?_
      (by positivity) (by positivity)) (Nat.le_ceil _)
    exact_mod_cast (Nat.choose_le_choose _ hrank).trans (Nat.choose_le_middle _ _)

variable (A : Type*) [Field A] [CharZero A]

/-- **Effective Hermite--Minkowski, generating step.** Each number field `K` (a finite extension of
`ℚ` inside `A`) with `|discr K| ≤ N` is generated over `ℚ` by a root in `A` of an integer polynomial
of degree at most `rankOfDiscrBdd N` and all coefficients of absolute value at most
`coeffBoundOfDiscrBdd N`. This is `NumberField.hermiteTheorem.finite_of_discr_bdd` recast to expose
its explicit generating set. -/
theorem exists_mem_rootSet_eq_adjoin_of_abs_discr_le [DecidableEq A] {N : ℕ}
    (K : IntermediateField ℚ A) (hK₀ : FiniteDimensional ℚ K)
    (hK : haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance hK₀
      |discr K| ≤ (N : ℤ)) :
    ∃ x ∈ (⋃ (f : ℤ[X]) (_ : f.natDegree ≤ rankOfDiscrBdd N ∧
        ∀ i, |f.coeff i| ≤ (coeffBoundOfDiscrBdd N : ℤ)),
        ((f.map (algebraMap ℤ A)).roots.toFinset : Set A)),
      (K : IntermediateField ℚ A) = ℚ⟮x⟯ := by
  classical
  have : CharZero K := SubsemiringClass.instCharZero K
  haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance hK₀
  obtain ⟨a, ha₁, haM⟩ := exists_primitive_element_infinitePlace_le hK
  refine ⟨a, ?_, ?_⟩
  · refine Set.mem_iUnion.mpr ⟨minpoly ℤ (a : K), Set.mem_iUnion.mpr
      ⟨⟨natDegree_le_rankOfDiscrBdd hK a ha₁, abs_coeff_minpoly_le_coeffBoundOfDiscrBdd
        (rank_le_rankOfDiscrBdd hK) ((le_iff_le (a : K) _).mp haM)⟩, ?_⟩⟩
    -- `a` is a root of its own `ℤ`-minimal polynomial, mapped into `A`.
    have hroot : ((minpoly ℤ (a : K)).map (algebraMap ℤ A)).IsRoot (a : A) := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact (aeval_algebraMap_eq_zero_iff A (a : K) _).mpr (minpoly.aeval ℤ (a : K))
    exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr
      ⟨((minpoly.monic a.isIntegral_coe).map (algebraMap ℤ A)).ne_zero, hroot⟩))
  · exact ((IntermediateField.lift_adjoin_simple ℚ K (a : K)).symm.trans
      ((congr_arg (IntermediateField.lift (F := K)) ha₁).trans
        (IntermediateField.lift_top ℚ K))).symm

variable (N : ℕ)

/-- **Effective Hermite--Minkowski.** Inside a fixed extension `A / ℚ`, the number of number fields
`K` (finite extensions of `ℚ`) with `|discr K| ≤ N` is at most
`(2 * coeffBoundOfDiscrBdd N + 1) ^ (rankOfDiscrBdd N + 1) * rankOfDiscrBdd N`, an explicit function
of `N` alone. This upgrades Mathlib's `NumberField.finite_of_discr_bdd` from finiteness to an
explicit count. -/
theorem ncard_setOf_finiteDimensional_abs_discr_le_le :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (N : ℤ)}.ncard ≤
      (2 * coeffBoundOfDiscrBdd N + 1) ^ (rankOfDiscrBdd N + 1) * rankOfDiscrBdd N := by
  classical
  set D := rankOfDiscrBdd N with hD
  set C := coeffBoundOfDiscrBdd N with hC
  set S := {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
      |discr K| ≤ (N : ℤ)} with hS
  have hfin : {E : IntermediateField ℚ A | ∃ x ∈ (⋃ (f : ℤ[X])
        (_ : f.natDegree ≤ D ∧ ∀ i, |f.coeff i| ≤ (C : ℤ)),
        ((f.map (algebraMap ℤ A)).roots.toFinset : Set A)), E = ℚ⟮x⟯}.Finite :=
    finite_setOf_exists_mem_eq_adjoin_simple_roots_natDegree_le_abs_intCoeff A D C
  have hsub : Subtype.val '' S ⊆ {E : IntermediateField ℚ A | ∃ x ∈ (⋃ (f : ℤ[X])
      (_ : f.natDegree ≤ D ∧ ∀ i, |f.coeff i| ≤ (C : ℤ)),
      ((f.map (algebraMap ℤ A)).roots.toFinset : Set A)), E = ℚ⟮x⟯} := by
    rintro E ⟨⟨K, hK₀⟩, hKmem, rfl⟩
    exact exists_mem_rootSet_eq_adjoin_of_abs_discr_le A K hK₀ hKmem
  calc S.ncard = (Subtype.val '' S).ncard :=
        (Set.ncard_image_of_injective S Subtype.val_injective).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin
    _ ≤ (2 * C + 1) ^ (D + 1) * D :=
        ncard_setOf_exists_mem_eq_adjoin_simple_roots_natDegree_le_abs_intCoeff_le A D C

/-- The elementary polynomial count appearing in effective Hermite--Minkowski: if every field is
generated by a root of an integer polynomial of degree at most `D` and coefficient height at most
`C`, then the number of possible generated fields is bounded by
`(2 * C + 1) ^ (D + 1) * D`. -/
def hermiteCountBound (D C : ℕ) : ℕ :=
  (2 * C + 1) ^ (D + 1) * D

@[simp]
theorem hermiteCountBound_def (D C : ℕ) :
    hermiteCountBound D C = (2 * C + 1) ^ (D + 1) * D :=
  by simp [hermiteCountBound]

theorem hermiteCountBound_zero_left (C : ℕ) : hermiteCountBound 0 C = 0 := by
  simp [hermiteCountBound]

theorem hermiteCountBound_zero_right (D : ℕ) : hermiteCountBound D 0 = D := by
  simp [hermiteCountBound]

/-- The Hermite-count expression is monotone in the degree bound and the coefficient-height
bound. -/
theorem hermiteCountBound_mono {D₁ D₂ C₁ C₂ : ℕ} (hD : D₁ ≤ D₂) (hC : C₁ ≤ C₂) :
    hermiteCountBound D₁ C₁ ≤ hermiteCountBound D₂ C₂ := by
  unfold hermiteCountBound
  gcongr
  omega

attribute [gcongr] hermiteCountBound_mono

/-- The effective Hermite--Minkowski count with the exact constants packaged as
`hermiteCountBound`. -/
theorem ncard_setOf_finiteDimensional_abs_discr_le_le_hermiteCountBound (N : ℕ) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (N : ℤ)}.ncard ≤
      hermiteCountBound (rankOfDiscrBdd N) (coeffBoundOfDiscrBdd N) := by
  simpa [hermiteCountBound] using
    ncard_setOf_finiteDimensional_abs_discr_le_le (A := A) N

/-- **Monotone effective Hermite--Minkowski.** If `D` and `C` are any explicit bounds above
Mathlib's degree bound `rankOfDiscrBdd N` and the coefficient bound `coeffBoundOfDiscrBdd N`, then
the number of finite-dimensional subfields of an ambient extension `A / ℚ` with discriminant at
most `N` is bounded by `(2 * C + 1) ^ (D + 1) * D`.

This is the usable form for later explicit estimates, where `D` and `C` are often replaced by
simpler closed-form upper bounds. -/
theorem ncard_setOf_finiteDimensional_abs_discr_le_le_of_bounds (N D C : ℕ)
    (hD : rankOfDiscrBdd N ≤ D) (hC : coeffBoundOfDiscrBdd N ≤ C) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (N : ℤ)}.ncard ≤
      hermiteCountBound D C :=
  (ncard_setOf_finiteDimensional_abs_discr_le_le_hermiteCountBound (A := A) N).trans
    (hermiteCountBound_mono hD hC)

/-- The bounded-discriminant subfields at threshold `N` form a subset of those at threshold `M`
whenever `N ≤ M`. -/
private theorem setOf_finiteDimensional_abs_discr_le_subset_of_le {N M : ℕ} (hNM : N ≤ M) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (N : ℤ)} ⊆
      {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (M : ℤ)} := by
  intro K hK
  haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
  exact @le_trans ℤ _ |discr K| (N : ℤ) (M : ℤ) hK (by exact_mod_cast hNM)

/-- **Threshold-monotone effective Hermite--Minkowski.** If `N ≤ M`, then the number of
finite-dimensional subfields of an ambient extension `A / ℚ` with absolute discriminant at most `N`
is bounded by the explicit Hermite-count expression attached to the larger threshold `M`. -/
theorem ncard_setOf_finiteDimensional_abs_discr_le_le_of_threshold_le {N M : ℕ}
    (hNM : N ≤ M) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (N : ℤ)}.ncard ≤
      hermiteCountBound (rankOfDiscrBdd M) (coeffBoundOfDiscrBdd M) :=
  (Set.ncard_le_ncard (setOf_finiteDimensional_abs_discr_le_subset_of_le (A := A) hNM)
      (NumberField.finite_of_discr_bdd A M)).trans
    (ncard_setOf_finiteDimensional_abs_discr_le_le_hermiteCountBound (A := A) M)

/-- **Threshold-monotone effective Hermite--Minkowski with coarser constants.** If `N ≤ M`, and
`D` and `C` bound the degree and coefficient-height constants attached to `M`, then the number of
finite-dimensional subfields of an ambient extension `A / ℚ` with absolute discriminant at most `N`
is at most `hermiteCountBound D C`. -/
theorem ncard_setOf_finiteDimensional_abs_discr_le_le_of_threshold_bounds {N M D C : ℕ}
    (hNM : N ≤ M) (hD : rankOfDiscrBdd M ≤ D) (hC : coeffBoundOfDiscrBdd M ≤ C) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (N : ℤ)}.ncard ≤ hermiteCountBound D C :=
  (ncard_setOf_finiteDimensional_abs_discr_le_le_of_threshold_le (A := A) hNM).trans
    (hermiteCountBound_mono hD hC)

/-- The subfields whose discriminant has natural absolute value at most `N` are contained in the
integer-absolute-value family used by Mathlib's Hermite theorem. -/
private theorem setOf_finiteDimensional_natAbs_discr_le_subset_abs_discr_le (N : ℕ) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        (discr K).natAbs ≤ N} ⊆
      {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        |discr K| ≤ (N : ℤ)} := by
  intro K hK
  haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
  -- The set predicate elaborates its own `haveI`; normalize the target to the local instance
  -- before rewriting `Int.natAbs`.
  change |discr K| ≤ (N : ℤ)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hK

/-- **Threshold-monotone effective Hermite--Minkowski, natural-discriminant form.** If `N ≤ M`,
then the number of finite-dimensional subfields of an ambient extension `A / ℚ` whose
discriminant has natural absolute value at most `N` is bounded by the explicit Hermite-count
expression attached to the larger threshold `M`. -/
theorem ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_threshold_le {N M : ℕ}
    (hNM : N ≤ M) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        (discr K).natAbs ≤ N}.ncard ≤
      hermiteCountBound (rankOfDiscrBdd M) (coeffBoundOfDiscrBdd M) :=
  (Set.ncard_le_ncard
      (setOf_finiteDimensional_natAbs_discr_le_subset_abs_discr_le (A := A) N)
      (NumberField.finite_of_discr_bdd A N)).trans
    (ncard_setOf_finiteDimensional_abs_discr_le_le_of_threshold_le (A := A) hNM)

/-- **Effective Hermite--Minkowski, natural-discriminant form.** Inside a fixed extension
`A / ℚ`, the number of finite-dimensional subfields whose discriminant has natural absolute value
at most `N` is bounded by the explicit Hermite-count expression attached to `N`. -/
theorem ncard_setOf_finiteDimensional_natAbs_discr_le_le_hermiteCountBound (N : ℕ) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        (discr K).natAbs ≤ N}.ncard ≤
      hermiteCountBound (rankOfDiscrBdd N) (coeffBoundOfDiscrBdd N) :=
  ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_threshold_le (A := A) le_rfl

/-- **Threshold-monotone effective Hermite--Minkowski with coarser constants,
natural-discriminant form.** If `N ≤ M`, and `D` and `C` bound the degree and coefficient-height
constants attached to `M`, then the number of finite-dimensional subfields of an ambient extension
`A / ℚ` whose discriminant has natural absolute value at most `N` is at most
`hermiteCountBound D C`. -/
theorem ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_threshold_bounds {N M D C : ℕ}
    (hNM : N ≤ M) (hD : rankOfDiscrBdd M ≤ D) (hC : coeffBoundOfDiscrBdd M ≤ C) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        (discr K).natAbs ≤ N}.ncard ≤ hermiteCountBound D C :=
  (ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_threshold_le (A := A) hNM).trans
    (hermiteCountBound_mono hD hC)

/-- **Monotone effective Hermite--Minkowski, natural-discriminant form.** If `D` and `C` bound the
degree and coefficient-height constants attached to `N`, then the number of finite-dimensional
subfields of an ambient extension `A / ℚ` whose discriminant has natural absolute value at most
`N` is at most `hermiteCountBound D C`. -/
theorem ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_bounds (N D C : ℕ)
    (hD : rankOfDiscrBdd N ≤ D) (hC : coeffBoundOfDiscrBdd N ≤ C) :
    {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        haveI : _root_.NumberField K := @NumberField.mk _ _ inferInstance K.prop
        (discr K).natAbs ≤ N}.ncard ≤ hermiteCountBound D C :=
  ncard_setOf_finiteDimensional_natAbs_discr_le_le_of_threshold_bounds
    (A := A) le_rfl hD hC

end TauCeti.NumberField
