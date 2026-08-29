/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import TauCeti.LinearAlgebra.Exact

/-!
# Finite Laurent support and graded dimension

A family of vector spaces indexed by `ℤ` has a Laurent-polynomial-valued graded dimension only
when every piece is finite-dimensional and only finitely many pieces are nonzero.  This file
packages those two conditions as `TauCeti.HasFiniteLaurentSupport` and defines
`TauCeti.gradedDimension` without using a totalized infinite sum.

For a family `V`, `gradedDimension k V h` has coefficient
`dim_k(V j)` in degree `j`.  The companion `targetShiftGradedDimension` implements the convention
used by the Grothendieck--Euler roadmap for target shifts:

```text
qdim(V) = ∑ j, q⁻ʲ dim_k(V j).
```

Both definitions are built from the canonical finitely supported function of dimensions, so no
chosen support appears in their public API.  The finite-sum theorems allow calculations with any
explicit bounding finset, while coefficient lemmas characterize the resulting Laurent polynomial.

## Main definitions

* `TauCeti.HasFiniteLaurentSupport`: termwise finite-dimensionality and finite support.
* `TauCeti.gradedDimension`: the Laurent polynomial with coefficient `dim_k(V j)` at `j`.
* `TauCeti.targetShiftGradedDimension`: the target-shift convention with exponent `-j`.

The predicate is closed under degreewise exact sequences, and both dimension conventions are
additive on degreewise short exact sequences.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 2.2, for graded dimensions and the
  target-shift convention.
* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layer 6, "Finite Laurent support".
-/

public section

namespace TauCeti

open LaurentPolynomial

universe u v v'

variable (k : Type u) [DivisionRing k]
variable (V : ℤ → Type v) [∀ j, AddCommGroup (V j)] [∀ j, Module k (V j)]

/-- A `ℤ`-graded family of vector spaces has **finite Laurent support** when every homogeneous
piece is finite-dimensional and the set of degrees with nonzero dimension is finite.

The second field records the canonical support of the dimension function rather than a chosen
bounding finset.  For finite-dimensional vector spaces, zero dimension is equivalent to the
piece being a subsingleton; see `HasFiniteLaurentSupport.exists_finset` for that formulation. -/
structure HasFiniteLaurentSupport : Prop where
  /-- Every homogeneous piece is finite-dimensional. -/
  finiteDimensional (j : ℤ) : FiniteDimensional k (V j)
  /-- Only finitely many homogeneous pieces have nonzero dimension. -/
  finite_finrankSupport : (Function.support fun j => Module.finrank k (V j)).Finite

namespace HasFiniteLaurentSupport

variable {k V}

/-- A finite set outside which every piece is zero proves finite Laurent support. -/
theorem of_finset
    (hfinite : ∀ j, FiniteDimensional k (V j)) (s : Finset ℤ)
    (hzero : ∀ j, j ∉ s → Subsingleton (V j)) : HasFiniteLaurentSupport k V := by
  refine ⟨hfinite, s.finite_toSet.subset ?_⟩
  intro j hj
  by_contra hjs
  let _ := hzero j (by simpa using hjs)
  exact hj (Module.finrank_zero_of_subsingleton (R := k) (M := V j))

/-- Finite Laurent support can be exhibited by a finite set outside which every piece is zero. -/
theorem exists_finset (h : HasFiniteLaurentSupport k V) :
    ∃ s : Finset ℤ, ∀ j, j ∉ s → Subsingleton (V j) := by
  let s := h.finite_finrankSupport.toFinset
  refine ⟨s, fun j hj => ?_⟩
  let _ := h.finiteDimensional j
  rw [← Module.finrank_zero_iff (R := k) (M := V j)]
  by_contra hne
  exact hj (by simpa [s] using hne)

/-- A pointwise linear equivalence preserves finite Laurent support. -/
theorem of_equiv
    {W : ℤ → Type v'} [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)]
    (h : HasFiniteLaurentSupport k V) (e : ∀ j, V j ≃ₗ[k] W j) :
    HasFiniteLaurentSupport k W := by
  refine ⟨fun j => ?_, ?_⟩
  · let _ := h.finiteDimensional j
    exact Module.Finite.equiv (e j)
  have heq : (fun j => Module.finrank k (W j)) = fun j => Module.finrank k (V j) := by
    funext j
    exact (LinearEquiv.finrank_eq (e j)).symm
  rw [heq]
  exact h.finite_finrankSupport

/-- The degreewise product of two finitely Laurent-supported families is finitely supported. -/
theorem prod
    {W : ℤ → Type v'} [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)]
    (hV : HasFiniteLaurentSupport k V) (hW : HasFiniteLaurentSupport k W) :
    HasFiniteLaurentSupport k (fun j => V j × W j) := by
  obtain ⟨sV, hsV⟩ := hV.exists_finset
  obtain ⟨sW, hsW⟩ := hW.exists_finset
  refine of_finset (fun j => ?_) (sV ∪ sW) fun j hj => ?_
  · let _ := hV.finiteDimensional j
    let _ := hW.finiteDimensional j
    infer_instance
  · rw [Finset.mem_union, not_or] at hj
    let _ := hsV j hj.1
    let _ := hsW j hj.2
    infer_instance

/-- In a degreewise exact sequence, finite Laurent support of the outer families implies finite
Laurent support of the middle family. -/
theorem of_exact
    {U : ℤ → Type v'} [∀ j, AddCommGroup (U j)] [∀ j, Module k (U j)]
    {W : ℤ → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)]
    (hU : HasFiniteLaurentSupport k U) (hW : HasFiniteLaurentSupport k W)
    (f : ∀ j, U j →ₗ[k] V j) (g : ∀ j, V j →ₗ[k] W j)
    (hfg : ∀ j, Function.Exact (f j) (g j)) : HasFiniteLaurentSupport k V := by
  obtain ⟨sU, hsU⟩ := hU.exists_finset
  obtain ⟨sW, hsW⟩ := hW.exists_finset
  refine of_finset (fun j => ?_) (sU ∪ sW) fun j hj => ?_
  · let _ := hU.finiteDimensional j
    let _ := hW.finiteDimensional j
    exact finiteDimensional_of_exact (hfg j)
  · rw [Finset.mem_union, not_or] at hj
    let _ := hsU j hj.1
    let _ := hsW j hj.2
    exact subsingleton_of_exact (hfg j) (map_zero (f j))

end HasFiniteLaurentSupport

/-- The **graded dimension** of a finitely Laurent-supported family of vector spaces.  Its
coefficient in degree `j` is `dim_k(V j)`. -/
noncomputable def gradedDimension (h : HasFiniteLaurentSupport k V) : LaurentPolynomial ℤ :=
  AddMonoidAlgebra.ofCoeff <| Finsupp.ofSupportFinite
    (fun j => (Module.finrank k (V j) : ℤ)) <|
      Set.Finite.subset h.finite_finrankSupport fun _ hj hzero =>
        hj (Int.ofNat_eq_zero.mpr hzero)

variable {k V}

/-- The coefficient of the graded dimension is the dimension of the corresponding piece. -/
@[simp]
theorem coeff_gradedDimension (h : HasFiniteLaurentSupport k V) (j : ℤ) :
    (gradedDimension k V h).coeff j = Module.finrank k (V j) := by
  rw [gradedDimension, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.ofSupportFinite_coe]

/-- The support of the graded dimension is exactly the set of degrees with nonzero dimension. -/
theorem support_gradedDimension (h : HasFiniteLaurentSupport k V) :
    (gradedDimension k V h).coeff.support = h.finite_finrankSupport.toFinset := by
  ext j
  simp only [Finsupp.mem_support_iff, Set.Finite.mem_toFinset, Function.mem_support,
    coeff_gradedDimension]
  norm_cast

/-- Any finite set outside which the pieces vanish computes the graded dimension as a finite
sum.  Thus calculations do not depend on the particular support bound supplied by a caller. -/
theorem gradedDimension_eq_sum (h : HasFiniteLaurentSupport k V) (s : Finset ℤ)
    (hs : ∀ j, j ∉ s → Subsingleton (V j)) :
    gradedDimension k V h =
      ∑ j ∈ s, C (Module.finrank k (V j) : ℤ) * T j := by
  classical
  ext j
  rw [coeff_gradedDimension]
  simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single]
  rw [Finset.sum_apply']
  by_cases hj : j ∈ s
  · simp [Finsupp.single_apply, hj]
  · let _ := hs j hj
    simp [Finsupp.single_apply, hj,
      Module.finrank_zero_of_subsingleton (R := k) (M := V j)]

/-- Pointwise equality of dimensions determines the graded dimension. -/
theorem gradedDimension_congr
    {W : ℤ → Type v'} [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)]
    (hV : HasFiniteLaurentSupport k V) (hW : HasFiniteLaurentSupport k W)
    (hdim : ∀ j, Module.finrank k (V j) = Module.finrank k (W j)) :
    gradedDimension k V hV = gradedDimension k W hW := by
  ext j
  simp [hdim]

/-- Pointwise linear equivalences preserve graded dimension. -/
theorem gradedDimension_equiv
    {W : ℤ → Type v'} [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)]
    (hV : HasFiniteLaurentSupport k V) (e : ∀ j, V j ≃ₗ[k] W j) :
    gradedDimension k V hV = gradedDimension k W (hV.of_equiv e) :=
  gradedDimension_congr hV (hV.of_equiv e) fun j => LinearEquiv.finrank_eq (e j)

/-- The graded dimension vanishes exactly when every homogeneous piece is zero. -/
@[simp]
theorem gradedDimension_eq_zero_iff (h : HasFiniteLaurentSupport k V) :
    gradedDimension k V h = 0 ↔ ∀ j, Subsingleton (V j) := by
  constructor
  · intro hzero j
    let _ := h.finiteDimensional j
    rw [← Module.finrank_zero_iff (R := k) (M := V j)]
    have hc := congrArg (fun p : LaurentPolynomial ℤ => p.coeff j) hzero
    simpa using hc
  · intro hzero
    ext j
    let _ := hzero j
    simp [Module.finrank_zero_of_subsingleton (R := k) (M := V j)]

/-- Graded dimension is additive on degreewise direct sums. -/
theorem gradedDimension_prod
    {W : ℤ → Type v'} [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)]
    (hV : HasFiniteLaurentSupport k V) (hW : HasFiniteLaurentSupport k W) :
    gradedDimension k (fun j => V j × W j) (hV.prod hW) =
      gradedDimension k V hV + gradedDimension k W hW := by
  ext j
  let _ := hV.finiteDimensional j
  let _ := hW.finiteDimensional j
  simp [Module.finrank_prod]

/-- Graded dimension is additive on a degreewise short exact sequence. -/
theorem gradedDimension_shortExact
    {U : ℤ → Type v'} [∀ j, AddCommGroup (U j)] [∀ j, Module k (U j)]
    {W : ℤ → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)]
    (hU : HasFiniteLaurentSupport k U) (hW : HasFiniteLaurentSupport k W)
    (f : ∀ j, U j →ₗ[k] V j) (g : ∀ j, V j →ₗ[k] W j)
    (hinj : ∀ j, Function.Injective (f j)) (hfg : ∀ j, Function.Exact (f j) (g j))
    (hsurj : ∀ j, Function.Surjective (g j)) :
    gradedDimension k V (HasFiniteLaurentSupport.of_exact hU hW f g hfg) =
      gradedDimension k U hU + gradedDimension k W hW := by
  ext j
  simp only [coeff_gradedDimension, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  let _ := hU.finiteDimensional j
  let _ := hW.finiteDimensional j
  let _ := finiteDimensional_of_exact (hfg j)
  have hrank := (g j).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (hsurj j), finrank_top, (hfg j).linearMap_ker_eq,
    LinearMap.finrank_range_of_inj (hinj j)] at hrank
  norm_cast
  omega

/-- The graded dimension in the **target-shift convention**: the piece indexed by `j` contributes
`dim_k(V j) q⁻ʲ`.  This is `gradedDimension` with the standard Laurent involution applied. -/
noncomputable def targetShiftGradedDimension (k : Type u) [DivisionRing k]
    (V : ℤ → Type v) [∀ j, AddCommGroup (V j)] [∀ j, Module k (V j)]
    (h : HasFiniteLaurentSupport k V) :
    LaurentPolynomial ℤ :=
  LaurentPolynomial.invert (gradedDimension k V h)

/-- The coefficient at exponent `j` in the target-shift graded dimension is the dimension of the
piece indexed by `-j`. -/
@[simp]
theorem coeff_targetShiftGradedDimension (h : HasFiniteLaurentSupport k V) (j : ℤ) :
    (targetShiftGradedDimension k V h).coeff j = Module.finrank k (V (-j)) := by
  simp [targetShiftGradedDimension]

/-- The support of the target-shift graded dimension is the negation of the set of degrees with
nonzero dimension. -/
theorem support_targetShiftGradedDimension (h : HasFiniteLaurentSupport k V) :
    (targetShiftGradedDimension k V h).coeff.support =
      h.finite_finrankSupport.toFinset.image fun j => -j := by
  classical
  ext j
  simp only [Finsupp.mem_support_iff, coeff_targetShiftGradedDimension, Finset.mem_image,
    Set.Finite.mem_toFinset, Function.mem_support]
  norm_cast
  constructor
  · intro hj
    exact ⟨-j, by simpa using hj, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    rw [neg_neg]
    exact hi

/-- Pointwise equality of dimensions determines the target-shift graded dimension. -/
theorem targetShiftGradedDimension_congr
    {W : ℤ → Type v'} [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)]
    (hV : HasFiniteLaurentSupport k V) (hW : HasFiniteLaurentSupport k W)
    (hdim : ∀ j, Module.finrank k (V j) = Module.finrank k (W j)) :
    targetShiftGradedDimension k V hV = targetShiftGradedDimension k W hW := by
  simp only [targetShiftGradedDimension]
  rw [gradedDimension_congr hV hW hdim]

/-- Pointwise linear equivalences preserve target-shift graded dimension. -/
theorem targetShiftGradedDimension_equiv
    {W : ℤ → Type v'} [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)]
    (hV : HasFiniteLaurentSupport k V) (e : ∀ j, V j ≃ₗ[k] W j) :
    targetShiftGradedDimension k V hV =
      targetShiftGradedDimension k W (hV.of_equiv e) :=
  targetShiftGradedDimension_congr hV (hV.of_equiv e) fun j =>
    LinearEquiv.finrank_eq (e j)

/-- The target-shift graded dimension vanishes exactly when every homogeneous piece is zero. -/
@[simp]
theorem targetShiftGradedDimension_eq_zero_iff (h : HasFiniteLaurentSupport k V) :
    targetShiftGradedDimension k V h = 0 ↔ ∀ j, Subsingleton (V j) := by
  simp [targetShiftGradedDimension]

/-- An explicit support bound computes the target-shift graded dimension as
`∑ j, dim_k(V j) q⁻ʲ`. -/
theorem targetShiftGradedDimension_eq_sum (h : HasFiniteLaurentSupport k V) (s : Finset ℤ)
    (hs : ∀ j, j ∉ s → Subsingleton (V j)) :
    targetShiftGradedDimension k V h =
      ∑ j ∈ s, C (Module.finrank k (V j) : ℤ) * T (-j) := by
  rw [targetShiftGradedDimension, gradedDimension_eq_sum h s hs, map_sum]
  exact Finset.sum_congr rfl fun j _ => by simp

/-- Target-shift graded dimension is additive on degreewise direct sums. -/
theorem targetShiftGradedDimension_prod
    {W : ℤ → Type v'} [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)]
    (hV : HasFiniteLaurentSupport k V) (hW : HasFiniteLaurentSupport k W) :
    targetShiftGradedDimension k (fun j => V j × W j) (hV.prod hW) =
      targetShiftGradedDimension k V hV + targetShiftGradedDimension k W hW := by
  simp only [targetShiftGradedDimension]
  rw [gradedDimension_prod hV hW, map_add]

/-- Target-shift graded dimension is additive on a degreewise short exact sequence. -/
theorem targetShiftGradedDimension_shortExact
    {U : ℤ → Type v'} [∀ j, AddCommGroup (U j)] [∀ j, Module k (U j)]
    {W : ℤ → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)]
    (hU : HasFiniteLaurentSupport k U) (hW : HasFiniteLaurentSupport k W)
    (f : ∀ j, U j →ₗ[k] V j) (g : ∀ j, V j →ₗ[k] W j)
    (hinj : ∀ j, Function.Injective (f j)) (hfg : ∀ j, Function.Exact (f j) (g j))
    (hsurj : ∀ j, Function.Surjective (g j)) :
    targetShiftGradedDimension k V (HasFiniteLaurentSupport.of_exact hU hW f g hfg) =
      targetShiftGradedDimension k U hU + targetShiftGradedDimension k W hW := by
  simp only [targetShiftGradedDimension]
  rw [gradedDimension_shortExact hU hW f g hinj hfg hsurj, map_add]

end TauCeti
