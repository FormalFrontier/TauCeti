/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation

/-!
# Taylor components of composites of graded coderivations

For the reduced tensor coalgebra `Tᶜ(M)`, the arity-`n` Taylor component of an endomorphism is
its restriction to words of length `n`, followed by projection to words of length one.  A
coderivation is zero exactly when all these components vanish.

This file computes the Taylor components of the graded Taylor expansion and of its square.  On
homogeneous letters the square's component is

`∑_{r+s+t=n} (-1)^(q (|x₁| + ⋯ + |xᵣ|))
  F(x₁,…,xᵣ,F(xᵣ₊₁,…,xᵣ₊ₛ),…,xₙ)`,

the suspended Stasheff sum when `q = 1`.  The general algebraic fact that a `q`-twisted
coderivation anticommuting with its Koszul twist has an ordinary coderivation as its square is in
`TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation`.  Consequently its square vanishes if
and only if every displayed Taylor component vanishes.

The anticommutation hypothesis is the intrinsic oddness condition used in the cancellation of the
two mixed co-Leibniz terms.  A later suspension bridge can discharge it from degree-one
homogeneity and identify the displayed sums with the unsuspended Stasheff identities.

## Main definitions

* `TauCeti.ReducedTensorWords.taylorComponent`: the arity component of a linear endomorphism of
  reduced tensor words.

## Main results

* `TauCeti.ReducedTensorWords.IsCoderivation.eq_zero_iff_taylorComponent_eq_zero`: a coderivation
  vanishes exactly when all of its Taylor components vanish.
* `TauCeti.ReducedTensorWords.taylorComponent_gradedCoderiv_comp_self_of_tprod_of_homogeneous`:
  the signed arity formula for the square of a graded Taylor expansion.
* `TauCeti.ReducedTensorWords.taylorComponent_gradedCoderiv`: the Taylor component of a graded
  Taylor expansion is the corresponding restriction of its defining Taylor map.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace ReducedTensorWords

section Semiring

variable {R : Type uR} {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The arity-`n` Taylor component of an endomorphism of reduced tensor words: include a word of
length `n`, apply the endomorphism, and retain its length-one component. -/
noncomputable def taylorComponent
    (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) (n : {n : ℕ // 0 < n}) :
    TensorPower R n.1 M →ₗ[R] M :=
  (letter R M ∘ₗ b) ∘ₗ of R M n

/-- Evaluation of a Taylor component is restriction to words of the specified length followed by
the projection to letters. -/
@[simp]
theorem taylorComponent_apply
    (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) (n : {n : ℕ // 0 < n})
    (x : TensorPower R n.1 M) :
    taylorComponent b n x = letter R M (b (of R M n x)) :=
  (rfl)

/-- A coderivation vanishes exactly when each of its aritywise Taylor components vanishes. -/
theorem IsCoderivation.eq_zero_iff_taylorComponent_eq_zero
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hb : IsCoderivation R b) :
    b = 0 ↔ ∀ n, taylorComponent b n = 0 := by
  constructor
  · rintro rfl n
    simp [taylorComponent]
  · intro h
    have hzero : IsCoderivation R
        (0 : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) := by
      rw [isCoderivation_iff]
      simp
    apply hb.eq_of_letter_comp_eq hzero
    apply linearMap_ext R M
    intro n x
    have hn := LinearMap.congr_fun (h n) (PiTensorProduct.tprod R x)
    simpa [taylorComponent, LinearMap.comp_apply] using hn

end Semiring

section Ring

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- The arity-`n` Taylor component of a graded Taylor expansion is the restriction of its
defining Taylor map to words of length `n`. -/
@[simp]
theorem taylorComponent_gradedCoderiv (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) (n : {n : ℕ // 0 < n}) :
    taylorComponent (gradedCoderiv G F q) n = F ∘ₗ of R M n := by
  rw [taylorComponent, letter_comp_gradedCoderiv]

/-- Under the intrinsic oddness relation, a graded coderivation squares to zero exactly when all
Taylor components of its square vanish. -/
theorem IsGradedCoderivation.comp_self_eq_zero_iff_taylorComponent_eq_zero
    {G : InternalGrading R M} {q : ℤ}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : IsGradedCoderivation G q b)
    (hodd : b ∘ₗ ReducedTensorWords.map (R := R) (InternalGrading.koszulTwist G q) +
        ReducedTensorWords.map (R := R) (InternalGrading.koszulTwist G q) ∘ₗ b = 0) :
    b ∘ₗ b = 0 ↔ ∀ n, taylorComponent (b ∘ₗ b) n = 0 :=
  (hb.isCoderivation_comp_self hodd).eq_zero_iff_taylorComponent_eq_zero

/-- The Taylor component of the square of a graded Taylor expansion is obtained by applying the
outer Taylor map to every signed nonempty one-block collapse made by the inner expansion. -/
theorem taylorComponent_gradedCoderiv_comp_self_of_tprod
    (G : InternalGrading R M) (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ)
    {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    taylorComponent (gradedCoderiv G F q ∘ₗ gradedCoderiv G F q) ⟨n, hn⟩
        (PiTensorProduct.tprod R x) =
      ∑ p ∈ Finset.range n, ∑ d ∈ Finset.Icc 1 (n - p),
        F (splice R (InternalGrading.twistedTuple G q x 0 p) 0 n p d
          (F (subword R x p d))) := by
  calc
    _ = ∑ p ∈ Finset.range n, ∑ d ∈ Finset.range (n + 1),
        F (splice R (InternalGrading.twistedTuple G q x 0 p) 0 n p d
          (F (subword R x p d))) := by
      rw [taylorComponent_apply]
      simp only [LinearMap.comp_apply]
      rw [← LinearMap.comp_apply (letter R M), letter_comp_gradedCoderiv,
        gradedCoderiv_of_tprod, map_sum]
      exact Finset.sum_congr rfl fun p _ ↦ by rw [map_sum]
    _ = _ := by
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      apply (Finset.sum_subset ?_ ?_).symm
      · intro d hd
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_range]
        omega
      · intro d _ hd
        have hfit : ¬(0 < d ∧ p + d ≤ n) := by
          intro h
          apply hd
          rw [Finset.mem_Icc]
          omega
        rw [splice_eq_zero_of_not_fits R _ _ hfit, map_zero]

/-- On homogeneous inputs, the Taylor component of the square is the Stasheff insertion sum with
the Koszul sign contributed by the degrees of the letters preceding the inserted operation. -/
theorem taylorComponent_gradedCoderiv_comp_self_of_tprod_of_homogeneous
    (G : InternalGrading R M) (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ)
    {n : ℕ} (hn : 0 < n) (x : Fin n → M) (𝒟 : Fin n → ℤ)
    (hx : ∀ i, x i ∈ G.piece (𝒟 i)) :
    taylorComponent (gradedCoderiv G F q ∘ₗ gradedCoderiv G F q) ⟨n, hn⟩
        (PiTensorProduct.tprod R x) =
      ∑ p ∈ Finset.range n, ∑ d ∈ Finset.Icc 1 (n - p),
        (((q * ∑ j ∈ Finset.range p,
          if h : j < n then 𝒟 ⟨j, h⟩ else 0).negOnePow : ℤ) : R) •
          F (splice R x 0 n p d (F (subword R x p d))) := by
  calc
    _ = ∑ p ∈ Finset.range n, ∑ d ∈ Finset.range (n + 1),
        (((q * ∑ j ∈ Finset.range p,
          if h : j < n then 𝒟 ⟨j, h⟩ else 0).negOnePow : ℤ) : R) •
          F (splice R x 0 n p d (F (subword R x p d))) := by
      rw [taylorComponent_apply]
      simp only [LinearMap.comp_apply]
      rw [← LinearMap.comp_apply (letter R M), letter_comp_gradedCoderiv,
        gradedCoderiv_of_tprod_of_homogeneous G F q hn x 𝒟 hx, map_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [map_sum]
      exact Finset.sum_congr rfl fun d _ ↦ by rw [map_smul]
    _ = _ := by
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      apply (Finset.sum_subset ?_ ?_).symm
      · intro d hd
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_range]
        omega
      · intro d _ hd
        have hfit : ¬(0 < d ∧ p + d ≤ n) := by
          intro h
          apply hd
          rw [Finset.mem_Icc]
          omega
        rw [splice_eq_zero_of_not_fits R _ _ hfit, map_zero, smul_zero]

/-- For a twist-one coderivation, the coefficient in the square's Taylor component is the usual
Koszul sign of the total degree of the prefix.  The indices are exactly the decompositions
`n = p + d + t` with `d ≥ 1`. -/
theorem taylorComponent_gradedCoderiv_one_comp_self_of_tprod_of_homogeneous
    (G : InternalGrading R M) (F : ReducedTensorWords R M →ₗ[R] M)
    {n : ℕ} (hn : 0 < n) (x : Fin n → M) (𝒟 : Fin n → ℤ)
    (hx : ∀ i, x i ∈ G.piece (𝒟 i)) :
    taylorComponent (gradedCoderiv G F 1 ∘ₗ gradedCoderiv G F 1) ⟨n, hn⟩
        (PiTensorProduct.tprod R x) =
      ∑ p ∈ Finset.range n, ∑ d ∈ Finset.Icc 1 (n - p),
        (((∑ j ∈ Finset.range p,
          if h : j < n then 𝒟 ⟨j, h⟩ else 0).negOnePow : ℤ) : R) •
          F (splice R x 0 n p d (F (subword R x p d))) := by
  simpa using
    taylorComponent_gradedCoderiv_comp_self_of_tprod_of_homogeneous G F 1 hn x 𝒟 hx

end Ring

end ReducedTensorWords

end TauCeti
