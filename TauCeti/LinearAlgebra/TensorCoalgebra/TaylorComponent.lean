/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation

/-!
# Taylor components of composites of graded Taylor expansions

For the reduced tensor coalgebra `Tᶜ(M)`, the arity-`n` Taylor component of an endomorphism,
defined in `TauCeti.LinearAlgebra.TensorCoalgebra.Coderivation`, is its restriction to words of
length `n`, followed by projection to words of length one.

This file computes the Taylor components of a composite of two graded Taylor expansions.  On
homogeneous letters, specializing both expansions to the same Taylor map gives the square formula

`∑_{r+s+t=n} (-1)^(q (|x₁| + ⋯ + |xᵣ|))
  F(x₁,…,xᵣ,F(xᵣ₊₁,…,xᵣ₊ₛ),…,xₙ)`,

the suspended Stasheff sum when `q = 1`.  The general algebraic fact that a `q`-twisted
coderivation anticommuting with its Koszul twist has an ordinary coderivation as its square is in
`TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation`.  It also shows that the square vanishes
if and only if every arity component map vanishes.

Anticommutation with the twist expresses oddness when `q` is odd; when `q` is even the twist is the
identity and the hypothesis reduces to `b + b = 0`.  A later suspension bridge can discharge the
odd case from degree-one homogeneity and identify the displayed sums with the unsuspended
Stasheff identities.

## Main results

* `TauCeti.ReducedTensorWords.taylorComponent_gradedCoderiv_comp_gradedCoderiv_of_tprod`: the
  arity formula for a composite of two graded Taylor expansions.
* `taylorComponent_gradedCoderiv_comp_gradedCoderiv_of_tprod_of_homogeneous`:
  the corresponding signed formula on homogeneous letters.
* `TauCeti.ReducedTensorWords.taylorComponent_gradedCoderiv_comp_self_of_tprod`: the square
  specialization on pure tensors.
* `TauCeti.ReducedTensorWords.taylorComponent_gradedCoderiv_comp_self_of_tprod_of_homogeneous`:
  the signed Stasheff insertion formula for the square.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace ReducedTensorWords

section Ring

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- The Taylor component of a composite of graded Taylor expansions is obtained by applying the
outer Taylor map to every signed nonempty one-block collapse made by the inner expansion.  Only
the inner twist parameter occurs in the resulting formula. -/
theorem taylorComponent_gradedCoderiv_comp_gradedCoderiv_of_tprod
    (G : InternalGrading R M)
    (F₁ : ReducedTensorWords R M →ₗ[R] M) (q₁ : ℤ)
    (F₂ : ReducedTensorWords R M →ₗ[R] M) (q₂ : ℤ)
    {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    taylorComponent (gradedCoderiv G F₁ q₁ ∘ₗ gradedCoderiv G F₂ q₂) ⟨n, hn⟩
        (PiTensorProduct.tprod R x) =
      ∑ p ∈ Finset.range n, ∑ d ∈ Finset.Icc 1 (n - p),
        F₁ (splice R (InternalGrading.twistedTuple G q₂ x 0 p) 0 n p d
          (F₂ (subword R x p d))) := by
  calc
    _ = ∑ p ∈ Finset.range n, ∑ d ∈ Finset.range (n + 1),
        F₁ (splice R (InternalGrading.twistedTuple G q₂ x 0 p) 0 n p d
          (F₂ (subword R x p d))) := by
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

/-- The pure-tensor formula for the square of one graded Taylor expansion. -/
theorem taylorComponent_gradedCoderiv_comp_self_of_tprod
    (G : InternalGrading R M) (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ)
    {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    taylorComponent (gradedCoderiv G F q ∘ₗ gradedCoderiv G F q) ⟨n, hn⟩
        (PiTensorProduct.tprod R x) =
      ∑ p ∈ Finset.range n, ∑ d ∈ Finset.Icc 1 (n - p),
        F (splice R (InternalGrading.twistedTuple G q x 0 p) 0 n p d
          (F (subword R x p d))) :=
  taylorComponent_gradedCoderiv_comp_gradedCoderiv_of_tprod G F q F q hn x

/-- On homogeneous inputs, the Taylor component of a composite is an insertion sum with the
Koszul sign contributed by the inner twist and the degrees of the letters preceding the inserted
operation. -/
theorem taylorComponent_gradedCoderiv_comp_gradedCoderiv_of_tprod_of_homogeneous
    (G : InternalGrading R M)
    (F₁ : ReducedTensorWords R M →ₗ[R] M) (q₁ : ℤ)
    (F₂ : ReducedTensorWords R M →ₗ[R] M) (q₂ : ℤ)
    {n : ℕ} (hn : 0 < n) (x : Fin n → M) (𝒟 : Fin n → ℤ)
    (hx : ∀ i, x i ∈ G.piece (𝒟 i)) :
    taylorComponent (gradedCoderiv G F₁ q₁ ∘ₗ gradedCoderiv G F₂ q₂) ⟨n, hn⟩
        (PiTensorProduct.tprod R x) =
      ∑ p ∈ Finset.range n, ∑ d ∈ Finset.Icc 1 (n - p),
        (((q₂ * ∑ j ∈ Finset.range p,
          if h : j < n then 𝒟 ⟨j, h⟩ else 0).negOnePow : ℤ) : R) •
          F₁ (splice R x 0 n p d (F₂ (subword R x p d))) := by
  rw [taylorComponent_gradedCoderiv_comp_gradedCoderiv_of_tprod G F₁ q₁ F₂ q₂ hn x]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [splice_twistedTuple_smul G q₂ x 𝒟 hx p d, map_smul]

/-- On homogeneous inputs, the Taylor component of the square is the Stasheff insertion sum with
the Koszul sign contributed by the degrees of the letters preceding the inserted operation.  The
indices are exactly the decompositions `n = p + d + t` with `d ≥ 1`. -/
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
  exact taylorComponent_gradedCoderiv_comp_gradedCoderiv_of_tprod_of_homogeneous
    G F q F q hn x 𝒟 hx

end Ring

end ReducedTensorWords

end TauCeti
