/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Parity
public import TauCeti.LinearAlgebra.IntegralLattice.Norm

/-!
# Even integral lattices

An integral lattice is **even** when the integral norm of every lattice vector is an even integer.
This file characterizes evenness on generating sets, integral bases, and Gram matrices, and
establishes non-existence results for odd or non-even norm vectors in even lattices. It also proves
that evenness is invariant under integral-lattice isometry.

The basis characterization is the practical entry point: a lattice given by a Gram matrix is even
exactly when every diagonal entry is even. In particular, off-diagonal entries impose no parity
condition, because they occur twice in the norm of an integral linear combination.

## Main definitions and results

* `TauCeti.IntegralLattice.IsEven`: every lattice-vector norm is even.
* `TauCeti.IntegralLattice.even_integralNorm_iff`: rational characterization of pointwise evenness.
* `TauCeti.IntegralLattice.isEven_iff_forall_norm`: rational characterization of lattice evenness.
* `TauCeti.IntegralLattice.isEven_of_span`: evenness can be checked on any generating set.
* `TauCeti.IntegralLattice.isEven_iff_basis`: evenness can be checked on any integral basis.
* `TauCeti.IntegralLattice.isEven_ofBasis_iff`: an `ofBasis` lattice is even iff basis norms are
  even.
* `TauCeti.IntegralLattice.isEven_ofGramMatrix_iff`: a Gram lattice is even exactly when its
  diagonal entries are even.
* `TauCeti.IntegralLattice.Isometry.isEven_iff`: evenness is invariant under lattice isometry.
* `TauCeti.IntegralLattice.IsEven.exists_eq_two_mul_of_mem_vectorsOfNorm`: a norm represented by an
  even lattice is twice an integer.
* `TauCeti.IntegralLattice.IsEven.vectorsOfNorm_eq_empty_of_not_even`: an even lattice has no
  vector of odd integer norm.
* `TauCeti.IntegralLattice.IsEven.vectorsOfNorm_eq_empty_of_not_exists_two_mul`: an even lattice has
  no vector of non-even rational norm.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`
* `TauCetiRoadmap/IntegralLattices/Suggested.lean`
-/

public section

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

open Module

namespace IntegralLattice

/-! ## Evenness -/

/-- An integral lattice is even when the norm of every lattice vector is an even integer. -/
def IsEven (L : IntegralLattice V) : Prop := ∀ x : L, Even (L.integralNorm x)

/-- Pointwise equivalence between evenness of the integral norm and two-divisibility of the
rational norm in `ℚ`. -/
theorem even_integralNorm_iff (L : IntegralLattice V) (x : L) :
    Even (L.integralNorm x) ↔ ∃ z : ℤ, L.norm x = 2 * z := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [← L.integralNorm_cast x, hz]
    push_cast
    ring
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [L.integralNorm_cast, hz]
    ring

/-- Evenness is equivalently the existence of an integer halving every lattice-vector norm. -/
theorem isEven_iff_forall_norm (L : IntegralLattice V) :
    L.IsEven ↔ ∀ x : L, ∃ z : ℤ, L.norm x = 2 * z := by
  simp only [IsEven, even_integralNorm_iff]

/-- The norm of a vector in an even lattice is twice an integer, as an equality in `ℚ`. -/
theorem IsEven.exists_norm_eq_two_mul {L : IntegralLattice V} (hL : L.IsEven) (x : L) :
    ∃ z : ℤ, L.norm x = 2 * z :=
  (L.even_integralNorm_iff x).mp (hL x)

/-- The sum of two vectors with even integral norm again has even integral norm. -/
theorem even_integralNorm_add (L : IntegralLattice V) {x y : L}
    (hx : Even (L.integralNorm x)) (hy : Even (L.integralNorm y)) :
    Even (L.integralNorm (x + y)) := by
  rw [L.integralNorm_add]
  exact (hx.add hy).add (even_two_mul _)

/-- Every integer multiple of a vector with even integral norm has even integral norm. -/
theorem even_integralNorm_zsmul (L : IntegralLattice V) {x : L}
    (hx : Even (L.integralNorm x)) (a : ℤ) : Even (L.integralNorm (a • x)) := by
  rw [L.integralNorm_zsmul]
  exact hx.mul_left _

/-- It is enough to check evenness on any `ℤ`-spanning subset of lattice vectors. -/
theorem isEven_of_span (L : IntegralLattice V) {s : Set L} (hs : Submodule.span ℤ s = ⊤)
    (h : ∀ x ∈ s, Even (L.integralNorm x)) : L.IsEven := by
  intro x
  have hx : x ∈ Submodule.span ℤ s := by rw [hs]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem v hv => exact h v hv
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv => exact L.even_integralNorm_add hu hv
  | smul a u _ hu => exact L.even_integralNorm_zsmul hu a

/-- It is enough to check evenness on the vectors of any integral basis. -/
theorem isEven_iff_basis {ι : Type*} (L : IntegralLattice V) (b : Basis ι ℤ L) :
    L.IsEven ↔ ∀ i, Even (L.integralNorm (b i)) := by
  constructor
  · exact fun h i ↦ h (b i)
  · intro h
    exact L.isEven_of_span b.span_eq (by rintro x ⟨i, rfl⟩; exact h i)

/-- An `ofBasis` lattice is even exactly when every basis vector has an even self-pairing. -/
theorem isEven_ofBasis_iff {ι : Type*} [Finite ι] (b : Basis ι ℚ V)
    (B : LinearMap.BilinForm ℚ V) (hB : B.IsSymm)
    (hint : ∀ i j, B (b i) (b j) ∈ (1 : Submodule ℤ ℚ)) :
    (ofBasis b B hB hint).IsEven ↔ ∀ i, ∃ z : ℤ, B (b i) (b i) = 2 * z := by
  rw [isEven_iff_basis (ofBasis b B hB hint) (ofBasis.basis b B hB hint)]
  apply forall_congr'
  intro i
  rw [even_integralNorm_iff, norm_apply, ofBasis_form, ofBasis.coe_basis]

/-- A lattice constructed from a Gram matrix is even exactly when every diagonal entry is even. -/
theorem isEven_ofGramMatrix_iff {ι : Type*} [Fintype ι] (b : Basis ι ℚ V)
    (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    (ofGramMatrix b G hG).IsEven ↔ ∀ i, Even (G i i) := by
  rw [isEven_iff_basis (ofGramMatrix b G hG) (ofGramMatrix.basis b G hG)]
  apply forall_congr'
  intro i
  rw [integralNorm_apply, integralForm_ofGramMatrix_apply]

/-- Evenness is invariant under integral-lattice isometry. -/
theorem Isometry.isEven_iff {W : Type*} [AddCommGroup W] [Module ℚ W]
    {L : IntegralLattice V} {M : IntegralLattice W} (e : Isometry L M) :
    L.IsEven ↔ M.IsEven := by
  constructor
  · intro hL y
    have h := hL (e.carrierEquiv.symm y)
    have hnorm := e.integralNorm_carrierEquiv (e.carrierEquiv.symm y)
    rw [LinearEquiv.apply_symm_apply] at hnorm
    rw [hnorm]
    exact h
  · intro hM x
    have h := hM (e.carrierEquiv x)
    rwa [e.integralNorm_carrierEquiv] at h

/-! ## Prescribed norm properties for even lattices -/

/-- A norm represented by an even lattice is twice an integer. -/
theorem IsEven.exists_eq_two_mul_of_mem_vectorsOfNorm {L : IntegralLattice V} (hL : L.IsEven)
    {n : ℚ} {x : L} (hx : x ∈ L.vectorsOfNorm n) : ∃ z : ℤ, n = 2 * z := by
  obtain ⟨z, hz⟩ := hL.exists_norm_eq_two_mul x
  have hx' : L.norm x = n := mem_vectorsOfNorm.mp hx
  exact ⟨z, hx'.symm.trans hz⟩

/-- An even lattice has no vector of integer norm that is odd. -/
theorem IsEven.vectorsOfNorm_eq_empty_of_not_even (L : IntegralLattice V) (hL : L.IsEven) {n : ℤ}
    (hn : ¬ Even n) : L.vectorsOfNorm (n : ℚ) = ∅ := by
  ext x
  simp only [mem_vectorsOfNorm_intCast, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hn (hx ▸ hL x)

/-- An even lattice has no vector of a rational norm that is not twice an integer. -/
theorem IsEven.vectorsOfNorm_eq_empty_of_not_exists_two_mul (L : IntegralLattice V) (hL : L.IsEven)
    {n : ℚ} (hn : ¬∃ z : ℤ, n = 2 * z) : L.vectorsOfNorm n = ∅ := by
  ext x
  simp only [mem_vectorsOfNorm, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hn (hL.exists_eq_two_mul_of_mem_vectorsOfNorm (mem_vectorsOfNorm.mpr hx))

end IntegralLattice

end TauCeti
