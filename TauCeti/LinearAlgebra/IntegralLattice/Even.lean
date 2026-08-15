/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Ring.Parity
public import TauCeti.LinearAlgebra.BilinearForm.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Basic

/-!
# Norms and even integral lattices

The norm of a vector in an integral lattice is its self-pairing.  On lattice vectors this
rational value has a canonical integral lift, and the lattice is **even** when every such lift is
an even integer.  This file develops the elementary norm identities, characterizes evenness on an
arbitrary integral basis, and defines the set of lattice vectors of a prescribed norm.

The basis characterization is the practical entry point: a lattice given by a Gram matrix is even
exactly when every diagonal entry is even.  In particular, off-diagonal entries impose no parity
condition, because they occur twice in the norm of an integral linear combination.

## Main definitions and results

* `TauCeti.IntegralLattice.norm`: the rational quadratic form on ambient vectors.
* `TauCeti.IntegralLattice.integralNorm`: the induced integer quadratic form on lattice vectors.
* `TauCeti.IntegralLattice.IsEven`: every lattice-vector norm is even.
* `TauCeti.IntegralLattice.even_integralNorm_iff`: rational characterization of pointwise evenness.
* `TauCeti.IntegralLattice.isEven_iff_forall_norm`: rational characterization of lattice evenness.
* `TauCeti.IntegralLattice.isEven_of_span`: evenness can be checked on any generating set.
* `TauCeti.IntegralLattice.isEven_iff_basis`: evenness can be checked on any integral basis.
* `TauCeti.IntegralLattice.isEven_ofBasis_iff`: an `ofBasis` lattice is even iff basis norms are
  even.
* `TauCeti.IntegralLattice.isEven_ofGramMatrix_iff`: a Gram lattice is even exactly when its
  diagonal entries are even.
* `TauCeti.IntegralLattice.vectorsOfNorm`: the lattice vectors of a specified rational norm.

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

/-! ## Norms -/

/-- The rational quadratic form on ambient vectors given by self-pairing. -/
def norm (L : IntegralLattice V) : QuadraticForm ℚ V := L.form.toQuadraticMap

-- The evaluation and negation identities below remain explicit rewrite lemmas. Registering them
-- with `simp` makes the specialized cast, zero, and scaling rules fail the `simpNF` linter.

/-- Evaluating the rational norm of an ambient vector yields its self-pairing. -/
theorem norm_apply (L : IntegralLattice V) (x : V) : L.norm x = L.form x x :=
  LinearMap.BilinMap.toQuadraticMap_apply L.form x

/-- The canonical integer quadratic form induced on the lattice carrier. -/
noncomputable def integralNorm (L : IntegralLattice V) : QuadraticForm ℤ L :=
  L.integralForm.toQuadraticMap

/-- Evaluating the integral norm of a lattice vector yields its integral self-pairing. -/
theorem integralNorm_apply (L : IntegralLattice V) (x : L) :
    L.integralNorm x = L.integralForm x x :=
  LinearMap.BilinMap.toQuadraticMap_apply L.integralForm x

/-- The integral norm recovers the rational norm after coercion to `ℚ`. -/
@[simp]
theorem integralNorm_cast (L : IntegralLattice V) (x : L) :
    (L.integralNorm x : ℚ) = L.norm x := by
  simpa only [integralNorm_apply, norm_apply] using L.integralForm_cast x x

/-- The rational norm of zero is zero. -/
@[simp]
theorem norm_zero (L : IntegralLattice V) : L.norm 0 = 0 :=
  L.norm.map_zero

/-- The rational norm is invariant under negation. -/
theorem norm_neg (L : IntegralLattice V) (x : V) : L.norm (-x) = L.norm x :=
  L.norm.map_neg x

/-- Scaling an ambient vector squares its rational norm. -/
@[simp]
theorem norm_smul (L : IntegralLattice V) (a : ℚ) (x : V) :
    L.norm (a • x) = a ^ 2 * L.norm x := by
  rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]

/-- Polarization of the norm using symmetry of the lattice form. -/
theorem norm_add (L : IntegralLattice V) (x y : V) :
    L.norm (x + y) = L.norm x + L.norm y + 2 * L.form x y :=
  L.isSymm.toQuadraticMap_add x y

/-- The subtraction form of the norm polarization identity. -/
theorem norm_sub (L : IntegralLattice V) (x y : V) :
    L.norm (x - y) = L.norm x + L.norm y - 2 * L.form x y :=
  L.isSymm.toQuadraticMap_sub x y

/-- The integral norm of zero is zero. -/
@[simp]
theorem integralNorm_zero (L : IntegralLattice V) : L.integralNorm 0 = 0 :=
  L.integralNorm.map_zero

/-- The integral norm is invariant under negation. -/
theorem integralNorm_neg (L : IntegralLattice V) (x : L) :
    L.integralNorm (-x) = L.integralNorm x :=
  L.integralNorm.map_neg x

/-- Scaling a lattice vector by an integer scales its integral norm by the square. -/
@[simp]
theorem integralNorm_zsmul (L : IntegralLattice V) (a : ℤ) (x : L) :
    L.integralNorm (a • x) = a ^ 2 * L.integralNorm x := by
  rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]

/-- Integral polarization of the norm. -/
theorem integralNorm_add (L : IntegralLattice V) (x y : L) :
    L.integralNorm (x + y) =
      L.integralNorm x + L.integralNorm y + 2 * L.integralForm x y :=
  L.isSymm_integralForm.toQuadraticMap_add x y

/-- Integral polarization for a difference. -/
theorem integralNorm_sub (L : IntegralLattice V) (x y : L) :
    L.integralNorm (x - y) =
      L.integralNorm x + L.integralNorm y - 2 * L.integralForm x y :=
  L.isSymm_integralForm.toQuadraticMap_sub x y

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
  rw [ofBasis.basis_apply, even_integralNorm_iff, norm_apply, ofBasis_form, ofBasis.coe_basisElem]

/-- A lattice constructed from a Gram matrix is even exactly when every diagonal entry is even. -/
theorem isEven_ofGramMatrix_iff {ι : Type*} [Fintype ι] (b : Basis ι ℚ V)
    (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    (ofGramMatrix b G hG).IsEven ↔ ∀ i, Even (G i i) := by
  rw [isEven_iff_basis (ofGramMatrix b G hG) (ofGramMatrix.basis b G hG)]
  apply forall_congr'
  intro i
  rw [ofGramMatrix.basis_apply, integralNorm_apply, integralForm_ofGramMatrix_apply]

/-! ## Vectors of prescribed norm -/

/-- The lattice vectors having the prescribed rational norm. -/
def vectorsOfNorm (L : IntegralLattice V) (n : ℚ) : Set L := {x | L.norm x = n}

/-- Membership condition for `vectorsOfNorm`. -/
@[simp]
theorem mem_vectorsOfNorm {L : IntegralLattice V} {n : ℚ} {x : L} :
    x ∈ L.vectorsOfNorm n ↔ L.norm x = n := Iff.rfl

/-- Membership in `vectorsOfNorm (n : ℚ)` for an integer `n` is equivalent to having integral norm
equal to `n`.  This remains an explicit rewrite lemma because `mem_vectorsOfNorm` already
simplifies its left-hand side, so tagging both lemmas would violate `simpNF`. -/
theorem mem_vectorsOfNorm_intCast (L : IntegralLattice V) {n : ℤ} {x : L} :
    x ∈ L.vectorsOfNorm (n : ℚ) ↔ L.integralNorm x = n := by
  rw [mem_vectorsOfNorm, ← L.integralNorm_cast x]
  exact Int.cast_inj

/-- The zero vector in an integral lattice has norm zero. -/
theorem zero_mem_vectorsOfNorm (L : IntegralLattice V) : (0 : L) ∈ L.vectorsOfNorm 0 := by
  simp

/-- A lattice vector has norm `n` if and only if its negation does. -/
theorem neg_mem_vectorsOfNorm_iff {L : IntegralLattice V} {n : ℚ} (x : L) :
    -x ∈ L.vectorsOfNorm n ↔ x ∈ L.vectorsOfNorm n := by
  simp [mem_vectorsOfNorm]

/-- If a rational number is not an integer, no lattice vector has that norm. -/
theorem vectorsOfNorm_eq_empty_of_forall_ne_intCast (L : IntegralLattice V) {n : ℚ}
    (hn : ∀ z : ℤ, n ≠ z) : L.vectorsOfNorm n = ∅ := by
  ext x
  simp only [mem_vectorsOfNorm, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hn (L.integralNorm x) (hx.symm.trans (L.integralNorm_cast x).symm)

/-- A norm represented by an even lattice is twice an integer. -/
theorem IsEven.exists_eq_two_mul_of_mem_vectorsOfNorm {L : IntegralLattice V} (hL : L.IsEven)
    {n : ℚ} {x : L} (hx : x ∈ L.vectorsOfNorm n) : ∃ z : ℤ, n = 2 * z := by
  obtain ⟨z, hz⟩ := hL.exists_norm_eq_two_mul x
  exact ⟨z, hx.symm.trans hz⟩

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
  exact hn (hL.exists_eq_two_mul_of_mem_vectorsOfNorm hx)

end IntegralLattice

end TauCeti
