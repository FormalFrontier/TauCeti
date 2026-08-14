/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.LinearAlgebra.Basis.Submodule
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

* `TauCeti.IntegralLattice.norm`: the rational self-pairing of an ambient vector.
* `TauCeti.IntegralLattice.integralNorm`: its canonical integer value on a lattice vector.
* `TauCeti.IntegralLattice.IsEven`: every lattice-vector norm is even.
* `TauCeti.IntegralLattice.isEven_iff_forall_basis`: evenness can be checked on any integral
  basis.
* `TauCeti.IntegralLattice.isEven_ofGramMatrix_iff`: a Gram lattice is even exactly when its
  diagonal entries are even.
* `TauCeti.IntegralLattice.roots`: the lattice vectors of a specified rational norm.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

open Module

namespace IntegralLattice

/-! ## Norms -/

/-- The rational norm of an ambient vector with respect to an integral lattice. -/
def norm (L : IntegralLattice V) (x : V) : ℚ := L.form x x

/-- The canonical integer lift of the norm of a lattice vector. -/
noncomputable def integralNorm (L : IntegralLattice V) (x : L) : ℤ := L.integralForm x x

/-- The integral norm recovers the rational norm after coercion to `ℚ`. -/
@[simp]
theorem integralNorm_cast (L : IntegralLattice V) (x : L) :
    (L.integralNorm x : ℚ) = L.norm x := by
  exact L.integralForm_cast x x

@[simp]
theorem norm_zero (L : IntegralLattice V) : L.norm 0 = 0 := by
  simp [norm]

@[simp]
theorem norm_neg (L : IntegralLattice V) (x : V) : L.norm (-x) = L.norm x := by
  simp [norm]

@[simp]
theorem norm_smul (L : IntegralLattice V) (a : ℚ) (x : V) :
    L.norm (a • x) = a ^ 2 * L.norm x := by
  simp only [norm, map_smul, LinearMap.smul_apply, smul_eq_mul, pow_two]
  ring

/-- Polarization of the norm using symmetry of the lattice form. -/
theorem norm_add (L : IntegralLattice V) (x y : V) :
    L.norm (x + y) = L.norm x + L.norm y + 2 * L.form x y := by
  simp only [norm, map_add, LinearMap.add_apply]
  rw [L.isSymm.eq y x]
  ring

/-- The subtraction form of the norm polarization identity. -/
theorem norm_sub (L : IntegralLattice V) (x y : V) :
    L.norm (x - y) = L.norm x + L.norm y - 2 * L.form x y := by
  rw [sub_eq_add_neg, L.norm_add, L.norm_neg]
  simp only [map_neg]
  ring

@[simp]
theorem integralNorm_zero (L : IntegralLattice V) : L.integralNorm 0 = 0 := by
  simp [integralNorm]

@[simp]
theorem integralNorm_neg (L : IntegralLattice V) (x : L) :
    L.integralNorm (-x) = L.integralNorm x := by
  simp [integralNorm]

@[simp]
theorem integralNorm_zsmul (L : IntegralLattice V) (a : ℤ) (x : L) :
    L.integralNorm (a • x) = a ^ 2 * L.integralNorm x := by
  simp [integralNorm, pow_two, mul_assoc]

/-- Integral polarization of the norm. -/
theorem integralNorm_add (L : IntegralLattice V) (x y : L) :
    L.integralNorm (x + y) =
      L.integralNorm x + L.integralNorm y + 2 * L.integralForm x y := by
  simp only [integralNorm, map_add, LinearMap.add_apply]
  rw [L.isSymm_integralForm.eq y x]
  ring

/-- Integral polarization for a difference. -/
theorem integralNorm_sub (L : IntegralLattice V) (x y : L) :
    L.integralNorm (x - y) =
      L.integralNorm x + L.integralNorm y - 2 * L.integralForm x y := by
  rw [sub_eq_add_neg, L.integralNorm_add, L.integralNorm_neg]
  simp only [map_neg]
  ring

/-! ## Evenness -/

/-- An integral lattice is even when the norm of every lattice vector is an even integer. -/
def IsEven (L : IntegralLattice V) : Prop := ∀ x : L, Even (L.integralNorm x)

/-- Evenness is equivalently divisibility of every integral norm by two. -/
theorem isEven_iff_two_dvd (L : IntegralLattice V) :
    L.IsEven ↔ ∀ x : L, 2 ∣ L.integralNorm x := by
  simp only [IsEven, even_iff_two_dvd]

/-- The norm of a vector in an even lattice is twice an integer, as an equality in `ℚ`. -/
theorem IsEven.exists_norm_eq_two_mul {L : IntegralLattice V} (hL : L.IsEven) (x : L) :
    ∃ z : ℤ, L.norm x = 2 * z := by
  obtain ⟨z, hz⟩ := hL x
  refine ⟨z, ?_⟩
  rw [← L.integralNorm_cast x, hz]
  norm_num
  ring

/-- The sum of two vectors with even integral norm again has even integral norm. -/
theorem even_integralNorm_add (L : IntegralLattice V) {x y : L}
    (hx : Even (L.integralNorm x)) (hy : Even (L.integralNorm y)) :
    Even (L.integralNorm (x + y)) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b + L.integralForm x y, ?_⟩
  rw [L.integralNorm_add, ha, hb]
  ring

/-- Every integer multiple of a vector with even integral norm has even integral norm. -/
theorem even_integralNorm_zsmul (L : IntegralLattice V) {x : L}
    (hx : Even (L.integralNorm x)) (a : ℤ) : Even (L.integralNorm (a • x)) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨a ^ 2 * z, ?_⟩
  rw [L.integralNorm_zsmul, hz]
  ring

/-- It is enough to check evenness on the vectors of any integral basis. -/
theorem isEven_iff_forall_basis {ι : Type*} (L : IntegralLattice V) (b : Basis ι ℤ L) :
    L.IsEven ↔ ∀ i, Even (L.integralNorm (b i)) := by
  constructor
  · exact fun h i ↦ h (b i)
  · intro h x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact h i
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy => exact L.even_integralNorm_add hx hy
    | smul a x _ hx => exact L.even_integralNorm_zsmul hx a

/-- A lattice constructed from a Gram matrix is even exactly when every diagonal entry is even. -/
theorem isEven_ofGramMatrix_iff {ι : Type*} [Fintype ι] (b : Basis ι ℚ V)
    (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    (ofGramMatrix b G hG).IsEven ↔ ∀ i, Even (G i i) := by
  let bInt : Basis ι ℤ (ofGramMatrix b G hG).carrier :=
    (b.restrictScalars ℤ).map
      (LinearEquiv.ofEq _ _ (ofGramMatrix_carrier b G hG).symm)
  rw [isEven_iff_forall_basis (ofGramMatrix b G hG) bInt]
  apply forall_congr'
  intro i
  have hb : bInt i = ofGramMatrix.basisElem b G hG i := by
    apply Subtype.ext
    simp [bInt]
  rw [hb, integralNorm, integralForm_ofGramMatrix_apply]

/-! ## Vectors of prescribed norm -/

/-- The lattice vectors having the prescribed rational norm. -/
def roots (L : IntegralLattice V) (n : ℚ) : Set L := {x | L.norm x = n}

@[simp]
theorem mem_roots {L : IntegralLattice V} {n : ℚ} {x : L} :
    x ∈ L.roots n ↔ L.norm x = n := Iff.rfl

@[simp]
theorem zero_mem_roots (L : IntegralLattice V) : (0 : L) ∈ L.roots 0 := by
  simp

@[simp]
theorem neg_mem_roots {L : IntegralLattice V} {n : ℚ} (x : L) :
    -x ∈ L.roots n ↔ x ∈ L.roots n := by
  simp [mem_roots]

/-- A norm represented by an even lattice is twice an integer. -/
theorem IsEven.exists_eq_two_mul_of_mem_roots {L : IntegralLattice V} (hL : L.IsEven)
    {n : ℚ} {x : L} (hx : x ∈ L.roots n) : ∃ z : ℤ, n = 2 * z := by
  obtain ⟨z, hz⟩ := hL.exists_norm_eq_two_mul x
  exact ⟨z, hx.symm.trans hz⟩

/-- An even lattice has no vector of a norm that is not twice an integer. -/
theorem IsEven.roots_eq_empty {L : IntegralLattice V} (hL : L.IsEven) {n : ℚ}
    (hn : ¬∃ z : ℤ, n = 2 * z) : L.roots n = ∅ := by
  ext x
  simp only [mem_roots, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hn (hL.exists_eq_two_mul_of_mem_roots hx)

end IntegralLattice

end TauCeti
