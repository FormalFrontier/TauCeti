/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.IntegralLattice.Basic

public import Mathlib.Algebra.Module.Lattice
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# The coordinate integral lattice in an exterior algebra

Let `b : Basis ι ℚ M`. The exterior basis `b.ExteriorAlgebra`, indexed by finite subsets of `ι`,
defines a canonical integral form of `ExteriorAlgebra ℚ M`: take the `ℤ`-span of its basis vectors.
This file constructs that lattice and proves that it is closed under the exterior product.

The multiplication statement is the useful point. Products of exterior basis vectors are either
zero or another basis vector with sign given by the shuffle permutation, so multiplication does
not introduce denominators. In particular, exterior multiplication by any basis vector preserves
the lattice. This is the creation-operator half of the integral spinor lattice used to construct
the simply connected type-`B` and type-`D` Chevalley carriers.

## Main definitions and results

* `TauCeti.ExteriorAlgebra.integralLattice`: the `ℤ`-span of an exterior basis.
* `TauCeti.ExteriorAlgebra.integralLatticeBasis`: the exterior basis restricted to `ℤ`.
* `TauCeti.ExteriorAlgebra.map_mem_integralLattice`: a linear map preserves the lattice as soon as
  it preserves it on the exterior basis.
* `TauCeti.ExteriorAlgebra.mem_integralLattice_iff`: membership means that every exterior-basis
  coordinate is integral.
* `TauCeti.ExteriorAlgebra.mul_mem_integralLattice`: the lattice is closed under multiplication.
* `TauCeti.ExteriorAlgebra.ι_basis_mul_mem_integralLattice`: creation by a basis vector preserves
  the lattice.
* `TauCeti.ExteriorAlgebra.contractLeft_coord_mem_integralLattice`: contraction by a dual basis
  coordinate preserves the lattice.
* `TauCeti.ExteriorAlgebra.involute_mem_integralLattice`: the grade involution preserves the
  lattice.

## Roadmap

This is the integral-lattice input for the full-weight spin carriers required by Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Those type-`B` and type-`D` carriers are in turn
consumed by milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.ExteriorAlgebra

universe u

variable {M : Type u} [AddCommGroup M] [Module ℚ M]
variable {ι : Type*} [LinearOrder ι] (b : Module.Basis ι ℚ M)

/-- The coordinate `ℤ`-lattice in an exterior algebra, spanned by the exterior basis attached to
`b`. -/
def integralLattice : Submodule ℤ (_root_.ExteriorAlgebra ℚ M) :=
  Submodule.span ℤ (Set.range b.ExteriorAlgebra)

/-- **A linear map preserves the coordinate integral lattice as soon as it does so on the exterior
basis**, since that basis spans the lattice. This is the shared induction behind every
lattice-preservation statement below. -/
theorem map_mem_integralLattice
    (f : _root_.ExteriorAlgebra ℚ M →ₗ[ℤ] _root_.ExteriorAlgebra ℚ M)
    (hf : ∀ s : Finset ι, f (b.ExteriorAlgebra s) ∈ integralLattice b)
    {x : _root_.ExteriorAlgebra ℚ M} (hx : x ∈ integralLattice b) :
    f x ∈ integralLattice b := by
  have hle : Submodule.span ℤ (Set.range b.ExteriorAlgebra) ≤
      Submodule.comap f (integralLattice b) := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact hf s
  exact hle hx

/-- An element belongs to the coordinate integral lattice exactly when all of its exterior-basis
coordinates are integers. -/
@[simp]
theorem mem_integralLattice_iff {x : _root_.ExteriorAlgebra ℚ M} :
    x ∈ integralLattice b ↔
      ∀ s, ∃ z : ℤ, (z : ℚ) = b.ExteriorAlgebra.repr x s := by
  rw [integralLattice, Module.Basis.mem_span_iff_repr_mem]
  simp only [algebraMap_int_eq, Int.coe_castRingHom, Set.mem_range]

/-- Every exterior-basis vector belongs to the coordinate integral lattice. -/
theorem basis_mem_integralLattice (s : Finset ι) :
    b.ExteriorAlgebra s ∈ integralLattice b := by
  rw [integralLattice]
  exact Submodule.subset_span (Set.mem_range_self s)

/-- The exterior basis, restricted from rational to integer scalars, is a basis of the coordinate
integral lattice. -/
noncomputable def integralLatticeBasis :
    Module.Basis (Finset ι) ℤ (integralLattice b) :=
  b.ExteriorAlgebra.restrictScalars ℤ

/-- A vector of the integral-lattice basis is the corresponding rational exterior-basis vector. -/
@[simp]
theorem coe_integralLatticeBasis (s : Finset ι) :
    ((integralLatticeBasis b s : integralLattice b) :
      _root_.ExteriorAlgebra ℚ M) = b.ExteriorAlgebra s := by
  unfold integralLatticeBasis integralLattice
  rw [Module.Basis.restrictScalars_apply]

noncomputable instance : Module.Free ℤ (integralLattice b) :=
  Module.Free.of_basis (integralLatticeBasis b)

/-- The rational span of the coordinate integral lattice is the whole exterior algebra. -/
theorem span_integralLattice_eq_top :
    Submodule.span ℚ (integralLattice b : Set (_root_.ExteriorAlgebra ℚ M)) = ⊤ := by
  rw [integralLattice, Submodule.span_span_of_tower, b.ExteriorAlgebra.span_eq]

section Finite

variable [Finite ι]

/-- The finite type structure on the index type used within this section. -/
noncomputable local instance finiteIndexFintype : Fintype ι := Fintype.ofFinite ι

noncomputable instance : Module.Finite ℤ (integralLattice b) :=
  Module.Finite.of_basis (integralLatticeBasis b)

/-- The coordinate integral lattice has rank `2 ^ card ι`. -/
@[simp]
theorem finrank_integralLattice :
    Module.finrank ℤ (integralLattice b) = 2 ^ Nat.card ι := by
  have h := Module.finrank_eq_card_basis (integralLatticeBasis b)
  simpa only [Fintype.card_finset, Nat.card_eq_fintype_card] using h

instance : Submodule.IsLattice ℚ (integralLattice b) where
  __ := TauCeti.IntegralLattice.isLattice_span_basis b.ExteriorAlgebra

end Finite

/-- The unit of the exterior algebra belongs to the coordinate integral lattice. -/
theorem one_mem_integralLattice :
    (1 : _root_.ExteriorAlgebra ℚ M) ∈ integralLattice b := by
  have h := basis_mem_integralLattice b (∅ : Finset ι)
  simpa [_root_.ExteriorAlgebra.basis_apply] using h

/-- The product of two exterior-basis vectors belongs to the coordinate integral lattice. -/
theorem basis_mul_basis_mem_integralLattice (s t : Finset ι) :
    b.ExteriorAlgebra s * b.ExteriorAlgebra t ∈ integralLattice b := by
  by_cases h : Disjoint s t
  · have h' : Disjoint
        (⟨s, rfl⟩ : Set.powersetCard ι s.card).val
        (⟨t, rfl⟩ : Set.powersetCard ι t.card).val := by
      simpa using h
    rw [_root_.ExteriorAlgebra.basis_mul_of_disjoint b
      (⟨s, rfl⟩ : Set.powersetCard ι s.card)
      (⟨t, rfl⟩ : Set.powersetCard ι t.card) h']
    exact Submodule.smul_mem _ _ (basis_mem_integralLattice b _)
  · have h' : ¬Disjoint
        (⟨s, rfl⟩ : Set.powersetCard ι s.card).val
        (⟨t, rfl⟩ : Set.powersetCard ι t.card).val := by
      simpa using h
    rw [_root_.ExteriorAlgebra.basis_mul_of_not_disjoint b
      (⟨s, rfl⟩ : Set.powersetCard ι s.card)
      (⟨t, rfl⟩ : Set.powersetCard ι t.card) h']
    exact zero_mem _

/-- The coordinate integral lattice is closed under the exterior-algebra multiplication. -/
theorem mul_mem_integralLattice {x y : _root_.ExteriorAlgebra ℚ M}
    (hx : x ∈ integralLattice b) (hy : y ∈ integralLattice b) :
    x * y ∈ integralLattice b := by
  have hxt : ∀ t : Finset ι, x * b.ExteriorAlgebra t ∈ integralLattice b := fun t =>
    map_mem_integralLattice b
      ((LinearMap.mulRight ℚ (b.ExteriorAlgebra t)).restrictScalars ℤ)
      (fun s => basis_mul_basis_mem_integralLattice b s t) hx
  exact map_mem_integralLattice b ((LinearMap.mulLeft ℚ x).restrictScalars ℤ) hxt hy

/-- Exterior multiplication by a basis vector preserves the coordinate integral lattice. -/
theorem ι_basis_mul_mem_integralLattice (i : ι) {x : _root_.ExteriorAlgebra ℚ M}
    (hx : x ∈ integralLattice b) :
    _root_.ExteriorAlgebra.ι ℚ (b i) * x ∈ integralLattice b := by
  have hi : _root_.ExteriorAlgebra.ι ℚ (b i) ∈ integralLattice b := by
    have h := basis_mem_integralLattice b ({i} : Finset ι)
    simpa only [basis_singleton] using h
  exact mul_mem_integralLattice b hi hx

/-- **The grade involution preserves the coordinate integral lattice**: it rescales each
exterior-basis vector by the sign of the parity of its index set. -/
theorem involute_mem_integralLattice {x : _root_.ExteriorAlgebra ℚ M}
    (hx : x ∈ integralLattice b) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm ℚ M)) x ∈ integralLattice b := by
  refine map_mem_integralLattice b
    ((CliffordAlgebra.involute (Q := (0 : QuadraticForm ℚ M))).toLinearMap.restrictScalars ℤ)
    (fun s => ?_) hx
  -- Expose the algebra map underneath the restriction of scalars before computing it.
  simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, involute_basis]
  have hsign : ((-1 : ℚ) ^ s.card) = (((-1 : ℤ) ^ s.card : ℤ) : ℚ) := by push_cast; ring
  rw [hsign, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (basis_mem_integralLattice b s)

/-- Contracting an exterior-basis vector by a dual basis coordinate gives an element of the
coordinate integral lattice. -/
theorem contractLeft_coord_basis_mem_integralLattice (i : ι) (s : Finset ι) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℚ M)) (b.coord i)
        (b.ExteriorAlgebra s) ∈ integralLattice b := by
  rw [contractLeft_coord_basis]
  split_ifs
  · exact Submodule.smul_mem _ (basisEraseSign i s : ℤ)
      (basis_mem_integralLattice b (s.erase i))
  · exact zero_mem _

/-- Contraction by a dual basis coordinate preserves the coordinate integral lattice. This is the
annihilation-operator counterpart of `ι_basis_mul_mem_integralLattice`. -/
theorem contractLeft_coord_mem_integralLattice (i : ι)
    {x : _root_.ExteriorAlgebra ℚ M} (hx : x ∈ integralLattice b) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℚ M)) (b.coord i) x ∈
      integralLattice b :=
  map_mem_integralLattice b
    ((CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℚ M))
      (b.coord i)).restrictScalars ℤ)
    (contractLeft_coord_basis_mem_integralLattice b i) hx

end TauCeti.ExteriorAlgebra
