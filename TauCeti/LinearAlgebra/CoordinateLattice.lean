/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The integral lattice in a rational coordinate space

For a finite index type `ι`, this file packages the standard integral lattice in `ι → ℚ`: the
`ℤ`-span of the coordinate vectors. It records its coordinatewise membership criterion and its
canonical basis. These declarations are shared by the standard Chevalley carriers and the Geck
module instead of rebuilding the same restricted-scalars basis in each construction.

## Main declarations

* `TauCeti.coordinateLattice`: the `ℤ`-span of the standard basis of `ι → ℚ`.
* `TauCeti.mem_coordinateLattice_iff`: membership means that every coordinate is integral.
* `TauCeti.basisFun_mem_coordinateLattice` and `TauCeti.coordinateLatticeBasis`: the standard
  coordinate vectors and basis over `ℤ`.

This is a reusable prerequisite for the Chevalley--Demazure carriers in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

namespace TauCeti

universe u

variable (ι : Type u) [Finite ι]

/-- The standard integral lattice in the rational coordinate space `ι → ℚ`. -/
def coordinateLattice : Submodule ℤ (ι → ℚ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℚ ι))

/-- A rational coordinate vector lies in the standard lattice exactly when every coordinate is
an integer. -/
@[simp] theorem mem_coordinateLattice_iff {v : ι → ℚ} :
    v ∈ coordinateLattice ι ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = v i := by
  rw [coordinateLattice, Module.Basis.mem_span_iff_repr_mem]
  simp only [Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom, Set.mem_range]

/-- Every standard coordinate basis vector lies in the coordinate lattice. -/
theorem basisFun_mem_coordinateLattice (i : ι) :
    Pi.basisFun ℚ ι i ∈ coordinateLattice ι := by
  rw [coordinateLattice]
  exact Submodule.subset_span (Set.mem_range_self i)

/-- To prove a property of every vector in the coordinate lattice, it is enough to prove it for
the standard coordinate vectors and show that it is preserved by the `ℤ`-module operations. -/
theorem coordinateLattice_induction {p : (ι → ℚ) → Prop} {v : ι → ℚ}
    (hv : v ∈ coordinateLattice ι)
    (basis : ∀ i, p (Pi.basisFun ℚ ι i))
    (zero : p 0)
    (add : ∀ x y, p x → p y → p (x + y))
    (smul : ∀ (z : ℤ) x, p x → p (z • x)) : p v := by
  rw [coordinateLattice] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact basis i
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul z x _ hx => exact smul z x hx

/-- The standard coordinate vectors, regarded as a basis of the coordinate lattice over `ℤ`. -/
noncomputable def coordinateLatticeBasis :
    Module.Basis ι ℤ (coordinateLattice ι) :=
  (Pi.basisFun ℚ ι).restrictScalars ℤ

/-- A coordinate-lattice basis vector is the corresponding standard coordinate vector. -/
@[simp] theorem coe_coordinateLatticeBasis (i : ι) :
    ((coordinateLatticeBasis ι i : coordinateLattice ι) : ι → ℚ) = Pi.basisFun ℚ ι i := by
  unfold coordinateLatticeBasis coordinateLattice
  rw [Module.Basis.restrictScalars_apply]

/-- Extending a coordinate-lattice basis coefficient to `ℚ` recovers the corresponding rational
coordinate. -/
@[simp] theorem intCast_coordinateLatticeBasis_repr (v : coordinateLattice ι) (i : ι) :
    ((coordinateLatticeBasis ι).repr v i : ℚ) = (v : ι → ℚ) i := by
  unfold coordinateLatticeBasis coordinateLattice at *
  rw [← eq_intCast (algebraMap ℤ ℚ) _, Module.Basis.restrictScalars_repr_apply,
    Pi.basisFun_repr]

/-- The standard coordinate lattice is finitely generated and spans its rational coordinate
space. -/
instance instIsLatticeCoordinateLattice : Submodule.IsLattice ℚ (coordinateLattice ι) where
  fg := by
    rw [coordinateLattice]
    exact Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [coordinateLattice, Submodule.span_span_of_tower, (Pi.basisFun ℚ ι).span_eq]

end TauCeti
