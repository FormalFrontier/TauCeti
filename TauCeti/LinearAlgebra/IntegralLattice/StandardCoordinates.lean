/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Dual.Basic

/-!
# Gram-matrix lattices on the standard rational coordinate space

An integral symmetric matrix `G` indexed by a finite type `ι` presents an integral lattice on
`ι → ℚ`, namely `ofGramMatrix (Pi.basisFun ℚ ι) G hG`, whose carrier is the standard integral
lattice `ι → ℤ`
and whose form is `⟨x, y⟩ = ∑ᵢⱼ xᵢ Gᵢⱼ yⱼ`.  This is how a Cartan matrix presents a root lattice,
the standard coordinate vectors playing the role of the simple roots.

This file expands the form, the carrier and the dual carrier of such a lattice in coordinates.  The
dual carrier is described by the row combinations of `G`: a vector is dual-integral exactly when
`G *ᵥ x` is an integer vector, which is what makes the discriminant group of a lattice given by a
Cartan matrix computable from that matrix alone.

## Main declarations

* `TauCeti.IntegralLattice.form_ofGramMatrix_basisFun_apply`: the form in coordinates.
* `TauCeti.IntegralLattice.form_ofGramMatrix_basisFun_right`: pairing against a standard
  coordinate vector is the corresponding row combination of `G`.
* `TauCeti.IntegralLattice.form_ofGramMatrix_basisFun_basisFun`: the Gram matrix of the standard
  coordinate basis is `G`.
* `TauCeti.IntegralLattice.mem_ofGramMatrix_basisFun_carrier_iff`: the carrier is `ℤⁿ`.
* `TauCeti.IntegralLattice.mem_ofGramMatrix_basisFun_dualCarrier_iff`: the dual carrier consists of
  the vectors whose row combinations against `G` are integers.

## References

* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 5.
-/

public section

namespace TauCeti

namespace IntegralLattice

open Finset

section StandardCoordinates

variable {ι : Type*} [Fintype ι] (G : Matrix ι ι ℤ) (hG : G.IsSymm)

/-- The form of the lattice presented by `G` on `ι → ℚ`, expanded in coordinates. -/
theorem form_ofGramMatrix_basisFun_apply (x y : ι → ℚ) :
    (ofGramMatrix (Pi.basisFun ℚ ι) G hG).form x y =
      ∑ i, x i * ∑ j, ((G i j : ℤ) : ℚ) * y j := by
  -- `ofGramMatrix` and its `form` lemma are stated with classical decidability, so the
  -- `Matrix.toBilin` rewrite has to elaborate against the same instance.
  let _ : DecidableEq ι := Classical.decEq _
  rw [ofGramMatrix_form, Matrix.toBilin_apply]
  simp only [Pi.basisFun_repr, Matrix.map_apply, algebraMap_int_eq, eq_intCast]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (mul_assoc _ _ _)

/-- Pairing an arbitrary vector against the `i`-th standard coordinate vector collapses the double
sum to the `i`-th row combination of the Gram matrix. -/
theorem form_ofGramMatrix_basisFun_right (x : ι → ℚ) (i : ι) :
    (ofGramMatrix (Pi.basisFun ℚ ι) G hG).form x (Pi.basisFun ℚ ι i) =
      ∑ j, ((G i j : ℤ) : ℚ) * x j := by
  classical
  rw [form_ofGramMatrix_basisFun_apply]
  have h : ∀ k : ι, (∑ j, ((G k j : ℤ) : ℚ) * (Pi.basisFun ℚ ι i) j)
      = ((G k i : ℤ) : ℚ) := by
    intro k
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp [Pi.basisFun_apply]
    · intro b _ hb
      simp [Pi.basisFun_apply, hb]
  simp_rw [h]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hG.apply i k]
  exact mul_comm _ _

/-- The Gram matrix of a Gram-matrix lattice in its standard coordinate basis is the given
matrix. -/
-- This is not a `simp` lemma because `ofGramMatrix_form` first unfolds its left-hand side to a
-- double sum over `Finsupp.single`. Concrete Cartan-matrix specializations can be simp lemmas.
theorem form_ofGramMatrix_basisFun_basisFun (i j : ι) :
    (ofGramMatrix (Pi.basisFun ℚ ι) G hG).form
        (Pi.basisFun ℚ ι i) (Pi.basisFun ℚ ι j) = ((G i j : ℤ) : ℚ) := by
  classical
  rw [form_ofGramMatrix_basisFun_right]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp [Pi.basisFun_apply, hG.apply i j]
  · intro b _ hb
    simp [Pi.basisFun_apply, hb]

/-- A vector belongs to a Gram-matrix lattice exactly when all of its standard coordinates are
integers. -/
-- This is not a `simp` lemma because `ofGramMatrix_carrier` first unfolds its left-hand side to
-- bare `Submodule.span` membership. Concrete root-lattice specializations can be simp lemmas.
theorem mem_ofGramMatrix_basisFun_carrier_iff (x : ι → ℚ) :
    x ∈ (ofGramMatrix (Pi.basisFun ℚ ι) G hG).carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i := by
  classical
  rw [ofGramMatrix_carrier, Module.Basis.mem_span_iff_repr_mem]
  simp [Pi.basisFun_repr]

/-- A vector belongs to the dual of a Gram-matrix lattice exactly when every row combination of the
Gram matrix against it is an integer. -/
@[simp]
theorem mem_ofGramMatrix_basisFun_dualCarrier_iff (x : ι → ℚ) :
    x ∈ (ofGramMatrix (Pi.basisFun ℚ ι) G hG).dualCarrier ↔
      ∀ i, ∃ z : ℤ, (z : ℚ) = ∑ j, ((G i j : ℤ) : ℚ) * x j := by
  classical
  rw [dualCarrier, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hx i
    have hi := hx (Pi.basisFun ℚ ι i)
      (by rw [ofGramMatrix_carrier]; exact Submodule.subset_span ⟨i, rfl⟩)
    rw [form_ofGramMatrix_basisFun_right] at hi
    exact Submodule.mem_one.mp hi
  · intro h y hy
    rw [ofGramMatrix_carrier] at hy
    induction hy using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨i, rfl⟩ := hv
        rw [form_ofGramMatrix_basisFun_right]
        exact Submodule.mem_one.mpr (h i)
    | zero => simp
    | add a b _ _ ha hb =>
        rw [map_add]
        exact add_mem ha hb
    | smul c a _ ha =>
        rw [map_zsmul]
        exact Submodule.smul_mem (1 : Submodule ℤ ℚ) c ha

end StandardCoordinates

end IntegralLattice

end TauCeti
