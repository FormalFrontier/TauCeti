/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Lattice
public import TauCeti.LinearAlgebra.Eigenspace.Binomial
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.KostantForm
public import TauCeti.RingTheory.Binomial

/-!
# The coordinate lattice in the pinned Geck module

The pinned split Lie algebra `TauCeti.DynkinType.lieAlgebra` acts faithfully on the explicit Geck
module `TauCeti.DynkinType.GeckIndex → ℚ`. This file equips that module with its coordinate
`ℤ`-lattice, spanned by the standard coordinate vectors. It is finite free, has the expected
coordinate basis, and spans the rational module.

The numbered Cartan, raising, and lowering generators preserve this lattice. For the Cartan
generators the stronger integral-form statement is proved: every generalized binomial coefficient
in a Cartan generator preserves the lattice, because the coordinate vectors have the integral
weights `TauCeti.DynkinType.geckWeight`.

Integrality of the higher divided powers of the raising and lowering generators remains separate.
It is the missing root-operator half needed to show that the entire simple-generator Kostant form
preserves this finite lattice.

## Main declarations

* `TauCeti.DynkinType.geckCoordinateLattice`: the coordinate `ℤ`-lattice in the Geck module.
* `TauCeti.DynkinType.geckCoordinateBasis`: its standard coordinate basis.
* `TauCeti.DynkinType.geckCoordinateFinBasis`: the same basis indexed by a finite ordinal, as
  required by the general-linear group-scheme construction.
* `TauCeti.DynkinType.geckRepresentation_lieBasis_e_mem_geckCoordinateLattice` and its lowering
  analogue: stability under the numbered root generators.
* `TauCeti.DynkinType.geckRepresentation_ringChoose_lieBasis_h_mem_geckCoordinateLattice`:
  stability under every Cartan binomial operator.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

This advances the Chevalley--Demazure construction of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is the explicit pinned ambient group in
milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

namespace TauCeti.DynkinType

open RootPairing.GeckConstruction Set
open scoped _root_.Matrix

noncomputable section

attribute [local instance] TauCeti.moduleNNRat

variable (t : DynkinType) (ht : t.Valid)

/-! ## The coordinate lattice and its basis -/

/-- **The coordinate `ℤ`-lattice in the pinned Geck module**, spanned by the standard coordinate
vectors. -/
def geckCoordinateLattice : Submodule ℤ (t.GeckIndex ht → ℚ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℚ (t.GeckIndex ht)))

/-- A vector belongs to the Geck coordinate lattice exactly when all its coordinates are
integer-valued. -/
@[simp]
theorem mem_geckCoordinateLattice_iff {v : t.GeckIndex ht → ℚ} :
    v ∈ t.geckCoordinateLattice ht ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = v i := by
  rw [geckCoordinateLattice, Module.Basis.mem_span_iff_repr_mem]
  simp only [Pi.basisFun_repr, Set.mem_range, eq_comm]
  rfl

/-- The standard coordinate basis of the Geck coordinate lattice. -/
def geckCoordinateBasis : Module.Basis (t.GeckIndex ht) ℤ (t.geckCoordinateLattice ht) :=
  (Pi.basisFun ℚ (t.GeckIndex ht)).restrictScalars ℤ

/-- The underlying vector of a Geck coordinate basis element is the corresponding standard
coordinate vector. -/
@[simp]
theorem coe_geckCoordinateBasis (i : t.GeckIndex ht) :
    ((t.geckCoordinateBasis ht i : t.geckCoordinateLattice ht) : t.GeckIndex ht → ℚ) =
      Pi.single i 1 := by
  unfold geckCoordinateBasis geckCoordinateLattice
  rw [Module.Basis.restrictScalars_apply, Pi.basisFun_apply]

/-- The coordinate basis reindexed by a finite ordinal. This is the basis shape consumed by the
Kostant generated-group-scheme construction. -/
def geckCoordinateFinBasis :
    Module.Basis (Fin (Fintype.card (t.GeckIndex ht))) ℤ (t.geckCoordinateLattice ht) :=
  (t.geckCoordinateBasis ht).reindex (Fintype.equivFin (t.GeckIndex ht))

/-- A finite-ordinal coordinate basis element is the standard vector at the corresponding Geck
coordinate. -/
@[simp]
theorem coe_geckCoordinateFinBasis (i : Fin (Fintype.card (t.GeckIndex ht))) :
    ((t.geckCoordinateFinBasis ht i : t.geckCoordinateLattice ht) : t.GeckIndex ht → ℚ) =
      Pi.single ((Fintype.equivFin (t.GeckIndex ht)).symm i) 1 := by
  rw [geckCoordinateFinBasis, Module.Basis.reindex_apply, coe_geckCoordinateBasis]

/-- The coordinate lattice is contained in the integral orbit of the pinned Kostant form, since
the latter contains every standard coordinate vector. -/
theorem geckCoordinateLattice_le_geckOrbit :
    t.geckCoordinateLattice ht ≤ t.geckOrbit ht := by
  rw [geckCoordinateLattice, Submodule.span_le]
  rintro - ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  exact t.single_mem_geckOrbit ht i

instance instIsLatticeGeckCoordinateLattice :
    Submodule.IsLattice ℚ (t.geckCoordinateLattice ht) where
  fg := by
    rw [geckCoordinateLattice]
    exact Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [geckCoordinateLattice, Submodule.span_span_of_tower,
      (Pi.basisFun ℚ (t.GeckIndex ht)).span_eq]

/-! ## Stability under integral matrices -/

private theorem matrix_mulVec_mem_geckCoordinateLattice
    (A : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)
    (hA : ∀ i j, ∃ z : ℤ, (z : ℚ) = A i j)
    {v : t.GeckIndex ht → ℚ} (hv : v ∈ t.geckCoordinateLattice ht) :
    A *ᵥ v ∈ t.geckCoordinateLattice ht := by
  classical
  rw [mem_geckCoordinateLattice_iff] at hv ⊢
  intro i
  choose a ha using hA i
  choose w hw using hv
  refine ⟨∑ j, a j * w j, ?_⟩
  simp only [Int.cast_sum, Int.cast_mul, ha, hw, Matrix.mulVec, dotProduct]

private theorem geck_e_has_integer_entries (i : Fin t.rank) (j k : t.GeckIndex ht) :
    ∃ z : ℤ, (z : ℚ) =
      RootPairing.GeckConstruction.e (t.simpleSupportEquiv ht i) j k := by
  classical
  cases j with
  | inl j =>
      cases k with
      | inl k => exact ⟨0, by simp [RootPairing.GeckConstruction.e]⟩
      | inr k =>
          simp only [RootPairing.GeckConstruction.e, Matrix.fromBlocks_apply₁₂,
            Matrix.of_apply]
          split_ifs
          · exact ⟨1, rfl⟩
          · exact ⟨0, rfl⟩
  | inr j =>
      cases k with
      | inl k =>
          simp only [RootPairing.GeckConstruction.e, Matrix.fromBlocks_apply₂₁,
            Matrix.of_apply]
          split_ifs
          · exact ⟨_, rfl⟩
          · exact ⟨0, rfl⟩
      | inr k =>
          simp only [RootPairing.GeckConstruction.e, Matrix.fromBlocks_apply₂₂,
            Matrix.of_apply]
          split_ifs
          · exact ⟨Int.ofNat ((t.rationalRootSystem ht).chainBotCoeff
                (t.simpleIndex ht i) k + 1), by simp⟩
          · exact ⟨0, rfl⟩

private theorem geck_f_has_integer_entries (i : Fin t.rank) (j k : t.GeckIndex ht) :
    ∃ z : ℤ, (z : ℚ) =
      RootPairing.GeckConstruction.f (t.simpleSupportEquiv ht i) j k := by
  classical
  cases j with
  | inl j =>
      cases k with
      | inl k => exact ⟨0, by simp [RootPairing.GeckConstruction.f]⟩
      | inr k =>
          simp only [RootPairing.GeckConstruction.f, Matrix.fromBlocks_apply₁₂,
            Matrix.of_apply]
          split_ifs
          · exact ⟨1, rfl⟩
          · exact ⟨0, rfl⟩
  | inr j =>
      cases k with
      | inl k =>
          simp only [RootPairing.GeckConstruction.f, Matrix.fromBlocks_apply₂₁,
            Matrix.of_apply]
          split_ifs
          · exact ⟨_, rfl⟩
          · exact ⟨0, rfl⟩
      | inr k =>
          simp only [RootPairing.GeckConstruction.f, Matrix.fromBlocks_apply₂₂,
            Matrix.of_apply]
          split_ifs
          · exact ⟨Int.ofNat ((t.rationalRootSystem ht).chainTopCoeff
                (t.simpleIndex ht i) k + 1), by simp⟩
          · exact ⟨0, rfl⟩

/-! ## The numbered Chevalley generators -/

/-- A numbered raising generator preserves the Geck coordinate lattice. -/
theorem geckRepresentation_lieBasis_e_mem_geckCoordinateLattice (i : Fin t.rank)
    {v : t.GeckIndex ht → ℚ} (hv : v ∈ t.geckCoordinateLattice ht) :
    t.geckRepresentation ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).e i)) v ∈
      t.geckCoordinateLattice ht := by
  rw [t.geckRepresentation_ι_apply ht, t.coe_lieBasis_e ht]
  exact t.matrix_mulVec_mem_geckCoordinateLattice ht _
    (t.geck_e_has_integer_entries ht i) hv

/-- A numbered lowering generator preserves the Geck coordinate lattice. -/
theorem geckRepresentation_lieBasis_f_mem_geckCoordinateLattice (i : Fin t.rank)
    {v : t.GeckIndex ht → ℚ} (hv : v ∈ t.geckCoordinateLattice ht) :
    t.geckRepresentation ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).f i)) v ∈
      t.geckCoordinateLattice ht := by
  rw [t.geckRepresentation_ι_apply ht, t.coe_lieBasis_f ht]
  exact t.matrix_mulVec_mem_geckCoordinateLattice ht _
    (t.geck_f_has_integer_entries ht i) hv

/-- A numbered root generator, raising or lowering, preserves the Geck coordinate lattice. -/
theorem geckRepresentation_rootGenerator_mem_geckCoordinateLattice
    (i : Fin t.rank ⊕ Fin t.rank) {v : t.GeckIndex ht → ℚ}
    (hv : v ∈ t.geckCoordinateLattice ht) :
    t.geckRepresentation ht
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i)) v ∈
      t.geckCoordinateLattice ht := by
  cases i with
  | inl i =>
      rw [LieAlgebra.Basis.rootGenerator_inl]
      exact t.geckRepresentation_lieBasis_e_mem_geckCoordinateLattice ht i hv
  | inr i =>
      rw [LieAlgebra.Basis.rootGenerator_inr]
      exact t.geckRepresentation_lieBasis_f_mem_geckCoordinateLattice ht i hv

/-! ## Cartan binomial operators -/

/-- **Every generalized binomial coefficient in a numbered Cartan generator preserves the Geck
coordinate lattice.** -/
theorem geckRepresentation_ringChoose_lieBasis_h_mem_geckCoordinateLattice
    (i : Fin t.rank) (n : ℕ)
    {v : t.GeckIndex ht → ℚ} (hv : v ∈ t.geckCoordinateLattice ht) :
    t.geckRepresentation ht
        (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).h i)) n) v ∈
      t.geckCoordinateLattice ht := by
  rw [geckCoordinateLattice] at hv ⊢
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      rw [Pi.basisFun_apply]
      rw [Ring.map_choose]
      have hweight := (UniversalEnvelopingAlgebra.isCartanWeightVector_iff
        (h := (t.lieBasis ht).h) (ρ := t.geckRepresentation ht)).1
          (t.isCartanWeightVector_geckRepresentation_single ht x) i
      rw [ringChoose_end_apply_of_apply_eq_smul hweight n,
        TauCeti.Ring.choose_intCast, Int.cast_smul_eq_zsmul ℚ]
      have hx : Pi.single x (1 : ℚ) ∈
          Submodule.span ℤ (range (Pi.basisFun ℚ (t.GeckIndex ht))) := by
        rw [← Pi.basisFun_apply]
        exact Submodule.subset_span (mem_range_self x)
      exact Submodule.smul_mem _ _ hx
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul z x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ z hx

end

end TauCeti.DynkinType
