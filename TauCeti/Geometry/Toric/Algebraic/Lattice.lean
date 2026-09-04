/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# Integral lattices in real vector spaces

This file defines the full integral-lattice datum used by the toric geometry development.  An
additive map from a finite free `ℤ`-module is a lattice map precisely when its scalar extension to
`ℝ` is an equivalence.  The resulting API records injectivity, fullness, and equality of the
integral and real ranks, which are the basic facts needed to make rational cones coordinate-free.

The scalar-extension formulation combines injectivity with full real spanning: it rules out, for
example, the injective map `ℤ² → ℝ` given by `(a, b) ↦ a + √2 * b`.

## References

* D. Cox, J. Little, and H. Schenck, *Toric Varieties*, §1.1.
* W. Fulton, *Introduction to Toric Varieties*, §1.2.
* The `AnalyticToricGeometry` roadmap, especially `AnalyticToricGeometry/README.md`, Layer 0,
  item 1, and `AnalyticToricGeometry/Suggested.lean`.
-/

public section

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace TauCeti

open TensorProduct

universe u v w u' v'

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]

private instance faithfulSMulIntReal : FaithfulSMul ℤ ℝ where
  eq_of_smul_eq_smul {m₁ m₂} h := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ))
    simpa only [Int.smul_one_eq_cast] using h (1 : ℝ)

private noncomputable instance moduleOfNormedSpace (E : Type w) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Module ℝ E :=
  NormedSpace.toModule

/-- An additive map is a full integral lattice when its scalar extension to `ℝ` is an equivalence.

The displayed equality says that the equivalence sends each pure tensor `1 ⊗ₜ n` to the chosen
lattice vector `i n`.  The requirement that the scalar extension be an equivalence gives fullness;
under the finiteness and freeness hypotheses used below, the API also derives discreteness. -/
def IsIntegralLattice (i : N →+ V) : Prop :=
  ∃ e : TensorProduct ℤ ℝ N ≃ₗ[ℝ] V,
    ∀ n : N, e ((1 : ℝ) ⊗ₜ[ℤ] n) = i n

section Lattice

variable [Module.Free ℤ N] [Module.Finite ℤ N]

omit [Module.Free ℤ N] [Module.Finite ℤ N] in
/-- Construct an integral lattice from its scalar-extension equivalence. -/
theorem IsIntegralLattice.of_equiv (i : N →+ V) (e : TensorProduct ℤ ℝ N ≃ₗ[ℝ] V)
    (he : ∀ n : N, e ((1 : ℝ) ⊗ₜ[ℤ] n) = i n) : IsIntegralLattice i :=
  ⟨e, he⟩

omit [Module.Free ℤ N] [Module.Finite ℤ N] in
/-- The scalar-extension equivalence witnessing an integral lattice. -/
noncomputable def IsIntegralLattice.Equiv (i : N →+ V) (h : IsIntegralLattice i) :
    TensorProduct ℤ ℝ N ≃ₗ[ℝ] V :=
  Classical.choose h

omit [Module.Free ℤ N] [Module.Finite ℤ N] in
/-- The chosen scalar-extension equivalence has the prescribed value on lattice vectors. -/
lemma IsIntegralLattice.equiv_one_tmul (i : N →+ V) (h : IsIntegralLattice i) (n : N) :
    IsIntegralLattice.Equiv i h ((1 : ℝ) ⊗ₜ[ℤ] n) = i n :=
  Classical.choose_spec h n

attribute [simp] IsIntegralLattice.equiv_one_tmul

omit [Module.Finite ℤ N] in
/-- An integral lattice map is injective. -/
theorem IsIntegralLattice.injective (i : N →+ V) (h : IsIntegralLattice i) :
    Function.Injective i := by
  intro m n hmn
  apply Module.Flat.tensorProduct_mk_injective ℤ N ℝ
  apply (IsIntegralLattice.Equiv i h).injective
  rw [TensorProduct.mk_apply, TensorProduct.mk_apply, IsIntegralLattice.equiv_one_tmul,
    IsIntegralLattice.equiv_one_tmul, hmn]

/-- The real basis obtained by extending a chosen integral basis through the lattice equivalence. -/
noncomputable def IsIntegralLattice.realBasis (i : N →+ V) (h : IsIntegralLattice i) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ N) ℝ V :=
  (Module.Free.chooseBasis ℤ N).baseChange ℝ |>.map (IsIntegralLattice.Equiv i h)

omit [Module.Finite ℤ N] in
/-- The induced real basis consists of the images of the chosen integral basis vectors. -/
@[simp]
theorem IsIntegralLattice.realBasis_apply (i : N →+ V) (h : IsIntegralLattice i)
    (j : Module.Free.ChooseBasisIndex ℤ N) :
    IsIntegralLattice.realBasis i h j = i (Module.Free.chooseBasis ℤ N j) := by
  simp only [IsIntegralLattice.realBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply]
  exact IsIntegralLattice.equiv_one_tmul i h _

omit [Module.Free ℤ N] [Module.Finite ℤ N] in
/-- The real span of the image of an integral lattice is the whole ambient space. -/
theorem IsIntegralLattice.span_range_eq_top (i : N →+ V) (h : IsIntegralLattice i) :
    Submodule.span ℝ (Set.range i) = ⊤ := by
  let e := IsIntegralLattice.Equiv i h
  let s : Set (TensorProduct ℤ ℝ N) := {t | ∃ a n, a ⊗ₜ[ℤ] n = t}
  have hs : Submodule.span ℝ s = ⊤ :=
    Submodule.span_eq_top_of_span_eq_top ℤ ℝ s (TensorProduct.span_tmul_eq_top ℤ ℝ N)
  have hmap : (Submodule.span ℝ s).map e.toLinearMap ≤
      Submodule.span ℝ (Set.range i) := by
    dsimp only [e]
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨a, n, rfl⟩, rfl⟩
    rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
    have he : (IsIntegralLattice.Equiv i h) ((1 : ℝ) ⊗ₜ[ℤ] n) = i n :=
      IsIntegralLattice.equiv_one_tmul i h n
    rw [show (IsIntegralLattice.Equiv i h).toLinearMap ((1 : ℝ) ⊗ₜ[ℤ] n) = i n from he]
    exact Submodule.smul_mem (Submodule.span ℝ (Set.range i)) a
      (Submodule.subset_span (Set.mem_range_self n))
  apply le_antisymm le_top
  calc
    (⊤ : Submodule ℝ V) = (Submodule.span ℝ s).map e.toLinearMap := by
      rw [hs, Submodule.map_top]
      exact e.range.symm
    _ ≤ Submodule.span ℝ (Set.range i) := hmap

omit [Module.Finite ℤ N] in
/-- The image of an integral lattice is the `ℤ`-span of the induced real basis. -/
theorem IsIntegralLattice.range_eq_span_realBasis (i : N →+ V) (h : IsIntegralLattice i) :
    Set.range i =
      (Submodule.span ℤ (Set.range (IsIntegralLattice.realBasis i h)) : Set V) := by
  change (LinearMap.range i.toIntLinearMap : Set V) = _
  have hrange : LinearMap.range i.toIntLinearMap =
      Submodule.span ℤ (Set.range (IsIntegralLattice.realBasis i h)) := by
    rw [LinearMap.range_eq_map, ← (Module.Free.chooseBasis ℤ N).span_eq,
      Submodule.map_span, ← Set.range_comp]
    congr 1
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, by simp only [Function.comp_apply, IsIntegralLattice.realBasis_apply,
        AddMonoidHom.coe_toIntLinearMap]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, by simp only [Function.comp_apply, IsIntegralLattice.realBasis_apply,
        AddMonoidHom.coe_toIntLinearMap]⟩
  exact congrArg (fun p : Submodule ℤ V => (p : Set V)) hrange

omit [Module.Finite ℤ N] in
/-- The rank of a full integral lattice equals the real dimension of its ambient space. -/
theorem IsIntegralLattice.finrank_eq (i : N →+ V) (h : IsIntegralLattice i) :
    Module.finrank ℤ N = Module.finrank ℝ V := by
  have he := (IsIntegralLattice.Equiv i h).finrank_eq
  simpa only [Module.finrank_baseChange] using he

variable {V₀ : Type w} [NormedAddCommGroup V₀] [NormedSpace ℝ V₀]

/-- With its usual real-vector-space topology, the image of an integral lattice is discrete. -/
theorem IsIntegralLattice.isDiscrete_range (i : N →+ V₀)
    (h : IsIntegralLattice i) :
    IsDiscrete (Set.range i) := by
  let b := IsIntegralLattice.realBasis i h
  have hd : DiscreteTopology (Submodule.span ℤ (Set.range b)) := by
    infer_instance
  rw [IsIntegralLattice.range_eq_span_realBasis i h]
  exact @DiscreteTopology.isDiscrete _ _ _ hd

omit [Module.Free ℤ N] [Module.Finite ℤ N] in
/-- A real-linear map carrying one integral lattice into another commutes with their lattice
vectors, after applying the corresponding integral additive map. -/
theorem IsIntegralLattice.comp_equiv_eq_equiv_comp_baseChange
    {N' : Type u'} {V' : Type v'} [AddCommGroup N']
    [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hf : ∀ n, g (i n) = i' (f n)) :
    g.comp (IsIntegralLattice.Equiv i h).toLinearMap =
      (IsIntegralLattice.Equiv i' h').toLinearMap.comp (f.toIntLinearMap.baseChange ℝ) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a n
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul]
  rw [TensorProduct.tmul_eq_smul_one_tmul a n,
    TensorProduct.tmul_eq_smul_one_tmul a (f.toIntLinearMap n)]
  simp only [map_smul]
  congr 1
  calc
    g ((IsIntegralLattice.Equiv i h) ((1 : ℝ) ⊗ₜ[ℤ] n)) = g (i n) :=
      congrArg g (IsIntegralLattice.equiv_one_tmul i h n)
    _ = i' (f n) := hf n
    _ = (IsIntegralLattice.Equiv i' h') ((1 : ℝ) ⊗ₜ[ℤ] f.toIntLinearMap n) := by
      simpa only [AddMonoidHom.coe_toIntLinearMap] using
        (IsIntegralLattice.equiv_one_tmul i' h' (f.toIntLinearMap n)).symm

end Lattice

end TauCeti

end
