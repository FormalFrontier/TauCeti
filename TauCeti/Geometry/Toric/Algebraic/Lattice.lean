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

The scalar-extension formulation is deliberately stronger than injectivity and density: it rules
out, for example, the injective map `ℤ² → ℝ` given by `(a, b) ↦ a + √2 * b`.

## References

* D. Cox, J. Little, and H. Schenck, *Toric Varieties*, §1.1.
* W. Fulton, *Introduction to Toric Varieties*, §1.2.
-/

public section

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace TauCeti

open TensorProduct

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]

private instance faithfulSMulIntReal : FaithfulSMul ℤ ℝ where
  eq_of_smul_eq_smul {m₁ m₂} h := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ))
    simpa only [Int.smul_one_eq_cast] using h (1 : ℝ)

private noncomputable instance moduleOfNormedSpace (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Module ℝ E :=
  NormedSpace.toModule

/-- An additive map is a full integral lattice when its scalar extension to `ℝ` is an equivalence.

The displayed equality says that the equivalence sends each pure tensor `1 ⊗ₜ n` to the chosen
lattice vector `i n`.  The requirement that the scalar extension be an equivalence gives fullness;
under the finiteness and freeness hypotheses used below, the API also derives discreteness. -/
def IsIntegralLattice (i : N →+ V) : Prop :=
  ∃ e : TensorProduct ℤ ℝ N ≃ₗ[ℝ] V,
    ∀ n : N, e ((1 : ℝ) ⊗ₜ[ℤ] n) = i n

/-- The scalar-extension equivalence witnessing an integral lattice. -/
noncomputable def IsIntegralLattice.Equiv (i : N →+ V) (h : IsIntegralLattice i) :
    TensorProduct ℤ ℝ N ≃ₗ[ℝ] V :=
  Classical.choose h

/-- The chosen scalar-extension equivalence has the prescribed value on lattice vectors. -/
lemma IsIntegralLattice.equiv_tmul_one (i : N →+ V) (h : IsIntegralLattice i) (n : N) :
    IsIntegralLattice.Equiv i h ((1 : ℝ) ⊗ₜ[ℤ] n) = i n :=
  Classical.choose_spec h n

attribute [simp] IsIntegralLattice.equiv_tmul_one

section Free

variable [Module.Free ℤ N]

/-- An integral lattice map is injective. -/
theorem IsIntegralLattice.injective (i : N →+ V) (h : IsIntegralLattice i) :
    Function.Injective i := by
  intro m n hmn
  apply Module.Flat.tensorProduct_mk_injective ℤ N ℝ
  apply (IsIntegralLattice.Equiv i h).injective
  rw [TensorProduct.mk_apply, TensorProduct.mk_apply, IsIntegralLattice.equiv_tmul_one,
    IsIntegralLattice.equiv_tmul_one, hmn]

/-- The real basis obtained by extending a chosen integral basis through the lattice equivalence. -/
noncomputable def IsIntegralLattice.realBasis (i : N →+ V) (h : IsIntegralLattice i) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ N) ℝ V :=
  (Module.Free.chooseBasis ℤ N).baseChange ℝ |>.map (IsIntegralLattice.Equiv i h)

/-- The induced real basis consists of the images of the chosen integral basis vectors. -/
@[simp]
theorem IsIntegralLattice.realBasis_apply (i : N →+ V) (h : IsIntegralLattice i)
    (j : Module.Free.ChooseBasisIndex ℤ N) :
    IsIntegralLattice.realBasis i h j = i (Module.Free.chooseBasis ℤ N j) := by
  simp only [IsIntegralLattice.realBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply]
  exact IsIntegralLattice.equiv_tmul_one i h _

end Free

/-- The real span of the image of an integral lattice is the whole ambient space. -/
theorem IsIntegralLattice.span_range_eq_top (i : N →+ V) (h : IsIntegralLattice i) :
    Submodule.span ℝ (Set.range i) = ⊤ := by
  have ht : ∀ t : TensorProduct ℤ ℝ N,
      (IsIntegralLattice.Equiv i h) t ∈ Submodule.span ℝ (Set.range i) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
        simpa only [map_zero] using (Submodule.span ℝ (Set.range i)).zero_mem
    | add t₁ t₂ ht₁ ht₂ =>
        simpa only [map_add] using
          (Submodule.span ℝ (Set.range i)).add_mem ht₁ ht₂
    | tmul a n =>
        rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
        apply Submodule.smul_mem _ a
        rw [IsIntegralLattice.equiv_tmul_one]
        exact Submodule.subset_span (Set.mem_range_self n)
  apply top_unique
  intro v _
  simpa only [LinearEquiv.apply_symm_apply] using ht ((IsIntegralLattice.Equiv i h).symm v)

section Basis

variable [Module.Free ℤ N]

/-- The image of an integral lattice is the `ℤ`-span of the induced real basis. -/
theorem IsIntegralLattice.range_eq_span_realBasis (i : N →+ V) (h : IsIntegralLattice i) :
    Set.range i =
      (Submodule.span ℤ (Set.range (IsIntegralLattice.realBasis i h)) : Set V) := by
  ext v
  constructor
  · rintro ⟨n, rfl⟩
    have hn : n ∈ Submodule.span ℤ (Set.range (Module.Free.chooseBasis ℤ N)) := by
      rw [(Module.Free.chooseBasis ℤ N).span_eq]
      trivial
    refine Submodule.span_induction (p := fun n _ =>
      i n ∈ Submodule.span ℤ (Set.range (IsIntegralLattice.realBasis i h))) ?_ ?_ ?_ ?_ hn
    · rintro n ⟨j, rfl⟩
      rw [← IsIntegralLattice.realBasis_apply i h j]
      exact Submodule.subset_span (Set.mem_range_self j)
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_zsmul]
      exact Submodule.smul_mem _ c hx
  · intro hv
    refine Submodule.span_induction (p := fun v _ => ∃ n, i n = v) ?_ ?_ ?_ ?_ hv
    · rintro v ⟨j, rfl⟩
      exact ⟨Module.Free.chooseBasis ℤ N j,
        (IsIntegralLattice.realBasis_apply i h j).symm⟩
    · exact ⟨0, by simp⟩
    · intro x y _ _ hx hy
      rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, rfl⟩
      exact ⟨m + n, by simp⟩
    · intro c x _ hx
      rcases hx with ⟨n, rfl⟩
      exact ⟨c • n, by simp⟩

end Basis

section Rank

variable [Module.Free ℤ N]

/-- The rank of a full integral lattice equals the real dimension of its ambient space. -/
theorem IsIntegralLattice.finrank_eq (i : N →+ V) (h : IsIntegralLattice i) :
    Module.finrank ℤ N = Module.finrank ℝ V := by
  have he := (IsIntegralLattice.Equiv i h).finrank_eq
  simpa only [Module.finrank_baseChange] using he

end Rank

section Discrete

variable {V₀ : Type u} [NormedAddCommGroup V₀] [NormedSpace ℝ V₀]
variable [Module.Free ℤ N] [Module.Finite ℤ N]

/-- With its usual real-vector-space topology, the image of an integral lattice is discrete. -/
theorem IsIntegralLattice.isDiscrete_range (i : N →+ V₀)
    (h : @IsIntegralLattice N V₀ _ _ (NormedSpace.toModule) i) :
    IsDiscrete (Set.range i) := by
  let b := @IsIntegralLattice.realBasis N V₀ _ _ (NormedSpace.toModule) _ i h
  have hd : DiscreteTopology (Submodule.span ℤ (Set.range b)) := by
    infer_instance
  rw [@IsIntegralLattice.range_eq_span_realBasis N V₀ _ _ (NormedSpace.toModule) _ i h]
  exact @DiscreteTopology.isDiscrete _ _ _ hd

end Discrete

/-- A real-linear map carrying one integral lattice into another commutes with their lattice
vectors, after applying the corresponding integral additive map. -/
theorem IsIntegralLattice.map_equiv
    {N' V' : Type u} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hf : ∀ n, g (i n) = i' (f n)) :
    g.comp (IsIntegralLattice.Equiv i h).toLinearMap =
      (IsIntegralLattice.Equiv i' h').toLinearMap.comp (f.toIntLinearMap.baseChange ℝ) := by
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t₁ t₂ ht₁ ht₂ =>
      simpa only [LinearMap.comp_apply, map_add] using congrArg₂ (· + ·) ht₁ ht₂
  | tmul a n =>
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul]
      rw [TensorProduct.tmul_eq_smul_one_tmul a n,
        TensorProduct.tmul_eq_smul_one_tmul a (f.toIntLinearMap n)]
      simp only [map_smul]
      congr 1
      calc
        g ((IsIntegralLattice.Equiv i h) ((1 : ℝ) ⊗ₜ[ℤ] n)) = g (i n) :=
          congrArg g (IsIntegralLattice.equiv_tmul_one i h n)
        _ = i' (f n) := hf n
        _ = (IsIntegralLattice.Equiv i' h') ((1 : ℝ) ⊗ₜ[ℤ] f.toIntLinearMap n) :=
          (IsIntegralLattice.equiv_tmul_one i' h' (f.toIntLinearMap n)).symm

end TauCeti

end
