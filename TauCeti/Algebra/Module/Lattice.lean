/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Module.Lattice

/-!
# Full submodule lattices

This file provides generic operations on full integral submodules of rational modules. In
particular, an integral linear equivalence between full submodules extends uniquely to a rational
linear equivalence of their ambient spaces, and rational linear equivalences preserve fullness.

## Main definitions

* `TauCeti.LinearEquiv.extendOfIsLattice`: extension of an integral linear equivalence between
  full submodules to their rational ambient spaces.
-/

public section

open Module

namespace TauCeti

universe u v

namespace LinearEquiv

variable {V : Type u} {W : Type v}
variable [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup W] [Module ℚ W]

/-- Extend an integral linear equivalence between full submodules uniquely to their rational
ambient spaces. -/
noncomputable def extendOfIsLattice {S : Submodule ℤ V} {T : Submodule ℤ W}
    [S.IsLattice ℚ] [T.IsLattice ℚ] (e : S ≃ₗ[ℤ] T) : V ≃ₗ[ℚ] W :=
  let b := Module.Free.chooseBasis ℤ S
  (b.extendOfIsLattice ℚ).equiv ((b.map e).extendOfIsLattice ℚ) (Equiv.refl _)

/-- The rational extension of a full-submodule equivalence agrees with it on the submodule. -/
@[simp]
theorem extendOfIsLattice_apply {S : Submodule ℤ V} {T : Submodule ℤ W}
    [S.IsLattice ℚ] [T.IsLattice ℚ] (e : S ≃ₗ[ℤ] T) (x : S) :
    extendOfIsLattice e (x : V) = (e x : W) := by
  let b := Module.Free.chooseBasis ℤ S
  have h : (extendOfIsLattice e).toLinearMap.restrictScalars ℤ ∘ₗ S.subtype =
      T.subtype ∘ₗ e.toLinearMap := by
    apply b.ext
    intro i
    dsimp only [b]
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.subtype_apply,
      LinearEquiv.coe_toLinearMap]
    rw [← Basis.extendOfIsLattice_apply ℚ (Module.Free.chooseBasis ℤ S) i]
    -- Expose the constructed basis equivalence so `Basis.equiv_apply` can identify its values.
    unfold extendOfIsLattice
    rw [Basis.equiv_apply, Basis.extendOfIsLattice_apply, Basis.map_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun h x

/-- A rational linear equivalence extending a given equivalence of full submodules is the
canonical extension. -/
theorem eq_extendOfIsLattice {S : Submodule ℤ V} {T : Submodule ℤ W}
    [S.IsLattice ℚ] [T.IsLattice ℚ] (e : S ≃ₗ[ℤ] T) (f : V ≃ₗ[ℚ] W)
    (h : ∀ x : S, f (x : V) = (e x : W)) : f = extendOfIsLattice e := by
  apply LinearEquiv.toLinearMap_injective
  apply (Module.Free.chooseBasis ℤ S).extendOfIsLattice ℚ |>.ext
  intro i
  rw [Basis.extendOfIsLattice_apply]
  exact (h (Module.Free.chooseBasis ℤ S i)).trans
    (extendOfIsLattice_apply e (Module.Free.chooseBasis ℤ S i)).symm

/-- The rational extension maps the source full submodule onto the target full submodule. -/
theorem extendOfIsLattice_map {S : Submodule ℤ V} {T : Submodule ℤ W}
    [S.IsLattice ℚ] [T.IsLattice ℚ] (e : S ≃ₗ[ℤ] T) :
    S.map ((extendOfIsLattice e).restrictScalars ℤ).toLinearMap = T := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hmem : (e (⟨x, hx⟩ : S) : W) ∈ T := (e ⟨x, hx⟩).2
    rw [← extendOfIsLattice_apply] at hmem
    simpa only [LinearEquiv.restrictScalars_apply, LinearEquiv.coe_toLinearMap] using hmem
  · intro y hy
    let yT : T := ⟨y, hy⟩
    let xS : S := e.symm yT
    refine ⟨(xS : V), xS.2, ?_⟩
    simpa only [LinearEquiv.restrictScalars_apply, LinearEquiv.coe_toLinearMap,
      extendOfIsLattice_apply] using congr_arg Subtype.val (e.apply_symm_apply yT)

end LinearEquiv

namespace Submodule

variable {V : Type u} {W : Type v}
variable [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup W] [Module ℚ W]

/-- A rational linear equivalence maps a full integral submodule to a full integral submodule. -/
theorem IsLattice.map (S : Submodule ℤ V) [S.IsLattice ℚ] (e : V ≃ₗ[ℚ] W) :
    (S.map (e.restrictScalars ℤ).toLinearMap).IsLattice ℚ where
  fg := Submodule.FG.map (e.restrictScalars ℤ).toLinearMap
    _root_.Submodule.IsLattice.fg
  span_eq_top := by
    simp [Submodule.map_coe, Submodule.span_image_linearEquiv,
      _root_.Submodule.IsLattice.span_eq_top]

end Submodule

end TauCeti
