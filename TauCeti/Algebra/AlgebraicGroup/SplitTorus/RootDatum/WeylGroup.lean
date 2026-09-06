/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.RootDatum.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Weyl groups of coordinate-difference root data

For a finite coordinate type `σ`, the roots of `SplitTorus.coordinateRootDatum σ` are all
differences `e_i - e_j`. Its root reflections are therefore exactly the transpositions of the
coordinates. Since transpositions generate the finite symmetric group, the Weyl group of this
root datum is canonically isomorphic to `Equiv.Perm σ`.

The equivalence constructed here is characterized both on reflections and on its actions on the
character lattice and the root-index type.

## Main declarations

* `TauCeti.SplitTorus.coordinatePermMulEquivWeylGroup`: the canonical multiplicative
  equivalence from coordinate permutations to the Weyl group.
* `TauCeti.SplitTorus.coordinatePermMulEquivWeylGroup_swap` and
  `coordinatePermMulEquivWeylGroup_symm_ofIdx`: coordinate transpositions correspond to root
  reflections in both directions.
* `TauCeti.SplitTorus.coordinatePermMulEquivWeylGroup_smul_apply` and
  `coordinatePermMulEquivWeylGroup_indexEquiv_apply`: the induced actions on characters and root
  indices.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 19.7 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 16.1 and 26.3.

This advances the split Weyl-group part of Layer 7, "Root datum of `(G, T)`", of the
ReductiveGroups roadmap.
-/

public section

open Function Set

namespace TauCeti.SplitTorus

noncomputable section

variable {σ : Type*}

private theorem domLCongr_coordinateRoot (e : Equiv.Perm σ) (p : CoordinateRootIndex σ) :
    Finsupp.domLCongr (R := ℤ) e (coordinateRoot p.1.1 p.1.2) =
      coordinateRoot (coordinatePermRootIndex e p).1.1
        (coordinatePermRootIndex e p).1.2 := by
  classical
  ext a
  simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply]
  rw [coordinateRoot_apply, coordinateRoot_apply, coordinatePermRootIndex_coe]
  simp only [Equiv.symm_apply_eq]

private theorem dotPairing_domLCongr (e : Equiv.Perm σ) (x : σ →₀ ℤ) (y : σ → ℤ) :
    dotPairing (Finsupp.domLCongr (R := ℤ) e x) y =
      dotPairing x (LinearEquiv.piCongrLeft' ℤ (fun _ : σ ↦ ℤ) e.symm y) := by
  rw [dotPairing_apply, dotPairing_apply]
  simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain, LinearEquiv.piCongrLeft'_apply,
    Equiv.symm_symm]
  exact Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul ..)

variable [Finite σ]

/-- The root-datum automorphism induced by a coordinate permutation. -/
private noncomputable def coordinatePermRootDatumAut (e : Equiv.Perm σ) :
    RootPairing.Aut (coordinateRootDatum σ) where
  weightMap := (Finsupp.domLCongr (R := ℤ) e).toLinearMap
  coweightMap := (LinearEquiv.piCongrLeft' ℤ (fun _ : σ ↦ ℤ) e.symm).toLinearMap
  indexEquiv := coordinatePermRootIndex e
  weight_coweight_transpose := by
    refine LinearMap.ext fun y => LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_comp, LinearMap.dualMap_apply, Function.comp_apply,
      LinearEquiv.coe_coe, LinearMap.toLinearMap_toPerfPair,
      RootPairing.flip_toLinearMap, coordinateRootDatum_toLinearMap,
      LinearMap.flip_apply]
    exact dotPairing_domLCongr e x y
  root_weightMap := by
    funext p
    simp only [Function.comp_apply, coordinateRootDatum_root]
    exact domLCongr_coordinateRoot e p
  coroot_coweightMap := by
    classical
    funext p
    simp only [Function.comp_apply, LinearEquiv.coe_coe]
    rw [coordinateRootDatum_coroot, coordinateRootDatum_coroot,
      coordinatePermRootIndex_symm, coordinatePermRootIndex_coe]
    ext a
    rw [LinearEquiv.piCongrLeft'_apply, coordinateCoroot_apply,
      coordinateCoroot_apply]
    simp only [Equiv.symm_symm, e.eq_symm_apply]
  bijective_weightMap := (Finsupp.domLCongr (R := ℤ) e).bijective
  bijective_coweightMap :=
    (LinearEquiv.piCongrLeft' ℤ (fun _ : σ ↦ ℤ) e.symm).bijective

private theorem coordinatePermRootDatumAut_weightMap_apply
    (e : Equiv.Perm σ) (x : σ →₀ ℤ) :
    ((coordinatePermRootDatumAut e : RootPairing.Aut (coordinateRootDatum σ)) :
        RootPairing.Equiv (coordinateRootDatum σ) (coordinateRootDatum σ)).weightMap x =
      Finsupp.domLCongr (R := ℤ) e x :=
  by
    rw [coordinatePermRootDatumAut]
    simp only [LinearEquiv.coe_coe]

private theorem coordinatePermRootDatumAut_indexEquiv (e : Equiv.Perm σ) :
    (coordinatePermRootDatumAut e).indexEquiv = coordinatePermRootIndex e := by
  rw [coordinatePermRootDatumAut]

/-- Coordinate permutations as a homomorphism into root-datum automorphisms. -/
private noncomputable def coordinatePermRootDatumAutHom :
    Equiv.Perm σ →* RootPairing.Aut (coordinateRootDatum σ) where
  toFun := coordinatePermRootDatumAut
  map_one' := by
    apply RootPairing.Equiv.weightHom_injective (coordinateRootDatum σ)
    apply LinearEquiv.ext
    intro x
    simp only [RootPairing.Equiv.weightHom_apply,
      RootPairing.Equiv.weightEquiv_apply, coordinatePermRootDatumAut_weightMap_apply,
      map_one, Equiv.Perm.one_def, Finsupp.domLCongr_refl,
      LinearEquiv.refl_apply]
    -- The remaining application of the identity linear equivalence is definitional.
    rfl
  map_mul' e f := by
    apply RootPairing.Equiv.weightHom_injective (coordinateRootDatum σ)
    apply LinearEquiv.ext
    intro x
    simp only [RootPairing.Equiv.weightHom_apply, map_mul, LinearEquiv.mul_apply,
      RootPairing.Equiv.weightEquiv_apply, coordinatePermRootDatumAut_weightMap_apply]
    simpa only [Equiv.Perm.mul_def, LinearEquiv.trans_apply] using
      congrArg (fun g : (σ →₀ ℤ) ≃ₗ[ℤ] (σ →₀ ℤ) ↦ g x)
        (Finsupp.domLCongr_trans (R := ℤ) f e).symm

private theorem coordinatePermRootDatumAutHom_swap [DecidableEq σ]
    (i j : σ) (hij : i ≠ j) :
    coordinatePermRootDatumAutHom (Equiv.swap i j) =
      RootPairing.Equiv.reflection (coordinateRootDatum σ)
        (⟨(i, j), hij⟩ : CoordinateRootIndex σ) := by
  cases Subsingleton.elim ‹DecidableEq σ› (Classical.decEq σ)
  classical
  apply RootPairing.Equiv.weightHom_injective (coordinateRootDatum σ)
  ext x a
  simp only [RootPairing.Equiv.weightHom_apply, coordinatePermRootDatumAutHom,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [RootPairing.Equiv.weightEquiv_apply,
    coordinatePermRootDatumAut_weightMap_apply]
  simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply, Equiv.symm_swap]
  exact coordinateRootDatum_reflection_apply
    (⟨(i, j), hij⟩ : CoordinateRootIndex σ) x a |>.symm

private theorem coordinatePermRootDatumAutHom_injective :
    Function.Injective (coordinatePermRootDatumAutHom (σ := σ)) := by
  intro e f hef
  ext i
  apply Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0)
  have h := congrArg
    (fun g : RootPairing.Aut (coordinateRootDatum σ) ↦
      RootPairing.Equiv.weightEquiv g (Finsupp.single i 1)) hef
  simpa only [coordinatePermRootDatumAutHom, MonoidHom.coe_mk, OneHom.coe_mk,
    RootPairing.Equiv.weightEquiv_apply,
    coordinatePermRootDatumAut_weightMap_apply, Finsupp.domLCongr_single] using h

private theorem coordinatePermRootDatumAutHom_range :
    MonoidHom.range (coordinatePermRootDatumAutHom (σ := σ)) =
      (coordinateRootDatum σ).weylGroup := by
  classical
  apply le_antisymm
  · rintro _ ⟨e, rfl⟩
    induction e using Equiv.Perm.swap_induction_on with
    | one =>
        rw [map_one]
        exact (coordinateRootDatum σ).weylGroup.one_mem
    | swap_mul e i j hij he =>
        rw [map_mul]
        exact Subgroup.mul_mem (coordinateRootDatum σ).weylGroup
          (coordinatePermRootDatumAutHom_swap i j hij ▸
            (coordinateRootDatum σ).reflection_mem_weylGroup
              (⟨(i, j), hij⟩ : CoordinateRootIndex σ)) he
  · rw [RootPairing.weylGroup, Subgroup.closure_le]
    rintro _ ⟨p, rfl⟩
    rcases p with ⟨⟨i, j⟩, hij⟩
    rw [← coordinatePermRootDatumAutHom_swap i j hij]
    exact ⟨Equiv.swap i j, rfl⟩

/-- Coordinate permutations as a homomorphism into the coordinate Weyl group. -/
private noncomputable def coordinatePermWeylGroupHom :
    Equiv.Perm σ →* (coordinateRootDatum σ).weylGroup :=
  (coordinatePermRootDatumAutHom (σ := σ)).codRestrict
    (coordinateRootDatum σ).weylGroup fun e ↦ by
      rw [← coordinatePermRootDatumAutHom_range]
      exact ⟨e, rfl⟩

private theorem coordinatePermWeylGroupHom_bijective :
    Function.Bijective (coordinatePermWeylGroupHom (σ := σ)) := by
  constructor
  · intro e f hef
    apply coordinatePermRootDatumAutHom_injective
    exact congrArg Subtype.val hef
  · intro w
    have hw : (w : RootPairing.Aut (coordinateRootDatum σ)) ∈
        MonoidHom.range (coordinatePermRootDatumAutHom (σ := σ)) := by
      rw [coordinatePermRootDatumAutHom_range]
      exact w.2
    obtain ⟨e, he⟩ := hw
    exact ⟨e, Subtype.ext he⟩

/-- The Weyl group of the coordinate-difference root datum is canonically the permutation group
of its coordinates. The equivalence sends a transposition to the reflection in the corresponding
root. -/
noncomputable def coordinatePermMulEquivWeylGroup :
    Equiv.Perm σ ≃* (coordinateRootDatum σ).weylGroup :=
  MulEquiv.ofBijective coordinatePermWeylGroupHom coordinatePermWeylGroupHom_bijective

private theorem coordinatePermMulEquivWeylGroup_val (e : Equiv.Perm σ) :
    (coordinatePermMulEquivWeylGroup e).1 = coordinatePermRootDatumAut e := by
  simp only [coordinatePermMulEquivWeylGroup, MulEquiv.ofBijective_apply,
    coordinatePermWeylGroupHom, MonoidHom.codRestrict_apply,
    coordinatePermRootDatumAutHom, MonoidHom.coe_mk, OneHom.coe_mk]

/-- The underlying root-datum automorphism pushes each character coordinate forward along the
permutation; equivalently, its value at `a` is the original value at `e.symm a`. -/
@[simp]
theorem coordinatePermMulEquivWeylGroup_weightMap_apply
    (e : Equiv.Perm σ) (x : σ →₀ ℤ) :
    (coordinatePermMulEquivWeylGroup e).1.weightMap x =
      Finsupp.domLCongr (R := ℤ) e x := by
  rw [coordinatePermMulEquivWeylGroup_val]
  exact coordinatePermRootDatumAut_weightMap_apply e x

/-- The underlying root-datum automorphism acts contravariantly on the cocharacter lattice. -/
@[simp]
theorem coordinatePermMulEquivWeylGroup_coweightMap_apply
    (e : Equiv.Perm σ) (x : σ → ℤ) (a : σ) :
    (coordinatePermMulEquivWeylGroup e).1.coweightMap x a = x (e a) := by
  rw [coordinatePermMulEquivWeylGroup_val, coordinatePermRootDatumAut]
  simp only [LinearEquiv.coe_coe, LinearEquiv.piCongrLeft'_apply, Equiv.symm_symm]

/-- The Weyl-group action is the restriction of Mathlib's root-datum automorphism action, which
is implemented by `RootPairing.Equiv.weightHom`. -/
private theorem coordinateRootDatumWeylGroup_smul_eq_weightMap
    (w : (coordinateRootDatum σ).weylGroup) (x : σ →₀ ℤ) :
    w • x = w.1.weightMap x := by
  rw [Subgroup.smul_def]
  -- Mathlib has no lemma unfolding this `DistribMulAction` instance to `weightHom`.
  change (RootPairing.Equiv.weightHom (coordinateRootDatum σ) w.1) x = _
  rw [RootPairing.Equiv.weightHom_apply, RootPairing.Equiv.weightEquiv_apply]

/-- A coordinate permutation acts on the character lattice by moving each coordinate through
that permutation. -/
@[simp]
theorem coordinatePermMulEquivWeylGroup_smul_apply
    (e : Equiv.Perm σ) (x : σ →₀ ℤ) (a : σ) :
    (coordinatePermMulEquivWeylGroup e • x) a = x (e.symm a) := by
  rw [coordinateRootDatumWeylGroup_smul_eq_weightMap,
    coordinatePermMulEquivWeylGroup_weightMap_apply,
    Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply]

/-- The Weyl element attached to a coordinate permutation applies that permutation to both
entries of every root index. -/
@[simp]
theorem coordinatePermMulEquivWeylGroup_indexEquiv_apply
    (e : Equiv.Perm σ) (p : CoordinateRootIndex σ) :
    (coordinatePermMulEquivWeylGroup e).1.indexEquiv p =
      coordinatePermRootIndex e p :=
  by
    rw [coordinatePermMulEquivWeylGroup_val,
      coordinatePermRootDatumAut_indexEquiv]

/-- A coordinate transposition corresponds to the reflection in the associated root. -/
@[simp]
theorem coordinatePermMulEquivWeylGroup_swap [DecidableEq σ]
    (i j : σ) (hij : i ≠ j) :
    coordinatePermMulEquivWeylGroup (Equiv.swap i j) =
      RootPairing.weylGroup.ofIdx (coordinateRootDatum σ)
        (⟨(i, j), hij⟩ : CoordinateRootIndex σ) := by
  apply Subtype.ext
  exact coordinatePermRootDatumAutHom_swap i j hij

/-- The inverse Weyl-group equivalence sends a root reflection to the transposition of its two
coordinates. -/
@[simp]
theorem coordinatePermMulEquivWeylGroup_symm_ofIdx [DecidableEq σ]
    (p : CoordinateRootIndex σ) :
    (coordinatePermMulEquivWeylGroup (σ := σ)).symm
        (RootPairing.weylGroup.ofIdx (coordinateRootDatum σ) p) =
      Equiv.swap p.1.1 p.1.2 := by
  apply (coordinatePermMulEquivWeylGroup (σ := σ)).injective
  rw [MulEquiv.apply_symm_apply]
  exact (coordinatePermMulEquivWeylGroup_swap p.1.1 p.1.2 p.2).symm

end

end TauCeti.SplitTorus
