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
character lattice and the root-index type. It applies in particular to the diagonal root datum of
`GL_n`, whose coordinate type is `ULift (Fin n)`.

## Main declarations

* `TauCeti.SplitTorus.coordinatePermRootIndex`: simultaneous application of a coordinate
  permutation to both entries of a root index.
* `TauCeti.SplitTorus.coordinateRootDatumWeylGroupMulEquiv`: the canonical multiplicative
  equivalence from coordinate permutations to the Weyl group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 19.7 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 16.1 and 26.3.

This completes the Weyl-group identification for the coordinate root datum used by the split
`GL_n` example in Layer 7, "Root datum of `(G, T)`", of the ReductiveGroups roadmap.
-/

public section

open Function Set

namespace TauCeti.SplitTorus

noncomputable section

variable {σ : Type*}

attribute [local instance] Classical.decEq

/-- A coordinate permutation acts on a root index by applying it to both entries. -/
noncomputable def coordinatePermRootIndex (e : Equiv.Perm σ) :
    CoordinateRootIndex σ ≃ CoordinateRootIndex σ :=
  Equiv.subtypeEquiv (e.prodCongr e) (fun p ↦ by simp)

/-- A coordinate permutation acts componentwise on an ordered root index. -/
@[simp]
theorem coordinatePermRootIndex_coe (e : Equiv.Perm σ) (p : CoordinateRootIndex σ) :
    (coordinatePermRootIndex e p).1 = (e p.1.1, e p.1.2) :=
  by
    rw [coordinatePermRootIndex]
    rfl

private theorem coordinatePermRootIndex_symm (e : Equiv.Perm σ) :
    (coordinatePermRootIndex e).symm = coordinatePermRootIndex e.symm := by
  apply Equiv.ext
  intro p
  apply (coordinatePermRootIndex e).injective
  apply Subtype.ext
  simp only [Equiv.apply_symm_apply, coordinatePermRootIndex_coe]

private theorem domLCongr_coordinateRoot (e : Equiv.Perm σ) (p : CoordinateRootIndex σ) :
    Finsupp.domLCongr (R := ℤ) e (coordinateRoot p.1.1 p.1.2) =
      coordinateRoot (coordinatePermRootIndex e p).1.1
        (coordinatePermRootIndex e p).1.2 := by
  ext a
  simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply]
  rw [coordinateRoot_apply, coordinateRoot_apply, coordinatePermRootIndex_coe]
  simp only [Equiv.symm_apply_eq]

/-- The contravariant action of a coordinate permutation on the cocharacter lattice. -/
private def coordinatePermCoweightEquiv (e : Equiv.Perm σ) :
    (σ → ℤ) ≃ₗ[ℤ] (σ → ℤ) where
  toFun x a := x (e a)
  invFun x a := x (e.symm a)
  left_inv x := by ext a; simp
  right_inv x := by ext a; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem coordinatePermCoweightEquiv_apply
    (e : Equiv.Perm σ) (x : σ → ℤ) (a : σ) :
    coordinatePermCoweightEquiv e x a = x (e a) :=
  rfl

private theorem dotPairing_domLCongr (e : Equiv.Perm σ) (x : σ →₀ ℤ) (y : σ → ℤ) :
    dotPairing (Finsupp.domLCongr (R := ℤ) e x) y =
      dotPairing x (coordinatePermCoweightEquiv e y) := by
  rw [dotPairing_apply, dotPairing_apply]
  simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain, coordinatePermCoweightEquiv_apply]
  exact Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul ..)

variable [Finite σ]

/-- The root-datum automorphism induced by a coordinate permutation. -/
private noncomputable def coordinatePermRootDatumAut (e : Equiv.Perm σ) :
    RootPairing.Aut (coordinateRootDatum σ) where
  weightMap := (Finsupp.domLCongr (R := ℤ) e).toLinearMap
  coweightMap := (coordinatePermCoweightEquiv e).toLinearMap
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
    funext p
    change coordinatePermCoweightEquiv e ((coordinateRootDatum σ).coroot p) =
      (coordinateRootDatum σ).coroot ((coordinatePermRootIndex e).symm p)
    rw [coordinateRootDatum_coroot, coordinateRootDatum_coroot,
      coordinatePermRootIndex_symm, coordinatePermRootIndex_coe]
    ext a
    rw [coordinatePermCoweightEquiv_apply, coordinateCoroot_apply,
      coordinateCoroot_apply]
    simp only [e.eq_symm_apply]
  bijective_weightMap := (Finsupp.domLCongr (R := ℤ) e).bijective
  bijective_coweightMap := (coordinatePermCoweightEquiv e).bijective

@[simp]
private theorem coordinatePermRootDatumAut_weightEquiv_apply
    (e : Equiv.Perm σ) (x : σ →₀ ℤ) :
    ((coordinatePermRootDatumAut e : RootPairing.Aut (coordinateRootDatum σ)) :
        RootPairing.Equiv (coordinateRootDatum σ) (coordinateRootDatum σ)).weightMap x =
      Finsupp.domLCongr (R := ℤ) e x :=
  by
    rw [coordinatePermRootDatumAut]
    rfl

private theorem coordinatePermRootDatumAut_indexEquiv (e : Equiv.Perm σ) :
    (coordinatePermRootDatumAut e).indexEquiv = coordinatePermRootIndex e := by
  rw [coordinatePermRootDatumAut]

/-- Coordinate permutations as a homomorphism into root-datum automorphisms. -/
private noncomputable def coordinatePermRootDatumAutHom :
    Equiv.Perm σ →* RootPairing.Aut (coordinateRootDatum σ) where
  toFun := coordinatePermRootDatumAut
  map_one' := by
    apply RootPairing.Equiv.weightHom_injective (coordinateRootDatum σ)
    ext x a
    simp only [RootPairing.Equiv.weightHom_apply]
    rfl
  map_mul' e f := by
    apply RootPairing.Equiv.weightHom_injective (coordinateRootDatum σ)
    ext x a
    simp only [RootPairing.Equiv.weightHom_apply, map_mul, LinearEquiv.mul_apply]
    rfl

private theorem coordinatePermRootDatumAutHom_swap (i j : σ) (hij : i ≠ j) :
    coordinatePermRootDatumAutHom (Equiv.swap i j) =
      RootPairing.Equiv.reflection (coordinateRootDatum σ)
        (⟨(i, j), hij⟩ : CoordinateRootIndex σ) := by
  apply RootPairing.Equiv.weightHom_injective (coordinateRootDatum σ)
  ext x a
  change (RootPairing.Equiv.weightEquiv (coordinateRootDatum σ) (coordinateRootDatum σ)
      (coordinatePermRootDatumAut (Equiv.swap i j)) x) a = _
  rw [RootPairing.Equiv.weightEquiv_apply,
    coordinatePermRootDatumAut_weightEquiv_apply]
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
      RootPairing.Equiv.weightEquiv (coordinateRootDatum σ) (coordinateRootDatum σ) g
        (Finsupp.single i 1)) hef
  simpa only [coordinatePermRootDatumAutHom, MonoidHom.coe_mk, OneHom.coe_mk,
    RootPairing.Equiv.weightEquiv_apply,
    coordinatePermRootDatumAut_weightEquiv_apply, Finsupp.domLCongr_single] using h

private theorem coordinatePermRootDatumAutHom_range :
    MonoidHom.range (coordinatePermRootDatumAutHom (σ := σ)) =
      (coordinateRootDatum σ).weylGroup := by
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
noncomputable def coordinateRootDatumWeylGroupMulEquiv :
    Equiv.Perm σ ≃* (coordinateRootDatum σ).weylGroup :=
  MulEquiv.ofBijective coordinatePermWeylGroupHom coordinatePermWeylGroupHom_bijective

/-- A coordinate permutation acts on the character lattice by moving each coordinate through
that permutation. -/
@[simp]
theorem coordinateRootDatumWeylGroupMulEquiv_smul_apply
    (e : Equiv.Perm σ) (x : σ →₀ ℤ) (a : σ) :
    (coordinateRootDatumWeylGroupMulEquiv e • x) a = x (e.symm a) := by
  change (RootPairing.Equiv.weightEquiv (coordinateRootDatum σ) (coordinateRootDatum σ)
      (coordinatePermRootDatumAut e) x) a = _
  rw [RootPairing.Equiv.weightEquiv_apply,
    coordinatePermRootDatumAut_weightEquiv_apply]
  rfl

/-- The Weyl element attached to a coordinate permutation applies that permutation to both
entries of every root index. -/
@[simp]
theorem coordinateRootDatumWeylGroupMulEquiv_rootIndex_apply
    (e : Equiv.Perm σ) (p : CoordinateRootIndex σ) :
    (coordinateRootDatumWeylGroupMulEquiv e).1.indexEquiv p =
      coordinatePermRootIndex e p :=
  by
    change (coordinatePermRootDatumAut e).indexEquiv p = coordinatePermRootIndex e p
    rw [coordinatePermRootDatumAut_indexEquiv]

/-- A coordinate transposition corresponds to the reflection in the associated root. -/
@[simp]
theorem coordinateRootDatumWeylGroupMulEquiv_swap (i j : σ) (hij : i ≠ j) :
    coordinateRootDatumWeylGroupMulEquiv (Equiv.swap i j) =
      RootPairing.weylGroup.ofIdx (coordinateRootDatum σ)
        (⟨(i, j), hij⟩ : CoordinateRootIndex σ) := by
  apply Subtype.ext
  exact coordinatePermRootDatumAutHom_swap i j hij

/-- The inverse Weyl-group equivalence sends a root reflection to the transposition of its two
coordinates. -/
@[simp]
theorem coordinateRootDatumWeylGroupMulEquiv_symm_ofIdx (p : CoordinateRootIndex σ) :
    (coordinateRootDatumWeylGroupMulEquiv (σ := σ)).symm
        (RootPairing.weylGroup.ofIdx (coordinateRootDatum σ) p) =
      Equiv.swap p.1.1 p.1.2 := by
  apply (coordinateRootDatumWeylGroupMulEquiv (σ := σ)).injective
  rw [MulEquiv.apply_symm_apply]
  exact (coordinateRootDatumWeylGroupMulEquiv_swap p.1.1 p.1.2 p.2).symm

end

end TauCeti.SplitTorus
