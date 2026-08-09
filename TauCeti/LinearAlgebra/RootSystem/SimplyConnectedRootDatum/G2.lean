/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.RootSystem.Base

public section

/-!
# The simply connected root datum of type G2

This file constructs the pinned integral root datum of type `G2` on the character and cocharacter
lattices `Fin 2 -> Z`. The character lattice is written in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. Consequently the two simple roots are the rows
`(2, -1)` and `(-3, 2)` of the Bourbaki-numbered Cartan matrix, while their coroots are the two
standard basis vectors.

The twelve roots are ordered with the two simple roots first, followed by the other four positive
roots and then their negatives. Their coroots use the same ordering. The displayed positive roots,
in simple-root coordinates, are

```text
alpha1, alpha2, alpha1 + alpha2, 2 alpha1 + alpha2,
3 alpha1 + alpha2, 3 alpha1 + 2 alpha2.
```

Here `alpha1` is short and `alpha2` is long. The corresponding positive coroot coordinates are
`(1,0)`, `(0,1)`, `(1,3)`, `(2,3)`, `(1,1)`, `(1,2)`. These tables make the carrier explicit and
also make the reflection-stability axioms of `RootPairing` decidable finite calculations.

## Main definitions and results

* `TauCeti.DynkinType.g2SimplyConnectedRootDatum` is the pinned twelve-root datum.
* `TauCeti.DynkinType.g2SimplyConnectedBase` is its Bourbaki-numbered base.
* `TauCeti.DynkinType.hasCartanType_g2SimplyConnectedRootDatum` identifies its Cartan type as `G2`.
* `TauCeti.DynkinType.span_coroot_g2SimplyConnectedRootDatum` records that its coroots span the
  cocharacter lattice, the simply connected condition.

## References

The coordinates and numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate IX. This is the `G2` branch of Layer 6 in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

namespace TauCeti

open _root_.Matrix Module Set Submodule

namespace DynkinType

/-- The roots of `G2` in the fundamental-weight basis, with simple roots first. -/
private def g2Root : Fin 12 ↪ (Fin 2 → ℤ) where
  toFun := ![
    ![2, -1], ![-3, 2], ![-1, 1], ![1, 0], ![3, -1], ![0, 1],
    ![-2, 1], ![3, -2], ![1, -1], ![-1, 0], ![-3, 1], ![0, -1]]
  inj' := by decide

/-- The coroots of `G2` in the simple-coroot basis, ordered compatibly with `g2Root`. -/
private def g2Coroot : Fin 12 ↪ (Fin 2 → ℤ) where
  toFun := ![
    ![1, 0], ![0, 1], ![1, 3], ![2, 3], ![1, 1], ![1, 2],
    ![-1, 0], ![0, -1], ![-1, -3], ![-2, -3], ![-1, -1], ![-1, -2]]
  inj' := by decide

/-- The permutation table for reflection in each of the twelve `G2` roots. -/
private def g2ReflectionIndex : Fin 12 → Fin 12 → Fin 12 := ![
  ![6, 4, 3, 2, 1, 5, 0, 10, 9, 8, 7, 11],
  ![2, 7, 0, 3, 5, 4, 8, 1, 6, 9, 11, 10],
  ![3, 11, 8, 0, 4, 7, 9, 5, 2, 6, 10, 1],
  ![8, 1, 6, 9, 11, 10, 2, 7, 0, 3, 5, 4],
  ![9, 5, 2, 6, 10, 1, 3, 11, 8, 0, 4, 7],
  ![0, 10, 9, 8, 7, 11, 6, 4, 3, 2, 1, 5],
  ![6, 4, 3, 2, 1, 5, 0, 10, 9, 8, 7, 11],
  ![2, 7, 0, 3, 5, 4, 8, 1, 6, 9, 11, 10],
  ![3, 11, 8, 0, 4, 7, 9, 5, 2, 6, 10, 1],
  ![8, 1, 6, 9, 11, 10, 2, 7, 0, 3, 5, 4],
  ![9, 5, 2, 6, 10, 1, 3, 11, 8, 0, 4, 7],
  ![0, 10, 9, 8, 7, 11, 6, 4, 3, 2, 1, 5]]

/-- Reflection in a `G2` root as a permutation of the pinned root indices. -/
private def g2ReflectionPerm (i : Fin 12) : Fin 12 ≃ Fin 12 where
  toFun := g2ReflectionIndex i
  invFun := g2ReflectionIndex i
  left_inv := by
    intro j
    fin_cases i <;> fin_cases j <;> rfl
  right_inv := by
    intro j
    fin_cases i <;> fin_cases j <;> rfl

@[simp] private lemma g2ReflectionPerm_apply (i j : Fin 12) :
    g2ReflectionPerm i j = g2ReflectionIndex i j := rfl

/-- The standard perfect pairing between the weight and coweight coordinate lattices. -/
private def g2Pairing : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) →ₗ[ℤ] ℤ :=
  dotProductBilin ℤ ℤ

private instance : g2Pairing.IsPerfPair := by
  change (dotProductEquiv ℤ (Fin 2)).toLinearMap.IsPerfPair
  infer_instance

private lemma g2Reflection_root (i j : Fin 12) :
    g2Root j - (g2Root j ⬝ᵥ g2Coroot i) • g2Root i =
      g2Root (g2ReflectionIndex i j) := by
  decide +revert

private lemma g2Reflection_coroot (i j : Fin 12) :
    g2Coroot j - (g2Root i ⬝ᵥ g2Coroot j) • g2Coroot i =
      g2Coroot (g2ReflectionIndex i j) := by
  decide +revert

/-- The pinned simply connected root datum of type `G2`.

Both lattices use `Fin 2 -> Z`: fundamental weights on the root side and simple coroots on the
coroot side. Root indices `0` and `1` are the short and long simple roots respectively. -/
def g2SimplyConnectedRootDatum : RootDatum (Fin 12) (Fin 2 → ℤ) (Fin 2 → ℤ) where
  toLinearMap := g2Pairing
  root := g2Root
  coroot := g2Coroot
  root_coroot_two := by
    intro i
    fin_cases i <;> norm_num [g2Pairing, g2Root, g2Coroot, dotProduct]
  reflectionPerm := g2ReflectionPerm
  reflectionPerm_root := by
    intro i j
    simpa only [g2Pairing, dotProductBilin_apply_apply, g2ReflectionPerm_apply] using
      g2Reflection_root i j
  reflectionPerm_coroot := by
    intro i j
    simpa only [g2Pairing, dotProductBilin_apply_apply, g2ReflectionPerm_apply] using
      g2Reflection_coroot i j

/-- Root indices `0` and `1` in the pinned `G2` datum are the two simple roots. -/
private def g2SimpleRootIndex : Fin 2 → Fin 12 := ![0, 1]

@[simp] private lemma g2SimpleRootIndex_val (i : Fin 2) :
    (g2SimpleRootIndex i : ℕ) = i := by fin_cases i <;> rfl

/-- The change of basis from simple-root coordinates to fundamental-weight coordinates. Its
matrix is the Bourbaki `G2` Cartan matrix and has determinant one. -/
private def g2SimpleRootEquiv : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![2 * x 0 - 3 * x 1, -x 0 + 2 * x 1]
  invFun x := ![2 * x 0 + 3 * x 1, x 0 + 2 * x 1]
  left_inv := by
    intro x
    ext i
    fin_cases i <;> simp <;> ring
  right_inv := by
    intro x
    ext i
    fin_cases i <;> simp <;> ring
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro c x
    ext i
    fin_cases i <;> simp <;> ring

/-- The first two pinned roots are a basis of the character lattice. -/
private noncomputable def g2SimpleRootBasis : Module.Basis (Fin 2) ℤ (Fin 2 → ℤ) :=
  (Pi.basisFun ℤ (Fin 2)).map g2SimpleRootEquiv

@[simp] private lemma g2SimpleRootBasis_apply (i : Fin 2) :
    g2SimpleRootBasis i = g2Root (g2SimpleRootIndex i) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [g2SimpleRootBasis, g2SimpleRootEquiv, g2SimpleRootIndex, g2Root]

private lemma span_g2Root_eq_top : span ℤ (range g2Root) = ⊤ := by
  apply top_unique
  rw [← g2SimpleRootBasis.span_eq]
  apply span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨g2SimpleRootIndex i, (g2SimpleRootBasis_apply i).symm⟩

private lemma span_g2Coroot_eq_top : span ℤ (range g2Coroot) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin 2)).span_eq]
  apply span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨g2SimpleRootIndex i, ?_⟩
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [g2SimpleRootIndex, g2Coroot]

/-- The pinned `G2` datum is a root system: its roots and coroots span their two lattices. -/
instance : g2SimplyConnectedRootDatum.IsRootSystem where
  span_root_eq_top := span_g2Root_eq_top
  span_coroot_eq_top := span_g2Coroot_eq_top

/-- The coroots of the pinned `G2` datum span the whole cocharacter lattice. This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. -/
theorem span_coroot_g2SimplyConnectedRootDatum :
    g2SimplyConnectedRootDatum.corootSpan ℤ = ⊤ :=
  RootPairing.IsRootSystem.span_coroot_eq_top

private lemma g2Root_mem_or_neg_mem (i : Fin 12) :
    g2Root i ∈ AddSubmonoid.closure (g2Root '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12))) ∨
      -g2Root i ∈
        AddSubmonoid.closure (g2Root '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12))) := by
  let C := AddSubmonoid.closure (g2Root '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12)))
  have h0 : g2Root 0 ∈ C := AddSubmonoid.subset_closure ⟨0, by simp, rfl⟩
  have h1 : g2Root 1 ∈ C := AddSubmonoid.subset_closure ⟨1, by simp, rfl⟩
  have comb (m n : ℕ) : m • g2Root 0 + n • g2Root 1 ∈ C :=
    C.add_mem (C.nsmul_mem h0 m) (C.nsmul_mem h1 n)
  fin_cases i
  · exact Or.inl h0
  · exact Or.inl h1
  · apply Or.inl
    convert comb 1 1 using 1
    ext j
    fin_cases j <;> norm_num [g2Root]
  · apply Or.inl
    convert comb 2 1 using 1
    ext j
    fin_cases j <;> norm_num [g2Root]
  · apply Or.inl
    convert comb 3 1 using 1
    ext j
    fin_cases j <;> norm_num [g2Root]
  · apply Or.inl
    convert comb 3 2 using 1
    ext j
    fin_cases j <;> norm_num [g2Root]
  · apply Or.inr
    convert comb 1 0 using 1
    ext j
    fin_cases j <;> norm_num [g2Root]
  · apply Or.inr
    convert comb 0 1 using 1
    ext j
    fin_cases j <;> norm_num [g2Root]
  · apply Or.inr
    convert comb 1 1 using 1
    ext j
    fin_cases j <;> norm_num [g2Root]
  · apply Or.inr
    convert comb 2 1 using 1
    ext j
    fin_cases j <;> norm_num [g2Root]
  · apply Or.inr
    convert comb 3 1 using 1
    ext j
    fin_cases j <;> norm_num [g2Root]
  · apply Or.inr
    convert comb 3 2 using 1
    ext j
    fin_cases j <;> norm_num [g2Root]

private lemma g2Coroot_mem_or_neg_mem (i : Fin 12) :
    g2Coroot i ∈
        AddSubmonoid.closure (g2Coroot '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12))) ∨
      -g2Coroot i ∈
        AddSubmonoid.closure (g2Coroot '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12))) := by
  let C := AddSubmonoid.closure (g2Coroot '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12)))
  have h0 : g2Coroot 0 ∈ C := AddSubmonoid.subset_closure ⟨0, by simp, rfl⟩
  have h1 : g2Coroot 1 ∈ C := AddSubmonoid.subset_closure ⟨1, by simp, rfl⟩
  have comb (m n : ℕ) : m • g2Coroot 0 + n • g2Coroot 1 ∈ C :=
    C.add_mem (C.nsmul_mem h0 m) (C.nsmul_mem h1 n)
  fin_cases i
  · exact Or.inl h0
  · exact Or.inl h1
  · apply Or.inl
    convert comb 1 3 using 1
    ext j
    fin_cases j <;> norm_num [g2Coroot]
  · apply Or.inl
    convert comb 2 3 using 1
    ext j
    fin_cases j <;> norm_num [g2Coroot]
  · apply Or.inl
    convert comb 1 1 using 1
    ext j
    fin_cases j <;> norm_num [g2Coroot]
  · apply Or.inl
    convert comb 1 2 using 1
    ext j
    fin_cases j <;> norm_num [g2Coroot]
  · apply Or.inr
    convert comb 1 0 using 1
    ext j
    fin_cases j <;> norm_num [g2Coroot]
  · apply Or.inr
    convert comb 0 1 using 1
    ext j
    fin_cases j <;> norm_num [g2Coroot]
  · apply Or.inr
    convert comb 1 3 using 1
    ext j
    fin_cases j <;> norm_num [g2Coroot]
  · apply Or.inr
    convert comb 2 3 using 1
    ext j
    fin_cases j <;> norm_num [g2Coroot]
  · apply Or.inr
    convert comb 1 1 using 1
    ext j
    fin_cases j <;> norm_num [g2Coroot]
  · apply Or.inr
    convert comb 1 2 using 1
    ext j
    fin_cases j <;> norm_num [g2Coroot]

/-- The Bourbaki-numbered base of the pinned simply connected `G2` root datum. Its support is the
first two root indices, short root first and long root second. -/
def g2SimplyConnectedBase : g2SimplyConnectedRootDatum.Base where
  support := {0, 1}
  linearIndepOn_root := by
    have hli : LinearIndepOn ℤ g2Root
        (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12)) := by
      rw [Finset.coe_insert, Finset.coe_singleton]
      refine (LinearIndepOn.pair_iff g2Root (by decide : (0 : Fin 12) ≠ 1)).2 ?_
      intro c d h
      have h0 : c * 2 + -(d * 3) = 0 := by simpa [g2Root] using congrFun h 0
      have h1 : -c + d * 2 = 0 := by simpa [g2Root] using congrFun h 1
      omega
    simpa only [g2SimplyConnectedRootDatum] using hli
  linearIndepOn_coroot := by
    have hli : LinearIndepOn ℤ g2Coroot
        (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12)) := by
      rw [Finset.coe_insert, Finset.coe_singleton]
      refine (LinearIndepOn.pair_iff g2Coroot (by decide : (0 : Fin 12) ≠ 1)).2 ?_
      intro c d h
      exact ⟨by simpa [g2Coroot] using congrFun h 0,
        by simpa [g2Coroot] using congrFun h 1⟩
    simpa only [g2SimplyConnectedRootDatum] using hli
  root_mem_or_neg_mem := g2Root_mem_or_neg_mem
  coroot_mem_or_neg_mem := g2Coroot_mem_or_neg_mem

@[simp] lemma g2SimplyConnectedBase_support : g2SimplyConnectedBase.support = {0, 1} := (rfl)

private lemma g2SimplyConnectedBase_coe_eq (i : g2SimplyConnectedBase.support) :
    (i : Fin 12) = 0 ∨ (i : Fin 12) = 1 := by
  simpa only [g2SimplyConnectedBase_support, Finset.mem_insert, Finset.mem_singleton] using
    i.property

/-- The ordered support of the pinned base is identified with the two Bourbaki nodes. -/
private def g2SimplyConnectedBaseEquiv : g2SimplyConnectedBase.support ≃ Fin 2 where
  toFun i := ⟨i, by
    rcases g2SimplyConnectedBase_coe_eq i with hi | hi <;> omega⟩
  invFun i := ⟨g2SimpleRootIndex i, by fin_cases i <;> simp [g2SimpleRootIndex]⟩
  left_inv := by
    intro i
    apply Subtype.ext
    apply Fin.ext
    exact g2SimpleRootIndex_val (⟨i, by
      rcases g2SimplyConnectedBase_coe_eq i with hi | hi <;> omega⟩ : Fin 2)
  right_inv := by
    intro i
    apply Fin.ext
    exact g2SimpleRootIndex_val i

/-- The Cartan matrix of the pinned simply connected `G2` datum is the Bourbaki matrix
`!![2, -1; -3, 2]`. -/
theorem hasCartanType_g2SimplyConnectedRootDatum :
    HasCartanType g2SimplyConnectedRootDatum g2SimplyConnectedBase G2 := by
  rw [hasCartanType_iff]
  refine ⟨g2SimplyConnectedBaseEquiv, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  all_goals
    rw [← (FaithfulSMul.algebraMap_injective ℤ ℤ).eq_iff]
    simp only [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
    norm_num [RootPairing.pairing, RootPairing.root', g2SimplyConnectedRootDatum,
      g2SimplyConnectedBaseEquiv, g2Pairing, g2Root, g2Coroot, g2SimpleRootIndex,
      cartanMatrix_G2, CartanMatrix.G₂, dotProduct] <;> decide

end DynkinType

end TauCeti
