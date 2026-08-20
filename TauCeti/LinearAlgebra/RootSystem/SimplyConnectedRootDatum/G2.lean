/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.Positive
public import Mathlib.LinearAlgebra.RootSystem.Reduced

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

* `TauCeti.DynkinType.g2SimplyConnectedRootDatum` is the pinned twelve-root datum, with `g2Root`
  and `g2Coroot` its coordinate tables and `g2SimplyConnectedRootDatum_root`,
  `g2SimplyConnectedRootDatum_coroot`, `g2SimplyConnectedRootDatum_toLinearMap` and
  `g2SimplyConnectedRootDatum_pairing` the lemmas that expose them.
* Its `RootPairing.IsRootSystem` instance records that the roots and the coroots span their
  lattices; coroot spanning is the simply connected condition.
* Its `RootPairing.IsReduced` instance rules out nontrivial scalar multiples among the roots.
* `TauCeti.DynkinType.g2SimplyConnectedBase` is its Bourbaki-numbered base.
* `TauCeti.DynkinType.g2SimplyConnectedRootDatum_pairing_eq_cartanMatrix_G2` pins that numbering
  entrywise: on the two base indices the Cartan integers are the Bourbaki matrix `!![2, -1; -3, 2]`.
* `TauCeti.DynkinType.hasCartanType_g2SimplyConnectedRootDatum` identifies its Cartan type as `G2`.
* `TauCeti.DynkinType.ncard_posRoots_g2SimplyConnectedRootDatum` counts its positive roots: there
  are six of them, for any base.

## References

The coordinates and numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate IX. This is the `G2` branch of Layer 6 in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, following the target signatures in
`TauCetiRoadmap/RepresentationTheory/RootSystems/Suggested.lean`. The positive-root count is the
corresponding clause of the `G₂` worked example in the "Worked examples (acceptance criteria)"
section of that README; it agrees with the count in Bourbaki, Plate IX.
-/

namespace TauCeti

open _root_.Matrix Module Set Submodule

namespace DynkinType

/-- The roots of `G2` in the fundamental-weight basis, with simple roots first. -/
def g2Root : Fin 12 ↪ (Fin 2 → ℤ) where
  toFun := ![
    ![2, -1], ![-3, 2], ![-1, 1], ![1, 0], ![3, -1], ![0, 1],
    ![-2, 1], ![3, -2], ![1, -1], ![-1, 0], ![-3, 1], ![0, -1]]
  inj' := by decide

/-- The coroots of `G2` in the simple-coroot basis, ordered compatibly with `g2Root`. -/
def g2Coroot : Fin 12 ↪ (Fin 2 → ℤ) where
  toFun := ![
    ![1, 0], ![0, 1], ![1, 3], ![2, 3], ![1, 1], ![1, 2],
    ![-1, 0], ![0, -1], ![-1, -3], ![-2, -3], ![-1, -1], ![-1, -2]]
  inj' := by decide

/-- The matrix action on the roots needed to construct the special isogeny of `G₂`. -/
theorem g2Root_specialIsogenyAction (i : Fin 12) :
    !![0, 3; 1, 0] *ᵥ g2Root i =
      (![1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3] i : ℤ) •
        g2Root (![1, 0, 4, 5, 2, 3, 7, 6, 10, 11, 8, 9] i) := by
  revert i
  decide

/-- The transposed matrix action on the coroots needed to construct the special isogeny of `G₂`. -/
theorem g2Coroot_specialIsogenyAction (i : Fin 12) :
    (!![0, 3; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)ᵀ *ᵥ
        g2Coroot (![1, 0, 4, 5, 2, 3, 7, 6, 10, 11, 8, 9] i) =
      (![1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3] i : ℤ) • g2Coroot i := by
  revert i
  decide

/-- The simple roots of `G2` sit at the first two indices, where they are the rows of its
Bourbaki-numbered Cartan matrix. -/
@[simp] lemma g2Root_castAdd (i : Fin 2) :
    g2Root (Fin.castAdd 10 i) = CartanMatrix.G₂ᵀ i := by
  fin_cases i <;> decide

/-- The simple coroots of `G2` sit at the first two indices, where they are the standard basis of
the cocharacter lattice. -/
@[simp] lemma g2Coroot_castAdd (i : Fin 2) :
    g2Coroot (Fin.castAdd 10 i) = Pi.single i 1 := by
  fin_cases i <;> decide

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
private def g2ReflectionPerm (i : Fin 12) : Fin 12 ≃ Fin 12 :=
  Function.Involutive.toPerm (g2ReflectionIndex i)
    (fun j => by fin_cases i <;> fin_cases j <;> rfl)

@[simp] private lemma g2ReflectionPerm_apply (i j : Fin 12) :
    g2ReflectionPerm i j = g2ReflectionIndex i j := rfl

private lemma g2ReflectionIndex_root (i j : Fin 12) :
    g2Root j - (g2Root j ⬝ᵥ g2Coroot i) • g2Root i =
      g2Root (g2ReflectionIndex i j) := by
  decide +revert

private lemma g2ReflectionIndex_coroot (i j : Fin 12) :
    g2Coroot j - (g2Root i ⬝ᵥ g2Coroot j) • g2Coroot i =
      g2Coroot (g2ReflectionIndex i j) := by
  decide +revert

/-- The pinned simply connected root datum of type `G2`.

Both lattices use `Fin 2 -> Z`: fundamental weights on the root side and simple coroots on the
coroot side. Root indices `0` and `1` are the short and long simple roots respectively, as pinned
by `g2SimplyConnectedRootDatum_pairing_eq_cartanMatrix_G2`. -/
def g2SimplyConnectedRootDatum : RootDatum (Fin 12) (Fin 2 → ℤ) (Fin 2 → ℤ) where
  toLinearMap := (dotProductEquiv ℤ (Fin 2)).toLinearMap
  root := g2Root
  coroot := g2Coroot
  root_coroot_two := by
    intro i
    fin_cases i <;> norm_num [g2Root, g2Coroot, dotProduct]
  reflectionPerm := g2ReflectionPerm
  reflectionPerm_root := by
    intro i j
    simpa [dotProductEquiv_apply_apply, g2ReflectionPerm_apply] using
      g2ReflectionIndex_root i j
  reflectionPerm_coroot := by
    intro i j
    simpa [dotProductEquiv_apply_apply, g2ReflectionPerm_apply] using
      g2ReflectionIndex_coroot i j

/-- The roots of the pinned `G2` datum are the coordinate table `g2Root`. -/
@[simp] lemma g2SimplyConnectedRootDatum_root : g2SimplyConnectedRootDatum.root = g2Root := (rfl)

/-- The coroots of the pinned `G2` datum are the coordinate table `g2Coroot`. -/
@[simp] lemma g2SimplyConnectedRootDatum_coroot :
    g2SimplyConnectedRootDatum.coroot = g2Coroot := (rfl)

/-- The perfect pairing of the pinned `G2` datum is the dot product of coordinate vectors, the
fundamental-weight and simple-coroot bases being dual to one another. -/
@[simp] lemma g2SimplyConnectedRootDatum_toLinearMap (x y : Fin 2 → ℤ) :
    g2SimplyConnectedRootDatum.toLinearMap x y = x ⬝ᵥ y := (rfl)

/-- The Cartan integer of the pinned `G2` datum at a pair of root indices is the dot product of the
tabulated root and coroot coordinates. -/
@[simp] lemma g2SimplyConnectedRootDatum_pairing (i j : Fin 12) :
    g2SimplyConnectedRootDatum.pairing i j = g2Root i ⬝ᵥ g2Coroot j := (rfl)

/-- The pinned simply connected root datum of type `G₂` is reduced. -/
instance instIsReducedG2SimplyConnectedRootDatum : g2SimplyConnectedRootDatum.IsReduced := by
  constructor
  intro i j hdependent
  have hproduct :
      g2SimplyConnectedRootDatum.pairing i j * g2SimplyConnectedRootDatum.pairing j i = 4 := by
    simpa only [RootPairing.coxeterWeight] using
      (g2SimplyConnectedRootDatum.coxeterWeight_eq_four_iff_not_linearIndependent.mpr hdependent)
  have htable : ∀ i j : Fin 12,
      (g2Root i ⬝ᵥ g2Coroot j) * (g2Root j ⬝ᵥ g2Coroot i) = 4 →
        g2Root i = g2Root j ∨ g2Root i = -g2Root j := by
    decide
  have hproduct' :
      (g2Root i ⬝ᵥ g2Coroot j) * (g2Root j ⬝ᵥ g2Coroot i) = 4 := by
    simpa only [g2SimplyConnectedRootDatum_pairing] using hproduct
  simpa only [g2SimplyConnectedRootDatum_root] using htable i j hproduct'

private lemma span_g2Root_eq_top : span ℤ (range g2Root) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin 2)).span_eq]
  apply span_mono
  rintro _ ⟨i, rfl⟩
  simp only [Pi.basisFun_apply]
  fin_cases i
  · exact ⟨3, by decide⟩
  · exact ⟨5, by decide⟩

private lemma span_g2Coroot_eq_top : span ℤ (range g2Coroot) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin 2)).span_eq]
  apply span_mono
  rintro _ ⟨i, rfl⟩
  simp only [Pi.basisFun_apply]
  fin_cases i
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩

/-- The pinned `G2` datum is a root system: its roots and coroots span their two lattices. Coroot
spanning is the simply connected lattice condition required by the pinned Chevalley--Demazure
construction. -/
instance : g2SimplyConnectedRootDatum.IsRootSystem where
  span_root_eq_top := span_g2Root_eq_top
  span_coroot_eq_top := span_g2Coroot_eq_top

/-- A family indexed by `Fin 12` whose members are, up to sign, prescribed `ℕ`-combinations of its
first two members satisfies the base condition of `RootPairing.Base` at the support `{0, 1}`. The
table `t` gives, for each index, the sign and the two coefficients. -/
private lemma mem_or_neg_mem_of_table (f : Fin 12 → (Fin 2 → ℤ)) (t : Fin 12 → Bool × ℕ × ℕ)
    (ht : ∀ i, (t i).2.1 • f 0 + (t i).2.2 • f 1 = cond (t i).1 (f i) (-f i)) (i : Fin 12) :
    f i ∈ AddSubmonoid.closure (f '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12))) ∨
      -f i ∈ AddSubmonoid.closure (f '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12))) := by
  set C := AddSubmonoid.closure (f '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12)))
  have h0 : f 0 ∈ C := AddSubmonoid.subset_closure ⟨0, by simp, rfl⟩
  have h1 : f 1 ∈ C := AddSubmonoid.subset_closure ⟨1, by simp, rfl⟩
  have comb : (t i).2.1 • f 0 + (t i).2.2 • f 1 ∈ C :=
    C.add_mem (C.nsmul_mem h0 _) (C.nsmul_mem h1 _)
  rw [ht i] at comb
  cases hs : (t i).1 <;> rw [hs] at comb
  · exact Or.inr comb
  · exact Or.inl comb

/-- The `G2` roots are, up to sign, `ℕ`-combinations of the two simple roots. -/
private lemma g2Root_mem_or_neg_mem (i : Fin 12) :
    g2Root i ∈ AddSubmonoid.closure (g2Root '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12))) ∨
      -g2Root i ∈
        AddSubmonoid.closure (g2Root '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12))) :=
  mem_or_neg_mem_of_table _
    ![(true, 1, 0), (true, 0, 1), (true, 1, 1), (true, 2, 1), (true, 3, 1), (true, 3, 2),
      (false, 1, 0), (false, 0, 1), (false, 1, 1), (false, 2, 1), (false, 3, 1), (false, 3, 2)]
    (fun j => by fin_cases j <;> ext k <;> fin_cases k <;> norm_num [g2Root]) i

/-- The `G2` coroots are, up to sign, `ℕ`-combinations of the two simple coroots. -/
private lemma g2Coroot_mem_or_neg_mem (i : Fin 12) :
    g2Coroot i ∈
        AddSubmonoid.closure (g2Coroot '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12))) ∨
      -g2Coroot i ∈
        AddSubmonoid.closure (g2Coroot '' (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12))) :=
  mem_or_neg_mem_of_table _
    ![(true, 1, 0), (true, 0, 1), (true, 1, 3), (true, 2, 3), (true, 1, 1), (true, 1, 2),
      (false, 1, 0), (false, 0, 1), (false, 1, 3), (false, 2, 3), (false, 1, 1), (false, 1, 2)]
    (fun j => by fin_cases j <;> ext k <;> fin_cases k <;> norm_num [g2Coroot]) i

/-- The Bourbaki-numbered base of the pinned simply connected `G2` root datum. Its support is the
first two root indices, short root first and long root second; see
`g2SimplyConnectedRootDatum_pairing_eq_cartanMatrix_G2`. -/
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
    simpa only [g2SimplyConnectedRootDatum_root] using hli
  linearIndepOn_coroot := by
    have hli : LinearIndepOn ℤ g2Coroot
        (↑({0, 1} : Finset (Fin 12)) : Set (Fin 12)) := by
      rw [Finset.coe_insert, Finset.coe_singleton]
      refine (LinearIndepOn.pair_iff g2Coroot (by decide : (0 : Fin 12) ≠ 1)).2 ?_
      intro c d h
      exact ⟨by simpa [g2Coroot] using congrFun h 0,
        by simpa [g2Coroot] using congrFun h 1⟩
    simpa only [g2SimplyConnectedRootDatum_coroot] using hli
  root_mem_or_neg_mem := g2Root_mem_or_neg_mem
  coroot_mem_or_neg_mem := g2Coroot_mem_or_neg_mem

@[simp] lemma g2SimplyConnectedBase_support : g2SimplyConnectedBase.support = {0, 1} := (rfl)

private lemma g2SimplyConnectedBase_coe_eq_zero_or_eq_one (i : g2SimplyConnectedBase.support) :
    (i : Fin 12) = 0 ∨ (i : Fin 12) = 1 := by
  simpa only [g2SimplyConnectedBase_support, Finset.mem_insert, Finset.mem_singleton] using
    i.property

/-- The Cartan integers of the pinned `G2` datum at the two base indices form the Bourbaki matrix
`!![2, -1; -3, 2]` in the pinned index order: index `0` is the short simple root and index `1` the
long one. This is what pins the numbering; `hasCartanType_g2SimplyConnectedRootDatum` cannot,
since the relabelling in `HasCartanType` is existential and at rank two it may transpose the two
off-diagonal entries. -/
theorem g2SimplyConnectedRootDatum_pairing_eq_cartanMatrix_G2 (i j : Fin 2) :
    g2SimplyConnectedRootDatum.pairing (Fin.castLE (by omega) i) (Fin.castLE (by omega) j) =
      !![2, -1; -3, 2] i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The ordered support of the pinned base is identified with the two Bourbaki nodes. -/
private def g2SimplyConnectedBaseEquiv : g2SimplyConnectedBase.support ≃ Fin 2 where
  toFun i := ⟨i, by
    rcases g2SimplyConnectedBase_coe_eq_zero_or_eq_one i with hi | hi <;> omega⟩
  invFun i := ⟨Fin.castLE (by omega) i, by fin_cases i <;> decide⟩
  left_inv := by
    intro i
    apply Subtype.ext
    apply Fin.ext
    simp
  right_inv := by
    intro i
    apply Fin.ext
    simp

/-- The pinned simply connected `G2` datum has Cartan type `G2`. The relabelling supplied by
`HasCartanType` is existential, so the Bourbaki node numbering itself is pinned separately by
`g2SimplyConnectedRootDatum_pairing_eq_cartanMatrix_G2`. -/
theorem hasCartanType_g2SimplyConnectedRootDatum :
    HasCartanType g2SimplyConnectedRootDatum g2SimplyConnectedBase G2 := by
  rw [hasCartanType_iff]
  refine ⟨g2SimplyConnectedBaseEquiv, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  all_goals
    rw [← (FaithfulSMul.algebraMap_injective ℤ ℤ).eq_iff]
    simp only [RootPairing.Base.algebraMap_cartanMatrixIn_apply,
      g2SimplyConnectedRootDatum_pairing, cartanMatrix_G2]
    decide

/-- **The pinned root datum of type `G₂` has six positive roots.** Exactly half of its twelve roots
are positive, for any base. -/
@[simp]
theorem ncard_posRoots_g2SimplyConnectedRootDatum (b : g2SimplyConnectedRootDatum.Base) :
    (posRoots g2SimplyConnectedRootDatum b).ncard = 6 := by
  rw [ncard_posRoots_eq_natCard_div_two]
  norm_num

end DynkinType

end TauCeti
