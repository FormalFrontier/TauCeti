/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `RootPairing.isReduced_of_pairing_comm` supplies the local reducedness witness used by the
-- base-induction proof that the lattice involution preserves the set of roots.
import TauCeti.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.Basic

/-!
# The graph automorphism of the pinned type `E₆` root datum

The Dynkin diagram of type `E₆` has an involution exchanging Bourbaki nodes `1 ↔ 6` and
`3 ↔ 5`.
The character and cocharacter lattices of `TauCeti.DynkinType.e6SimplyConnectedRootDatum` are
written in bases indexed by those nodes, so the involution acts on each lattice by reindexing
coordinates with `TauCeti.graphPermE6`.

This file packages those lattice maps and the induced permutation of all seventy-two roots as an
automorphism of the pinned root datum. Its restriction to the pinned simple roots is exactly
`TauCeti.graphPermE6`, the numbered permutation used for the graph-twisted family `²E₆`.

## Main declarations

* `TauCeti.DynkinType.e6GraphIndexEquiv`: the induced permutation of all root indices.
* `TauCeti.DynkinType.e6GraphAut`: the graph automorphism of the pinned simply connected datum.
* `TauCeti.DynkinType.e6GraphAut_sq`: the automorphism has square one.
* `TauCeti.DynkinType.image_e6GraphAut_indexEquiv_e6SimplyConnectedBase_support`: the pinned base
  support is preserved.

## References

The coordinates and node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate V. The graph automorphism and its role in the twisted family `²E₆` follow R. W. Carter,
*Simple Groups of Lie Type*, §12.2.

This supplies the type-`E₆` root-datum input to the pinned-isomorphism target in Layer 9 of the
ReductiveGroups roadmap. The pinned isomorphism theorem will lift it to the group-scheme
automorphism used in the graph-twisted Steinberg endomorphism.
-/

public section

namespace TauCeti

open Function Set

namespace DynkinType

/-! ## The lattice and root-index permutations -/

private lemma graphPermE6_symm : graphPermE6.symm = graphPermE6 := by
  exact (mul_eq_one_iff_eq_inv.mp (by simpa only [pow_two] using graphPermE6_sq)).symm

private lemma graphPermE6_apply_apply (i : Fin 6) : graphPermE6 (graphPermE6 i) = i := by
  have h := congrArg (fun e : Equiv.Perm (Fin 6) => e i) graphPermE6_sq
  simpa only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h

/-- Reindex fundamental-weight or simple-coroot coordinates by the `E₆` graph permutation. -/
private def e6GraphLatticeEquiv : (Fin 6 → ℤ) ≃ₗ[ℤ] Fin 6 → ℤ :=
  LinearEquiv.piCongrLeft' ℤ (fun _ : Fin 6 => ℤ) graphPermE6

private lemma e6GraphLatticeEquiv_apply (x : Fin 6 → ℤ) (i : Fin 6) :
    e6GraphLatticeEquiv x i = x (graphPermE6 i) := by
  rw [e6GraphLatticeEquiv, LinearEquiv.piCongrLeft'_apply, graphPermE6_symm]

private lemma e6GraphLatticeEquiv_involutive : Involutive e6GraphLatticeEquiv := by
  intro x
  funext i
  rw [e6GraphLatticeEquiv_apply, e6GraphLatticeEquiv_apply]
  rw [graphPermE6_apply_apply]

private lemma e6GraphLatticeEquiv_dotProduct (x y : Fin 6 → ℤ) :
    e6GraphLatticeEquiv x ⬝ᵥ e6GraphLatticeEquiv y = x ⬝ᵥ y := by
  simp only [dotProduct, e6GraphLatticeEquiv_apply]
  apply Fintype.sum_equiv graphPermE6
  intro i
  rfl

private lemma e6GraphLatticeEquiv_dotProduct_left (x y : Fin 6 → ℤ) :
    e6GraphLatticeEquiv x ⬝ᵥ y = x ⬝ᵥ e6GraphLatticeEquiv y := by
  have h := e6GraphLatticeEquiv_dotProduct x (e6GraphLatticeEquiv y)
  rw [e6GraphLatticeEquiv_involutive] at h
  exact h

private lemma e6GraphLatticeEquiv_simpleCoroot (i : Fin 6) :
    e6GraphLatticeEquiv (e6SimplyConnectedRootDatum.coroot (e6SimpleIndex i)) =
      e6SimplyConnectedRootDatum.coroot (e6SimpleIndex (graphPermE6 i)) := by
  simp only [e6SimplyConnectedRootDatum_coroot, coroot_e6SimpleIndex]
  funext j
  rw [e6GraphLatticeEquiv_apply]
  simp only [Pi.single_apply]
  by_cases hji : graphPermE6 j = i
  · have hij : j = graphPermE6 i := by
      rw [← graphPermE6_apply_apply j, hji]
    simp only [hij, graphPermE6_apply_apply, ↓reduceIte]
  · have hij : j ≠ graphPermE6 i := by
      intro hij
      apply hji
      rw [hij, graphPermE6_apply_apply]
    simp only [hji, hij, ↓reduceIte]

private lemma e6GraphLatticeEquiv_simpleRoot (i : Fin 6) :
    e6GraphLatticeEquiv (e6SimplyConnectedRootDatum.root (e6SimpleIndex i)) =
      e6SimplyConnectedRootDatum.root (e6SimpleIndex (graphPermE6 i)) := by
  simp only [e6SimplyConnectedRootDatum_root, root_e6SimpleIndex]
  funext j
  rw [e6GraphLatticeEquiv_apply]
  have h := cartanMatrix_E6_graphPermE6 i (graphPermE6 j)
  simpa only [DynkinType.cartanMatrix_E6, graphPermE6_apply_apply] using h.symm

private lemma e6GraphLatticeEquiv_mulVec (x : Fin 6 → ℤ) :
    e6GraphLatticeEquiv ((CartanMatrix.E 6).mulVec x) =
      (CartanMatrix.E 6).mulVec (e6GraphLatticeEquiv x) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, e6GraphLatticeEquiv_apply]
  apply Fintype.sum_equiv graphPermE6
  intro i
  rw [graphPermE6_apply_apply]
  have h := cartanMatrix_E6_graphPermE6 j (graphPermE6 i)
  simpa only [DynkinType.cartanMatrix_E6, graphPermE6_apply_apply] using
    congrArg (fun z => z * x i) h

private lemma e6GraphLatticeEquiv_root_mem_range (i : Fin 72) :
    e6GraphLatticeEquiv (e6SimplyConnectedRootDatum.root i) ∈
      range e6SimplyConnectedRootDatum.root := by
  let _ : e6SimplyConnectedRootDatum.IsReduced :=
    RootPairing.isReduced_of_pairing_comm _ fun j k => by
      simpa only [e6SimplyConnectedRootDatum_pairing] using
        e6Root_dotProduct_e6Coroot_comm j k
  apply e6SimplyConnectedBase.induction_reflect i
  · intro j hj
    rw [e6SimplyConnectedRootDatum.root_reflectionPerm,
      e6SimplyConnectedRootDatum.reflection_apply_self, map_neg,
      e6SimplyConnectedRootDatum.neg_mem_range_root_iff]
    exact hj
  · intro j hj
    rw [mem_e6SimplyConnectedBase_support] at hj
    let a : Fin 6 := ⟨j, hj⟩
    have hja : j = e6SimpleIndex a := by
      apply Fin.ext
      rw [e6SimpleIndex_val]
    refine ⟨e6SimpleIndex (graphPermE6 a), ?_⟩
    rw [hja, e6GraphLatticeEquiv_simpleRoot]
  · intro j k hj hk
    obtain ⟨l, hl⟩ := hj
    rw [mem_e6SimplyConnectedBase_support] at hk
    let a : Fin 6 := ⟨k, hk⟩
    have hka : k = e6SimpleIndex a := by
      apply Fin.ext
      rw [e6SimpleIndex_val]
    have hpair : e6SimplyConnectedRootDatum.pairing l (e6SimpleIndex (graphPermE6 a)) =
        e6SimplyConnectedRootDatum.pairing j k := by
      -- Expose `pairing` as the perfect bilinear map so the two lattice-equivariance facts apply.
      change e6SimplyConnectedRootDatum.toLinearMap (e6SimplyConnectedRootDatum.root l)
          (e6SimplyConnectedRootDatum.coroot (e6SimpleIndex (graphPermE6 a))) =
        e6SimplyConnectedRootDatum.toLinearMap (e6SimplyConnectedRootDatum.root j)
          (e6SimplyConnectedRootDatum.coroot k)
      rw [hl, ← e6GraphLatticeEquiv_simpleCoroot, hka,
        e6SimplyConnectedRootDatum_toLinearMap,
        e6SimplyConnectedRootDatum_toLinearMap, e6GraphLatticeEquiv_dotProduct]
    refine ⟨e6SimplyConnectedRootDatum.reflectionPerm
      (e6SimpleIndex (graphPermE6 a)) l, ?_⟩
    rw [e6SimplyConnectedRootDatum.root_reflectionPerm,
      e6SimplyConnectedRootDatum.root_reflectionPerm,
      e6SimplyConnectedRootDatum.reflection_apply,
      e6SimplyConnectedRootDatum.reflection_apply, map_sub, map_smul,
      hka, e6GraphLatticeEquiv_simpleRoot]
    rw [← hl, e6SimplyConnectedRootDatum.root_coroot'_eq_pairing,
      e6SimplyConnectedRootDatum.root_coroot'_eq_pairing, hpair, ← hka]

/-- The root index selected by the image of a root under the lattice involution. -/
private noncomputable def e6GraphIndex (i : Fin 72) : Fin 72 :=
  e6SimplyConnectedRootDatum.root.invOfMemRange
    ⟨e6GraphLatticeEquiv (e6SimplyConnectedRootDatum.root i),
      e6GraphLatticeEquiv_root_mem_range i⟩

private lemma root_e6GraphIndex (i : Fin 72) :
    e6SimplyConnectedRootDatum.root (e6GraphIndex i) =
      e6GraphLatticeEquiv (e6SimplyConnectedRootDatum.root i) :=
  e6SimplyConnectedRootDatum.root.left_inv_of_invOfMemRange
    ⟨e6GraphLatticeEquiv (e6SimplyConnectedRootDatum.root i),
      e6GraphLatticeEquiv_root_mem_range i⟩

private lemma e6GraphIndex_involutive : Involutive e6GraphIndex := by
  intro i
  apply e6SimplyConnectedRootDatum.root.injective
  rw [root_e6GraphIndex, root_e6GraphIndex, e6GraphLatticeEquiv_involutive]

/-- The permutation of all roots induced by the graph symmetry, expressed on the native root
indices of the pinned type-`E₆` datum. -/
noncomputable def e6GraphIndexEquiv : Equiv.Perm (Fin 72) :=
  e6GraphIndex_involutive.toPerm

private lemma e6GraphLatticeEquiv_root (i : Fin 72) :
    e6GraphLatticeEquiv (e6SimplyConnectedRootDatum.root i) =
      e6SimplyConnectedRootDatum.root (e6GraphIndexEquiv i) := by
  exact (root_e6GraphIndex i).symm

/-- Applying the type-`E₆` root permutation twice is the identity. -/
@[simp] theorem e6GraphIndexEquiv_apply_apply (i : Fin 72) :
    e6GraphIndexEquiv (e6GraphIndexEquiv i) = i := by
  apply e6SimplyConnectedRootDatum.root.injective
  rw [← e6GraphLatticeEquiv_root, ← e6GraphLatticeEquiv_root,
    e6GraphLatticeEquiv_involutive]

private lemma e6GraphLatticeEquiv_coroot (i : Fin 72) :
    e6GraphLatticeEquiv (e6SimplyConnectedRootDatum.coroot i) =
      e6SimplyConnectedRootDatum.coroot (e6GraphIndexEquiv i) := by
  simp only [e6SimplyConnectedRootDatum_coroot]
  apply Matrix.mulVec_injective_of_det_ne_zero (by rw [CartanMatrix.E₆_det]; norm_num)
  rw [← e6GraphLatticeEquiv_mulVec, ← e6Root_eq_mulVec, ← e6Root_eq_mulVec]
  simpa only [← e6SimplyConnectedRootDatum_root] using e6GraphLatticeEquiv_root i

/-! ## The root-datum automorphism -/

/-- The diagram symmetry as an automorphism of the pinned simply connected root datum of type
`E₆`. Both lattice maps exchange the node coordinates according to `TauCeti.graphPermE6`, and the
root-index map is the induced permutation of the seventy-two roots. -/
noncomputable def e6GraphAut : _root_.RootPairing.Aut e6SimplyConnectedRootDatum where
  weightMap := e6GraphLatticeEquiv.toLinearMap
  coweightMap := e6GraphLatticeEquiv.toLinearMap
  indexEquiv := e6GraphIndexEquiv
  weight_coweight_transpose := by
    ext y x
    -- The structure field equates compositions of linear maps. After extensionality, unfold
    -- those wrappers to expose the concrete perfect pairing and the two lattice arguments.
    change e6SimplyConnectedRootDatum.toLinearMap
        (e6GraphLatticeEquiv (Pi.single x 1)) (Pi.single y 1) =
      e6SimplyConnectedRootDatum.toLinearMap (Pi.single x 1)
        (e6GraphLatticeEquiv (Pi.single y 1))
    rw [e6SimplyConnectedRootDatum_toLinearMap, e6SimplyConnectedRootDatum_toLinearMap]
    exact e6GraphLatticeEquiv_dotProduct_left _ _
  root_weightMap := by
    funext i
    exact e6GraphLatticeEquiv_root i
  coroot_coweightMap := by
    funext i
    rw [e6GraphIndexEquiv, Function.Involutive.toPerm_symm e6GraphIndex_involutive]
    exact e6GraphLatticeEquiv_coroot i
  bijective_weightMap := e6GraphLatticeEquiv.bijective
  bijective_coweightMap := e6GraphLatticeEquiv.bijective

/-- The graph automorphism carries every root to the root selected by its public root-index
permutation. -/
@[simp] theorem e6GraphAut_weightMap_root (i : Fin 72) :
    e6GraphAut.weightMap (e6Root i) = e6Root (e6GraphIndexEquiv i) := by
  -- Expose the linear equivalence packaged as the automorphism's weight linear map.
  change e6GraphLatticeEquiv (e6Root i) = e6Root (e6GraphIndexEquiv i)
  simpa only [e6SimplyConnectedRootDatum_root] using e6GraphLatticeEquiv_root i

/-- The graph automorphism carries every coroot to the coroot selected by its public root-index
permutation. -/
@[simp] theorem e6GraphAut_coweightMap_coroot (i : Fin 72) :
    e6GraphAut.coweightMap (e6Coroot i) = e6Coroot (e6GraphIndexEquiv i) := by
  -- Expose the linear equivalence packaged as the automorphism's coweight linear map.
  change e6GraphLatticeEquiv (e6Coroot i) = e6Coroot (e6GraphIndexEquiv i)
  simpa only [e6SimplyConnectedRootDatum_coroot] using e6GraphLatticeEquiv_coroot i

/-- The character-lattice action of the type-`E₆` graph automorphism permutes the node
coordinates. -/
@[simp] theorem e6GraphAut_weightMap_apply (x : Fin 6 → ℤ) (i : Fin 6) :
    e6GraphAut.weightMap x i = x (graphPermE6 i) :=
  e6GraphLatticeEquiv_apply x i

/-- The cocharacter-lattice action of the type-`E₆` graph automorphism permutes the node
coordinates. -/
@[simp] theorem e6GraphAut_coweightMap_apply (x : Fin 6 → ℤ) (i : Fin 6) :
    e6GraphAut.coweightMap x i = x (graphPermE6 i) :=
  e6GraphLatticeEquiv_apply x i

/-- The root-index action of the type-`E₆` graph automorphism restricts to the numbered diagram
involution on the pinned simple roots. -/
@[simp] theorem e6GraphAut_indexEquiv_e6SimpleIndex (i : Fin 6) :
    e6GraphAut.indexEquiv (e6SimpleIndex i) = e6SimpleIndex (graphPermE6 i) := by
  -- Unfold the automorphism field to the separately named induced root permutation before using
  -- the characteristic equation proved from injectivity of the root embedding.
  change e6GraphIndexEquiv (e6SimpleIndex i) = e6SimpleIndex (graphPermE6 i)
  apply e6SimplyConnectedRootDatum.root.injective
  rw [← e6GraphLatticeEquiv_root, e6GraphLatticeEquiv_simpleRoot]

/-- Applying the type-`E₆` graph automorphism twice is the identity. -/
@[simp] theorem e6GraphAut_sq : e6GraphAut ^ 2 = 1 := by
  apply _root_.RootPairing.Equiv.ext
  · apply LinearMap.ext
    exact e6GraphLatticeEquiv_involutive
  · apply LinearMap.ext
    exact e6GraphLatticeEquiv_involutive
  · apply Equiv.ext
    exact e6GraphIndexEquiv_apply_apply

/-- The type-`E₆` graph automorphism is nontrivial: it exchanges the first and sixth simple
roots. -/
theorem e6GraphAut_ne_one : e6GraphAut ≠ 1 := by
  intro h
  have hsimple : e6SimpleIndex 5 = e6SimpleIndex 0 := by
    calc
      e6SimpleIndex 5 = e6GraphAut.indexEquiv (e6SimpleIndex 0) := by
        rw [e6GraphAut_indexEquiv_e6SimpleIndex, graphPermE6_apply_zero]
      _ = (1 : _root_.RootPairing.Aut e6SimplyConnectedRootDatum).indexEquiv
          (e6SimpleIndex 0) := congrArg (fun e => e.indexEquiv (e6SimpleIndex 0)) h
      _ = e6SimpleIndex 0 := rfl
  have := congrArg Fin.val hsimple
  simp only [e6SimpleIndex_val] at this
  omega

/-- The graph symmetry preserves the support of the pinned type-`E₆` base. Together with
`RootPairing.Base.support_map_eq`, this computes the support of the transported base. -/
@[simp] theorem image_e6GraphAut_indexEquiv_e6SimplyConnectedBase_support :
    e6SimplyConnectedBase.support.image e6GraphAut.indexEquiv =
      e6SimplyConnectedBase.support := by
  ext i
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [mem_e6SimplyConnectedBase_support] at hj ⊢
    let a : Fin 6 := ⟨j, hj⟩
    have hja : j = e6SimpleIndex a := by
      apply Fin.ext
      rw [e6SimpleIndex_val]
    rw [hja, e6GraphAut_indexEquiv_e6SimpleIndex, e6SimpleIndex_val]
    exact (graphPermE6 a).isLt
  · intro hi
    rw [mem_e6SimplyConnectedBase_support] at hi
    let a : Fin 6 := ⟨i, hi⟩
    refine ⟨e6SimpleIndex (graphPermE6 a), ?_, ?_⟩
    · rw [mem_e6SimplyConnectedBase_support, e6SimpleIndex_val]
      exact (graphPermE6 a).isLt
    · rw [e6GraphAut_indexEquiv_e6SimpleIndex]
      rw [graphPermE6_apply_apply]
      apply Fin.ext
      rw [e6SimpleIndex_val]

end DynkinType

end TauCeti
