/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.Basic

/-!
# The graph automorphism of the pinned type `Dₙ` root datum

For `4 ≤ n`, the Dynkin diagram of type `Dₙ` has an involution exchanging its two fork nodes.
On the classical realization by roots `±e_a ± e_b`, this involution changes the sign of the last
coordinate. On the character and cocharacter lattices of the pinned simply connected datum, both
written in bases indexed by the simple nodes, it exchanges the final two coordinates.

This file packages those maps as an automorphism of
`TauCeti.DynkinType.typeDSimplyConnectedRootDatum`. The induced permutation of all root indices is
obtained by conjugating the last-coordinate sign change through the existing enumeration
`TauCeti.DynkinType.typeDRootEquiv`. Its restriction to the pinned simple roots is the numbered
permutation `TauCeti.graphPermD` used by the graph-twisted finite groups of Lie type.

## Main declarations

* `TauCeti.DynkinType.typeDGraphIndexEquiv`: the permutation of every root index induced by the
  fork symmetry.
* `TauCeti.DynkinType.typeDGraphAut`: the resulting automorphism of the pinned simply connected
  root datum.
* `TauCeti.DynkinType.typeDGraphAut_sq`: the automorphism has square one.
* `TauCeti.DynkinType.image_typeDGraphAut_indexEquiv_typeDSimplyConnectedBase_support`: the
  pinned base support is preserved.

## References

The coordinates and node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate IV. The graph automorphism and its role in the twisted family `²Dₙ` follow R. W. Carter,
*Simple Groups of Lie Type*, §12.2.

This supplies the type-`D` root-datum input to the pinned-isomorphism target in Layer 9 of the
ReductiveGroups roadmap. The pinned isomorphism theorem will lift it to the group-scheme
automorphism used in the graph-twisted Steinberg endomorphism.
-/

public section

namespace TauCeti

open Function Submodule

namespace DynkinType

variable {n : ℕ}

/-! ## The classical sign change -/

/-- Change the sign of the final coordinate in the classical type-`Dₙ` realization. -/
private def typeDLastSign (n : ℕ) (x : Fin n → ℤ) : Fin n → ℤ :=
  fun i => if (i : ℕ) = n - 1 then -x i else x i

private lemma typeDLastSign_apply (x : Fin n → ℤ) (i : Fin n) :
    typeDLastSign n x i = if (i : ℕ) = n - 1 then -x i else x i :=
  rfl

private lemma typeDLastSign_involutive : Involutive (typeDLastSign n) := by
  intro x
  funext i
  by_cases hi : (i : ℕ) = n - 1 <;> simp [typeDLastSign, hi]

private lemma typeDLastSign_dotProduct (x y : Fin n → ℤ) :
    typeDLastSign n x ⬝ᵥ typeDLastSign n y = x ⬝ᵥ y := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [typeDLastSign_apply]
  split_ifs <;> ring

/-- The involution of the classical type-`Dₙ` roots induced by changing the sign of the last
coordinate. -/
private def typeDClassicalGraphEquiv (n : ℕ) : TypeDRoot n ≃ TypeDRoot n where
  toFun x := ⟨typeDLastSign n x, by rw [typeDLastSign_dotProduct, x.property]⟩
  invFun x := ⟨typeDLastSign n x, by rw [typeDLastSign_dotProduct, x.property]⟩
  left_inv x := Subtype.ext (typeDLastSign_involutive x.1)
  right_inv x := Subtype.ext (typeDLastSign_involutive x.1)

private lemma typeDClassicalGraphEquiv_val (x : TypeDRoot n) :
    (typeDClassicalGraphEquiv n x).1 = typeDLastSign n x :=
  rfl

private lemma typeDClassicalGraphEquiv_involutive :
    Involutive (typeDClassicalGraphEquiv n : TypeDRoot n → TypeDRoot n) := by
  intro x
  exact (typeDClassicalGraphEquiv n).left_inv x

/-! ## Root and lattice permutations -/

/-- The permutation of all roots induced by the fork symmetry, expressed on the native root
indices of the pinned type-`Dₙ` datum. -/
noncomputable def typeDGraphIndexEquiv (n : ℕ) (hn : 4 ≤ n) :
    Equiv.Perm (Fin (2 * n * (n - 1))) :=
  (typeDRootEquiv n hn).trans ((typeDClassicalGraphEquiv n).trans (typeDRootEquiv n hn).symm)

/-- Applying the type-`D` root permutation and then enumerating gives the last-coordinate sign
change of the original classical root. -/
private theorem typeDRootEquiv_typeDGraphIndexEquiv (hn : 4 ≤ n)
    (i : Fin (2 * n * (n - 1))) :
    typeDRootEquiv n hn (typeDGraphIndexEquiv n hn i) =
      typeDClassicalGraphEquiv n (typeDRootEquiv n hn i) := by
  simp [typeDGraphIndexEquiv]

/-- On every classical type-`D` root, the root-index permutation changes exactly the sign of the
final coordinate. -/
theorem typeDRootEquiv_typeDGraphIndexEquiv_apply (hn : 4 ≤ n)
    (i : Fin (2 * n * (n - 1))) (j : Fin n) :
    (typeDRootEquiv n hn (typeDGraphIndexEquiv n hn i)).1 j =
      if (j : ℕ) = n - 1 then -(typeDRootEquiv n hn i).1 j
      else (typeDRootEquiv n hn i).1 j := by
  rw [typeDRootEquiv_typeDGraphIndexEquiv, typeDClassicalGraphEquiv_val]
  exact typeDLastSign_apply _ _

/-- The type-`D` root permutation is an involution. -/
@[simp] theorem typeDGraphIndexEquiv_apply_apply (hn : 4 ≤ n)
    (i : Fin (2 * n * (n - 1))) :
    typeDGraphIndexEquiv n hn (typeDGraphIndexEquiv n hn i) = i := by
  apply (typeDRootEquiv n hn).injective
  rw [typeDRootEquiv_typeDGraphIndexEquiv, typeDRootEquiv_typeDGraphIndexEquiv,
    typeDClassicalGraphEquiv_involutive]

private lemma typeDLastSign_typeDSimpleRoot (hn : 4 ≤ n) (i : Fin n) :
    typeDLastSign n (typeDSimpleRoot n hn i) =
      typeDSimpleRoot n hn (graphPermD n (by omega) i) := by
  ext j
  by_cases hi₁ : (i : ℕ) = n - 1
  · have hieq : i = (⟨n - 1, by omega⟩ : Fin n) := Fin.ext hi₁
    rw [hieq]
    have hi : ¬((⟨n - 1, by omega⟩ : Fin n) : ℕ) + 1 < n := by omega
    rw [typeDSimpleRoot_of_not_add_one_lt hn hi, graphPermD_apply_right]
    have hperm : (⟨n - 2, by omega⟩ : Fin n).val + 1 < n := by
      -- Expose the value hidden by the proof-carrying `Fin` literal.
      change n - 2 + 1 < n
      omega
    rw [typeDSimpleRoot_of_add_one_lt hn hperm]
    simp [typeDLastSign, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  · by_cases hi₂ : (i : ℕ) = n - 2
    · have hieq : i = (⟨n - 2, by omega⟩ : Fin n) := Fin.ext hi₂
      rw [hieq]
      have hi : ((⟨n - 2, by omega⟩ : Fin n) : ℕ) + 1 < n := by omega
      rw [typeDSimpleRoot_of_add_one_lt hn hi, graphPermD_apply_left]
      have hperm : ¬(⟨n - 1, by omega⟩ : Fin n).val + 1 < n := by
        -- Expose the value hidden by the proof-carrying `Fin` literal.
        change ¬(n - 1 + 1 < n)
        omega
      rw [typeDSimpleRoot_of_not_add_one_lt hn hperm]
      simp [typeDLastSign, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
    · rw [graphPermD_apply_of_ne_of_ne n (by omega) i hi₂ hi₁]
      have hi : (i : ℕ) + 1 < n := by omega
      rw [typeDSimpleRoot_of_add_one_lt hn hi]
      simp [typeDLastSign, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega

private lemma typeDClassicalGraphEquiv_typeDSimpleRoot (hn : 4 ≤ n) (i : Fin n) :
    typeDClassicalGraphEquiv n
        (typeDRootEquiv n hn (typeDSimpleIndex n hn i)) =
      typeDRootEquiv n hn (typeDSimpleIndex n hn (graphPermD n (by omega) i)) := by
  apply Subtype.ext
  rw [typeDClassicalGraphEquiv_val, typeDRootEquiv_apply_typeDSimpleIndex,
    typeDRootEquiv_apply_typeDSimpleIndex]
  exact typeDLastSign_typeDSimpleRoot hn i

/-- On the pinned simple-root indices, the induced permutation is the numbered fork swap
`TauCeti.graphPermD`. -/
@[simp] theorem typeDGraphIndexEquiv_typeDSimpleIndex (hn : 4 ≤ n) (i : Fin n) :
    typeDGraphIndexEquiv n hn (typeDSimpleIndex n hn i) =
      typeDSimpleIndex n hn (graphPermD n (by omega) i) := by
  apply (typeDRootEquiv n hn).injective
  rw [typeDRootEquiv_typeDGraphIndexEquiv]
  exact typeDClassicalGraphEquiv_typeDSimpleRoot hn i

/-- Reindex the fundamental-weight or simple-coroot coordinates by the fork swap. -/
private noncomputable def typeDGraphLatticeEquiv (n : ℕ) (hn : 4 ≤ n) :
    (Fin n → ℤ) ≃ₗ[ℤ] Fin n → ℤ :=
  LinearEquiv.piCongrLeft' ℤ (fun _ : Fin n => ℤ) (graphPermD n (by omega))

private lemma typeDGraphLatticeEquiv_apply (hn : 4 ≤ n) (x : Fin n → ℤ) (i : Fin n) :
    typeDGraphLatticeEquiv n hn x i = x (graphPermD n (by omega) i) := by
  rw [typeDGraphLatticeEquiv, LinearEquiv.piCongrLeft'_apply, graphPermD_symm]

private lemma graphPermD_apply_apply' (hn : 4 ≤ n) (i : Fin n) :
    graphPermD n (by omega) (graphPermD n (by omega) i) = i := by
  have hi := congrArg (fun e : Equiv.Perm (Fin n) => e i) (graphPermD_sq n (by omega))
  simp only [pow_two, Equiv.Perm.mul_apply] at hi
  -- The right side remains written as the identity permutation applied to `i`.
  change graphPermD n (by omega) (graphPermD n (by omega) i) = i at hi
  exact hi

private lemma typeDGraphLatticeEquiv_involutive (hn : 4 ≤ n) :
    Involutive (typeDGraphLatticeEquiv n hn : (Fin n → ℤ) → Fin n → ℤ) := by
  intro x
  funext i
  rw [typeDGraphLatticeEquiv_apply, typeDGraphLatticeEquiv_apply]
  rw [graphPermD_apply_apply' hn]

private lemma typeDGraphLatticeEquiv_root (hn : 4 ≤ n)
    (i : Fin (2 * n * (n - 1))) :
    typeDGraphLatticeEquiv n hn
        ((typeDSimplyConnectedRootDatum n hn).root i) =
      (typeDSimplyConnectedRootDatum n hn).root (typeDGraphIndexEquiv n hn i) := by
  funext j
  rw [typeDGraphLatticeEquiv_apply, root_typeDSimplyConnectedRootDatum,
    root_typeDSimplyConnectedRootDatum, typeDRootEquiv_typeDGraphIndexEquiv,
    typeDClassicalGraphEquiv_val]
  rw [← typeDLastSign_dotProduct (typeDRootEquiv n hn i).1
    (typeDSimpleRoot n hn (graphPermD n (by omega) j)),
    typeDLastSign_typeDSimpleRoot]
  rw [graphPermD_apply_apply' hn]

private lemma typeDGraphLatticeEquiv_coordinates (hn : 4 ≤ n) (x : TypeDRoot n) :
    typeDGraphLatticeEquiv n hn (typeDSimpleRootCoordinates n hn x) =
      typeDSimpleRootCoordinates n hn (typeDClassicalGraphEquiv n x) := by
  let c : Fin n → ℤ := typeDGraphLatticeEquiv n hn (typeDSimpleRootCoordinates n hn x)
  have hdistrib (a : Fin n → ℤ) (v : Fin n → Fin n → ℤ) :
      typeDLastSign n (∑ i, a i • v i) = ∑ i, a i • typeDLastSign n (v i) := by
    funext j
    by_cases hj : (j : ℕ) = n - 1 <;>
      simp [typeDLastSign, hj]
  have hreindex :
      (∑ i : Fin n, typeDSimpleRootCoordinates n hn x i •
          typeDSimpleRoot n hn (graphPermD n (by omega) i)) =
        ∑ i : Fin n, c i • typeDSimpleRoot n hn i := by
    apply Fintype.sum_equiv (graphPermD n (by omega))
    intro i
    -- Unfold the local coefficient family only at the reindexed summand.
    change _ = typeDGraphLatticeEquiv n hn (typeDSimpleRootCoordinates n hn x)
      (graphPermD n (by omega) i) • typeDSimpleRoot n hn (graphPermD n (by omega) i)
    rw [typeDGraphLatticeEquiv_apply, graphPermD_apply_apply' hn]
  have hsum : ∑ i : Fin n, c i • typeDSimpleRoot n hn i =
      (typeDClassicalGraphEquiv n x).1 := by
    rw [typeDClassicalGraphEquiv_val]
    rw [← hreindex]
    simp_rw [← typeDLastSign_typeDSimpleRoot hn]
    rw [← hdistrib, sum_smul_typeDSimpleRootCoordinates]
  have hzero : ∑ i : Fin n,
      (c i - typeDSimpleRootCoordinates n hn (typeDClassicalGraphEquiv n x) i) •
        typeDSimpleRoot n hn i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hsum,
      sum_smul_typeDSimpleRootCoordinates, sub_self]
  have hcoeff := Fintype.linearIndependent_iff.mp (linearIndependent_typeDSimpleRoot hn)
    (fun i => c i - typeDSimpleRootCoordinates n hn (typeDClassicalGraphEquiv n x) i) hzero
  funext i
  exact sub_eq_zero.mp (hcoeff i)

private lemma typeDGraphLatticeEquiv_coroot (hn : 4 ≤ n)
    (i : Fin (2 * n * (n - 1))) :
    typeDGraphLatticeEquiv n hn
        ((typeDSimplyConnectedRootDatum n hn).coroot i) =
      (typeDSimplyConnectedRootDatum n hn).coroot (typeDGraphIndexEquiv n hn i) := by
  rw [coroot_typeDSimplyConnectedRootDatum, coroot_typeDSimplyConnectedRootDatum,
    typeDRootEquiv_typeDGraphIndexEquiv]
  exact typeDGraphLatticeEquiv_coordinates hn (typeDRootEquiv n hn i)

/-! ## The root-datum automorphism -/

/-- The fork symmetry as an automorphism of the pinned simply connected root datum of type `Dₙ`.
Both lattice maps exchange the final two node coordinates, and the root-index map is the induced
last-coordinate sign change in the classical realization. -/
noncomputable def typeDGraphAut (n : ℕ) (hn : 4 ≤ n) :
    _root_.RootPairing.Aut (typeDSimplyConnectedRootDatum n hn) where
  weightMap := (typeDGraphLatticeEquiv n hn).toLinearMap
  coweightMap := (typeDGraphLatticeEquiv n hn).toLinearMap
  indexEquiv := typeDGraphIndexEquiv n hn
  weight_coweight_transpose := by
    ext y x
    simp only [LinearMap.coe_comp, LinearMap.dualMap_apply, Function.comp_apply,
      LinearEquiv.coe_coe]
    -- `ext` tests equality of the dual maps on the standard basis; expose those evaluations as
    -- the pinned dot-product pairing before reindexing the finite sum.
    change (typeDSimplyConnectedRootDatum n hn).toLinearMap
        (typeDGraphLatticeEquiv n hn (Pi.single x 1)) (Pi.single y 1) =
      (typeDSimplyConnectedRootDatum n hn).toLinearMap (Pi.single x 1)
        (typeDGraphLatticeEquiv n hn (Pi.single y 1))
    rw [toLinearMap_typeDSimplyConnectedRootDatum,
      toLinearMap_typeDSimplyConnectedRootDatum]
    simp only [dotProduct, typeDGraphLatticeEquiv_apply, Pi.single_apply]
    apply Fintype.sum_equiv (graphPermD n (by omega))
    intro i
    rw [graphPermD_apply_apply' hn]
  root_weightMap := by
    funext i
    exact typeDGraphLatticeEquiv_root hn i
  coroot_coweightMap := by
    funext i
    -- Expose the two compositions in the structure field before using involutivity of the index.
    change typeDGraphLatticeEquiv n hn
        ((typeDSimplyConnectedRootDatum n hn).coroot i) =
      (typeDSimplyConnectedRootDatum n hn).coroot ((typeDGraphIndexEquiv n hn).symm i)
    rw [show (typeDGraphIndexEquiv n hn).symm i = typeDGraphIndexEquiv n hn i by
      apply (typeDGraphIndexEquiv n hn).injective
      rw [Equiv.apply_symm_apply, typeDGraphIndexEquiv_apply_apply]]
    exact typeDGraphLatticeEquiv_coroot hn i
  bijective_weightMap := (typeDGraphLatticeEquiv n hn).bijective
  bijective_coweightMap := (typeDGraphLatticeEquiv n hn).bijective

/-- The root-index action bundled in the type-`D` graph automorphism is the explicit permutation
induced by changing the sign of the final classical coordinate. -/
@[simp] theorem indexEquiv_typeDGraphAut (hn : 4 ≤ n)
    (i : Fin (2 * n * (n - 1))) :
    (typeDGraphAut n hn).indexEquiv i = typeDGraphIndexEquiv n hn i :=
  by rw [typeDGraphAut]

/-- The character-lattice action of the type-`D` graph automorphism exchanges the final two
node coordinates. -/
@[simp] theorem weightMap_typeDGraphAut_apply (hn : 4 ≤ n) (x : Fin n → ℤ) (i : Fin n) :
    (typeDGraphAut n hn).weightMap x i = x (graphPermD n (by omega) i) :=
  typeDGraphLatticeEquiv_apply hn x i

/-- The cocharacter-lattice action of the type-`D` graph automorphism exchanges the final two
node coordinates. -/
@[simp] theorem coweightMap_typeDGraphAut_apply (hn : 4 ≤ n) (x : Fin n → ℤ) (i : Fin n) :
    (typeDGraphAut n hn).coweightMap x i = x (graphPermD n (by omega) i) :=
  typeDGraphLatticeEquiv_apply hn x i

/-- The root-index action of the type-`D` graph automorphism restricts to the fork swap on the
pinned simple roots. -/
theorem indexEquiv_typeDGraphAut_typeDSimpleIndex (hn : 4 ≤ n) (i : Fin n) :
    (typeDGraphAut n hn).indexEquiv (typeDSimpleIndex n hn i) =
      typeDSimpleIndex n hn (graphPermD n (by omega) i) :=
  typeDGraphIndexEquiv_typeDSimpleIndex hn i

/-- Applying the type-`D` graph automorphism twice is the identity. -/
@[simp] theorem typeDGraphAut_sq (n : ℕ) (hn : 4 ≤ n) :
    typeDGraphAut n hn ^ 2 = 1 := by
  -- The generated extensionality theorem leaves bundled maps; expose each as the concrete
  -- coordinate or index involution constructed above.
  apply _root_.RootPairing.Equiv.ext
  · apply LinearMap.ext
    intro x
    change typeDGraphLatticeEquiv n hn (typeDGraphLatticeEquiv n hn x) = x
    exact typeDGraphLatticeEquiv_involutive hn x
  · apply LinearMap.ext
    intro x
    change typeDGraphLatticeEquiv n hn (typeDGraphLatticeEquiv n hn x) = x
    exact typeDGraphLatticeEquiv_involutive hn x
  · apply Equiv.ext
    intro i
    change typeDGraphIndexEquiv n hn (typeDGraphIndexEquiv n hn i) = i
    exact typeDGraphIndexEquiv_apply_apply hn i

/-- The type-`D` graph automorphism is nontrivial: it exchanges the two fork simple roots. -/
theorem typeDGraphAut_ne_one (n : ℕ) (hn : 4 ≤ n) : typeDGraphAut n hn ≠ 1 := by
  intro h
  have hindex := congrArg (fun e => e.indexEquiv (typeDSimpleIndex n hn
    (⟨n - 2, by omega⟩ : Fin n))) h
  simp only [indexEquiv_typeDGraphAut_typeDSimpleIndex, graphPermD_apply_left] at hindex
  -- The identity automorphism fixes the chosen root index; expose that definitional action.
  change typeDSimpleIndex n hn (⟨n - 1, by omega⟩ : Fin n) =
    typeDSimpleIndex n hn (⟨n - 2, by omega⟩ : Fin n) at hindex
  have := congrArg Fin.val hindex
  simp only [typeDSimpleIndex_val] at this
  omega

/-- The fork symmetry preserves the support of the pinned type-`D` base. Together with
`RootPairing.Base.support_map_eq`, this computes the support of the transported base. -/
@[simp] theorem image_typeDGraphAut_indexEquiv_typeDSimplyConnectedBase_support
    (n : ℕ) (hn : 4 ≤ n) :
    (typeDSimplyConnectedBase n hn).support.image (typeDGraphAut n hn).indexEquiv =
      (typeDSimplyConnectedBase n hn).support := by
  ext i
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [mem_typeDSimplyConnectedBase_support] at hj ⊢
    let a : Fin n := ⟨j, hj⟩
    have hja : j = typeDSimpleIndex n hn a := by
      apply Fin.ext
      rw [typeDSimpleIndex_val]
    rw [hja, indexEquiv_typeDGraphAut_typeDSimpleIndex,
      typeDSimpleIndex_val]
    exact (graphPermD n (by omega) a).isLt
  · intro hi
    rw [mem_typeDSimplyConnectedBase_support] at hi
    let a : Fin n := ⟨i, hi⟩
    refine ⟨typeDSimpleIndex n hn (graphPermD n (by omega) a), ?_, ?_⟩
    · rw [mem_typeDSimplyConnectedBase_support, typeDSimpleIndex_val]
      exact (graphPermD n (by omega) a).isLt
    · rw [indexEquiv_typeDGraphAut_typeDSimpleIndex, graphPermD_apply_apply' hn]
      apply Fin.ext
      rw [typeDSimpleIndex_val]

end DynkinType

end TauCeti
