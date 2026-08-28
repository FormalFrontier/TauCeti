/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Bruhat

import TauCeti.Data.Fin.Basic

/-!
# The rank-one Tits system of `GL₂`

Let `B` be the upper-triangular subgroup of `GL₂(k)` and let `N` be the normalizer of its
diagonal torus `T`. Over a field whose unit group is nontrivial, these subgroups form a Tits
system. Its single simple reflection is represented by the permutation matrix
`w = !![0, 1; 1, 0]`.

The proof assembles the rank-one results already available for `GL₂`: Bruhat decomposition and
generation by `B` and `w`; the equality `B ∩ N = T`; the permutation quotient `N / T ≃ S₂`;
and the fact that conjugating a nontrivial upper unipotent element by `w` gives a lower
unipotent element outside `B`.

## Main results

* `TauCeti.gl2TitsSystem`: the standard Tits system of `GL₂(k)`.
* `TauCeti.gl2TitsSystem_mem_intersection`: its subgroup `B ∩ N` is the diagonal torus inside
  `N`.
* `TauCeti.gl2TitsSystemSimpleRep` and `TauCeti.gl2TitsSystem_simple`: its Weyl group has the
  single simple reflection represented by `GL2WeylElement k`.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 26.2–26.3 and 28.1.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Sections 8.3–8.4.

This completes the rank-one example of Layer 7, "Bruhat decomposition and BN-pairs / Tits
systems", of the ReductiveGroups roadmap.
-/

public section

open Matrix
open scoped Pointwise

namespace TauCeti

universe u

noncomputable section

variable (k : Type u) [Field k] [Nontrivial kˣ]

/-- The normalizer of the diagonal torus, abbreviated within the construction. -/
private abbrev GL2DiagonalNormalizer : Subgroup (GL (Fin 2) k) :=
  Subgroup.normalizer (diagonalTorus k 2 : Set (GL (Fin 2) k))

/-- The Weyl permutation matrix as an element of the diagonal-torus normalizer. -/
private def gl2WeylNormalizer : GL2DiagonalNormalizer k :=
  ⟨GL2WeylElement k, gl2WeylElement_mem_normalizer_diagonalTorus (R := k)⟩

private theorem gl2_borel_comap_normalizer_eq_diagonal :
    (GL2Borel k).comap (GL2DiagonalNormalizer k).subtype =
      (diagonalTorus k 2).subgroupOf (GL2DiagonalNormalizer k) := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    have hmem : (g : GL (Fin 2) k) ∈
        GL2Borel k ⊓ GL2DiagonalNormalizer k := ⟨hg, g.property⟩
    rw [UpperTriangularGroup.inf_normalizer_diagonalTorus_eq] at hmem
    exact hmem
  · intro hg
    exact UpperTriangularGroup.diagonalTorus_le (R := k) (n := 2) hg

private theorem gl2_mem_borel_iff_normalizerPerm_eq_one (g : GL2DiagonalNormalizer k) :
    (g : GL (Fin 2) k) ∈ GL2Borel k ↔
      diagonalNormalizerPerm (k := k) (n := 2) g = 1 := by
  have hinter := SetLike.ext_iff.mp (gl2_borel_comap_normalizer_eq_diagonal k) g
  constructor
  · exact fun hg ↦ (diagonalNormalizerPerm_eq_one_iff g).mpr (hinter.mp hg)
  · exact fun hg ↦ hinter.mpr ((diagonalNormalizerPerm_eq_one_iff g).mp hg)

private theorem gl2_normalizer_closure :
    Subgroup.closure
        (((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype :
            Set (GL2DiagonalNormalizer k)) ∪ {gl2WeylNormalizer k}) = ⊤ := by
  apply top_unique
  intro g _
  let C : Subgroup (GL2DiagonalNormalizer k) :=
    Subgroup.closure
      (((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype :
          Set (GL2DiagonalNormalizer k)) ∪ {gl2WeylNormalizer k})
  have hinter_le :
      (GL2Borel k).comap (GL2DiagonalNormalizer k).subtype ≤ C := by
    intro x hx
    exact Subgroup.subset_closure (Or.inl hx)
  have hweyl : gl2WeylNormalizer k ∈ C :=
    Subgroup.subset_closure (Or.inr (Set.mem_singleton _))
  let φ := diagonalNormalizerPerm (k := k) (n := 2)
  have hφweyl : φ (gl2WeylNormalizer k) = Equiv.swap 0 1 :=
    diagonalNormalizerPerm_gl2WeylElement (k := k)
  rcases perm_fin_two_eq_one_or_swap (φ g) with hg | hg
  · exact hinter_le ((gl2_mem_borel_iff_normalizerPerm_eq_one k g).mpr hg)
  · have hker : g * (gl2WeylNormalizer k)⁻¹ ∈
        (GL2Borel k).comap (GL2DiagonalNormalizer k).subtype := by
      rw [Subgroup.mem_comap, Subgroup.subtype_apply]
      apply (gl2_mem_borel_iff_normalizerPerm_eq_one k _).mpr
      rw [map_mul, map_inv, hg, hφweyl, mul_inv_cancel]
    have hfactor : g = (g * (gl2WeylNormalizer k)⁻¹) * gl2WeylNormalizer k := by
      simp
    rw [hfactor]
    exact C.mul_mem (hinter_le hker) hweyl

omit [Nontrivial kˣ] in
private theorem gl2_borel_normalizer_closure :
    Subgroup.closure
        ((GL2Borel k : Set (GL (Fin 2) k)) ∪ GL2DiagonalNormalizer k) = ⊤ := by
  have hle :
      Subgroup.closure (insert (GL2WeylElement k) (GL2Borel k : Set (GL (Fin 2) k))) ≤
        Subgroup.closure ((GL2Borel k : Set (GL (Fin 2) k)) ∪ GL2DiagonalNormalizer k) :=
    Subgroup.closure_mono (by
      intro g hg
      rcases hg with (rfl | hg)
      · exact Or.inr (gl2WeylNormalizer k).property
      · exact Or.inl hg)
  rw [GL2Borel.closure_insert_gl2WeylElement_eq_top] at hle
  exact top_unique hle

private theorem gl2_doubleCoset_weyl_mul_union_eq_univ (g : GL2DiagonalNormalizer k) :
    DoubleCoset.doubleCoset
          ((gl2WeylNormalizer k * g : GL2DiagonalNormalizer k) : GL (Fin 2) k)
          (GL2Borel k) (GL2Borel k) ∪
        DoubleCoset.doubleCoset (g : GL (Fin 2) k) (GL2Borel k) (GL2Borel k) =
      Set.univ := by
  let φ := diagonalNormalizerPerm (k := k) (n := 2)
  have hφweyl : φ (gl2WeylNormalizer k) = Equiv.swap 0 1 :=
    diagonalNormalizerPerm_gl2WeylElement (k := k)
  rcases perm_fin_two_eq_one_or_swap (φ g) with hg | hg
  · have hgB : (g : GL (Fin 2) k) ∈ GL2Borel k :=
      (gl2_mem_borel_iff_normalizerPerm_eq_one k g).mpr hg
    have hwg : ((gl2WeylNormalizer k * g : GL2DiagonalNormalizer k) :
        GL (Fin 2) k) ∉ GL2Borel k := by
      rw [gl2_mem_borel_iff_normalizerPerm_eq_one]
      simp [φ, hφweyl, hg]
    have hwgCoset := DoubleCoset.doubleCoset_eq_of_mem
      (GL2Borel.mem_doubleCoset_weyl_of_notMem hwg)
    have hgCoset :
        DoubleCoset.doubleCoset (g : GL (Fin 2) k) (GL2Borel k) (GL2Borel k) =
          DoubleCoset.doubleCoset (1 : GL (Fin 2) k) (GL2Borel k) (GL2Borel k) :=
      DoubleCoset.doubleCoset_eq_of_mem (by
        rw [GL2Borel.doubleCoset_one_eq]
        exact hgB)
    rw [hwgCoset, hgCoset, GL2Borel.doubleCoset_one_eq, Set.union_comm,
      GL2Borel.union_doubleCoset_weyl_eq_univ]
  · have hgB : (g : GL (Fin 2) k) ∉ GL2Borel k := by
      rw [gl2_mem_borel_iff_normalizerPerm_eq_one]
      exact hg.trans_ne (Equiv.swap_eq_one_iff.not.mpr Fin.zero_ne_one)
    have hwg : ((gl2WeylNormalizer k * g : GL2DiagonalNormalizer k) :
        GL (Fin 2) k) ∈ GL2Borel k := by
      rw [gl2_mem_borel_iff_normalizerPerm_eq_one]
      simp [φ, hφweyl, hg]
    have hwgCoset :
        DoubleCoset.doubleCoset
            ((gl2WeylNormalizer k * g : GL2DiagonalNormalizer k) : GL (Fin 2) k)
            (GL2Borel k) (GL2Borel k) =
          DoubleCoset.doubleCoset (1 : GL (Fin 2) k) (GL2Borel k) (GL2Borel k) :=
      DoubleCoset.doubleCoset_eq_of_mem (by
        rw [GL2Borel.doubleCoset_one_eq]
        exact hwg)
    have hgCoset := DoubleCoset.doubleCoset_eq_of_mem
      (GL2Borel.mem_doubleCoset_weyl_of_notMem hgB)
    rw [hwgCoset, GL2Borel.doubleCoset_one_eq, hgCoset,
      GL2Borel.union_doubleCoset_weyl_eq_univ]

omit [Nontrivial kˣ] in
private theorem gl2_tits_exists_conj_not_mem
    (s : GL2DiagonalNormalizer k)
    (hs : s ∈ ({gl2WeylNormalizer k} : Set (GL2DiagonalNormalizer k))) :
    ∃ b : GL2Borel k,
      (s : GL (Fin 2) k) * (b : GL (Fin 2) k) * (s : GL (Fin 2) k)⁻¹ ∉ GL2Borel k := by
  rw [Set.mem_singleton_iff.mp hs]
  refine ⟨⟨GL2Borel.mk 1 1 1, GL2Borel.mk_mem 1 1 1⟩, ?_⟩
  rw [GL2Borel.mem_iff]
  simp [gl2WeylNormalizer, Units.val_mul, GL2Borel.coe_mk, Matrix.mul_apply,
    Fin.sum_univ_two]

/-- The standard rank-one Tits system of `GL₂(k)`: `B` is the upper-triangular subgroup,
`N` is the diagonal-torus normalizer, and its unique simple reflection is represented by the
Weyl permutation matrix. -/
def gl2TitsSystem : TitsSystem (GL (Fin 2) k) where
  subgroupB := GL2Borel k
  subgroupN := GL2DiagonalNormalizer k
  closure_subgroupB_union_subgroupN := gl2_borel_normalizer_closure k
  intersection_normal := by
    rw [gl2_borel_comap_normalizer_eq_diagonal]
    exact Subgroup.normal_in_normalizer
  simple := {QuotientGroup.mk (gl2WeylNormalizer k)}
  closure_simple := by
    let _ : ((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype).Normal := by
      rw [gl2_borel_comap_normalizer_eq_diagonal]
      exact Subgroup.normal_in_normalizer
    apply top_unique
    intro s _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      ((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype) s
    have hg : g ∈ Subgroup.closure
        (((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype :
            Set (GL2DiagonalNormalizer k)) ∪ {gl2WeylNormalizer k}) := by
      rw [gl2_normalizer_closure]
      exact Subgroup.mem_top g
    have hmap : QuotientGroup.mk'
          ((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype) g ∈
        (Subgroup.closure
          (((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype :
              Set (GL2DiagonalNormalizer k)) ∪ {gl2WeylNormalizer k})).map
            (QuotientGroup.mk'
              ((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype)) :=
      ⟨g, hg, rfl⟩
    rw [MonoidHom.map_closure] at hmap
    exact ((Subgroup.closure_le
      (Subgroup.closure
        ({QuotientGroup.mk (gl2WeylNormalizer k)} :
          Set (GL2DiagonalNormalizer k ⧸
            (GL2Borel k).comap (GL2DiagonalNormalizer k).subtype)))).mpr (fun x hx ↦ by
      obtain ⟨y, hy, rfl⟩ := hx
      rcases hy with hy | hy
      · have hqy : QuotientGroup.mk'
            ((GL2Borel k).comap (GL2DiagonalNormalizer k).subtype) y = 1 :=
          (QuotientGroup.eq_one_iff y).mpr hy
        rw [hqy]
        exact (Subgroup.closure
          ({QuotientGroup.mk (gl2WeylNormalizer k)} :
            Set (GL2DiagonalNormalizer k ⧸
              (GL2Borel k).comap (GL2DiagonalNormalizer k).subtype))).one_mem
      · rw [Set.mem_singleton_iff] at hy
        subst y
        exact Subgroup.subset_closure (Set.mem_singleton _))) hmap
  exists_simpleRep_sq_mem s hs := by
    rw [Set.mem_singleton_iff] at hs
    refine ⟨gl2WeylNormalizer k, hs.symm, ?_⟩
    rw [Subgroup.mem_comap, map_mul]
    simp only [Subgroup.subtype_apply, gl2WeylNormalizer]
    rw [gl2WeylElement_mul_self]
    exact (GL2Borel k).one_mem
  mul_doubleCoset_subset s hs := by
    rw [Set.mem_singleton_iff] at hs
    refine ⟨gl2WeylNormalizer k, hs.symm, fun g ↦ ?_⟩
    rw [gl2_doubleCoset_weyl_mul_union_eq_univ]
    exact Set.subset_univ _
  exists_conj_not_mem s hs := by
    rw [Set.mem_singleton_iff] at hs
    obtain ⟨b, hb⟩ := gl2_tits_exists_conj_not_mem k
      (gl2WeylNormalizer k) (Set.mem_singleton _)
    exact ⟨gl2WeylNormalizer k, hs.symm, b, hb⟩

/-- The `B` subgroup of the standard `GL₂` Tits system is the upper-triangular subgroup. -/
@[simp]
theorem gl2TitsSystem_subgroupB : (gl2TitsSystem k).subgroupB = GL2Borel k :=
  by rw [gl2TitsSystem]

/-- The `N` subgroup of the standard `GL₂` Tits system is the diagonal-torus normalizer. -/
@[simp]
theorem gl2TitsSystem_subgroupN :
    (gl2TitsSystem k).subgroupN =
      Subgroup.normalizer (diagonalTorus k 2 : Set (GL (Fin 2) k)) :=
  by rw [gl2TitsSystem]

/-- The standard representative of the simple reflection in the `GL₂` Tits system. -/
def gl2TitsSystemSimpleRep : (gl2TitsSystem k).subgroupN :=
  gl2WeylNormalizer k

/-- The standard simple representative is the Weyl permutation matrix after forgetting the
normalizer subtype. -/
@[simp]
theorem coe_gl2TitsSystemSimpleRep :
    (gl2TitsSystemSimpleRep k : GL (Fin 2) k) = GL2WeylElement k :=
  (rfl)

/-- In the standard `GL₂` Tits system, membership in `B ∩ N` is exactly membership in the
diagonal torus after forgetting the normalizer subtype. -/
theorem gl2TitsSystem_mem_intersection (n : (gl2TitsSystem k).subgroupN) :
    n ∈ (gl2TitsSystem k).intersection ↔
      (n : GL (Fin 2) k) ∈ diagonalTorus k 2 := by
  rw [TitsSystem.mem_intersection]
  let n' : GL2DiagonalNormalizer k :=
    ⟨n, by simpa only [gl2TitsSystem] using n.property⟩
  have hinter := SetLike.ext_iff.mp (gl2_borel_comap_normalizer_eq_diagonal k)
    n'
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.subtype_apply] at hinter
  simpa only [n', gl2TitsSystem] using hinter

/-- The simple set of the standard `GL₂` Tits system is the singleton represented by the Weyl
permutation matrix. -/
theorem gl2TitsSystem_simple :
    (gl2TitsSystem k).simple =
      {(QuotientGroup.mk (gl2TitsSystemSimpleRep k) : (gl2TitsSystem k).WeylGroup)} := by
  ext s
  simp only [gl2TitsSystem, gl2TitsSystemSimpleRep]
  rfl

end


end TauCeti
