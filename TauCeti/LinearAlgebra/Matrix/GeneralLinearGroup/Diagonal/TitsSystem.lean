/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Bruhat

-- Non-public: `perm_fin_two_eq_one_or_swap` classifies the permutation quotient in rank one.
import TauCeti.LinearAlgebra.TensorSquare

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
  change (g : GL (Fin 2) k) ∈ GL2Borel k ↔ (g : GL (Fin 2) k) ∈ diagonalTorus k 2
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

private theorem finTwo_swap_ne_one : Equiv.swap (0 : Fin 2) 1 ≠ 1 := by
  intro h
  have h0 := congrArg (fun σ : Equiv.Perm (Fin 2) ↦ σ 0) h
  simp at h0

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
      change ((g * (gl2WeylNormalizer k)⁻¹ : GL2DiagonalNormalizer k) :
        GL (Fin 2) k) ∈ GL2Borel k
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

omit [Nontrivial kˣ] in
private theorem gl2_doubleCoset_eq_borel_of_mem
    {g : GL (Fin 2) k} (hg : g ∈ GL2Borel k) :
    DoubleCoset.doubleCoset g (GL2Borel k) (GL2Borel k) = (GL2Borel k : Set _) := by
  calc
    DoubleCoset.doubleCoset g (GL2Borel k) (GL2Borel k) =
        DoubleCoset.doubleCoset 1 (GL2Borel k) (GL2Borel k) :=
      DoubleCoset.doubleCoset_eq_of_mem (by
        rw [GL2Borel.doubleCoset_one_eq]
        exact hg)
    _ = (GL2Borel k : Set _) := GL2Borel.doubleCoset_one_eq

omit [Nontrivial kˣ] in
private theorem gl2_doubleCoset_eq_weyl_of_notMem
    {g : GL (Fin 2) k} (hg : g ∉ GL2Borel k) :
    DoubleCoset.doubleCoset g (GL2Borel k) (GL2Borel k) =
      DoubleCoset.doubleCoset (GL2WeylElement k) (GL2Borel k) (GL2Borel k) :=
  DoubleCoset.doubleCoset_eq_of_mem (GL2Borel.mem_doubleCoset_weyl_of_notMem hg)

private theorem gl2_tits_mul_doubleCoset_subset
    (s : GL2DiagonalNormalizer k)
    (hs : s ∈ ({gl2WeylNormalizer k} : Set (GL2DiagonalNormalizer k)))
    (g : GL2DiagonalNormalizer k) :
    DoubleCoset.doubleCoset (s : GL (Fin 2) k) (GL2Borel k) (GL2Borel k) *
        DoubleCoset.doubleCoset (g : GL (Fin 2) k) (GL2Borel k) (GL2Borel k) ⊆
      DoubleCoset.doubleCoset ((s * g : GL2DiagonalNormalizer k) : GL (Fin 2) k)
          (GL2Borel k) (GL2Borel k) ∪
        DoubleCoset.doubleCoset (g : GL (Fin 2) k) (GL2Borel k) (GL2Borel k) := by
  rw [Set.mem_singleton_iff.mp hs]
  intro x _
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
    rw [gl2_doubleCoset_eq_weyl_of_notMem k hwg,
      gl2_doubleCoset_eq_borel_of_mem k hgB, Set.union_comm,
      GL2Borel.union_doubleCoset_weyl_eq_univ]
    exact Set.mem_univ x
  · have hgB : (g : GL (Fin 2) k) ∉ GL2Borel k := by
      rw [gl2_mem_borel_iff_normalizerPerm_eq_one]
      exact hg.trans_ne finTwo_swap_ne_one
    have hwg : ((gl2WeylNormalizer k * g : GL2DiagonalNormalizer k) :
        GL (Fin 2) k) ∈ GL2Borel k := by
      rw [gl2_mem_borel_iff_normalizerPerm_eq_one]
      simp [φ, hφweyl, hg]
    rw [gl2_doubleCoset_eq_borel_of_mem k hwg,
      gl2_doubleCoset_eq_weyl_of_notMem k hgB,
      GL2Borel.union_doubleCoset_weyl_eq_univ]
    exact Set.mem_univ x

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
`N` is the diagonal-torus normalizer, and the unique simple reflection is lifted by the Weyl
permutation matrix. -/
def gl2TitsSystem : TitsSystem (GL (Fin 2) k) where
  borel := GL2Borel k
  normalizer := GL2DiagonalNormalizer k
  simpleReps := {gl2WeylNormalizer k}
  closure_borel_union_normalizer := gl2_borel_normalizer_closure k
  intersection_normal := by
    rw [gl2_borel_comap_normalizer_eq_diagonal]
    exact Subgroup.normal_in_normalizer
  closure_intersection_union_simpleReps := gl2_normalizer_closure k
  simpleRep_sq_mem s hs := by
    rw [Set.mem_singleton_iff.mp hs]
    change GL2WeylElement k * GL2WeylElement k ∈ GL2Borel k
    rw [gl2WeylElement_mul_self]
    exact (GL2Borel k).one_mem
  mul_doubleCoset_subset := gl2_tits_mul_doubleCoset_subset k
  exists_conj_not_mem := gl2_tits_exists_conj_not_mem k

/-- The chosen lift of the simple reflection in the standard `GL₂` Tits system. -/
def gl2TitsSystemSimpleRep : (gl2TitsSystem k).normalizer := by
  change GL2DiagonalNormalizer k
  exact gl2WeylNormalizer k

/-- The chosen simple lift is the usual Weyl permutation matrix after forgetting the normalizer
subtype. -/
@[simp]
theorem coe_gl2TitsSystemSimpleRep :
    (gl2TitsSystemSimpleRep k : GL (Fin 2) k) = GL2WeylElement k :=
  (rfl)

/-- In the standard `GL₂` Tits system, membership in `B ∩ N` is exactly membership in the
diagonal torus after forgetting the normalizer subtype. -/
theorem gl2TitsSystem_mem_intersection (n : (gl2TitsSystem k).normalizer) :
    n ∈ (gl2TitsSystem k).intersection ↔
      (n : GL (Fin 2) k) ∈ diagonalTorus k 2 := by
  rw [TitsSystem.mem_intersection]
  rw [show (gl2TitsSystem k).borel = GL2Borel k from rfl]
  have hn : (n : GL (Fin 2) k) ∈ GL2DiagonalNormalizer k := by
    have hn' := n.property
    change (n : GL (Fin 2) k) ∈ GL2DiagonalNormalizer k at hn'
    exact hn'
  have hinter := SetLike.ext_iff.mp (gl2_borel_comap_normalizer_eq_diagonal k)
    ⟨n, hn⟩
  exact hinter

/-- The simple set of the standard `GL₂` Tits system is the singleton represented by the Weyl
permutation matrix. -/
theorem gl2TitsSystem_simple :
    (gl2TitsSystem k).simple =
      {QuotientGroup.mk' (gl2TitsSystem k).intersection (gl2TitsSystemSimpleRep k)} := by
  rw [TitsSystem.simple_def]
  have hreps : (gl2TitsSystem k).simpleReps = {gl2TitsSystemSimpleRep k} := by
    rfl
  rw [hreps, Set.image_singleton]

end


end TauCeti
