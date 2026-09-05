/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.NumberTheory.Supernatural
public import TauCeti.Topology.Algebra.Group.Profinite.Basic

/-!
# Indices of subgroups of profinite groups

The index of a subgroup of a profinite group is a supernatural number. Its exponent at a
prime `ℓ` is the supremum of the `ℓ`-adic valuations of the indices of the subgroup's images
in all finite continuous quotients.

The definition applies to an arbitrary subgroup. It only sees the subgroup's topological
closure, as every finite continuous quotient has discrete topology. In particular, its index
is one exactly when the subgroup is dense; for closed subgroups, this says exactly that the
subgroup is the whole group. These closure comparisons are the starting point for the usual
description as the least common multiple of the indices of open overgroups.

## Main results

* `TauCeti.Subgroup.profiniteIndex`: the supernatural index of a subgroup of a profinite group.
* `TauCeti.Subgroup.profiniteIndex_anti`: subgroup inclusion reverses supernatural indices.
* `TauCeti.Subgroup.profiniteIndex_eq_iSup_openSubgroup`: the description as the least common
  multiple of the indices of open overgroups.
* `TauCeti.OpenSubgroup.profiniteIndex`: agreement with the ordinary index for an open subgroup.
* `TauCeti.Subgroup.profiniteIndex_topologicalClosure`: taking topological closure does not change
  the index.
* `TauCeti.Subgroup.profiniteIndex_eq_one_iff_topologicalClosure_eq_top`: the index is one exactly
  for dense subgroups.
* `TauCeti.Subgroup.profiniteIndex_eq_one_iff`: the closed-subgroup specialization.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

open scoped ENat

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace Subgroup

/-- The **index of a subgroup of a profinite group**, as a supernatural number. At a prime
`ℓ`, it is the supremum over open normal subgroups `N` of the `ℓ`-adic valuations of
`[G/N : HN/N]`.

The definition makes sense for an arbitrary subgroup; closedness is required only by results
that regard the subgroup itself as profinite. -/
noncomputable def profiniteIndex (H : Subgroup G) : Supernatural :=
  Supernatural.ofFun fun ℓ ↦ ⨆ N : OpenNormalSubgroup G,
    (padicValNat ℓ ((H.map (QuotientGroup.mk' N.toSubgroup)).index) : ℕ∞)

/-- The exponent of a profinite index at a prime is the supremum of the valuations of the
indices in the finite continuous quotients. -/
@[simp]
theorem profiniteIndex_apply (H : Subgroup G) (ℓ : Nat.Primes) :
    profiniteIndex H ℓ = ⨆ N : OpenNormalSubgroup G,
      (padicValNat ℓ ((H.map (QuotientGroup.mk' N.toSubgroup)).index) : ℕ∞) :=
  by rw [profiniteIndex, Supernatural.ofFun_apply]

end Subgroup

/-- The whole group has supernatural index one. -/
@[simp]
theorem profiniteIndex_top : Subgroup.profiniteIndex (⊤ : Subgroup G) = 1 := by
  have hmap : ∀ N : OpenNormalSubgroup G,
      (⊤ : Subgroup G).map (QuotientGroup.mk' N.toSubgroup) = ⊤ := fun N ↦
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N.toSubgroup)
  ext ℓ
  simp_rw [Subgroup.profiniteIndex_apply, hmap]
  simp

section Profinite

variable [IsTopologicalGroup G] [CompactSpace G]

namespace Subgroup

/-- The supernatural index is equivalently the supremum of the ordinary positive indices of
the images in finite continuous quotients. -/
theorem profiniteIndex_eq_iSup_ofNat (H : Subgroup G) :
    profiniteIndex H = ⨆ N : OpenNormalSubgroup G,
      Supernatural.ofNat
        ⟨(H.map (QuotientGroup.mk' N.toSubgroup)).index,
          Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩ := by
  ext ℓ
  rw [profiniteIndex_apply, Supernatural.iSup_apply]
  congr 1
  funext N
  exact
    (Supernatural.ofNat_apply
      ⟨(H.map (QuotientGroup.mk' N.toSubgroup)).index,
        Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩ ℓ).symm

/-- Inclusion of subgroups reverses their supernatural indices. -/
theorem profiniteIndex_anti {H K : Subgroup G} (h : H ≤ K) :
    profiniteIndex K ≤ profiniteIndex H := by
  rw [profiniteIndex_eq_iSup_ofNat, profiniteIndex_eq_iSup_ofNat]
  refine iSup_le fun N ↦ ?_
  refine (Supernatural.ofNat_le_ofNat_iff.mpr ?_).trans
    (le_iSup (fun N : OpenNormalSubgroup G ↦
      Supernatural.ofNat
        ⟨(H.map (QuotientGroup.mk' N.toSubgroup)).index,
          Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩) N)
  exact PNat.dvd_iff.mpr (Subgroup.index_dvd_of_le (Subgroup.map_mono h))

/-- The profinite index is the least common multiple, in the supernatural lattice, of the
ordinary indices of the open subgroups containing `H`.

Although the usual statement assumes that `H` is closed, the formula holds for every subgroup:
an open subgroup contains `H` exactly when it contains its closure. -/
theorem profiniteIndex_eq_iSup_openSubgroup [TotallyDisconnectedSpace G] (H : Subgroup G) :
    profiniteIndex H = ⨆ U : {U : OpenSubgroup G // H ≤ U.toSubgroup},
      Supernatural.ofNat
        (⟨U.1.toSubgroup.index,
          Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩ : ℕ+) := by
  rw [profiniteIndex_eq_iSup_ofNat]
  have index_image_eq (N : OpenNormalSubgroup G) :
      (H.map (QuotientGroup.mk' N.toSubgroup)).index =
        (H ⊔ N.toSubgroup).index := by
    rw [H.index_map, QuotientGroup.ker_mk',
      (QuotientGroup.mk' N.toSubgroup).range_eq_top_of_surjective
        (QuotientGroup.mk'_surjective N.toSubgroup), Subgroup.index_top, mul_one]
  apply le_antisymm
  · refine iSup_le fun N ↦ ?_
    let V : OpenSubgroup G :=
      { toSubgroup := H ⊔ N.toSubgroup
        isOpen' := Subgroup.isOpen_of_openSubgroup _ le_sup_right }
    let V' : {U : OpenSubgroup G // H ≤ U.toSubgroup} := ⟨V, le_sup_left⟩
    have hVpos : 0 < V.toSubgroup.index := by
      rw [← index_image_eq N]
      exact Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite
    calc
      Supernatural.ofNat
          (⟨(H.map (QuotientGroup.mk' N.toSubgroup)).index,
            Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩ : ℕ+) =
          Supernatural.ofNat
            (⟨V.toSubgroup.index,
              hVpos⟩ : ℕ+) := by
        apply congrArg Supernatural.ofNat
        exact Subtype.ext (index_image_eq N)
      _ ≤ ⨆ U : {U : OpenSubgroup G // H ≤ U.toSubgroup},
          Supernatural.ofNat
            (⟨U.1.toSubgroup.index,
              Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩ : ℕ+) := by
        simpa only [V'] using le_iSup (fun U : {U : OpenSubgroup G // H ≤ U.toSubgroup} ↦
          Supernatural.ofNat
            (⟨U.1.toSubgroup.index,
              Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩ : ℕ+)) V'
  · refine iSup_le fun U ↦ ?_
    obtain ⟨N, hN⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one U.1.isOpen U.1.one_mem'
    have hdvd : U.1.toSubgroup.index ∣
        (H.map (QuotientGroup.mk' N.toSubgroup)).index := by
      rw [index_image_eq N]
      exact Subgroup.index_dvd_of_le (sup_le U.2 fun _ hx ↦ hN hx)
    refine le_trans ?_ (le_iSup (fun N : OpenNormalSubgroup G ↦
      Supernatural.ofNat
        (⟨(H.map (QuotientGroup.mk' N.toSubgroup)).index,
          Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩ : ℕ+)) N)
    apply Supernatural.ofNat_le_ofNat_iff.mpr
    exact PNat.dvd_iff.mpr hdvd

/-- Primewise form of `profiniteIndex_eq_iSup_openSubgroup`. -/
theorem profiniteIndex_apply_eq_iSup_openSubgroup [TotallyDisconnectedSpace G]
    (H : Subgroup G) (ℓ : Nat.Primes) :
    profiniteIndex H ℓ = ⨆ U : {U : OpenSubgroup G // H ≤ U.toSubgroup},
      (padicValNat ℓ U.1.toSubgroup.index : ℕ∞) := by
  rw [profiniteIndex_eq_iSup_openSubgroup, Supernatural.iSup_apply]
  congr 1
  funext U
  exact Supernatural.ofNat_apply _ _

end Subgroup

namespace OpenSubgroup

/-- For an open subgroup, the supernatural index is the prime factorization of its ordinary
index. -/
@[simp]
theorem profiniteIndex [TotallyDisconnectedSpace G] (U : OpenSubgroup G) :
    Subgroup.profiniteIndex U.toSubgroup =
      Supernatural.ofNat
        (⟨U.toSubgroup.index,
          Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩ : ℕ+) := by
  rw [Subgroup.profiniteIndex_eq_iSup_openSubgroup]
  apply le_antisymm
  · refine iSup_le fun V ↦ ?_
    exact Supernatural.ofNat_le_ofNat_iff.mpr <|
      PNat.dvd_iff.mpr (Subgroup.index_dvd_of_le V.2)
  · exact le_iSup (fun V : {V : OpenSubgroup G // U.toSubgroup ≤ V.toSubgroup} ↦
      Supernatural.ofNat
        (⟨V.1.toSubgroup.index,
          Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩ : ℕ+)) ⟨U, le_rfl⟩

/-- Primewise, the profinite index of an open subgroup is the valuation of its ordinary
index. -/
theorem profiniteIndex_apply [TotallyDisconnectedSpace G]
    (U : OpenSubgroup G) (ℓ : Nat.Primes) :
    Subgroup.profiniteIndex U.toSubgroup ℓ =
      (padicValNat ℓ U.toSubgroup.index : ℕ∞) := by
  rw [profiniteIndex]
  exact Supernatural.ofNat_apply
    (⟨U.toSubgroup.index,
      Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩ : ℕ+) ℓ

end OpenSubgroup

private theorem map_topologicalClosure_quotient_eq (H : Subgroup G)
    (N : OpenNormalSubgroup G) :
    H.topologicalClosure.map (QuotientGroup.mk' N.toSubgroup) =
      H.map (QuotientGroup.mk' N.toSubgroup) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply H.topologicalClosure_minimal
      (Subgroup.le_comap_map (QuotientGroup.mk' N.toSubgroup) H)
    exact
      (Set.toFinite
        (H.map (QuotientGroup.mk' N.toSubgroup) : Set (G ⧸ N.toSubgroup))).isClosed.preimage
          (QuotientGroup.continuous_mk (N := N.toSubgroup))
  · exact Subgroup.map_mono H.le_topologicalClosure

namespace Subgroup

/-- Taking the topological closure of a subgroup does not change its supernatural index. -/
@[simp]
theorem profiniteIndex_topologicalClosure (H : Subgroup G) :
    profiniteIndex H.topologicalClosure = profiniteIndex H := by
  ext ℓ
  simp_rw [profiniteIndex_apply, map_topologicalClosure_quotient_eq]

variable [TotallyDisconnectedSpace G]

/-- A subgroup of a profinite group has supernatural index one exactly when it is dense. -/
theorem profiniteIndex_eq_one_iff_topologicalClosure_eq_top (H : Subgroup G) :
    profiniteIndex H = 1 ↔ H.topologicalClosure = ⊤ := by
  constructor
  · intro hindex
    have himage : ∀ N : OpenNormalSubgroup G,
        H.map (QuotientGroup.mk' N.toSubgroup) = ⊤ := by
      intro N
      rw [← Subgroup.index_eq_one]
      let n : ℕ+ :=
        ⟨(H.map (QuotientGroup.mk' N.toSubgroup)).index,
          Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩
      have hle : Supernatural.ofNat n ≤ profiniteIndex H := by
        rw [profiniteIndex_eq_iSup_ofNat]
        exact le_iSup (fun U : OpenNormalSubgroup G ↦
          Supernatural.ofNat
            ⟨(H.map (QuotientGroup.mk' U.toSubgroup)).index,
              Nat.zero_lt_of_ne_zero Subgroup.index_ne_zero_of_finite⟩) N
      rw [hindex, ← Supernatural.ofNat_one, Supernatural.ofNat_le_ofNat_iff] at hle
      exact congrArg Subtype.val ((PNat.dvd_one_iff n).mp hle)
    rw [Subgroup.eq_iInf_sup_openNormalSubgroup H.topologicalClosure
      H.isClosed_topologicalClosure]
    apply iInf_eq_top.mpr
    intro N
    apply top_unique
    calc
      ⊤ = H ⊔ N.toSubgroup := by
        rw [sup_comm, ← QuotientGroup.comap_map_mk' N.toSubgroup H, himage N,
          Subgroup.comap_top]
      _ ≤ H.topologicalClosure ⊔ N.toSubgroup := sup_le_sup_right H.le_topologicalClosure _
  · intro hclosure
    rw [← profiniteIndex_topologicalClosure H, hclosure, profiniteIndex_top]

/-- A closed subgroup of a profinite group has supernatural index one exactly when it is the
whole group. -/
theorem profiniteIndex_eq_one_iff (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    profiniteIndex H = 1 ↔ H = ⊤ := by
  have hclosure : H.topologicalClosure = H := by
    apply SetLike.coe_injective
    rw [Subgroup.topologicalClosure_coe, hH.closure_eq]
  rw [profiniteIndex_eq_one_iff_topologicalClosure_eq_top,
    hclosure]

end Subgroup

end Profinite

end TauCeti
