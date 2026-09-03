/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.NumberTheory.Supernatural
public import TauCeti.Topology.Algebra.Group.Profinite.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The supernatural index of a subgroup of a profinite group

An open subgroup of a compact group has a finite index, but a general closed subgroup — the
`p`-Sylow subgroups of the next layer, for instance — does not.  The right invariant is a
supernatural number: at each prime `ℓ`, the index records the supremum of the `ℓ`-adic
valuations of the finite indices `[G/N : HN/N]`, taken over the open normal subgroups `N`
of `G`.

`TauCeti.profiniteIndex H` is that invariant.  It is defined for an arbitrary subgroup of an
arbitrary topological group, so that it can be spoken of before `H` has been assembled as a
profinite group in its own right, and the topological hypotheses appear only on the theorems
that need them.

## Main definitions

* `TauCeti.profiniteIndex`: the supernatural index of a subgroup.

## Main results

* `TauCeti.profiniteIndex_apply_eq_iSup_sup`: the index computed through the joins `H ⊔ N`
  rather than through the images in the finite quotients, in an arbitrary topological group.
* `TauCeti.profiniteIndex_topologicalClosure`: the index depends only on the topological
  closure of `H`.
* `TauCeti.profiniteIndex_apply_eq_iSup_openSubgroup`: the description used in the literature,
  as the supremum of the ordinary indices of the open subgroups containing `H`.
* `TauCeti.profiniteIndex_apply_of_isOpen`, `TauCeti.profiniteIndex_eq_ofNat_of_isOpen`: on an
  open subgroup the supernatural index is the factorization of Mathlib's `Subgroup.index`.
* `TauCeti.profiniteIndex_eq_one_iff_topologicalClosure_eq_top`,
  `TauCeti.profiniteIndex_eq_one_iff`: the index is `1` exactly for a (topologically) dense
  subgroup.
* `TauCeti.isOpen_iff_isClosed_and_isNatural_profiniteIndex`: a subgroup of a profinite group
  is open if and only if it is closed of natural-number index.
* `TauCeti.profiniteIndex_map_dvd`, `TauCeti.profiniteIndex_map_continuousMulEquiv`: the index
  of a continuous surjective image divides the index, and is invariant under a topological
  isomorphism.

The closedness of `H` that the literature attaches to the description as a supremum over open
subgroups is not needed: an open subgroup is closed, so it contains `H` exactly when it
contains the closure of `H`, and both sides of the description therefore only see that
closure.  Closedness reappears in `profiniteIndex_eq_one_iff`, which converts the conclusion
`H.topologicalClosure = ⊤` into `H = ⊤`, and in
`isOpen_iff_isClosed_and_isNatural_profiniteIndex`.

## References

This is the "index of a closed subgroup" milestone of Layer 1, "supernatural order and
index", of the human-authored roadmap `TauCetiRoadmap/ProfiniteProPGroups/README.md`, whose
primewise definition is pinned in that roadmap's `Suggested.lean`, together with the parts of
its "Index API" checklist that do not mention `profiniteOrder`.

The definition and the statements follow L. Ribes and P. Zalesskii, *Profinite Groups*,
Section 2.3.
-/

public section

namespace TauCeti

open Supernatural

/-- A positive natural number divides another exactly when it does so prime by prime.  This is
the numerical shadow of `Supernatural.ofNat_dvd_ofNat_iff`, used to move between the
supernatural index and Mathlib's `Subgroup.index`. -/
private theorem dvd_iff_forall_padicValNat_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a ∣ b ↔ ∀ ℓ : Nat.Primes, padicValNat ℓ a ≤ padicValNat ℓ b := by
  rw [← Nat.factorization_prime_le_iff_dvd ha hb]
  exact ⟨fun h ℓ => by simpa [Nat.factorization_def _ ℓ.prop] using h ℓ ℓ.prop,
    fun h q hq => by simpa [Nat.factorization_def _ hq] using h ⟨q, hq⟩⟩

/-- Divisibility of positive natural numbers is monotone for the `ℓ`-adic valuations. -/
private theorem padicValNat_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) (ℓ : Nat.Primes) :
    padicValNat ℓ a ≤ padicValNat ℓ b :=
  (dvd_iff_forall_padicValNat_le (ne_zero_of_dvd_ne_zero hb hab) hb).mp hab ℓ

/-- Two nested subgroups of the same finite index coincide. -/
private theorem eq_of_le_of_index_eq {G : Type*} [Group G] {K L : Subgroup G} (h : K ≤ L)
    (hL : L.index ≠ 0) (hidx : K.index = L.index) : K = L :=
  le_antisymm h <| Subgroup.relIndex_eq_one.mp <|
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hL)
      ((Subgroup.relIndex_mul_index h).trans (hidx.trans (one_mul _).symm))

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

/-- The **supernatural index** of a subgroup `H` of a topological group `G`: at each prime `ℓ`,
the supremum over the open normal subgroups `N` of `G` of the `ℓ`-adic valuation of the finite
index `[G/N : HN/N]`.

For an open subgroup this is the factorization of Mathlib's `Subgroup.index`
(`profiniteIndex_eq_ofNat_of_isOpen`), and for a closed subgroup of a profinite group it is the
supremum of the indices of the open subgroups containing `H`
(`profiniteIndex_apply_eq_iSup_openSubgroup`). -/
noncomputable def profiniteIndex (H : Subgroup G) : Supernatural :=
  ofFun fun ℓ ↦ ⨆ N : OpenNormalSubgroup G,
    (padicValNat ℓ (H.map (QuotientGroup.mk' N.toSubgroup)).index : ℕ∞)

/-- The defining description of the supernatural index, prime by prime. -/
theorem profiniteIndex_apply (H : Subgroup G) (ℓ : Nat.Primes) :
    profiniteIndex H ℓ = ⨆ N : OpenNormalSubgroup G,
      (padicValNat ℓ (H.map (QuotientGroup.mk' N.toSubgroup)).index : ℕ∞) :=
  ofFun_apply _ ℓ

omit [TopologicalSpace G] in
/-- The image of `H` in `G ⧸ N` has the index of `H ⊔ N` in `G`. -/
private theorem index_map_mk' (H N : Subgroup G) [N.Normal] :
    (H.map (QuotientGroup.mk' N)).index = (H ⊔ N).index := by
  rw [Subgroup.index_map, QuotientGroup.ker_mk',
    MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective N),
    Subgroup.index_top, mul_one]

/-- The supernatural index computed through the joins `H ⊔ N` instead of through the images of
`H` in the finite quotients. -/
theorem profiniteIndex_apply_eq_iSup_sup (H : Subgroup G) (ℓ : Nat.Primes) :
    profiniteIndex H ℓ =
      ⨆ N : OpenNormalSubgroup G, (padicValNat ℓ (H ⊔ N.toSubgroup).index : ℕ∞) := by
  simp only [profiniteIndex_apply, index_map_mk']

/-- The whole group has supernatural index `1`. -/
@[simp]
theorem profiniteIndex_top : profiniteIndex (⊤ : Subgroup G) = 1 := by
  ext ℓ
  simp [profiniteIndex_apply_eq_iSup_sup]

section IsTopologicalGroup

variable [IsTopologicalGroup G]

/-- The join of a subgroup with an open normal subgroup is open. -/
private theorem isOpen_sup_openNormalSubgroup (H : Subgroup G) (N : OpenNormalSubgroup G) :
    IsOpen ((H ⊔ N.toSubgroup : Subgroup G) : Set G) :=
  Subgroup.isOpen_mono (le_sup_right : N.toSubgroup ≤ H ⊔ N.toSubgroup) N.isOpen

/-- The supernatural index only sees the topological closure of `H`: the joins `H ⊔ N` are
open, hence closed, hence already contain that closure. -/
@[simp]
theorem profiniteIndex_topologicalClosure (H : Subgroup G) :
    profiniteIndex H.topologicalClosure = profiniteIndex H := by
  have key : ∀ N : OpenNormalSubgroup G,
      H.topologicalClosure ⊔ N.toSubgroup = H ⊔ N.toSubgroup := by
    intro N
    refine le_antisymm (sup_le ?_ le_sup_right) (sup_le (le_sup_of_le_left H.le_topologicalClosure)
      le_sup_right)
    exact H.topologicalClosure_minimal le_sup_left
      (Subgroup.isClosed_of_isOpen _ (isOpen_sup_openNormalSubgroup H N))
  ext ℓ
  simp only [profiniteIndex_apply_eq_iSup_sup, key]

section CompactSpace

variable [CompactSpace G]

/-- An open subgroup of a compact group has finite index. -/
private theorem index_ne_zero_of_isOpen {H : Subgroup G} (hH : IsOpen (H : Set G)) :
    H.index ≠ 0 :=
  have := Subgroup.quotient_finite_of_isOpen H hH
  Subgroup.index_ne_zero_of_finite

/-- In a compact group the joins `H ⊔ N` with `N` open normal have finite index. -/
private theorem index_sup_ne_zero (H : Subgroup G) (N : OpenNormalSubgroup G) :
    (H ⊔ N.toSubgroup).index ≠ 0 :=
  index_ne_zero_of_isOpen (isOpen_sup_openNormalSubgroup H N)

/-- Every open subgroup of a compact group contains an open normal subgroup. -/
private theorem exists_openNormalSubgroup_le {H : Subgroup G} (hH : IsOpen (H : Set G)) :
    ∃ N : OpenNormalSubgroup G, N.toSubgroup ≤ H :=
  IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    ⟨Subgroup.isClosed_of_isOpen H hH, hH⟩ H.one_mem

/-- The supernatural index is antitone: a larger subgroup has a smaller index. -/
theorem profiniteIndex_dvd_of_le {H K : Subgroup G} (h : H ≤ K) :
    profiniteIndex K ∣ profiniteIndex H := by
  rw [Supernatural.dvd_iff]
  intro ℓ
  rw [profiniteIndex_apply_eq_iSup_sup, profiniteIndex_apply_eq_iSup_sup]
  refine iSup_le fun N => le_iSup_of_le N ?_
  exact_mod_cast padicValNat_le_of_dvd (index_sup_ne_zero H N)
    (Subgroup.index_dvd_of_le (sup_le_sup_right h _)) ℓ

/-- On an open subgroup the supernatural index is the prime factorization of Mathlib's
`Subgroup.index`. -/
theorem profiniteIndex_apply_of_isOpen {H : Subgroup G} (hH : IsOpen (H : Set G))
    (ℓ : Nat.Primes) : profiniteIndex H ℓ = (padicValNat ℓ H.index : ℕ∞) := by
  obtain ⟨N₀, hN₀⟩ := exists_openNormalSubgroup_le hH
  rw [profiniteIndex_apply_eq_iSup_sup]
  refine le_antisymm (iSup_le fun N => ?_) (le_iSup_of_le N₀ ?_)
  · exact_mod_cast padicValNat_le_of_dvd (index_ne_zero_of_isOpen hH)
      (Subgroup.index_dvd_of_le (le_sup_left : H ≤ H ⊔ N.toSubgroup)) ℓ
  · rw [sup_eq_left.mpr hN₀]

/-- The supernatural index of an open subgroup is a natural number, namely its ordinary
index.  The positive natural number `n` is supplied together with the equation `↑n = H.index`
so that the statement does not have to carry a positivity proof. -/
theorem profiniteIndex_eq_ofNat_of_isOpen {H : Subgroup G} (hH : IsOpen (H : Set G)) {n : ℕ+}
    (hn : (n : ℕ) = H.index) : profiniteIndex H = ofNat n := by
  ext ℓ
  rw [profiniteIndex_apply_of_isOpen hH, ofNat_apply, hn]

/-- The supernatural index of an open subgroup is a natural number. -/
theorem isNatural_profiniteIndex_of_isOpen {H : Subgroup G} (hH : IsOpen (H : Set G)) :
    (profiniteIndex H).IsNatural :=
  have hne := Nat.pos_of_ne_zero (index_ne_zero_of_isOpen hH)
  isNatural_def.mpr ⟨⟨H.index, hne⟩,
    (profiniteIndex_eq_ofNat_of_isOpen hH (n := ⟨H.index, hne⟩) rfl).symm⟩

/-- The description of the supernatural index used in the literature: the supremum, over the
open subgroups `U` containing `H`, of the `ℓ`-adic valuations of the ordinary indices `[G : U]`.

Closedness of `H` is not required.  An open subgroup is closed, so it contains `H` exactly when
it contains `H.topologicalClosure`; both sides of the identity therefore only depend on that
closure, in accordance with `profiniteIndex_topologicalClosure`. -/
theorem profiniteIndex_apply_eq_iSup_openSubgroup (H : Subgroup G) (ℓ : Nat.Primes) :
    profiniteIndex H ℓ =
      ⨆ U : {U : OpenSubgroup G // H ≤ U.toSubgroup},
        (padicValNat ℓ U.1.toSubgroup.index : ℕ∞) := by
  rw [profiniteIndex_apply_eq_iSup_sup]
  refine le_antisymm (iSup_le fun N => ?_) (iSup_le fun U => ?_)
  · exact le_iSup_of_le ⟨⟨H ⊔ N.toSubgroup, isOpen_sup_openNormalSubgroup H N⟩, le_sup_left⟩ le_rfl
  · obtain ⟨N, hN⟩ := exists_openNormalSubgroup_le U.1.isOpen
    refine le_iSup_of_le N ?_
    exact_mod_cast padicValNat_le_of_dvd (index_sup_ne_zero H N)
      (Subgroup.index_dvd_of_le (sup_le U.2 hN)) ℓ

/-- When the supernatural index of `H` is the natural number `n`, every open subgroup above `H`
has ordinary index dividing `n`. -/
private theorem index_dvd_of_profiniteIndex_eq_ofNat {H : Subgroup G} {n : ℕ+}
    (hn : profiniteIndex H = ofNat n) {U : OpenSubgroup G} (hU : H ≤ U.toSubgroup) :
    U.toSubgroup.index ∣ (n : ℕ) := by
  refine (dvd_iff_forall_padicValNat_le (index_ne_zero_of_isOpen U.isOpen) n.ne_zero).mpr
    fun ℓ => ?_
  have hle : ((padicValNat ℓ U.toSubgroup.index : ℕ∞)) ≤ profiniteIndex H ℓ := by
    rw [profiniteIndex_apply_eq_iSup_openSubgroup]
    exact le_iSup (fun U : {U : OpenSubgroup G // H ≤ U.toSubgroup} =>
      ((padicValNat ℓ U.1.toSubgroup.index : ℕ∞))) ⟨U, hU⟩
  rw [hn, ofNat_apply] at hle
  exact_mod_cast hle

end CompactSpace

end IsTopologicalGroup

section Profinite

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A subgroup of a profinite group has supernatural index `1` exactly when it is dense. -/
theorem profiniteIndex_eq_one_iff_topologicalClosure_eq_top (H : Subgroup G) :
    profiniteIndex H = 1 ↔ H.topologicalClosure = ⊤ := by
  refine ⟨fun h => ?_, fun h => by rw [← profiniteIndex_topologicalClosure, h, profiniteIndex_top]⟩
  have hsup : ∀ N : OpenNormalSubgroup G, H ⊔ N.toSubgroup = ⊤ := by
    intro N
    rw [← Subgroup.index_eq_one]
    refine Nat.dvd_one.mp
      ((dvd_iff_forall_padicValNat_le (index_sup_ne_zero H N) one_ne_zero).mpr fun ℓ => ?_)
    have hle : ((padicValNat ℓ (H ⊔ N.toSubgroup).index : ℕ∞)) ≤ profiniteIndex H ℓ := by
      rw [profiniteIndex_apply_eq_iSup_sup]
      exact le_iSup (fun N : OpenNormalSubgroup G =>
        ((padicValNat ℓ (H ⊔ N.toSubgroup).index : ℕ∞))) N
    rw [h, one_apply, nonpos_iff_eq_zero, Nat.cast_eq_zero] at hle
    simp [hle]
  have hclos : ∀ N : OpenNormalSubgroup G, H.topologicalClosure ⊔ N.toSubgroup = ⊤ := fun N =>
    top_le_iff.mp ((hsup N).ge.trans (sup_le_sup_right H.le_topologicalClosure _))
  rw [Subgroup.eq_iInf_sup_openNormalSubgroup H.topologicalClosure H.isClosed_topologicalClosure]
  simp [hclos]

/-- A closed subgroup of a profinite group has supernatural index `1` exactly when it is the
whole group. -/
theorem profiniteIndex_eq_one_iff {H : Subgroup G} (hH : IsClosed (H : Set G)) :
    profiniteIndex H = 1 ↔ H = ⊤ := by
  rw [profiniteIndex_eq_one_iff_topologicalClosure_eq_top,
    le_antisymm (H.topologicalClosure_minimal le_rfl hH) H.le_topologicalClosure]

/-- **A subgroup of a profinite group is open if and only if it is closed of natural-number
index.**  The substance is the converse direction: the open subgroups above `H` then have
indices bounded by a fixed natural number, so one of them, `U₀`, has the largest index; that
maximality forces `U₀` to be contained in every open subgroup above `H`, and `H` is the
infimum of those. -/
theorem isOpen_iff_isClosed_and_isNatural_profiniteIndex (H : Subgroup G) :
    IsOpen (H : Set G) ↔ IsClosed (H : Set G) ∧ (profiniteIndex H).IsNatural := by
  refine ⟨fun hH => ⟨Subgroup.isClosed_of_isOpen H hH, isNatural_profiniteIndex_of_isOpen hH⟩,
    fun ⟨hclosed, hnat⟩ => ?_⟩
  obtain ⟨n, hn⟩ := isNatural_def.mp hnat
  -- the open subgroups above `H` have indices bounded by `n`, so one of them has the largest
  set S : Set ℕ := {k | ∃ U : OpenSubgroup G, H ≤ U.toSubgroup ∧ U.toSubgroup.index = k}
  have hSne : S.Nonempty := ⟨(⊤ : OpenSubgroup G).toSubgroup.index, ⊤, le_top, rfl⟩
  have hSbdd : BddAbove S := by
    refine ⟨n, ?_⟩
    rintro _ ⟨U, hU, rfl⟩
    exact Nat.le_of_dvd n.pos (index_dvd_of_profiniteIndex_eq_ofNat hn.symm hU)
  obtain ⟨U₀, hU₀, hU₀max⟩ := Nat.sSup_mem hSne hSbdd
  -- that maximality makes `U₀` the smallest open subgroup above `H`
  have hmin : ∀ U : OpenSubgroup G, H ≤ U.toSubgroup → U₀.toSubgroup ≤ U.toSubgroup := by
    intro U hU
    have hle : (U ⊓ U₀).toSubgroup ≤ U₀.toSubgroup := by
      rw [OpenSubgroup.toSubgroup_inf]; exact inf_le_right
    have heq : (U ⊓ U₀).toSubgroup.index = U₀.toSubgroup.index :=
      le_antisymm
        (hU₀max ▸ le_csSup hSbdd
          ⟨U ⊓ U₀, by rw [OpenSubgroup.toSubgroup_inf]; exact le_inf hU hU₀, rfl⟩)
        (Nat.le_of_dvd (Nat.pos_of_ne_zero (index_ne_zero_of_isOpen (U ⊓ U₀).isOpen))
          (Subgroup.index_dvd_of_le hle))
    have hsub := eq_of_le_of_index_eq hle (index_ne_zero_of_isOpen U₀.isOpen) heq
    rw [OpenSubgroup.toSubgroup_inf] at hsub
    exact hsub.ge.trans inf_le_left
  -- so `U₀` sits inside the intersection of the open subgroups above `H`, which is `H` itself
  have hHU₀ : U₀.toSubgroup ≤ H := by
    rw [show (H : Subgroup G) = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ H ≤ N} from
      ProfiniteGrp.closedSubgroup_eq_sInf_open ⟨H, hclosed⟩]
    exact le_sInf fun N hN => hmin ⟨N, hN.1⟩ hN.2
  exact le_antisymm hU₀ hHU₀ ▸ U₀.isOpen

end Profinite

section Map

/-- The supernatural index of a continuous surjective image divides the supernatural index.
Equality can fail: for distinct primes `p` and `q`, the trivial subgroup of `ℤ_p × ℤ_q` has
index `p^∞ q^∞`, while its image under the first projection has index `p^∞`. -/
theorem profiniteIndex_map_dvd (H : Subgroup G) {f : G →* G'} (hf : Continuous f)
    (hsurj : Function.Surjective f) : profiniteIndex (H.map f) ∣ profiniteIndex H := by
  rw [Supernatural.dvd_iff]
  intro ℓ
  rw [profiniteIndex_apply_eq_iSup_sup, profiniteIndex_apply_eq_iSup_sup]
  refine iSup_le fun N' => le_iSup_of_le
    { toSubgroup := N'.toSubgroup.comap f
      isOpen' := N'.isOpen.preimage hf
      isNormal' := Subgroup.normal_comap f } (le_of_eq ?_)
  rw [show (H.map f ⊔ N'.toSubgroup) = (H ⊔ N'.toSubgroup.comap f).map f by
      rw [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective hsurj],
    Subgroup.index_map_eq _ hsurj (le_sup_of_le_right (Subgroup.ker_le_comap f _))]

/-- The supernatural index is invariant under a topological isomorphism of the ambient
group. -/
@[simp]
theorem profiniteIndex_map_continuousMulEquiv (H : Subgroup G) (e : G ≃ₜ* G') :
    profiniteIndex (H.map ((e : G ≃* G') : G →* G')) = profiniteIndex H := by
  have hcont : Continuous (((e : G ≃* G') : G →* G') : G → G') := map_continuous e
  have hsurj : Function.Surjective (((e : G ≃* G') : G →* G') : G → G') := EquivLike.surjective e
  have hcont' : Continuous (((e.symm : G' ≃* G) : G' →* G) : G' → G) := map_continuous e.symm
  have hsurj' : Function.Surjective (((e.symm : G' ≃* G) : G' →* G) : G' → G) :=
    EquivLike.surjective e.symm
  refine le_antisymm (Supernatural.dvd_iff_le.mp (profiniteIndex_map_dvd H hcont hsurj)) ?_
  have hback := profiniteIndex_map_dvd (H.map ((e : G ≃* G') : G →* G')) hcont' hsurj'
  rw [Subgroup.map_map, show (((e.symm : G' ≃* G) : G' →* G).comp ((e : G ≃* G') : G →* G'))
    = MonoidHom.id G from MonoidHom.ext fun x => e.symm_apply_apply x, Subgroup.map_id] at hback
  exact Supernatural.dvd_iff_le.mp hback

end Map

end TauCeti
