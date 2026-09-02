/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.NumberTheory.Supernatural
public import TauCeti.Topology.Algebra.Group.Profinite.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP

/-!
# The supernatural order of a profinite group

A profinite group is rarely finite, so its order is not a natural number.  It is instead a
supernatural number: at each prime `p` one records the supremum of the `p`-adic valuations of
the orders of the continuous finite quotients, which for the unbundled profinite groups used
here are the quotients by the open normal subgroups.  This file defines that order and proves
the facts that pin it down: the order of a continuous surjective image divides it, it is the
prime factorization of `Nat.card G` on a finite discrete group, it is `1` exactly on the
trivial profinite group, and it is supported at a single prime `p` exactly when the group is
pro-`p`.

The definition is stated for an arbitrary topological group, so that it can be applied to a
subgroup or a quotient before that object has been assembled as a profinite group; compactness
enters only where the finite quotients are genuinely used.

## Main definitions

* `TauCeti.profiniteOrder`: the order of a topological group as a supernatural number.

## Main results

* `TauCeti.profiniteOrder_le_of_surjective`, `TauCeti.profiniteOrder_dvd_of_surjective`: the
  order of a continuous surjective image divides the order of the group.
* `TauCeti.profiniteOrder_apply_of_finite`: on a finite discrete group the order is the prime
  factorization of `Nat.card G`.
* `TauCeti.profiniteOrder_eq_one_iff`: a profinite group has order `1` exactly when it is
  trivial.
* `TauCeti.isProP_iff_profiniteOrder_apply_eq_zero`: a compact topological group is pro-`p`
  exactly when its order has vanishing exponent at every prime other than `p`.

## References

This is the `profiniteOrder` milestone of Layer 1, "supernatural order and index", of the
human-authored roadmap `TauCetiRoadmap/ProfiniteProPGroups/README.md`, together with the
Layer 1 to Layer 3 comparison "`G` is pro-`p` if and only if `profiniteOrder G` is supported at
`p`".  The supernatural carrier itself is `TauCeti.Supernatural`.

The definitions and terminology follow L. Ribes and P. Zalesskii, *Profinite Groups*,
Section 2.3.
-/

public section

namespace TauCeti

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- The **order** of a topological group as a supernatural number: its exponent at a prime `p`
is the supremum of the `p`-adic valuations of the orders of the quotients by the open normal
subgroups.  For a profinite group these quotients are exactly the continuous finite quotients,
so this is the Steinitz order of the group. -/
noncomputable def profiniteOrder (G : Type u) [Group G] [TopologicalSpace G] : Supernatural :=
  Supernatural.ofFun fun p ↦ ⨆ U : OpenNormalSubgroup G,
    (padicValNat p (Nat.card (G ⧸ U.toSubgroup)) : ℕ∞)

/-- The defining description of `profiniteOrder`: its exponent at `p` is a supremum over the
open normal subgroups. -/
theorem profiniteOrder_apply (G : Type u) [Group G] [TopologicalSpace G] (p : Nat.Primes) :
    profiniteOrder G p = ⨆ U : OpenNormalSubgroup G,
      (padicValNat p (Nat.card (G ⧸ U.toSubgroup)) : ℕ∞) :=
  Supernatural.ofFun_apply _ p

/-- The exponent of the order at `p` vanishes exactly when the order of every quotient by an
open normal subgroup has vanishing `p`-adic valuation. -/
theorem profiniteOrder_apply_eq_zero_iff (G : Type u) [Group G] [TopologicalSpace G]
    (p : Nat.Primes) :
    profiniteOrder G p = 0 ↔
      ∀ U : OpenNormalSubgroup G, padicValNat p (Nat.card (G ⧸ U.toSubgroup)) = 0 := by
  rw [profiniteOrder_apply]
  constructor
  · intro h U
    have hle : ((padicValNat p (Nat.card (G ⧸ U.toSubgroup)) : ℕ∞)) ≤ 0 := by
      rw [← h]
      exact le_iSup (fun U : OpenNormalSubgroup G ↦
        (padicValNat p (Nat.card (G ⧸ U.toSubgroup)) : ℕ∞)) U
    exact_mod_cast nonpos_iff_eq_zero.mp hle
  · intro h
    refine le_antisymm (iSup_le fun U ↦ ?_) (by simp)
    simp [h U]

section Surjective

/-- The order of a continuous surjective image is at most the order of the group: every
open normal subgroup of the image pulls back to one of the source with the same quotient. -/
theorem profiniteOrder_le_of_surjective (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) : profiniteOrder H ≤ profiniteOrder G := by
  rw [Supernatural.le_iff]
  intro p
  rw [profiniteOrder_apply, profiniteOrder_apply]
  refine iSup_le fun V ↦ ?_
  let U : OpenNormalSubgroup G :=
    { toOpenSubgroup := V.toOpenSubgroup.comap f hf
      isNormal' := V.isNormal'.comap f }
  let _ : U.toSubgroup.Normal := U.isNormal'
  have hsurj' : Function.Surjective ⇑((QuotientGroup.mk' V.toSubgroup).comp f) :=
    (QuotientGroup.mk'_surjective V.toSubgroup).comp hsurj
  have hker : MonoidHom.ker ((QuotientGroup.mk' V.toSubgroup).comp f) = U.toSubgroup := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hcard : Nat.card (H ⧸ V.toSubgroup) = Nat.card (G ⧸ U.toSubgroup) :=
    Nat.card_congr
      ((QuotientGroup.quotientKerEquivOfSurjective _ hsurj').symm.trans
        (QuotientGroup.quotientMulEquivOfEq hker)).toEquiv
  rw [hcard]
  exact le_iSup (fun U : OpenNormalSubgroup G ↦
    (padicValNat p (Nat.card (G ⧸ U.toSubgroup)) : ℕ∞)) U

/-- The order of a continuous surjective image divides the order of the group. -/
theorem profiniteOrder_dvd_of_surjective (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) : profiniteOrder H ∣ profiniteOrder G :=
  Supernatural.dvd_iff_le.mpr (profiniteOrder_le_of_surjective f hf hsurj)

/-- The order of a quotient by a normal subgroup divides the order of the group. -/
theorem profiniteOrder_quotient_dvd (N : Subgroup G) [N.Normal] :
    profiniteOrder (G ⧸ N) ∣ profiniteOrder G :=
  profiniteOrder_dvd_of_surjective (QuotientGroup.mk' N) QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective N)

/-- The order is invariant under topological group isomorphism. -/
theorem profiniteOrder_congr (e : G ≃ₜ* H) : profiniteOrder G = profiniteOrder H :=
  le_antisymm
    (profiniteOrder_le_of_surjective e.symm.toMulEquiv.toMonoidHom e.symm.continuous
      e.symm.surjective)
    (profiniteOrder_le_of_surjective e.toMulEquiv.toMonoidHom e.continuous e.surjective)

end Surjective

/-- On a finite group with the discrete topology the supernatural order is the prime
factorization of `Nat.card G`. -/
@[simp]
theorem profiniteOrder_apply_of_finite [DiscreteTopology G] [Finite G] (p : Nat.Primes) :
    profiniteOrder G p = (padicValNat p (Nat.card G) : ℕ∞) := by
  have : Fact (p : ℕ).Prime := ⟨p.prop⟩
  have hcard : Nat.card G ≠ 0 := Nat.card_pos.ne'
  rw [profiniteOrder_apply]
  refine le_antisymm (iSup_le fun U ↦ ?_) ?_
  · have hquot : Nat.card (G ⧸ U.toSubgroup) ≠ 0 := Nat.card_pos.ne'
    have hdvd : Nat.card (G ⧸ U.toSubgroup) ∣ Nat.card G := by
      rw [← Subgroup.index_eq_card]
      exact U.toSubgroup.index_dvd_card
    have hfact := Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd hquot hcard).mpr hdvd) p
    rw [Nat.factorization_def _ p.prop, Nat.factorization_def _ p.prop] at hfact
    exact_mod_cast hfact
  · -- The trivial subgroup is open normal, and `G ⧸ ⊥` recovers `G`.
    let U : OpenNormalSubgroup G :=
      { toOpenSubgroup := ⟨⊥, isOpen_discrete _⟩
        isNormal' := inferInstance }
    have hcardU : Nat.card (G ⧸ U.toSubgroup) = Nat.card G :=
      Nat.card_congr QuotientGroup.quotientBot.toEquiv
    calc (padicValNat p (Nat.card G) : ℕ∞)
        = (padicValNat p (Nat.card (G ⧸ U.toSubgroup)) : ℕ∞) := by rw [hcardU]
      _ ≤ _ := le_iSup (fun U : OpenNormalSubgroup G ↦
            (padicValNat p (Nat.card (G ⧸ U.toSubgroup)) : ℕ∞)) U

/-- The trivial group has order `1`. -/
@[simp]
theorem profiniteOrder_of_subsingleton (G : Type u) [Group G] [TopologicalSpace G]
    [Subsingleton G] : profiniteOrder G = 1 := by
  ext p
  rw [Supernatural.one_apply, profiniteOrder_apply_eq_zero_iff]
  intro U
  have hsub : Subsingleton (G ⧸ U.toSubgroup) :=
    (QuotientGroup.mk'_surjective U.toSubgroup).subsingleton
  rw [Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩]
  simp

/-- A profinite group has order `1` exactly when it is trivial: an open normal subgroup whose
quotient has order `1` is the whole group, and the open normal subgroups of a profinite group
intersect in the trivial subgroup. -/
theorem profiniteOrder_eq_one_iff [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] : profiniteOrder G = 1 ↔ Subsingleton G := by
  refine ⟨fun h ↦ ?_, fun _ ↦ profiniteOrder_of_subsingleton G⟩
  have htop : ∀ U : OpenNormalSubgroup G, U.toSubgroup = ⊤ := by
    intro U
    rw [← Subgroup.index_eq_one, Subgroup.index_eq_card]
    by_contra hne
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
    have : Fact q.Prime := ⟨hq⟩
    have hzero : padicValNat q (Nat.card (G ⧸ U.toSubgroup)) = 0 :=
      (profiniteOrder_apply_eq_zero_iff G ⟨q, hq⟩).mp
        (by rw [h]; exact Supernatural.one_apply _) U
    exact (dvd_iff_padicValNat_ne_zero Nat.card_pos.ne').mp hqdvd hzero
  have hone : ∀ a : G, a = 1 := fun a ↦
    Subgroup.eq_one_of_mem_iInf_openNormalSubgroup fun U ↦ by
      rw [htop U]; exact Subgroup.mem_top a
  exact ⟨fun a b ↦ by rw [hone a, hone b]⟩

section ProP

variable (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

/-- A compact topological group is pro-`p` exactly when its supernatural order is supported at
`p`, that is, when every other prime has vanishing exponent. -/
theorem isProP_iff_profiniteOrder_apply_eq_zero :
    IsProP p G ↔ ∀ q : Nat.Primes, (q : ℕ) ≠ p → profiniteOrder G q = 0 := by
  constructor
  · intro hG q hq
    have : Fact (q : ℕ).Prime := ⟨q.prop⟩
    rw [profiniteOrder_apply_eq_zero_iff]
    intro U
    obtain ⟨n, hn⟩ := (isProP_def.mp hG U).exists_card_eq
    refine padicValNat.eq_zero_of_not_dvd fun hdvd ↦ hq ?_
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq q.prop Fact.out).mp (q.prop.dvd_of_dvd_pow hdvd)
  · intro h
    rw [isProP_def]
    intro U
    have hzero : Nat.card (G ⧸ U.toSubgroup) ≠ 0 := Nat.card_pos.ne'
    refine IsPGroup.of_card (n := (Nat.card (G ⧸ U.toSubgroup)).primeFactorsList.length) ?_
    refine Nat.eq_prime_pow_of_unique_prime_dvd hzero fun {d} hd hdvd ↦ ?_
    by_contra hdp
    have : Fact d.Prime := ⟨hd⟩
    exact (dvd_iff_padicValNat_ne_zero hzero).mp hdvd
      ((profiniteOrder_apply_eq_zero_iff G ⟨d, hd⟩).mp (h ⟨d, hd⟩ hdp) U)

end ProP

/-- A compact topological group is pro-`p` exactly when the prime-to-`p` part of its
supernatural order is trivial. -/
theorem isProP_iff_primeToPart_profiniteOrder_eq_one (p : Nat.Primes) (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] :
    IsProP p G ↔ Supernatural.primeToPart p (profiniteOrder G) = 1 := by
  have : Fact (p : ℕ).Prime := ⟨p.prop⟩
  rw [isProP_iff_profiniteOrder_apply_eq_zero]
  constructor
  · intro h
    ext q
    rcases eq_or_ne q p with rfl | hq
    · simp
    · rw [Supernatural.primeToPart_apply_of_ne hq, Supernatural.one_apply]
      exact h q fun hqp ↦ hq (Subtype.ext hqp)
  · intro h q hq
    have hne : q ≠ p := fun hqp ↦ hq (congrArg Subtype.val hqp)
    have := congrFun h q
    rwa [Supernatural.primeToPart_apply_of_ne hne, Supernatural.one_apply] at this

end TauCeti
