/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.NumberTheory.Supernatural
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup

/-!
# The supernatural order of a profinite group

The order of a profinite group is the least common multiple, in the supernatural-number
lattice, of the orders of all its continuous finite quotients.  We define it primewise using
the quotients by open normal subgroups and identify it with the supremum of their finite
supernatural orders.

For a finite group with the discrete topology, the trivial subgroup occurs among the open
normal subgroups.  Its quotient is the whole group, while every other quotient has order
dividing the group order.  Consequently the supernatural order recovers the ordinary finite
order exactly.

## Main results

* `profiniteOrder`: the supernatural order, defined from the `Nat.card` of quotients by open
  normal subgroups.
* `profiniteOrder_eq_iSup_ofNat`: its description as the supremum of the embedded quotient
  orders.
* `profiniteOrder_le_of_surjective`: continuous surjections do not increase supernatural
  order.
* `profiniteOrder_congr`: topological group isomorphisms preserve supernatural order.
* `profiniteOrder_eq_of_finite`: agreement with `Nat.card` for a finite discrete group.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

universe u v

/-- The supernatural number whose exponent at a prime is the supremum of the corresponding
valuations of the `Nat.card` of all quotients by open normal subgroups.  For a profinite group,
this is its order. -/
noncomputable def profiniteOrder (G : Type u) [Group G] [TopologicalSpace G] : Supernatural :=
  Supernatural.ofFun fun p ↦
    ⨆ U : OpenNormalSubgroup G, (padicValNat p (Nat.card (G ⧸ U.toSubgroup)) : ℕ∞)

/-- The exponent of a prime in `profiniteOrder` is the supremum of the valuations of the
`Nat.card` of the quotients by open normal subgroups. -/
@[simp]
theorem profiniteOrder_apply (G : Type u) [Group G] [TopologicalSpace G] (p : Nat.Primes) :
    profiniteOrder G p =
      ⨆ U : OpenNormalSubgroup G, (padicValNat p (Nat.card (G ⧸ U.toSubgroup)) : ℕ∞) :=
  Supernatural.ofFun_apply _ _

section Functoriality

variable {G : Type u} {H : Type v} [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H]

/-- A continuous surjective homomorphism cannot increase `profiniteOrder`. -/
theorem profiniteOrder_le_of_surjective (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) : profiniteOrder H ≤ profiniteOrder G := by
  refine Supernatural.le_iff.mpr fun p ↦ ?_
  rw [profiniteOrder_apply]
  refine iSup_le fun U ↦ ?_
  let V := OpenNormalSubgroup.comap U f hf
  let q : G →* H ⧸ U.toSubgroup := (QuotientGroup.mk' U.toSubgroup).comp f
  have hqsurj : Function.Surjective q :=
    (QuotientGroup.mk'_surjective U.toSubgroup).comp hsurj
  have hker : q.ker = V.toSubgroup := by
    ext g
    simp [q, V]
  have hcard : Nat.card (H ⧸ U.toSubgroup) = Nat.card (G ⧸ V.toSubgroup) := by
    have heq := Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective q hqsurj).toEquiv
    simpa only [hker] using heq.symm
  rw [hcard]
  rw [profiniteOrder_apply]
  exact le_iSup
    (fun W : OpenNormalSubgroup G ↦
      (padicValNat p (Nat.card (G ⧸ W.toSubgroup)) : ℕ∞)) V

/-- Topologically isomorphic groups have the same supernatural order. -/
theorem profiniteOrder_congr (e : G ≃ₜ* H) : profiniteOrder G = profiniteOrder H := by
  apply le_antisymm
  · exact profiniteOrder_le_of_surjective e.symm.toMulEquiv.toMonoidHom
      e.symm.continuous e.symm.surjective
  · exact profiniteOrder_le_of_surjective e.toMulEquiv.toMonoidHom
      e.continuous e.surjective

/-- Passing to a quotient cannot increase `profiniteOrder`. -/
theorem profiniteOrder_quotient_le (N : Subgroup G) [N.Normal] :
    profiniteOrder (G ⧸ N) ≤ profiniteOrder G :=
  profiniteOrder_le_of_surjective (QuotientGroup.mk' N) QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective N)

end Functoriality

section Profinite

variable (G : Type u) [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [CompactSpace G]

/-- The supernatural order is the supremum of the ordinary orders of the finite continuous
quotients, embedded into the supernatural numbers. -/
theorem profiniteOrder_eq_iSup_ofNat :
    profiniteOrder G =
      ⨆ U : OpenNormalSubgroup G,
        Supernatural.ofNat
          (⟨Nat.card (G ⧸ U.toSubgroup), Nat.card_pos⟩ : ℕ+) := by
  ext p
  rw [profiniteOrder_apply, Supernatural.iSup_apply]
  congr 1
  funext U
  exact
    (Supernatural.ofNat_apply
      (⟨Nat.card (G ⧸ U.toSubgroup), Nat.card_pos⟩ : ℕ+) p).symm

/-- The supernatural order is bounded by `n` exactly when the order of every finite continuous
quotient is bounded by `n`. -/
@[simp]
theorem profiniteOrder_le_iff {n : Supernatural} :
    profiniteOrder G ≤ n ↔
      ∀ U : OpenNormalSubgroup G,
        Supernatural.ofNat
            (⟨Nat.card (G ⧸ U.toSubgroup), Nat.card_pos⟩ : ℕ+) ≤ n := by
  rw [profiniteOrder_eq_iSup_ofNat]
  exact iSup_le_iff

/-- The ordinary order of each finite continuous quotient divides `profiniteOrder G`. -/
theorem ofNat_card_quotient_le_profiniteOrder (U : OpenNormalSubgroup G) :
    Supernatural.ofNat (⟨Nat.card (G ⧸ U.toSubgroup), Nat.card_pos⟩ : ℕ+) ≤
      profiniteOrder G := by
  rw [profiniteOrder_eq_iSup_ofNat]
  exact le_iSup
    (fun V : OpenNormalSubgroup G ↦
      Supernatural.ofNat (⟨Nat.card (G ⧸ V.toSubgroup), Nat.card_pos⟩ : ℕ+)) U

end Profinite

section Finite

variable (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G]

/-- On a finite group with the discrete topology, supernatural order is the prime
factorization of the ordinary group order. -/
@[simp]
theorem profiniteOrder_eq_of_finite :
    profiniteOrder G = Supernatural.ofNat (⟨Nat.card G, Nat.card_pos⟩ : ℕ+) := by
  rw [profiniteOrder_eq_iSup_ofNat]
  apply le_antisymm
  · refine iSup_le fun U ↦ (Supernatural.ofNat_le_ofNat_iff).2 ?_
    apply PNat.dvd_iff.mpr
    simpa only [PNat.mk_coe, U.toSubgroup.index_eq_card] using
      U.toSubgroup.index_dvd_card
  · let U := openNormalSubgroupBot G
    refine le_iSup_of_le U ?_
    have hcard : Nat.card (G ⧸ U.toSubgroup) = Nat.card G := by
      simpa [U] using Nat.card_congr QuotientGroup.quotientBot.toEquiv
    exact le_of_eq <| congrArg Supernatural.ofNat <| Subtype.ext hcard.symm

/-- Pointwise form of `profiniteOrder_eq_of_finite`.  Its `simp` priority is above that of
`profiniteOrder_apply`, so that a finite discrete group simplifies to the valuation of its
order rather than to the defining supremum. -/
@[simp high]
theorem profiniteOrder_apply_of_finite (p : Nat.Primes) :
    profiniteOrder G p = (padicValNat p (Nat.card G) : ℕ∞) := by
  rw [profiniteOrder_eq_of_finite]
  exact Supernatural.ofNat_apply _ _

end Finite

end TauCeti
