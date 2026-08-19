/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import TauCeti.LinearAlgebra.Dimension.DirectSum
public import TauCeti.LinearAlgebra.RootSystem.Positive

public section

/-!
# The dimension count of the root-space decomposition

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, and let `H` be a splitting Cartan subalgebra. The root-space decomposition
writes `L` as the internal direct sum of one root space for each weight of `H` on `L`; the zero
weight contributes `H` itself, and every other root space is a line
(`LieAlgebra.IsKilling.finrank_rootSpace_eq_one`). Counting dimensions there gives

`dim L = dim H + #Δ`,

and, after choosing a base of the root system, the parity identity

`dim L = dim H + 2 · #Δ⁺`,

because root negation exchanges the positive and the negative roots
(`TauCeti.two_mul_ncard_posRoots`). Both identities are stated additively, with no truncated
subtraction; the subtracted and added forms `dim L - dim H = 2 · #Δ⁺` and
`dim L + dim H = 2 · (dim H + #Δ⁺)` are then recorded separately, so that a consumer forming the
exponents `(dim L ± dim H) / 2` is dividing exactly.

The `dim H` summand comes from the zero root space, which for a Cartan subalgebra is `H` itself
(`LieAlgebra.zeroRootSubalgebra_eq_of_is_cartan`). `TauCeti.finrank_rootSpace_zero` records this at
the level of dimensions, covering also the degenerate case `H = ⊥`, where the zero functional is
not a weight at all and both sides vanish; that is why the sum below is split over `H.root` and its
complement rather than by removing a named zero weight, which need not exist.

## Main results

* `TauCeti.isInternal_rootSpace`: `L` is the internal direct sum of the root spaces of `H`, indexed
  by the weights of `H` on `L`.
* `TauCeti.finrank_rootSpace_zero`: the zero root space has the dimension of `H`.
* `TauCeti.finrank_eq_finrank_cartan_add_card_root`: **`dim L = dim H + #Δ`**, whence
  `TauCeti.finrank_cartan_le`.
* `TauCeti.card_root_eq_two_mul_ncard_posRoots`: `#Δ = 2 · #Δ⁺`, and `TauCeti.even_card_root` the
  parity of `#Δ` it gives.
* `TauCeti.finrank_eq_finrank_cartan_add_two_mul_ncard_posRoots` and
  `TauCeti.finrank_eq_finrank_cartan_add_two_mul_card_isPos`: **`dim L = dim H + 2 · #Δ⁺`**, with
  the positive roots counted as a set and as a `Finset`.
* `TauCeti.finrank_sub_finrank_cartan` and `TauCeti.finrank_add_finrank_cartan`: the two
  combinations `dim L ∓ dim H` are twice something, so halving them is exact.

## References

This is the numerical shadow of the root-space decomposition of Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, *"`L = H ⊕ ⨁_{α ∈ roots} Lα` with
`finrank_rootSpace_eq_one` making each `Lα` a line"*. It is also the parity half of the bookkeeping
pin `finrank_eq_rank_add_two_mul_card_isPos` of Layer 9 of
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`, *"the parity identity
`d = l + 2 · #Δ⁺`, stated additively so the exponents `(d ± l)/2` below are exact divisions"*. That
pin states the identity with `LieAlgebra.rank ℂ L` in place of `dim H`; comparing Mathlib's
`LieAlgebra.rank`, defined through the nilpotency degree of a generic element, with the dimension of
a Cartan subalgebra is a separate statement and is not proved here.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Springer GTM 9 (1972),
  §8.1 (the root-space decomposition) and §10.1 (the pairing of positive and negative roots).
-/

namespace TauCeti

open LieAlgebra LieModule Module

section RootSpaceDecomposition

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

omit [FiniteDimensional K L] [H.IsCartanSubalgebra] in
/-- Reading the dimension of a Lie submodule through its underlying submodule changes nothing.
This is the bridge between `TauCeti.finrank_eq_sum_finrank_of_isInternal`, which sums over
submodules, and Mathlib's root-space dimension lemmas, which are stated for the Lie submodule. -/
private theorem finrank_toSubmodule (N : LieSubmodule K H L) :
    finrank K N.toSubmodule = finrank K N :=
  rfl

/-- Membership in the `Finset` of roots of a Cartan subalgebra is nonvanishing of the weight. -/
theorem mem_root_iff {α : Weight K H L} : α ∈ H.root ↔ α.IsNonZero := by
  simp [LieSubalgebra.root]

open scoped Classical in
/-- **The root-space decomposition.** A finite-dimensional Lie algebra that is triangularizable
over a Cartan subalgebra `H` is the internal direct sum of the root spaces of `H`, indexed by the
weights of `H` on `L`: the roots, together with the zero weight whose root space is `H` itself. -/
theorem isInternal_rootSpace [LieModule.IsTriangularizable K H L] :
    DirectSum.IsInternal fun α : Weight K H L ↦ (rootSpace H (α : H → K)).toSubmodule := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [LieSubmodule.iSupIndep_toSubmodule]
    exact iSupIndep_genWeightSpace' K H L
  · rw [← LieSubmodule.iSup_toSubmodule, iSup_genWeightSpace_eq_top' K H L]
    simp

/-- **The zero root space is the Cartan subalgebra**, at the level of dimensions. When the zero
functional is not a weight of `H` on `L` both sides vanish, since then `H` itself is trivial. -/
theorem finrank_rootSpace_zero : finrank K (rootSpace H (0 : H → K)) = finrank K H := by
  have h : (rootSpace H (0 : H → K)).toSubmodule = H.toSubmodule := by
    rw [← LieAlgebra.coe_zeroRootSubalgebra K L H, zeroRootSubalgebra_eq_of_is_cartan K L H]
  exact congrArg (fun N : Submodule K L ↦ finrank K N) h

end RootSpaceDecomposition

section Killing

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- The root spaces indexed by the *nonzero* weights are lines, so they contribute `#Δ` in
total. -/
private theorem sum_finrank_rootSpace_root :
    ∑ α ∈ H.root, finrank K (rootSpace H (α : H → K)) = H.root.card := by
  rw [Finset.sum_congr rfl fun α hα ↦
    IsKilling.finrank_rootSpace_eq_one α ((mem_root_iff H).mp hα), Finset.sum_const, smul_eq_mul,
    mul_one]

omit [CharZero K] [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L] in
open scoped Classical in
/-- The root spaces indexed by the weights that are *not* roots contribute `dim H` in total: there
is at most one such weight, the zero one, and its root space is `H`. -/
private theorem sum_finrank_rootSpace_compl_root :
    ∑ α ∈ H.rootᶜ, finrank K (rootSpace H (α : H → K)) = finrank K H := by
  by_cases h0 : rootSpace H (0 : H → K) = ⊥
  · have hH : finrank K H = 0 := by
      rw [← finrank_rootSpace_zero H, ← finrank_toSubmodule, h0, LieSubmodule.bot_toSubmodule]
      simp
    have hempty : (H.rootᶜ : Finset (Weight K H L)) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun α hα ↦ Weight.genWeightSpace_ne_bot L α ?_
      rw [Finset.mem_compl, mem_root_iff, not_not] at hα
      rw [show (α : H → K) = 0 from hα]
      exact h0
    rw [hempty, Finset.sum_empty, hH]
  · have hsingle : (H.rootᶜ : Finset (Weight K H L)) = {⟨0, h0⟩} := by
      ext α
      rw [Finset.mem_compl, mem_root_iff, not_not, Finset.mem_singleton]
      refine ⟨fun hα ↦ Weight.ext fun x ↦ ?_, ?_⟩
      · rw [congr_fun (show (α : H → K) = 0 from hα) x]
        rfl
      · rintro rfl
        rfl
    rw [hsingle, Finset.sum_singleton]
    exact finrank_rootSpace_zero H

/-- **The dimension count of the root-space decomposition**: the dimension of a Lie algebra with
non-degenerate Killing form is the dimension of a Cartan subalgebra plus the number of roots. -/
theorem finrank_eq_finrank_cartan_add_card_root :
    finrank K L = finrank K H + H.root.card := by
  classical
  rw [finrank_eq_sum_finrank_of_isInternal (isInternal_rootSpace H)]
  simp only [finrank_toSubmodule]
  rw [← Finset.sum_compl_add_sum H.root fun α : Weight K H L ↦
      finrank K (rootSpace H (α : H → K)),
    sum_finrank_rootSpace_compl_root H, sum_finrank_rootSpace_root H]

/-- The dimension of a Cartan subalgebra is at most the dimension of the whole Lie algebra. -/
theorem finrank_cartan_le : finrank K H ≤ finrank K L :=
  finrank_eq_finrank_cartan_add_card_root H ▸ Nat.le_add_right _ _

/-- **The number of roots is twice the number of positive roots** for any base, since root
negation exchanges the positive and the negative roots. -/
theorem card_root_eq_two_mul_ncard_posRoots (b : (IsKilling.rootSystem H).Base) :
    H.root.card = 2 * (posRoots (IsKilling.rootSystem H) b).ncard := by
  rw [two_mul_ncard_posRoots, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- **The parity identity `d = l + 2 · #Δ⁺`**: the dimension of a Lie algebra with non-degenerate
Killing form is the dimension of a Cartan subalgebra plus twice the number of positive roots,
for any base of its root system. -/
theorem finrank_eq_finrank_cartan_add_two_mul_ncard_posRoots
    (b : (IsKilling.rootSystem H).Base) :
    finrank K L = finrank K H + 2 * (posRoots (IsKilling.rootSystem H) b).ncard := by
  rw [← card_root_eq_two_mul_ncard_posRoots H b]
  exact finrank_eq_finrank_cartan_add_card_root H

open scoped Classical in
/-- **The parity identity `d = l + 2 · #Δ⁺`**, with the positive roots counted as a `Finset` of the
root index type. -/
theorem finrank_eq_finrank_cartan_add_two_mul_card_isPos
    (b : (IsKilling.rootSystem H).Base) :
    finrank K L
      = finrank K H + 2 * (Finset.univ.filter fun i : H.root ↦ b.IsPos i).card := by
  rw [finrank_eq_finrank_cartan_add_two_mul_ncard_posRoots H b,
    show posRoots (IsKilling.rootSystem H) b
      = ↑(Finset.univ.filter fun i : H.root ↦ b.IsPos i) from Set.ext fun i ↦ by
        simp [mem_posRoots],
    Set.ncard_coe_finset]

/-- The number of roots is even: root negation pairs them up. No base has to be supplied, since
one always exists (`RootPairing.nonempty_base`). -/
theorem even_card_root : Even H.root.card :=
  let b := (IsKilling.rootSystem H).nonempty_base.some
  ⟨(posRoots (IsKilling.rootSystem H) b).ncard, by
    rw [card_root_eq_two_mul_ncard_posRoots H b, two_mul]⟩

/-- **`dim L - dim H` is twice the number of positive roots**, so halving it is exact. -/
theorem finrank_sub_finrank_cartan (b : (IsKilling.rootSystem H).Base) :
    finrank K L - finrank K H = 2 * (posRoots (IsKilling.rootSystem H) b).ncard := by
  have h := finrank_eq_finrank_cartan_add_two_mul_ncard_posRoots H b
  omega

/-- **`dim L + dim H` is twice `dim H` plus the number of positive roots**, so halving it is
exact. -/
theorem finrank_add_finrank_cartan (b : (IsKilling.rootSystem H).Base) :
    finrank K L + finrank K H
      = 2 * (finrank K H + (posRoots (IsKilling.rootSystem H) b).ncard) := by
  have h := finrank_eq_finrank_cartan_add_two_mul_ncard_posRoots H b
  omega

end Killing

end TauCeti
