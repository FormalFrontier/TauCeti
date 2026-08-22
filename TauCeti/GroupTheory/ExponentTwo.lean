/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Exponent
import Mathlib.Order.Preorder.Finite

/-!
# The index-two subgroups of a group of exponent two separate its points

A finite group `G` all of whose elements satisfy `g ^ 2 = 1` is an elementary abelian `2`-group,
that is, an `𝔽₂`-vector space written multiplicatively. Its subgroups of index `2` are the
hyperplanes, and the point of this file is that they **separate points**: every `σ ≠ 1` is avoided
by some index-two subgroup, equivalently the intersection of all of them is trivial.

The proof is elementary and avoids setting up the vector-space structure. Take `H` maximal among
the (finitely many) subgroups not containing `σ`. If `b ∉ H` then `H ⊔ ⟨b⟩` is strictly larger, so
by maximality it contains `σ`; as `G` is commutative and `b ^ 2 = 1` the elements of `H ⊔ ⟨b⟩` are
`h` and `h * b` with `h ∈ H`, and `σ = h` is excluded, so `σ = h * b` and therefore `b * σ = h ∈ H`.
That is exactly the criterion `Subgroup.index_eq_two_iff` for `H` to have index two.

Commutativity is not an extra hypothesis: a group of exponent two is automatically abelian
(`Commute.of_orderOf_dvd_two`).

## Main results

* `TauCeti.mul_comm_of_sq_eq_one`: a group in which every element squares to `1` is commutative.
* `TauCeti.exists_index_eq_two_notMem`: in a finite group of exponent two, every `σ ≠ 1` lies
  outside some subgroup of index `2`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- **A group of exponent two is commutative.** -/
theorem mul_comm_of_sq_eq_one (h : ∀ g : G, g ^ 2 = 1) (a b : G) : a * b = b * a :=
  Commute.of_orderOf_dvd_two (fun g => orderOf_dvd_of_pow_eq_one (h g)) a b

/-- An integer power of an element of order dividing two is either `1` or that element. -/
theorem zpow_eq_one_or_eq_self {b : G} (hb : b ^ 2 = 1) (n : ℤ) : b ^ n = 1 ∨ b ^ n = b := by
  have hb2 : b ^ (2 : ℤ) = 1 := by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hb]
  have hred : b ^ n = b ^ (n % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod n 2]
    rw [zpow_add, zpow_mul, hb2, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [hred, h]
  · exact Or.inl (zpow_zero b)
  · exact Or.inr (zpow_one b)

/-- **Index-two subgroups separate the points of a group of exponent two.** In a finite group all
of whose elements square to `1`, every `σ ≠ 1` lies outside some subgroup of index `2`.

Equivalently: the intersection of the index-two subgroups — the Frattini subgroup of an elementary
abelian `2`-group — is trivial. -/
theorem exists_index_eq_two_notMem [Finite G] (hexp : ∀ g : G, g ^ 2 = 1) {σ : G} (hσ : σ ≠ 1) :
    ∃ H : Subgroup G, H.index = 2 ∧ σ ∉ H := by
  classical
  have hcomm := mul_comm_of_sq_eq_one hexp
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  -- Choose a subgroup maximal among those avoiding `σ`; the trivial subgroup is one such.
  obtain ⟨H, hHσ, hmax⟩ :=
    Set.Finite.exists_maximal (s := {H : Subgroup G | σ ∉ H}) (Set.toFinite _)
      ⟨⊥, by simpa using hσ⟩
  refine ⟨H, ?_, hHσ⟩
  rw [Subgroup.index_eq_two_iff]
  refine ⟨σ, fun b => ?_⟩
  by_cases hb : b ∈ H
  · -- Multiplying an element of `H` by `σ` leaves `H`, since `σ ∉ H`.
    refine Or.inr ⟨hb, fun hbσ => hHσ ?_⟩
    simpa using mul_mem (inv_mem hb) hbσ
  · -- Otherwise `H ⊔ ⟨b⟩` is strictly bigger than `H`, hence contains `σ` by maximality.
    refine Or.inl ⟨?_, hb⟩
    set N : Subgroup G := Subgroup.closure {b} with hN
    have hbN : b ∈ N := Subgroup.subset_closure rfl
    have : N.Normal := ⟨fun n hn g => by
      rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
    have hlt : H < H ⊔ N :=
      lt_of_le_of_ne le_sup_left fun heq => hb (heq ▸ Subgroup.mem_sup_right hbN)
    have hσmem : σ ∈ H ⊔ N := by
      by_contra hcon
      exact absurd (hmax hcon le_sup_left) (not_le_of_gt hlt)
    -- Read off the normal form `σ = h * bⁿ` and use `b ^ 2 = 1`.
    rw [← SetLike.mem_coe, Subgroup.mul_normal H N, Set.mem_mul] at hσmem
    obtain ⟨h, hh, m, hm, hσeq⟩ := hσmem
    obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.mp hm
    rcases zpow_eq_one_or_eq_self (hexp b) n with hbn | hbn
    · exact absurd (show σ ∈ H by rw [← hσeq, hbn, mul_one]; exact hh) hHσ
    · rw [← hσeq, hbn, ← mul_assoc, hcomm b h, mul_assoc, ← sq, hexp b, mul_one]
      exact hh

end TauCeti
