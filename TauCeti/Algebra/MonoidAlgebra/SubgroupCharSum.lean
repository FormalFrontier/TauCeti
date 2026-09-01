/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Character sums over a subgroup

For a finite subgroup `H` of a group `G` and a multiplicative character `χ : G →* k`, this file
studies the element `∑_{h ∈ H} χ(h) h` of the group algebra `k[G]`, here
`TauCeti.subgroupCharSum χ H`.

Two instances of it occur throughout representation theory, and are what this file exists to
share: the **norm element** `∑_{h ∈ H} h` of a subgroup, which is `χ = 1`, and the **signed sum**
`∑_{h ∈ H} sgn(h) h` of a subgroup of a permutation group, which is `χ = sgn`.  The row
symmetrizer and the column antisymmetrizer of a Young tableau are exactly these two.

Everything here follows from `χ` being multiplicative; no assumption that `χ` takes values in
square roots of `1` is needed, even for the square.  The translation laws say that left or right
multiplication by `p ∈ H` rescales the sum by `χ(p⁻¹)`, which is proved by reindexing the sum
along the bijection `h ↦ p * h` of `H`; the square is then obtained by summing the left
translation law over `H`, where the scalars `χ(h) χ(h⁻¹) = χ(1) = 1` collapse and leave the order
of `H`.

## Main definitions and results

* `TauCeti.subgroupCharSum`: the character sum `∑_{h ∈ H} χ(h) h` in `k[G]`;
* `TauCeti.subgroupCharSum_coeff`: its coefficients are `χ` on `H` and zero off `H`;
* `TauCeti.single_mul_subgroupCharSum` and `TauCeti.subgroupCharSum_mul_single`: the two
  translation laws, scaling by `χ(p⁻¹)` for `p ∈ H`;
* `TauCeti.subgroupCharSum_mul_self`: the character sum squares to `Nat.card H` times itself;
* `TauCeti.subgroupCharSum_eq_one` and `TauCeti.subgroupCharSum_eq_sum_of_eq_top`: its values on
  the two extreme subgroups, `⊥` and `⊤`.
-/

public section

namespace TauCeti

variable {k G : Type*} [CommSemiring k] [Group G] (χ : G →* k) (H : Subgroup G) [Fintype H]

/-- The **character sum** `∑_{h ∈ H} χ(h) h` of a multiplicative character `χ` over a finite
subgroup `H`, as an element of the group algebra `k[G]`. -/
noncomputable def subgroupCharSum : MonoidAlgebra k G :=
  ∑ h : H, χ (h : G) • MonoidAlgebra.of k G (h : G)

/-- The character sum is the `χ`-weighted sum of the basis elements indexed by `H`. -/
theorem subgroupCharSum_def :
    subgroupCharSum χ H = ∑ h : H, χ (h : G) • MonoidAlgebra.of k G (h : G) :=
  (rfl)

/-- The coefficient of a group element in the character sum is `χ` on `H` and zero off `H`. -/
@[simp]
theorem subgroupCharSum_coeff [DecidablePred (· ∈ H)] (g : G) :
    (subgroupCharSum χ H).coeff g = if g ∈ H then χ g else 0 := by
  rw [subgroupCharSum_def, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single,
    smul_eq_mul]
  by_cases hg : g ∈ H
  · rw [ite_eq_left hg, Finset.sum_eq_single (⟨g, hg⟩ : H)]
    · rw [Finsupp.single_eq_same, mul_one]
    · exact fun h _ hh => by
        rw [Finsupp.single_eq_of_ne' fun e => hh (Subtype.ext e), mul_zero]
    · simp
  · rw [ite_eq_right hg]
    exact Finset.sum_eq_zero fun h _ => by
      rw [Finsupp.single_eq_of_ne' fun e : (h : G) = g => hg (e ▸ h.property), mul_zero]

/-- Left multiplication by a member of `H` scales the character sum by `χ` of its inverse. -/
@[simp]
theorem single_mul_subgroupCharSum (p : H) :
    MonoidAlgebra.single (p : G) 1 * subgroupCharSum χ H =
      χ ((p : G)⁻¹) • subgroupCharSum χ H := by
  rw [subgroupCharSum_def, ← MonoidAlgebra.of_apply, Finset.mul_sum, Finset.smul_sum]
  simp_rw [mul_smul_comm, ← (MonoidAlgebra.of k G).map_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft p)
  intro h
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, smul_smul]
  rw [← mul_assoc, map_mul_eq_one χ (inv_mul_cancel (p : G)), one_mul]

/-- Right multiplication by a member of `H` scales the character sum by `χ` of its inverse. -/
@[simp]
theorem subgroupCharSum_mul_single (p : H) :
    subgroupCharSum χ H * MonoidAlgebra.single (p : G) 1 =
      χ ((p : G)⁻¹) • subgroupCharSum χ H := by
  rw [subgroupCharSum_def, ← MonoidAlgebra.of_apply, Finset.sum_mul, Finset.smul_sum]
  simp_rw [smul_mul_assoc, ← (MonoidAlgebra.of k G).map_mul]
  apply Fintype.sum_equiv (Equiv.mulRight p)
  intro h
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, smul_smul]
  rw [mul_left_comm, map_mul_eq_one χ (inv_mul_cancel (p : G)), mul_one]

/-- The character sum squares to the order of `H` times itself. -/
@[simp]
theorem subgroupCharSum_mul_self :
    subgroupCharSum χ H * subgroupCharSum χ H = Nat.card H • subgroupCharSum χ H := by
  nth_rewrite 1 [subgroupCharSum_def]
  rw [Finset.sum_mul]
  simp_rw [smul_mul_assoc, MonoidAlgebra.of_apply, single_mul_subgroupCharSum, smul_smul,
    ← map_mul, mul_inv_cancel, map_one, one_smul]
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- Over the trivial subgroup the character sum has the single term `χ 1 • 1`, so it is `1`. -/
theorem subgroupCharSum_eq_one (h : H = ⊥) : subgroupCharSum χ H = 1 := by
  classical
  ext g
  by_cases hg : g = 1
  · simp [subgroupCharSum_coeff, h, MonoidAlgebra.one_def, hg]
  · simp [subgroupCharSum_coeff, h, MonoidAlgebra.one_def, Subgroup.mem_bot, hg]

/-- The character sum over the whole group is the `χ`-weighted sum over the group. -/
theorem subgroupCharSum_eq_sum_of_eq_top [Fintype G] (h : H = ⊤) :
    subgroupCharSum χ H = ∑ g : G, χ g • MonoidAlgebra.of k G g := by
  rw [subgroupCharSum_def]
  refine Finset.sum_bij (fun h _ => (h : G)) (fun _ _ => Finset.mem_univ _)
    (fun _ _ _ _ hab => Subtype.ext hab) (fun g _ => ?_) fun _ _ => rfl
  exact ⟨⟨g, by rw [h]; exact Subgroup.mem_top g⟩, Finset.mem_univ _, rfl⟩

end TauCeti
