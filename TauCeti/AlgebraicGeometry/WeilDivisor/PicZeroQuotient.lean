/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic

/-!
# The degree-zero divisor quotient model of abstract `Pic⁰`

This file adds a small Layer A bridge for the Jacobian roadmap.  The file
`TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic` defines the abstract divisor class group
`Cl(X)` of an order system and defines `Pic⁰` as the kernel of the descended weighted degree on
`Cl(X)`.  Classically, the same group is also described as degree-zero divisors modulo
principal divisors.  This file identifies those two descriptions.

For an order system `S` whose principal divisors have weighted degree zero, the natural map from
weighted-degree-zero divisors to `S.picZero w h`,

`D ↦ [D]`,

is surjective, and its kernel is the subgroup of weighted-degree-zero divisors whose underlying
divisor is principal.  The first isomorphism theorem then gives

`(weighted-degree-zero divisors) / (principal divisors) ≃+ Pic⁰`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, specifically the item
"Degree. ... Then `Pic⁰ X = ker deg` (as an abstract group; the functorial `Pic⁰` is defined
in Layer D)."  No external mathematics is vendored; the proof uses Tau Ceti's existing
`WeilDivisor`/`OrderSystem` API and Mathlib's quotient-group first isomorphism theorem.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

noncomputable section

/-! ### Weighted degree-zero divisors modulo principal divisors -/

/-- Principal divisors inside the weighted-degree-zero divisor group: a degree-zero
divisor belongs to this subgroup exactly when its underlying divisor is principal. -/
def principalSubgroupOfWeightedDegreeZero (w : X → ℤ) :
    AddSubgroup (weightedDegreeZeroSubgroup w) :=
  S.principalSubgroup.comap (weightedDegreeZeroSubgroup w).subtype

@[simp]
lemma mem_principalSubgroupOfWeightedDegreeZero {w : X → ℤ} {D : weightedDegreeZeroSubgroup w} :
    D ∈ S.principalSubgroupOfWeightedDegreeZero w ↔
      (D : WeilDivisor X) ∈ S.principalSubgroup :=
  Iff.rfl

/-- The natural map from weighted-degree-zero divisors to the abstract degree-zero divisor
class group `Pic⁰`, sending a divisor to its divisor class. -/
@[expose]
def weightedDegreeZeroClassHom (w : X → ℤ) (h : S.IsWeightedDegreeZero w) :
    weightedDegreeZeroSubgroup w →+ S.picZero w h where
  toFun D :=
    ⟨S.divisorClass (D : WeilDivisor X), by
      rw [divisorClass_mem_picZero]
      exact weightedDegree_coe_weightedDegreeZeroSubgroup w D⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' D E := by
    apply Subtype.ext
    simp

@[simp]
lemma coe_weightedDegreeZeroClassHom_apply {w : X → ℤ} (h : S.IsWeightedDegreeZero w)
    (D : weightedDegreeZeroSubgroup w) : (S.weightedDegreeZeroClassHom w h D : S.ClassGroup) =
      S.divisorClass (D : WeilDivisor X) :=
  rfl

lemma weightedDegreeZeroClassHom_apply {w : X → ℤ} (h : S.IsWeightedDegreeZero w)
    (D : weightedDegreeZeroSubgroup w) :
    S.weightedDegreeZeroClassHom w h D =
      ⟨S.divisorClass (D : WeilDivisor X), by
        rw [divisorClass_mem_picZero]
        exact weightedDegree_coe_weightedDegreeZeroSubgroup w D⟩ :=
  rfl

/-- The natural map from weighted-degree-zero divisors to `Pic⁰` is surjective: every
degree-zero divisor class has a weighted-degree-zero representative. -/
lemma weightedDegreeZeroClassHom_surjective {w : X → ℤ} (h : S.IsWeightedDegreeZero w) :
    Function.Surjective (S.weightedDegreeZeroClassHom w h) := by
  rintro ⟨c, hc⟩
  obtain ⟨D, rfl⟩ := S.divisorClass_surjective c
  refine ⟨⟨D, ?_⟩, ?_⟩
  · rw [mem_weightedDegreeZeroSubgroup]
    exact (S.divisorClass_mem_picZero w h).mp hc
  · rfl

@[simp]
lemma weightedDegreeZeroClassHom_eq_zero_iff {w : X → ℤ}
    (h : S.IsWeightedDegreeZero w) {D : weightedDegreeZeroSubgroup w} :
    S.weightedDegreeZeroClassHom w h D = 0 ↔
      (D : WeilDivisor X) ∈ S.principalSubgroup := by
  rw [Subtype.ext_iff]
  exact S.divisorClass_eq_zero_iff

/-- The kernel of the map from weighted-degree-zero divisors to `Pic⁰` is exactly the subgroup
of principal divisors inside the weighted-degree-zero divisor group. -/
lemma weightedDegreeZeroClassHom_ker {w : X → ℤ} (h : S.IsWeightedDegreeZero w) :
    (S.weightedDegreeZeroClassHom w h).ker =
      S.principalSubgroupOfWeightedDegreeZero w := by
  ext D
  rw [AddMonoidHom.mem_ker, mem_principalSubgroupOfWeightedDegreeZero,
    weightedDegreeZeroClassHom_eq_zero_iff]

/-- The quotient of weighted-degree-zero divisors by principal divisors is the abstract
degree-zero divisor class group `Pic⁰`. -/
@[expose]
def weightedDegreeZeroQuotientEquivPicZero (w : X → ℤ) (h : S.IsWeightedDegreeZero w) :
    weightedDegreeZeroSubgroup w ⧸ S.principalSubgroupOfWeightedDegreeZero w ≃+
      S.picZero w h :=
  (QuotientAddGroup.quotientAddEquivOfEq (S.weightedDegreeZeroClassHom_ker h).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (φ := S.weightedDegreeZeroClassHom w h)
      (S.weightedDegreeZeroClassHom_surjective h))

@[simp]
lemma weightedDegreeZeroQuotientEquivPicZero_mk {w : X → ℤ}
    (h : S.IsWeightedDegreeZero w) (D : weightedDegreeZeroSubgroup w) :
    S.weightedDegreeZeroQuotientEquivPicZero w h
      (QuotientAddGroup.mk D) = S.weightedDegreeZeroClassHom w h D := by
  simp only [weightedDegreeZeroQuotientEquivPicZero, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  -- The first-isomorphism equivalence is defined through `kerLift`, so unfold the composed
  -- equivalence to expose its quotient-map simp lemma.
  change QuotientAddGroup.kerLift (S.weightedDegreeZeroClassHom w h)
      (QuotientAddGroup.mk D) = S.weightedDegreeZeroClassHom w h D
  rw [QuotientAddGroup.kerLift_mk]

lemma coe_weightedDegreeZeroQuotientEquivPicZero_mk {w : X → ℤ}
    (h : S.IsWeightedDegreeZero w) (D : weightedDegreeZeroSubgroup w) :
    (S.weightedDegreeZeroQuotientEquivPicZero w h (QuotientAddGroup.mk D) : S.ClassGroup) =
      S.divisorClass (D : WeilDivisor X) := by
  simp

end

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
