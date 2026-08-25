/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic

/-!
# The kernel of the principal-divisor map

This file records the exactness at the rational-function side of the formal divisor-class
sequence built in `TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic`.

For an order system `S : OrderSystem X G`, the homomorphism
`S.principalHom : G →+ WeilDivisor X` sends a function to its principal divisor. Its kernel is
the subgroup of functions with zero order at every point. Quotienting `G` by this kernel gives
the abstract group of principal divisors, canonically identified with
`S.principalSubgroup`.

In geometric applications, `G` is the additive form of the multiplicative group of a function
field. After additional geometric input identifying the zero-principal-divisor functions with
constants, this quotient specializes to rational functions modulo constants, embedded as
principal divisors before taking the divisor class quotient.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, specifically the
"principal divisors" and "`Cl(X) ≅ Pic X`" prerequisite lane: the class group is the quotient by
principal divisors, and this file packages the source-side quotient that maps onto that
subgroup. It reuses Tau Ceti's `OrderSystem.principalHom` API and Mathlib's first isomorphism
theorem for quotient groups; no external mathematics is vendored.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

noncomputable section

/-! ### The kernel of the principal-divisor map -/

/-- The subgroup of functions whose principal divisor is zero.

In geometric applications this is the subgroup quotiented out before passing from rational
functions to principal divisors. Identifying it with constants requires additional geometric
input, such as a global-units or constant-field theorem. -/
abbrev principalKernel : AddSubgroup G :=
  S.principalHom.ker

lemma mem_principalKernel {g : G} :
    g ∈ S.principalKernel ↔ S.principalDivisor g = 0 := by
  simp only [principalKernel, AddMonoidHom.mem_ker, principalHom_apply]

/-- A function has zero principal divisor exactly when all of its orders vanish. -/
lemma mem_principalKernel_iff_forall_ord_eq_zero {g : G} :
    g ∈ S.principalKernel ↔ ∀ x, S.ord x g = 0 := by
  rw [mem_principalKernel]
  constructor
  · intro h x
    rw [← S.coeff_principalDivisor g x, h]
    simp
  · intro h
    ext x
    rw [S.coeff_principalDivisor, h x]
    simp

lemma zero_mem_principalKernel : (0 : G) ∈ S.principalKernel := by
  rw [mem_principalKernel]
  simp

lemma principalKernel_eq_bot_iff :
    S.principalKernel = ⊥ ↔ Function.Injective S.principalHom :=
  AddMonoidHom.ker_eq_bot_iff S.principalHom

/-- If the only function with zero principal divisor is zero, the principal-divisor map is
injective. -/
lemma principalHom_injective_of_principalKernel_eq_bot (h : S.principalKernel = ⊥) :
    Function.Injective S.principalHom :=
  S.principalKernel_eq_bot_iff.mp h

/-- An injective principal-divisor map has trivial kernel. -/
lemma principalKernel_eq_bot_of_principalHom_injective
    (h : Function.Injective S.principalHom) : S.principalKernel = ⊥ :=
  S.principalKernel_eq_bot_iff.mpr h

/-! ### Principal divisors as a quotient of functions -/

/-- The quotient of the function group by functions with zero principal divisor.

In geometric applications this is the group of rational functions modulo the subgroup with
zero principal divisor. Under further hypotheses identifying that subgroup with the base-field
constants, it specializes to the usual rational-functions-modulo-constants group. -/
abbrev PrincipalFunctionClass : Type _ :=
  G ⧸ S.principalKernel

/-- The principal divisor associated to a function class, as a homomorphism into all Weil
divisors. -/
def principalFunctionClassDivisor : S.PrincipalFunctionClass →+ WeilDivisor X :=
  QuotientAddGroup.kerLift S.principalHom

@[simp]
lemma principalFunctionClassDivisor_mk (g : G) :
    S.principalFunctionClassDivisor (QuotientAddGroup.mk g) = S.principalDivisor g := by
  rw [principalFunctionClassDivisor, QuotientAddGroup.kerLift_mk, principalHom_apply]

/-- The map from function classes to principal divisors is injective. -/
lemma principalFunctionClassDivisor_injective :
    Function.Injective S.principalFunctionClassDivisor :=
  QuotientAddGroup.kerLift_injective S.principalHom

/-- Every divisor attached to a function class is principal. -/
@[simp]
lemma principalFunctionClassDivisor_mem_principalSubgroup (q : S.PrincipalFunctionClass) :
    S.principalFunctionClassDivisor q ∈ S.principalSubgroup := by
  induction q using QuotientAddGroup.induction_on with
  | _ g => simp

/-- The image of function classes in all Weil divisors is exactly the subgroup of principal
divisors. -/
lemma principalFunctionClassDivisor_range :
    S.principalFunctionClassDivisor.range = S.principalSubgroup := by
  ext D
  constructor
  · rintro ⟨q, rfl⟩
    exact S.principalFunctionClassDivisor_mem_principalSubgroup q
  · intro hD
    rcases S.mem_principalSubgroup.mp hD with ⟨g, rfl⟩
    exact ⟨QuotientAddGroup.mk g, by simp⟩

/-- The quotient of functions by the zero-principal-divisor subgroup is canonically equivalent
to the subgroup of principal divisors. -/
def principalFunctionClassEquivPrincipalSubgroup :
    S.PrincipalFunctionClass ≃+ S.principalSubgroup :=
  (QuotientAddGroup.quotientKerEquivRange S.principalHom).trans
    (AddEquiv.addSubgroupCongr S.principalSubgroup_eq_range.symm)

@[simp]
lemma principalFunctionClassEquivPrincipalSubgroup_mk (g : G) :
    S.principalFunctionClassEquivPrincipalSubgroup (QuotientAddGroup.mk g) =
      ⟨S.principalDivisor g, S.principalDivisor_mem_principalSubgroup g⟩ :=
  Subtype.ext <| by
    simp only [principalFunctionClassEquivPrincipalSubgroup, AddEquiv.trans_apply,
      AddEquiv.addSubgroupCongr_apply, QuotientAddGroup.quotientKerEquivRange]
    exact S.principalHom_apply g

@[simp]
lemma coe_principalFunctionClassEquivPrincipalSubgroup (q : S.PrincipalFunctionClass) :
    ((S.principalFunctionClassEquivPrincipalSubgroup q : S.principalSubgroup) : WeilDivisor X) =
      S.principalFunctionClassDivisor q := by
  induction q using QuotientAddGroup.induction_on with
  | _ g => simp

@[simp]
lemma principalFunctionClassDivisor_eq_zero_iff {q : S.PrincipalFunctionClass} :
    S.principalFunctionClassDivisor q = 0 ↔ q = 0 :=
  S.principalFunctionClassDivisor_injective.eq_iff' (map_zero S.principalFunctionClassDivisor)

/-- Equality of principal divisors is equality of the corresponding function classes. -/
lemma principalDivisor_eq_iff_mk_eq_mk {g h : G} :
    S.principalDivisor g = S.principalDivisor h ↔
      QuotientAddGroup.mk g = (QuotientAddGroup.mk h : S.PrincipalFunctionClass) := by
  constructor
  · intro hgh
    apply S.principalFunctionClassDivisor_injective
    simpa using hgh
  · intro hgh
    simpa using congr_arg S.principalFunctionClassDivisor hgh

/-- Two functions define the same class modulo the zero-principal-divisor subgroup exactly when
their principal divisors are equal. -/
lemma mk_eq_mk_iff_principalDivisor_eq {g h : G} :
    QuotientAddGroup.mk g = (QuotientAddGroup.mk h : S.PrincipalFunctionClass) ↔
      S.principalDivisor g = S.principalDivisor h :=
  (S.principalDivisor_eq_iff_mk_eq_mk).symm

/-- A function class is zero exactly when the representative has zero principal divisor. -/
lemma mk_eq_zero_iff_principalDivisor_eq_zero {g : G} :
    (QuotientAddGroup.mk g : S.PrincipalFunctionClass) = 0 ↔ S.principalDivisor g = 0 := by
  rw [← principalFunctionClassDivisor_eq_zero_iff]
  simp

end

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
