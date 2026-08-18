/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.GaloisDescent
public import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# Galois invariants of a group algebra

Let `L/k` be a Galois extension and let `M` be an abelian group carrying an integral
representation of `Gal(L/k)`. The simultaneous action on coefficients and exponents of
`L[Multiplicative M]` has a fixed `k`-subalgebra. This file constructs that subalgebra and proves
that the Hopf operations preserve the corresponding descent data.

The counit of an invariant element is fixed by every automorphism of `L/k`, hence belongs to `k`.
The antipode preserves the invariant subalgebra. Comultiplication lands in the fixed submodule of
the tensor square for the diagonal semilinear action. The latter is deliberately not identified
here with the tensor square of the invariant subalgebra: that identification is the faithfully
flat scalar-extension theorem needed in the next descent step.

## Main declarations

* `TauCeti.GaloisDescent.groupAlgebraInvariants`: the fixed `k`-subalgebra of the split group
  algebra.
* `TauCeti.GaloisDescent.groupAlgebraInvariantsCounit`: its counit with values in `k`.
* `TauCeti.GaloisDescent.groupAlgebraInvariantsAntipode`: the antipode restricted to invariants.
* `TauCeti.GaloisDescent.groupAlgebraTensorInvariants`: fixed tensors for the diagonal action.
* `TauCeti.GaloisDescent.groupAlgebraInvariantsComul`: comultiplication from invariant elements to
  invariant tensors.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Corollary 12.24.

This is the invariant-algebra step in Layer 4, "Tori: split and non-split", of the
ReductiveGroups roadmap. It follows the semilinear group-algebra action and precedes the theorem
identifying scalar extension of the invariant algebra with the original split coordinate algebra.
-/

public section

open scoped TensorProduct TauCeti.GaloisDescent

namespace TauCeti.GaloisDescent

universe u_k u_L u_M

variable {k : Type u_k} {L : Type u_L} {M : Type u_M}
variable [Field k] [Field L] [Algebra k L]
variable [AddCommGroup M]

/-- The fixed `k`-subalgebra of `L[Multiplicative M]` for the simultaneous action on
coefficients and exponents. -/
noncomputable def groupAlgebraInvariants
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Subalgebra k (MonoidAlgebra L (Multiplicative M)) where
  carrier := {x | ∀ sigma, groupAlgebraAction rho sigma x = x}
  zero_mem' sigma := map_zero _
  one_mem' sigma := map_one _
  add_mem' {x y} hx hy sigma := by rw [map_add, hx sigma, hy sigma]
  mul_mem' {x y} hx hy sigma := by rw [map_mul, hx sigma, hy sigma]
  algebraMap_mem' r sigma := (groupAlgebraAction rho sigma).commutes r

/-- Membership in the invariant subalgebra means being fixed by every automorphism of `L/k`. -/
@[simp]
theorem mem_groupAlgebraInvariants_iff
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : MonoidAlgebra L (Multiplicative M)) :
    x ∈ groupAlgebraInvariants rho ↔
      ∀ sigma, groupAlgebraAction rho sigma x = x :=
  Iff.rfl

/-- Coefficientwise characterization of the invariant group algebra. The coefficient at `m`
after applying `sigma` is read at the inverse translate of `m`. -/
theorem mem_groupAlgebraInvariants_iff_coeff
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : MonoidAlgebra L (Multiplicative M)) :
    x ∈ groupAlgebraInvariants rho ↔
      ∀ (sigma : L ≃ₐ[k] L) (m : Multiplicative M),
        sigma (x.coeff (Multiplicative.ofAdd (rho sigma⁻¹ m.toAdd))) = x.coeff m := by
  rw [mem_groupAlgebraInvariants_iff]
  constructor
  · intro hx sigma m
    have h := congrArg (fun y : MonoidAlgebra L (Multiplicative M) ↦ y.coeff m) (hx sigma)
    simpa only [coeff_groupAlgebraAction] using h
  · intro hx sigma
    ext m
    simpa only [coeff_groupAlgebraAction] using hx sigma m

/-- A monomial is invariant if its coefficient and exponent are fixed by every Galois
automorphism. -/
theorem single_mem_groupAlgebraInvariants
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (m : Multiplicative M) (a : L)
    (hm : ∀ sigma : L ≃ₐ[k] L, rho sigma m.toAdd = m.toAdd)
    (ha : ∀ sigma : L ≃ₐ[k] L, sigma a = a) :
    MonoidAlgebra.single m a ∈ groupAlgebraInvariants rho := by
  rw [mem_groupAlgebraInvariants_iff]
  intro sigma
  rw [groupAlgebraAction_single, hm sigma, ofAdd_toAdd, ha sigma]

section Galois

variable [IsGalois k L]

/-- The original `L`-valued counit, restricted to invariant elements and with its codomain
restricted to the copy of `k` inside `L`. -/
private noncomputable def groupAlgebraInvariantsCounitToBot
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    groupAlgebraInvariants rho →ₐ[k] (⊥ : IntermediateField k L) := by
  let f : groupAlgebraInvariants rho →ₐ[k] L :=
    ((Bialgebra.counitAlgHom L
      (MonoidAlgebra L (Multiplicative M))).restrictScalars k).comp
        (groupAlgebraInvariants rho).val
  exact
  { toFun := fun x ↦ ⟨f x, by
      rw [InfiniteGalois.mem_bot_iff_fixed]
      intro sigma
      simp only [f, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Subalgebra.val_apply, Bialgebra.counitAlgHom_apply]
      rw [← counit_groupAlgebraAction rho sigma, x.property sigma]⟩
    map_one' := Subtype.ext f.map_one
    map_mul' x y := Subtype.ext (f.map_mul x y)
    map_zero' := Subtype.ext f.map_zero
    map_add' x y := Subtype.ext (f.map_add x y)
    commutes' r := Subtype.ext (f.commutes r) }

/-- The counit of the descended invariant algebra. Invariance forces the original `L`-valued
counit to lie in the image of `k`, and Galois fixed-field descent identifies that image with `k`.
-/
noncomputable def groupAlgebraInvariantsCounit
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    groupAlgebraInvariants rho →ₐ[k] k :=
  (IntermediateField.botEquiv k L).toAlgHom.comp
    (groupAlgebraInvariantsCounitToBot rho)

/-- Extending the descended counit value back to `L` recovers the ordinary group-algebra
counit. -/
@[simp]
theorem algebraMap_groupAlgebraInvariantsCounit
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : groupAlgebraInvariants rho) :
    algebraMap k L (groupAlgebraInvariantsCounit rho x) =
      Coalgebra.counit (R := L) (x : MonoidAlgebra L (Multiplicative M)) := by
  let y := groupAlgebraInvariantsCounitToBot rho x
  have h := congrArg Subtype.val ((IntermediateField.botEquiv k L).symm_apply_apply y)
  rw [groupAlgebraInvariantsCounit, AlgHom.comp_apply]
  calc
    algebraMap k L ((IntermediateField.botEquiv k L) y) =
        ((algebraMap k (⊥ : IntermediateField k L)
          ((IntermediateField.botEquiv k L) y) : (⊥ : IntermediateField k L)) : L) :=
      (IntermediateField.coe_algebraMap_apply (S := (⊥ : IntermediateField k L)) _).symm
    _ = (y : L) := h
    _ = Coalgebra.counit (R := L) (x : MonoidAlgebra L (Multiplicative M)) := rfl

end Galois

/-- The antipode preserves the invariant group algebra. -/
private theorem antipode_mem_groupAlgebraInvariants
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : groupAlgebraInvariants rho) :
    HopfAlgebra.antipode L (x : MonoidAlgebra L (Multiplicative M)) ∈
      groupAlgebraInvariants rho := by
  rw [mem_groupAlgebraInvariants_iff]
  intro sigma
  rw [← antipode_groupAlgebraAction rho sigma, x.property sigma]

/-- The algebra homomorphism underlying the restricted antipode. -/
private noncomputable def groupAlgebraInvariantsAntipodeHom
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    groupAlgebraInvariants rho →ₐ[k] groupAlgebraInvariants rho :=
  ((((HopfAlgebra.antipodeAlgHom L
      (MonoidAlgebra L (Multiplicative M))).restrictScalars k).comp
        (groupAlgebraInvariants rho).val).codRestrict
          (groupAlgebraInvariants rho) fun x ↦ antipode_mem_groupAlgebraInvariants rho x)

private theorem coe_groupAlgebraInvariantsAntipodeHom_apply
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : groupAlgebraInvariants rho) :
    (groupAlgebraInvariantsAntipodeHom rho x : MonoidAlgebra L (Multiplicative M)) =
      HopfAlgebra.antipode L (x : MonoidAlgebra L (Multiplicative M)) := by
  have h := AlgHom.congr_fun
    (AlgHom.val_comp_codRestrict
      (((HopfAlgebra.antipodeAlgHom L
        (MonoidAlgebra L (Multiplicative M))).restrictScalars k).comp
          (groupAlgebraInvariants rho).val)
      (groupAlgebraInvariants rho) fun x ↦ antipode_mem_groupAlgebraInvariants rho x) x
  simpa only [groupAlgebraInvariantsAntipodeHom, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Subalgebra.val_apply,
    HopfAlgebra.antipodeAlgHom_apply] using h

/-- The group-algebra antipode restricted to the Galois-invariant subalgebra. -/
noncomputable def groupAlgebraInvariantsAntipode
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    groupAlgebraInvariants rho ≃ₐ[k] groupAlgebraInvariants rho := by
  exact AlgEquiv.ofAlgHom (groupAlgebraInvariantsAntipodeHom rho)
    (groupAlgebraInvariantsAntipodeHom rho)
    (AlgHom.ext fun x ↦ by
      rw [AlgHom.comp_apply, AlgHom.id_apply]
      apply Subtype.ext
      rw [coe_groupAlgebraInvariantsAntipodeHom_apply,
        coe_groupAlgebraInvariantsAntipodeHom_apply,
        HopfAlgebra.antipode_antipode])
    (AlgHom.ext fun x ↦ by
      rw [AlgHom.comp_apply, AlgHom.id_apply]
      apply Subtype.ext
      rw [coe_groupAlgebraInvariantsAntipodeHom_apply,
        coe_groupAlgebraInvariantsAntipodeHom_apply,
        HopfAlgebra.antipode_antipode])

/-- The restricted antipode acts by the ordinary group-algebra antipode. -/
@[simp]
theorem groupAlgebraInvariantsAntipode_apply
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : groupAlgebraInvariants rho) :
    (groupAlgebraInvariantsAntipode rho x : MonoidAlgebra L (Multiplicative M)) =
      HopfAlgebra.antipode L (x : MonoidAlgebra L (Multiplicative M)) :=
  by
    simpa only [groupAlgebraInvariantsAntipode, AlgEquiv.ofAlgHom_apply] using
      coe_groupAlgebraInvariantsAntipodeHom_apply rho x

/-- The antipode on the invariant algebra is involutive. -/
@[simp]
theorem groupAlgebraInvariantsAntipode_apply_apply
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : groupAlgebraInvariants rho) :
    groupAlgebraInvariantsAntipode rho (groupAlgebraInvariantsAntipode rho x) = x := by
  apply Subtype.ext
  simp

/-- The restricted antipode equivalence is its own inverse. -/
@[simp]
theorem groupAlgebraInvariantsAntipode_symm
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    (groupAlgebraInvariantsAntipode rho).symm = groupAlgebraInvariantsAntipode rho := by
  apply AlgEquiv.ext
  intro x
  apply (groupAlgebraInvariantsAntipode rho).injective
  rw [AlgEquiv.apply_symm_apply, groupAlgebraInvariantsAntipode_apply_apply]

/-- The fixed `k`-submodule of the tensor square for the diagonal semilinear Galois action. -/
noncomputable def groupAlgebraTensorInvariants
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Submodule k
      (MonoidAlgebra L (Multiplicative M) ⊗[L]
        MonoidAlgebra L (Multiplicative M)) where
  carrier := {t | ∀ sigma, groupAlgebraTensorActionSemilinearEquiv rho sigma t = t}
  zero_mem' sigma := map_zero _
  add_mem' {x y} hx hy sigma := by rw [map_add, hx sigma, hy sigma]
  smul_mem' r x hx sigma := by
    rw [← IsScalarTower.algebraMap_smul L r x,
      (groupAlgebraTensorActionSemilinearEquiv rho sigma).map_smulₛₗ]
    change sigma (algebraMap k L r) •
        groupAlgebraTensorActionSemilinearEquiv rho sigma x =
      algebraMap k L r • x
    rw [sigma.commutes, hx sigma, IsScalarTower.algebraMap_smul L r x]

/-- Membership among invariant tensors means being fixed by the diagonal action. -/
@[simp]
theorem mem_groupAlgebraTensorInvariants_iff
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (t : MonoidAlgebra L (Multiplicative M) ⊗[L]
      MonoidAlgebra L (Multiplicative M)) :
    t ∈ groupAlgebraTensorInvariants rho ↔
      ∀ sigma, groupAlgebraTensorActionSemilinearEquiv rho sigma t = t :=
  Iff.rfl

/-- Comultiplication sends an invariant element to a tensor fixed by the diagonal action. -/
private theorem comul_mem_groupAlgebraTensorInvariants
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : groupAlgebraInvariants rho) :
    Coalgebra.comul (R := L) (x : MonoidAlgebra L (Multiplicative M)) ∈
      groupAlgebraTensorInvariants rho := by
  rw [mem_groupAlgebraTensorInvariants_iff]
  intro sigma
  rw [← comul_groupAlgebraAction rho sigma, x.property sigma]

/-- The linear map underlying comultiplication into invariant tensors. -/
private noncomputable def groupAlgebraInvariantsComulLinearMap
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    groupAlgebraInvariants rho →ₗ[k] groupAlgebraTensorInvariants rho :=
  ((((Coalgebra.comul (R := L)
      (A := MonoidAlgebra L (Multiplicative M))).restrictScalars k).comp
        (groupAlgebraInvariants rho).val.toLinearMap).codRestrict
          (groupAlgebraTensorInvariants rho) fun x ↦
            comul_mem_groupAlgebraTensorInvariants rho x)

private theorem coe_groupAlgebraInvariantsComulLinearMap_apply
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : groupAlgebraInvariants rho) :
    (groupAlgebraInvariantsComulLinearMap rho x :
        MonoidAlgebra L (Multiplicative M) ⊗[L]
          MonoidAlgebra L (Multiplicative M)) =
      Coalgebra.comul (R := L) (x : MonoidAlgebra L (Multiplicative M)) := by
  have h := LinearMap.congr_fun
    (LinearMap.subtype_comp_codRestrict
      (f := ((Coalgebra.comul (R := L)
        (A := MonoidAlgebra L (Multiplicative M))).restrictScalars k).comp
          (groupAlgebraInvariants rho).val.toLinearMap)
      (groupAlgebraTensorInvariants rho) fun x ↦
        comul_mem_groupAlgebraTensorInvariants rho x) x
  simpa only [groupAlgebraInvariantsComulLinearMap, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply,
    Subalgebra.val_apply] using h

/-- Comultiplication from invariant elements to tensors invariant under the diagonal action.

Identifying the codomain with the tensor square of `groupAlgebraInvariants rho` is the subsequent
faithfully flat descent step. -/
noncomputable def groupAlgebraInvariantsComul
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    groupAlgebraInvariants rho →ₗ[k] groupAlgebraTensorInvariants rho :=
  groupAlgebraInvariantsComulLinearMap rho

/-- The restricted comultiplication acts by the ordinary group-algebra comultiplication. -/
@[simp]
theorem groupAlgebraInvariantsComul_apply
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : groupAlgebraInvariants rho) :
    (groupAlgebraInvariantsComul rho x :
        MonoidAlgebra L (Multiplicative M) ⊗[L]
          MonoidAlgebra L (Multiplicative M)) =
      Coalgebra.comul (R := L) (x : MonoidAlgebra L (Multiplicative M)) :=
  by
    exact coe_groupAlgebraInvariantsComulLinearMap_apply rho x

end TauCeti.GaloisDescent
