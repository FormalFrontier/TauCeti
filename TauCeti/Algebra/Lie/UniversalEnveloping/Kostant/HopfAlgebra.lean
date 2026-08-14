/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.HopfAlgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Antipode
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Comultiplication

/-!
# The Kostant form as a Hopf algebra over the integers

The comultiplication, counit, and antipode of a rational universal enveloping algebra preserve
its Kostant integral form. This file assembles those three restrictions into a genuine
`HopfAlgebra ℤ` instance on the form. In particular, all coalgebra and antipode identities hold
integrally; they are not merely identities after extending scalars to `ℚ`.

The proof reflects each identity into the rational universal enveloping algebra, where it is one
of the standard Hopf algebra laws. For coassociativity this requires an injective map from the
integral triple tensor product into the rational triple tensor product. Its injectivity follows
from flatness over `ℤ`: the Kostant form is torsion-free because it is a subring of a rational
algebra, and tensor products of flat modules are flat.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.instHopfAlgebraKostantForm`: the Kostant form is a Hopf
  algebra over `ℤ`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantForm_comul` and
  `TauCeti.UniversalEnvelopingAlgebra.kostantForm_counit`: the bundled coalgebra maps are the
  previously constructed integral restrictions.
* `TauCeti.UniversalEnvelopingAlgebra.kostantForm_antipode`: the bundled antipode is the
  restriction of the rational universal-enveloping antipode.

## References

The Hopf order on the Kostant form is standard; see J. E. Humphreys, *Introduction to Lie
Algebras and Representation Theory*, §26, and J. C. Jantzen, *Representations of Algebraic
Groups*, II.1. This completes the Hopf-algebra packaging of the Kostant-form prerequisite for the
explicit Chevalley--Demazure construction in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, consumed by milestone L0 of the `CFSGStatement`
roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type v} {J : Type w}

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L
local notation "K" => kostantForm (L := L)

/-- The module structure on the tensor square of the Kostant form definitionally
aligned with its algebra structure; both canonical instances have the same action,
but iterated tensor maps must use one consistently. -/
local instance kostantTensorModule (e : I → L) (h : J → L) :
    Module ℤ (K e h ⊗[ℤ] K e h) := Algebra.toModule

/-! ## Faithful scalar extension for three tensor factors -/

private noncomputable def kostantTripleMap (e : I → L) (h : J → L) :
    K e h ⊗[ℤ] (K e h ⊗[ℤ] K e h) →ₗ[ℤ] U ⊗[ℚ] (U ⊗[ℚ] U) :=
  (TensorProduct.equivOfCompatibleSMul ℤ ℚ ℤ U (U ⊗[ℚ] U)).symm.toLinearMap.comp
    (TensorProduct.map (K e h).subtype.toIntAlgHom.toLinearMap
      (kostantTensorMap e h).toLinearMap)

@[simp]
private theorem kostantTripleMap_tmul (e : I → L) (h : J → L)
    (x : K e h) (t : K e h ⊗[ℤ] K e h) :
    kostantTripleMap e h (x ⊗ₜ[ℤ] t) =
      (x : U) ⊗ₜ[ℚ] kostantTensorMap e h t := by
  rfl

private theorem kostantTripleMap_injective (e : I → L) (h : J → L) :
    Function.Injective (kostantTripleMap e h) := by
  let : IsAddTorsionFree U := .of_module_rat U
  let : IsAddTorsionFree (U ⊗[ℚ] U) := .of_module_rat (U ⊗[ℚ] U)
  let : IsAddTorsionFree (K e h) :=
    Function.Injective.isAddTorsionFree (K e h).subtype.toAddMonoidHom
      (K e h).subtype_injective
  let : Module.Flat ℤ (K e h) := inferInstance
  let f : K e h →ₗ[ℤ] U := (K e h).subtype.toIntAlgHom.toLinearMap
  let g : K e h ⊗[ℤ] K e h →ₗ[ℤ] U ⊗[ℚ] U := (kostantTensorMap e h).toLinearMap
  have hinjective : Function.Injective (TensorProduct.map f g) :=
    TensorProduct.map_injective_of_flat_flat'
      (R := ℤ) f g (K e h).subtype_injective (kostantTensorMap_injective e h)
  intro x y hxy
  apply hinjective
  apply (TensorProduct.equivOfCompatibleSMul ℤ ℚ ℤ U (U ⊗[ℚ] U)).symm.injective
  exact hxy

private theorem kostantTripleMap_assoc_tmul (e : I → L) (h : J → L)
    (t : K e h ⊗[ℤ] K e h) (z : K e h) :
    kostantTripleMap e h
        (TensorProduct.assoc ℤ (K e h) (K e h) (K e h) (t ⊗ₜ[ℤ] z)) =
      TensorProduct.assoc ℚ U U U (kostantTensorMap e h t ⊗ₜ[ℚ] (z : U)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add x y hx hy =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
      rw [TensorProduct.assoc_tmul, kostantTripleMap_tmul]
      have ht := kostantTensorMap_tmul e h x y
      have ht' := kostantTensorMap_tmul e h y z
      rw [ht]
      rw [ht']
      rfl

private theorem kostantTripleMap_comul_rTensor (e : I → L) (h : J → L)
    (t : K e h ⊗[ℤ] K e h) :
    kostantTripleMap e h
        (TensorProduct.assoc ℤ (K e h) (K e h) (K e h)
          ((kostantFormComul e h).toLinearMap.rTensor (K e h) t)) =
      TensorProduct.assoc ℚ U U U
        (Coalgebra.comul.rTensor U (kostantTensorMap e h t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
      rw [LinearMap.rTensor_tmul, kostantTensorMap_tmul, LinearMap.rTensor_tmul,
        kostantTripleMap_assoc_tmul, AlgHom.toLinearMap_apply,
        kostantTensorMap_kostantFormComul_apply]

private theorem kostantTripleMap_comul_lTensor (e : I → L) (h : J → L)
    (t : K e h ⊗[ℤ] K e h) :
    kostantTripleMap e h ((kostantFormComul e h).toLinearMap.lTensor (K e h) t) =
      Coalgebra.comul.lTensor U (kostantTensorMap e h t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
      rw [LinearMap.lTensor_tmul, kostantTensorMap_tmul, LinearMap.lTensor_tmul,
        kostantTripleMap_tmul, AlgHom.toLinearMap_apply,
        kostantTensorMap_kostantFormComul_apply]

private theorem coe_lid_counit_rTensor (e : I → L) (h : J → L)
    (t : K e h ⊗[ℤ] K e h) :
    ((TensorProduct.lid ℤ (K e h))
        ((kostantFormCounit e h).toLinearMap.rTensor (K e h) t) : K e h) =
      TensorProduct.lid ℚ U (Coalgebra.counit.rTensor U (kostantTensorMap e h t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, Subring.coe_add, hx, hy]
  | tmul x y =>
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, kostantTensorMap_tmul,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      -- Definitional reduction of integral scalar action in the rational ambient module.
      change ((kostantFormCounit e h x : ℤ) : ℚ) • (y : U) =
        Coalgebra.counit (R := ℚ) (x : U) • (y : U)
      rw [intCast_kostantFormCounit_apply]

private theorem coe_rid_counit_lTensor (e : I → L) (h : J → L)
    (t : K e h ⊗[ℤ] K e h) :
    ((TensorProduct.rid ℤ (K e h))
        ((kostantFormCounit e h).toLinearMap.lTensor (K e h) t) : K e h) =
      TensorProduct.rid ℚ U (Coalgebra.counit.lTensor U (kostantTensorMap e h t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, Subring.coe_add, hx, hy]
  | tmul x y =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, kostantTensorMap_tmul,
        LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
      -- Definitional reduction of integral scalar action in the rational ambient module.
      change ((kostantFormCounit e h y : ℤ) : ℚ) • (x : U) =
        Coalgebra.counit (R := ℚ) (y : U) • (x : U)
      rw [intCast_kostantFormCounit_apply]

/-! ## The bialgebra structure -/

/-- The Kostant integral form is a bialgebra over `ℤ`. Its comultiplication and counit are the
canonical restrictions of those on the rational universal enveloping algebra. -/
noncomputable instance instBialgebraKostantForm (e : I → L) (h : J → L) :
    Bialgebra ℤ (K e h) :=
  Bialgebra.ofAlgHom (kostantFormComul e h) (kostantFormCounit e h)
    (by
      ext a
      -- Definitional reduction from bundled AlgHom tensor maps to linear tensor operations.
      change TensorProduct.assoc ℤ (K e h) (K e h) (K e h)
          ((kostantFormComul e h).toLinearMap.rTensor (K e h)
            (kostantFormComul e h a)) =
        (kostantFormComul e h).toLinearMap.lTensor (K e h)
          (kostantFormComul e h a)
      apply kostantTripleMap_injective e h
      rw [kostantTripleMap_comul_rTensor, kostantTripleMap_comul_lTensor,
        kostantTensorMap_kostantFormComul_apply]
      exact Coalgebra.coassoc_apply (R := ℚ) (a : U))
    (by
      ext a
      -- Definitional reduction from AlgHom map to linear rTensor and AlgEquiv to LinearEquiv.
      change (kostantFormCounit e h).toLinearMap.rTensor (K e h)
          (kostantFormComul e h a) = (TensorProduct.lid ℤ (K e h)).symm a
      apply (TensorProduct.lid ℤ (K e h)).injective
      apply (K e h).subtype_injective
      rw [LinearEquiv.apply_symm_apply]
      -- Definitional reduction across subtype coercion.
      change ((TensorProduct.lid ℤ (K e h))
          ((kostantFormCounit e h).toLinearMap.rTensor (K e h)
            (kostantFormComul e h a)) : K e h) = (a : U)
      rw [coe_lid_counit_rTensor, kostantTensorMap_kostantFormComul_apply,
        Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul])
    (by
      ext a
      -- Definitional reduction from AlgHom map to linear lTensor and AlgEquiv to LinearEquiv.
      change (kostantFormCounit e h).toLinearMap.lTensor (K e h)
          (kostantFormComul e h a) = (TensorProduct.rid ℤ (K e h)).symm a
      apply (TensorProduct.rid ℤ (K e h)).injective
      apply (K e h).subtype_injective
      rw [LinearEquiv.apply_symm_apply]
      -- Definitional reduction across subtype coercion.
      change ((TensorProduct.rid ℤ (K e h))
          ((kostantFormCounit e h).toLinearMap.lTensor (K e h)
            (kostantFormComul e h a)) : K e h) = (a : U)
      rw [coe_rid_counit_lTensor, kostantTensorMap_kostantFormComul_apply,
        Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul])

/-- The bialgebra comultiplication on the Kostant form is its canonical integral
comultiplication. -/
@[simp low]
theorem kostantForm_comul (e : I → L) (h : J → L) :
    Coalgebra.comul (R := ℤ) = (kostantFormComul e h).toLinearMap := rfl

/-- The bialgebra counit on the Kostant form is its canonical integral counit. -/
@[simp low]
theorem kostantForm_counit (e : I → L) (h : J → L) :
    Coalgebra.counit (R := ℤ) = (kostantFormCounit e h).toLinearMap := rfl

private theorem kostantTensorMap_comm (e : I → L) (h : J → L)
    (t : K e h ⊗[ℤ] K e h) :
    kostantTensorMap e h (TensorProduct.comm ℤ (K e h) (K e h) t) =
      TensorProduct.comm ℚ U U (kostantTensorMap e h t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
      rw [TensorProduct.comm_tmul]
      have hxy := kostantTensorMap_tmul e h x y
      have hyx := kostantTensorMap_tmul e h y x
      rw [hxy, hyx, TensorProduct.comm_tmul]

/-- The standard coalgebra structure on the Kostant form is cocommutative. -/
instance instIsCocommKostantForm (e : I → L) (h : J → L) :
    Coalgebra.IsCocomm ℤ (K e h) where
  comm_comp_comul := by
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, kostantForm_comul, AlgHom.toLinearMap_apply,
      LinearEquiv.coe_toLinearMap]
    apply kostantTensorMap_injective e h
    rw [kostantTensorMap_comm, kostantTensorMap_kostantFormComul_apply,
      Coalgebra.comm_comul]

/-! ## The antipode and Hopf algebra structure -/

/-- The restricted Kostant-form antipode, regarded as a `ℤ`-linear endomorphism rather than an
equivalence with the opposite ring. -/
noncomputable def kostantFormAntipodeLinearMap (e : I → L) (h : J → L) :
    K e h →ₗ[ℤ] K e h :=
  ((kostantFormAntipode e h).toIntAlgEquiv.toLinearEquiv.trans
    (MulOpposite.opLinearEquiv ℤ).symm).toLinearMap

/-- The integral linear antipode agrees with the rational universal-enveloping antipode after
including the Kostant form in its ambient algebra. -/
@[simp]
theorem coe_kostantFormAntipodeLinearMap_apply (e : I → L) (h : J → L)
    (a : K e h) :
    (kostantFormAntipodeLinearMap e h a : U) =
      HopfAlgebra.antipode ℚ (a : U) := by
  exact coe_unop_kostantFormAntipode_apply e h a

private theorem coe_mul_antipode_rTensor (e : I → L) (h : J → L)
    (t : K e h ⊗[ℤ] K e h) :
    (LinearMap.mul' ℤ (K e h)
        ((kostantFormAntipodeLinearMap e h).rTensor (K e h) t) : K e h) =
      LinearMap.mul' ℚ U
        ((HopfAlgebra.antipode ℚ (A := U)).rTensor U (kostantTensorMap e h t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, Subring.coe_add, hx, hy]
  | tmul x y =>
      rw [LinearMap.rTensor_tmul, LinearMap.mul'_apply, kostantTensorMap_tmul,
        LinearMap.rTensor_tmul, LinearMap.mul'_apply, Subring.coe_mul,
        coe_kostantFormAntipodeLinearMap_apply]

private theorem coe_mul_antipode_lTensor (e : I → L) (h : J → L)
    (t : K e h ⊗[ℤ] K e h) :
    (LinearMap.mul' ℤ (K e h)
        ((kostantFormAntipodeLinearMap e h).lTensor (K e h) t) : K e h) =
      LinearMap.mul' ℚ U
        ((HopfAlgebra.antipode ℚ (A := U)).lTensor U (kostantTensorMap e h t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, Subring.coe_add, hx, hy]
  | tmul x y =>
      rw [LinearMap.lTensor_tmul, LinearMap.mul'_apply, kostantTensorMap_tmul,
        LinearMap.lTensor_tmul, LinearMap.mul'_apply, Subring.coe_mul,
        coe_kostantFormAntipodeLinearMap_apply]

/-- The Kostant integral form, with its restricted standard operations, is a Hopf algebra over
the integers. -/
noncomputable instance instHopfAlgebraKostantForm (e : I → L) (h : J → L) :
    HopfAlgebra ℤ (K e h) where
  antipode := kostantFormAntipodeLinearMap e h
  mul_antipode_rTensor_comul := by
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply]
    rw [kostantForm_comul e h, kostantForm_counit e h]
    apply (K e h).subtype_injective
    simp only [AlgHom.toLinearMap_apply, Algebra.linearMap_apply]
    calc
      (K e h).subtype (LinearMap.mul' ℤ (K e h)
          ((kostantFormAntipodeLinearMap e h).rTensor (K e h)
            (kostantFormComul e h a))) =
          LinearMap.mul' ℚ U ((HopfAlgebra.antipode ℚ (A := U)).rTensor U
            (kostantTensorMap e h (kostantFormComul e h a))) :=
        coe_mul_antipode_rTensor e h (kostantFormComul e h a)
      _ = algebraMap ℚ U (Coalgebra.counit (R := ℚ) (a : U)) := by
        rw [kostantTensorMap_kostantFormComul_apply,
          HopfAlgebra.mul_antipode_rTensor_comul_apply]
      _ = (K e h).subtype (algebraMap ℤ (K e h) (kostantFormCounit e h a)) := by
        -- Definitional agreement of the rationalized counit scalar with the integral scalar.
        change algebraMap ℚ U (Coalgebra.counit (R := ℚ) (a : U)) =
          algebraMap ℚ U ((kostantFormCounit e h a : ℤ) : ℚ)
        rw [intCast_kostantFormCounit_apply]
  mul_antipode_lTensor_comul := by
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply]
    rw [kostantForm_comul e h, kostantForm_counit e h]
    apply (K e h).subtype_injective
    simp only [AlgHom.toLinearMap_apply, Algebra.linearMap_apply]
    calc
      (K e h).subtype (LinearMap.mul' ℤ (K e h)
          ((kostantFormAntipodeLinearMap e h).lTensor (K e h)
            (kostantFormComul e h a))) =
          LinearMap.mul' ℚ U ((HopfAlgebra.antipode ℚ (A := U)).lTensor U
            (kostantTensorMap e h (kostantFormComul e h a))) :=
        coe_mul_antipode_lTensor e h (kostantFormComul e h a)
      _ = algebraMap ℚ U (Coalgebra.counit (R := ℚ) (a : U)) := by
        rw [kostantTensorMap_kostantFormComul_apply,
          HopfAlgebra.mul_antipode_lTensor_comul_apply]
      _ = (K e h).subtype (algebraMap ℤ (K e h) (kostantFormCounit e h a)) := by
        -- Definitional agreement of the rationalized counit scalar with the integral scalar.
        change algebraMap ℚ U (Coalgebra.counit (R := ℚ) (a : U)) =
          algebraMap ℚ U ((kostantFormCounit e h a : ℤ) : ℚ)
        rw [intCast_kostantFormCounit_apply]

/-- The Hopf algebra antipode on the Kostant form is the restriction of the rational
universal-enveloping antipode. -/
@[simp low]
theorem kostantForm_antipode (e : I → L) (h : J → L) :
    HopfAlgebra.antipode ℤ (A := K e h) = kostantFormAntipodeLinearMap e h := rfl

end TauCeti.UniversalEnvelopingAlgebra
