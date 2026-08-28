/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Bialgebra maps and base change for tensor products

This file packages the canonical inclusions into and projections out of a tensor product of
bialgebras as bialgebra morphisms, and records their action on pure tensors. The projections are
obtained by applying the counit to the other tensor factor.

Scalar extension also commutes with tensor products of bialgebras. The resulting bialgebra
equivalence upgrades `TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv` and records its
action on pure tensors in both directions.

The underlying algebra equivalence upgrades Mathlib's
`TensorProduct.AlgebraTensorModule.distribBaseChange`. The bialgebra comparison supplies the
product/base-change identification needed for direct-product closure in Layer 6 of the
ReductiveGroups roadmap.

The tensor-product bialgebra structure and its unit isomorphisms are from Mathlib's
`Mathlib.RingTheory.Bialgebra.TensorProduct`.
-/

public section

open TensorProduct

namespace TauCeti

namespace Bialgebra.TensorProduct

universe u v w x

variable {R H₁ H₂ : Type*} [CommSemiring R]
variable [Semiring H₁] [Semiring H₂] [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]

/-- The left inclusion `x ↦ x ⊗ₜ 1` of a bialgebra into a tensor product of bialgebras,
packaged as a bialgebra morphism. It is the unit `R →ₐc[R] H₂` tensored on the right with `H₁`,
precomposed with the right-unit isomorphism `H₁ ≃ₐc[R] H₁ ⊗[R] R`. -/
noncomputable def includeLeft : H₁ →ₐc[R] H₁ ⊗[R] H₂ :=
  (_root_.Bialgebra.TensorProduct.map (BialgHom.id R H₁) (_root_.Bialgebra.unitBialgHom R H₂)).comp
    (_root_.Bialgebra.TensorProduct.rid R R H₁).symm.toBialgHom

/-- The right inclusion `y ↦ 1 ⊗ₜ y` of a bialgebra into a tensor product of bialgebras,
packaged as a bialgebra morphism. It is the unit `R →ₐc[R] H₁` tensored on the left with `H₂`,
precomposed with the left-unit isomorphism `H₂ ≃ₐc[R] R ⊗[R] H₂`. -/
noncomputable def includeRight : H₂ →ₐc[R] H₁ ⊗[R] H₂ :=
  (_root_.Bialgebra.TensorProduct.map (_root_.Bialgebra.unitBialgHom R H₁) (BialgHom.id R H₂)).comp
    (_root_.Bialgebra.TensorProduct.lid R H₂).symm.toBialgHom

@[simp]
theorem includeLeft_apply (x : H₁) : includeLeft (H₂ := H₂) x = x ⊗ₜ[R] (1 : H₂) := by
  simp [includeLeft, _root_.Bialgebra.unitBialgHom, Algebra.ofId_apply]

@[simp]
theorem includeRight_apply (y : H₂) : includeRight (H₁ := H₁) y = (1 : H₁) ⊗ₜ[R] y := by
  simp [includeRight, _root_.Bialgebra.unitBialgHom, Algebra.ofId_apply]

@[simp]
theorem includeLeft_toAlgHom :
    (includeLeft : H₁ →ₐc[R] H₁ ⊗[R] H₂).toAlgHom = Algebra.TensorProduct.includeLeft := by
  ext x
  simp only [BialgHom.coe_toAlgHom, includeLeft_apply, Algebra.TensorProduct.includeLeft_apply]

@[simp]
theorem includeRight_toAlgHom :
    (includeRight : H₂ →ₐc[R] H₁ ⊗[R] H₂).toAlgHom = Algebra.TensorProduct.includeRight := by
  ext y
  simp only [BialgHom.coe_toAlgHom, includeRight_apply, Algebra.TensorProduct.includeRight_apply]

/-- The left projection `H₁ ⊗[R] H₂ → H₁`, given on pure tensors by
`x ⊗ₜ y ↦ ε(y) • x`, as a bialgebra morphism. -/
noncomputable def projectLeft : H₁ ⊗[R] H₂ →ₐc[R] H₁ :=
  (_root_.Bialgebra.TensorProduct.rid R R H₁).toBialgHom.comp <|
    _root_.Bialgebra.TensorProduct.map (BialgHom.id R H₁)
      (_root_.Bialgebra.counitBialgHom R H₂)

/-- The right projection `H₁ ⊗[R] H₂ → H₂`, given on pure tensors by
`x ⊗ₜ y ↦ ε(x) • y`, as a bialgebra morphism. -/
noncomputable def projectRight : H₁ ⊗[R] H₂ →ₐc[R] H₂ :=
  (_root_.Bialgebra.TensorProduct.lid R H₂).toBialgHom.comp <|
    _root_.Bialgebra.TensorProduct.map (_root_.Bialgebra.counitBialgHom R H₁)
      (BialgHom.id R H₂)

@[simp]
theorem projectLeft_tmul (x : H₁) (y : H₂) :
    projectLeft (R := R) (H₁ := H₁) (H₂ := H₂) (x ⊗ₜ[R] y) =
      Coalgebra.counit (R := R) (A := H₂) y • x := by
  simp [projectLeft]

@[simp]
theorem projectRight_tmul (x : H₁) (y : H₂) :
    projectRight (R := R) (H₁ := H₁) (H₂ := H₂) (x ⊗ₜ[R] y) =
      Coalgebra.counit (R := R) (A := H₁) x • y := by
  simp [projectRight]

/-- The left projection is a retraction of the left inclusion. -/
@[simp]
theorem projectLeft_comp_includeLeft :
    (projectLeft (R := R) (H₁ := H₁) (H₂ := H₂)).comp includeLeft = BialgHom.id R H₁ := by
  ext x
  rw [BialgHom.comp_apply, includeLeft_apply, projectLeft_tmul,
    Bialgebra.counit_one, one_smul]
  rfl

/-- The right projection is a retraction of the right inclusion. -/
@[simp]
theorem projectRight_comp_includeRight :
    (projectRight (R := R) (H₁ := H₁) (H₂ := H₂)).comp includeRight = BialgHom.id R H₂ := by
  ext y
  rw [BialgHom.comp_apply, includeRight_apply, projectRight_tmul,
    Bialgebra.counit_one, one_smul]
  rfl

section BaseChange

variable (k : Type u) (K : Type w) [CommSemiring k] [CommSemiring K] [Algebra k K]
variable (H : Type v) (L : Type x) [Semiring H] [Semiring L]
variable [_root_.Bialgebra k H] [_root_.Bialgebra k L]

private theorem baseChangeTensorAlgEquiv_counit_comp :
    (Bialgebra.counitAlgHom K
        ((K ⊗[k] H) ⊗[K] (K ⊗[k] L))).comp
      (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom =
    Bialgebra.counitAlgHom K (K ⊗[k] (H ⊗[k] L)) := by
  apply Algebra.TensorProduct.ext'
  intro s z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | tmul h l => simp [smul_smul, mul_comm]

-- This is the comultiplication compatibility on pure tensors after rewriting by
-- `TensorProduct.comul_tmul` and `CommSemiring.comul_apply`, so it compares the two
-- `tensorTensorTensorComm` reorderings.
private theorem _root_.TensorProduct.baseChangeTensorAlgEquiv_comul_aux
    (s : K) (x : H ⊗[k] H) (y : L ⊗[k] L) :
    (Algebra.TensorProduct.map
        (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom
        (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom)
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
        k K k K K K (H ⊗[k] L) (H ⊗[k] L)
        (1 ⊗ₜ[K] s ⊗ₜ[k]
          TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
            k k k k H H L L (x ⊗ₜ[k] y))) =
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
      K K K K (K ⊗[k] H) (K ⊗[k] H) (K ⊗[k] L) (K ⊗[k] L)
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
          k K k K K K H H (1 ⊗ₜ[K] s ⊗ₜ[k] x) ⊗ₜ[K]
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
          k K k K K K L L (1 ⊗ₜ[K] 1 ⊗ₜ[k] y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
      simpa only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add] using
        congrArg₂ (· + ·) hx₁ hx₂
  | tmul h₁ h₂ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
        simpa only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add] using
          congrArg₂ (· + ·) hy₁ hy₂
    | tmul l₁ l₂ =>
        simp

private theorem baseChangeTensorAlgEquiv_map_comp_comul :
    (Algebra.TensorProduct.map
        (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom
        (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom).comp
      (Bialgebra.comulAlgHom K (K ⊗[k] (H ⊗[k] L))) =
    (Bialgebra.comulAlgHom K ((K ⊗[k] H) ⊗[K] (K ⊗[k] L))).comp
      (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro s z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | tmul h l =>
      simp only [AlgHom.coe_comp, Function.comp_apply]
      have he :
          (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom
              (s ⊗ₜ[k] (h ⊗ₜ[k] l)) =
            (s ⊗ₜ[k] h) ⊗ₜ[K] (1 ⊗ₜ[k] l) := by
        simpa only [AlgEquiv.coe_toAlgHom] using
          Algebra.TensorProduct.baseChangeTensorAlgEquiv_tmul k K H L s h l
      rw [he]
      simpa only [Bialgebra.comulAlgHom_apply, TensorProduct.comul_tmul,
        CommSemiring.comul_apply] using
        _root_.TensorProduct.baseChangeTensorAlgEquiv_comul_aux k K H L s
          (Coalgebra.comul (R := k) h) (Coalgebra.comul (R := k) l)

/-- **Base change commutes with tensor products of bialgebras.**

The underlying algebra equivalence distributes scalar extension across a tensor product. This
bundling records that it also preserves the counit and comultiplication. For commutative Hopf
algebras, it is contravariantly the canonical identification `(G × H)_K ≅ G_K × H_K` of affine
groups. -/
noncomputable def baseChangeTensorBialgEquiv :
    K ⊗[k] (H ⊗[k] L) ≃ₐc[K]
      ((K ⊗[k] H) ⊗[K] (K ⊗[k] L)) :=
  BialgEquiv.ofAlgEquiv (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L)
    (R := K) (A := K ⊗[k] (H ⊗[k] L))
    (B := (K ⊗[k] H) ⊗[K] (K ⊗[k] L))
    (baseChangeTensorAlgEquiv_counit_comp k K H L)
    (baseChangeTensorAlgEquiv_map_comp_comul k K H L)

/-- On a pure tensor, the product/base-change equivalence puts the scalar in the first
base-changed factor. -/
@[simp]
theorem baseChangeTensorBialgEquiv_tmul (s : K) (h : H) (l : L) :
    baseChangeTensorBialgEquiv k K H L (s ⊗ₜ[k] (h ⊗ₜ[k] l)) =
      (s ⊗ₜ[k] h) ⊗ₜ[K] (1 ⊗ₜ[k] l) := by
  rw [baseChangeTensorBialgEquiv, _root_.BialgEquiv.ofAlgEquiv_apply]
  exact Algebra.TensorProduct.baseChangeTensorAlgEquiv_tmul k K H L s h l

/-- The inverse product/base-change equivalence multiplies the two scalar coefficients. -/
@[simp]
theorem baseChangeTensorBialgEquiv_symm_tmul
    (s t : K) (h : H) (l : L) :
    (baseChangeTensorBialgEquiv k K H L).symm
        ((s ⊗ₜ[k] h) ⊗ₜ[K] (t ⊗ₜ[k] l)) =
      (s * t) ⊗ₜ[k] (h ⊗ₜ[k] l) := by
  -- `BialgEquiv.ofAlgEquiv` retains the inverse of the supplied algebra equivalence.
  change (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).symm
      ((s ⊗ₜ[k] h) ⊗ₜ[K] (t ⊗ₜ[k] l)) = _
  exact Algebra.TensorProduct.baseChangeTensorAlgEquiv_symm_tmul k K H L s t h l

end BaseChange

end Bialgebra.TensorProduct

end TauCeti
