/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import TauCeti.Algebra.Coalgebra.Comodule.Basic

/-!
# Base change of comodules and their coefficient coalgebras

Let `H` be a coalgebra over a commutative semiring `R`, let `A` be a commutative
`R`-algebra, and let `M` be a right `H`-comodule. Extending scalars in both the coefficient
coalgebra and the underlying module gives a right comodule

```text
A ⊗[R] M  over  A ⊗[R] H.
```

The coaction is scalar extension of the original coaction followed by the canonical
distributivity equivalence

```text
A ⊗[R] (M ⊗[R] H) ≃ (A ⊗[R] M) ⊗[A] (A ⊗[R] H).
```

This is coefficient-ring base change, rather than the existing scalar-extension functor that
only changes the module on which an `H`-valued point acts. It is the representation transport
needed to compare geometric unipotence before and after a field extension.

## Main declarations

* `TauCeti.Comodule.baseChangeCoact`: the base-changed coaction.
* `TauCeti.Comodule.baseChange`: the induced comodule structure over the base-changed
  coefficient coalgebra.
* `TauCeti.Comodule.baseChangeCoact_tmul`: the coaction formula on pure tensors.
* `TauCeti.Comodule.Hom.baseChange`: base change of a comodule morphism.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.

This supplies a prerequisite for base-change invariance of geometric unipotence and hence for
comparison of unipotent radicals in Layer 5 of the ReductiveGroups roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x y

variable {R : Type u} {H : Type v} {M : Type w} (A : Type x)
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid H] [Module R H] [Coalgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- The scalar extension of a coaction, with the scalar extension distributed across its two
tensor factors. -/
noncomputable def baseChangeCoact :
    A ⊗[R] M →ₗ[A] (A ⊗[R] M) ⊗[A] (A ⊗[R] H) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange R A M H).toLinearMap ∘ₗ
    (coact (R := R) (C := H) (M := M)).baseChange A

/-- On a pure tensor, the base-changed coaction applies the old coaction and distributes the
new scalar across the two extended tensor factors. -/
theorem baseChangeCoact_tmul (a : A) (m : M) :
    baseChangeCoact (R := R) (H := H) A (a ⊗ₜ[R] m) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M H)
        (a ⊗ₜ[R] coact (R := R) (C := H) (M := M) m) := by
  rw [baseChangeCoact, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.baseChange_tmul]
  rfl

/-- Collapse a threefold tensor product of scalar extensions to the scalar extension of the
original threefold tensor product. -/
private noncomputable def collapseTriple :
    (A ⊗[R] M) ⊗[A] ((A ⊗[R] H) ⊗[A] (A ⊗[R] H)) ≃ₗ[A]
      A ⊗[R] (M ⊗[R] (H ⊗[R] H)) :=
  (TensorProduct.congr (LinearEquiv.refl A (A ⊗[R] M))
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A H H).symm).trans
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M (H ⊗[R] H)).symm

omit [Coalgebra R H] [Comodule R H M] in
private theorem collapseTriple_tmul (a : A) (z : M ⊗[R] H) (h : H) :
    collapseTriple (R := R) (H := H) (M := M) A
        (TensorProduct.assoc A (A ⊗[R] M) (A ⊗[R] H) (A ⊗[R] H)
          ((TensorProduct.AlgebraTensorModule.distribBaseChange R A M H
            (a ⊗ₜ[R] z)) ⊗ₜ[A] (1 ⊗ₜ[R] h))) =
      a ⊗ₜ[R] TensorProduct.assoc R M H H (z ⊗ₜ[R] h) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hx, hy]
  | tmul m g => simp [collapseTriple]

private theorem collapseTriple_coact (a : A) (z : M ⊗[R] H) :
    collapseTriple (R := R) (H := H) (M := M) A
        (TensorProduct.assoc A (A ⊗[R] M) (A ⊗[R] H) (A ⊗[R] H)
          ((baseChangeCoact (R := R) (H := H) A).rTensor (A ⊗[R] H)
            ((TensorProduct.AlgebraTensorModule.distribBaseChange R A M H)
              (a ⊗ₜ[R] z)))) =
      a ⊗ₜ[R] TensorProduct.assoc R M H H
        ((coact (R := R) (C := H) (M := M)).rTensor H z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul m h =>
      rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        LinearMap.rTensor_tmul, baseChangeCoact_tmul, LinearMap.rTensor_tmul]
      exact collapseTriple_tmul (R := R) (H := H) (M := M) A a
        (coact (R := R) (C := H) (M := M) m) h

omit [Coalgebra R H] in
private theorem tensorTensorTensorComm_one_one (z : H ⊗[R] H) :
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R A R A A A H H
        ((1 ⊗ₜ[A] 1) ⊗ₜ[R] z) =
      TensorProduct.AlgebraTensorModule.distribBaseChange R A H H (1 ⊗ₜ[R] z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul g h => rfl

private theorem comul_one_tmul (h : H) :
    Coalgebra.comul (R := A) (A := A ⊗[R] H) (1 ⊗ₜ[R] h) =
      TensorProduct.AlgebraTensorModule.distribBaseChange R A H H
        (1 ⊗ₜ[R] Coalgebra.comul (R := R) (A := H) h) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  exact tensorTensorTensorComm_one_one (R := R) (H := H) A
    (Coalgebra.comul (R := R) (A := H) h)

omit [Coalgebra R H] [Comodule R H M] in
private theorem collapseTriple_comulTensor (a : A) (m : M) (z : H ⊗[R] H) :
    collapseTriple (R := R) (H := H) (M := M) A
        ((a ⊗ₜ[R] m) ⊗ₜ[A]
          (TensorProduct.AlgebraTensorModule.distribBaseChange R A H H (1 ⊗ₜ[R] z))) =
      a ⊗ₜ[R] (m ⊗ₜ[R] z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul g h => simp [collapseTriple]

omit [Comodule R H M] in
private theorem collapseTriple_comul (a : A) (z : M ⊗[R] H) :
    collapseTriple (R := R) (H := H) (M := M) A
        (Coalgebra.comul.lTensor (A ⊗[R] M)
          ((TensorProduct.AlgebraTensorModule.distribBaseChange R A M H)
            (a ⊗ₜ[R] z))) =
      a ⊗ₜ[R] Coalgebra.comul.lTensor M z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul m h =>
      rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        LinearMap.lTensor_tmul, comul_one_tmul,
        collapseTriple_comulTensor, LinearMap.lTensor_tmul]

omit [Comodule R H M] in
private theorem rid_counit_distrib (a : A) (z : M ⊗[R] H) :
    TensorProduct.AlgebraTensorModule.rid A A (A ⊗[R] M)
        (Coalgebra.counit.lTensor (A ⊗[R] M)
          ((TensorProduct.AlgebraTensorModule.distribBaseChange R A M H)
            (a ⊗ₜ[R] z))) =
      a ⊗ₜ[R] TensorProduct.rid R M (Coalgebra.counit.lTensor M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul m h =>
      rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        LinearMap.lTensor_tmul, TensorProduct.counit_tmul,
        CommSemiring.counit_apply]
      rw [TensorProduct.AlgebraTensorModule.rid_tmul,
        LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
      rw [TensorProduct.tmul_smul]
      simp [Algebra.smul_def, mul_comm]

/-- Extending the coefficient Hopf algebra and the underlying module of a comodule along the
same scalar morphism gives a comodule over the base-changed Hopf algebra. -/
@[expose, instance_reducible]
noncomputable def baseChange : Comodule A (A ⊗[R] H) (A ⊗[R] M) where
  coact := baseChangeCoact (R := R) (H := H) A
  coassoc := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    apply (collapseTriple (R := R) (H := H) (M := M) A).injective
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [baseChangeCoact_tmul]
    rw [collapseTriple_coact, collapseTriple_comul, coassoc_apply]
  lTensor_counit_comp_coact := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    apply (TensorProduct.AlgebraTensorModule.rid A A (A ⊗[R] M)).injective
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [baseChangeCoact_tmul]
    rw [rid_counit_distrib, Comodule.lTensor_counit_coact]
    simp

/-- The coaction of the base-changed comodule is scalar extension of the original coaction,
followed by distribution across the two tensor factors. -/
theorem baseChange_coact :
    letI := baseChange (R := R) (H := H) (M := M) A
    coact (R := A) (C := A ⊗[R] H) (M := A ⊗[R] M) =
      baseChangeCoact (R := R) (H := H) A :=
  rfl

/-- Formula for the coaction of the base-changed comodule on a pure tensor. -/
theorem baseChange_coact_tmul (a : A) (m : M) :
    letI := baseChange (R := R) (H := H) (M := M) A
    coact (R := A) (C := A ⊗[R] H) (M := A ⊗[R] M) (a ⊗ₜ[R] m) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M H)
        (a ⊗ₜ[R] coact (R := R) (C := H) (M := M) m) :=
  baseChangeCoact_tmul (R := R) (H := H) A a m

namespace Hom

variable {N : Type y} [AddCommMonoid N] [Module R N] [Comodule R H N]

/-- Base change of a comodule morphism, extending both its source and its coefficient coalgebra
algebra along the same scalar morphism. -/
@[expose] noncomputable def baseChange (f : Hom R H M N) :
    letI := Comodule.baseChange (R := R) (H := H) (M := M) A
    letI := Comodule.baseChange (R := R) (H := H) (M := N) A
    Hom A (A ⊗[R] H) (A ⊗[R] M) (A ⊗[R] N) := by
  letI := Comodule.baseChange (R := R) (H := H) (M := M) A
  letI := Comodule.baseChange (R := R) (H := H) (M := N) A
  refine
    { toLinearMap := f.toLinearMap.baseChange A
      map_coact := ?_ }
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  simp only [LinearMap.coe_comp, Function.comp_apply, baseChange_coact_tmul,
    LinearMap.baseChange_tmul]
  rw [coe_toLinearMap, ← f.map_coact_apply m]
  induction coact (R := R) (C := H) (M := M) m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | tmul n h => simp

/-- The underlying linear map of a base-changed comodule morphism is the base change of its
underlying linear map. -/
@[simp]
theorem baseChange_toLinearMap (f : Hom R H M N) :
    letI := Comodule.baseChange (R := R) (H := H) (M := M) A
    letI := Comodule.baseChange (R := R) (H := H) (M := N) A
    (baseChange A f).toLinearMap = f.toLinearMap.baseChange A :=
  rfl

/-- A base-changed comodule morphism acts on a pure tensor by applying the original morphism
to the module factor. -/
@[simp]
theorem baseChange_tmul (f : Hom R H M N) (a : A) (m : M) :
    letI := Comodule.baseChange (R := R) (H := H) (M := M) A
    letI := Comodule.baseChange (R := R) (H := H) (M := N) A
    baseChange A f (a ⊗ₜ[R] m) = a ⊗ₜ[R] f m :=
  rfl

end Hom

end TauCeti.Comodule
