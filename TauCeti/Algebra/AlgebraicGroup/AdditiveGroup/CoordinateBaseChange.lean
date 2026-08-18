/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme

/-!
# Base change of the additive-group coordinate algebra

For a commutative semiring extension `k → K`, scalar extension of the coordinate bialgebra of the
additive monoid is canonically the coordinate bialgebra of the additive monoid over `K`:

```text
K ⊗[k] k[X] ≃ₐc[K] K[X].
```

Both polynomial algebras are presented here as symmetric algebras.  The forward map sends
`s ⊗ ι(r)` to `s · ι(algebraMap k K r)`; its inverse sends `ι(t)` to
`t · (1 ⊗ ι(1))`.  The primitive-generator formulas show that the underlying algebra
equivalence preserves the counit and comultiplication.

## Main declarations

* `TauCeti.AdditiveGroup.scalarTensorBialgEquiv`: the bialgebra equivalence after scalar extension.
* `TauCeti.AdditiveGroup.scalarTensorBialgEquiv_tmul_ι`: its formula on scalar multiples of the
  additive coordinate.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §1.

This completes the coordinate-algebra base-change calculation for the additive-group worked
example in Layer 0 of the ReductiveGroups roadmap.  It specializes the roadmap's generic Hopf
base-change construction to the canonical additive coordinate.
-/

public section

open SymmetricAlgebra TensorProduct

namespace TauCeti.AdditiveGroup

universe u v

variable (k : Type u) (K : Type v) [CommSemiring k] [CommSemiring K] [Algebra k K]

/-- The forward algebra map from the scalar extension of the additive coordinate algebra. -/
private noncomputable def toScalarTensor :
    K ⊗[k] SymmetricAlgebra k k →ₐ[K] SymmetricAlgebra K K :=
  AlgHom.liftEquiv k K (SymmetricAlgebra k k) (SymmetricAlgebra K K) <|
    SymmetricAlgebra.lift <|
      (SymmetricAlgebra.ι K K).restrictScalars k ∘ₗ Algebra.linearMap k K

/-- The algebra map sending the additive coordinate over `K` to its base-changed coordinate. -/
private noncomputable def fromScalarTensor :
    SymmetricAlgebra K K →ₐ[K] K ⊗[k] SymmetricAlgebra k k :=
  SymmetricAlgebra.lift <|
    LinearMap.toSpanSingleton K _ (1 ⊗ₜ[k] SymmetricAlgebra.ι k k 1)

@[simp]
private theorem toScalarTensor_tmul_ι (s : K) (r : k) :
    toScalarTensor k K (s ⊗ₜ[k] SymmetricAlgebra.ι k k r) =
      s • SymmetricAlgebra.ι K K (algebraMap k K r) := by
  simp [toScalarTensor, LinearMap.comp_apply]

@[simp]
private theorem toScalarTensor_tmul_one (s : K) :
    toScalarTensor k K (s ⊗ₜ[k] 1) = algebraMap K (SymmetricAlgebra K K) s := by
  rw [toScalarTensor, AlgHom.liftEquiv_tmul, map_one, Algebra.smul_def, mul_one]

@[simp]
private theorem fromScalarTensor_ι (s : K) :
    fromScalarTensor k K (SymmetricAlgebra.ι K K s) =
      s • (1 ⊗ₜ[k] SymmetricAlgebra.ι k k 1) := by
  simp [fromScalarTensor, LinearMap.toSpanSingleton_apply]

/-- Moving a scalar from `k` across the tensor product agrees with applying it to the additive
coordinate. -/
private theorem algebraMap_smul_tmul_one_ι (r : k) :
    algebraMap k K r • ((1 : K) ⊗ₜ[k] SymmetricAlgebra.ι k k 1) =
      (1 : K) ⊗ₜ[k] SymmetricAlgebra.ι k k r := by
  rw [IsScalarTower.algebraMap_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
    ← map_smul, smul_eq_mul, mul_one]

private theorem fromScalarTensor_toScalarTensor_tmul_ι (r : k) :
    fromScalarTensor k K (toScalarTensor k K (1 ⊗ₜ[k] SymmetricAlgebra.ι k k r)) =
      1 ⊗ₜ[k] SymmetricAlgebra.ι k k r := by
  rw [toScalarTensor_tmul_ι, map_smul, fromScalarTensor_ι]
  simpa only [one_smul] using algebraMap_smul_tmul_one_ι k K r

private theorem toScalarTensor_fromScalarTensor_ι (s : K) :
    toScalarTensor k K (fromScalarTensor k K (SymmetricAlgebra.ι K K s)) =
      SymmetricAlgebra.ι K K s := by
  rw [fromScalarTensor_ι, map_smul, toScalarTensor_tmul_ι]
  simpa [Algebra.smul_def] using (map_smul (SymmetricAlgebra.ι K K) s (1 : K)).symm

private theorem fromScalarTensor_comp_toScalarTensor :
    (fromScalarTensor k K).comp (toScalarTensor k K) = AlgHom.id K _ := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro s
    simp [toScalarTensor, fromScalarTensor, Algebra.smul_def]
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro r
    exact fromScalarTensor_toScalarTensor_tmul_ι k K r

private theorem toScalarTensor_comp_fromScalarTensor :
    (toScalarTensor k K).comp (fromScalarTensor k K) = AlgHom.id K _ := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro s
  exact toScalarTensor_fromScalarTensor_ι k K s

/-- **The additive coordinate algebra commutes with scalar extension.**

The equivalence sends `s ⊗ ι(r)` to `s • ι(algebraMap k K r)` and sends the target generator
`ι(t)` back to `t • (1 ⊗ ι(1))`. -/
private noncomputable def scalarTensorAlgEquiv :
    K ⊗[k] SymmetricAlgebra k k ≃ₐ[K] SymmetricAlgebra K K :=
  AlgEquiv.ofAlgHom (toScalarTensor k K) (fromScalarTensor k K)
    (toScalarTensor_comp_fromScalarTensor k K)
    (fromScalarTensor_comp_toScalarTensor k K)

/-- On scalar multiples of the base-changed additive coordinate, the algebra equivalence applies
the scalar and extends the coefficient from `k` to `K`. -/
@[simp]
private theorem scalarTensorAlgEquiv_tmul_ι (s : K) (r : k) :
    scalarTensorAlgEquiv k K (s ⊗ₜ[k] SymmetricAlgebra.ι k k r) =
      s • SymmetricAlgebra.ι K K (algebraMap k K r) := by
  rw [scalarTensorAlgEquiv, AlgEquiv.ofAlgHom_apply]
  exact toScalarTensor_tmul_ι k K s r

/-- The algebra equivalence identifies the scalar copy of `K` in the tensor product with the
scalar copy of `K` in the target. -/
@[simp]
private theorem scalarTensorAlgEquiv_tmul_one (s : K) :
    scalarTensorAlgEquiv k K (s ⊗ₜ[k] 1) = algebraMap K (SymmetricAlgebra K K) s := by
  rw [scalarTensorAlgEquiv, AlgEquiv.ofAlgHom_apply]
  exact toScalarTensor_tmul_one k K s

/-- The inverse algebra equivalence sends the additive coordinate over `K` to the corresponding
base-changed coordinate. -/
@[simp]
private theorem scalarTensorAlgEquiv_symm_ι (s : K) :
    (scalarTensorAlgEquiv k K).symm (SymmetricAlgebra.ι K K s) =
      s • (1 ⊗ₜ[k] SymmetricAlgebra.ι k k 1) := by
  rw [scalarTensorAlgEquiv, AlgEquiv.ofAlgHom_symm_apply]
  exact fromScalarTensor_ι k K s

private theorem scalarTensorAlgEquiv_counit_tmul_ι (r : k) :
    (Bialgebra.counitAlgHom K (SymmetricAlgebra K K))
        (scalarTensorAlgEquiv k K (1 ⊗ₜ[k] SymmetricAlgebra.ι k k r)) =
      (Bialgebra.counitAlgHom K (K ⊗[k] SymmetricAlgebra k k))
        (1 ⊗ₜ[k] SymmetricAlgebra.ι k k r) := by
  rw [scalarTensorAlgEquiv_tmul_ι]
  simpa using SymmetricAlgebra.algebraMapInv_ι
    (R := K) (M := K) (algebraMap k K r)

private theorem scalarTensorAlgEquiv_counit_comp :
    (Bialgebra.counitAlgHom K (SymmetricAlgebra K K)).comp
        (scalarTensorAlgEquiv k K).toAlgHom =
      Bialgebra.counitAlgHom K (K ⊗[k] SymmetricAlgebra k k) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro s
    simp [scalarTensorAlgEquiv_tmul_one]
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro r
    exact scalarTensorAlgEquiv_counit_tmul_ι k K r

private theorem scalarTensorAlgEquiv_comul_tmul_ι (r : k) :
    (Algebra.TensorProduct.map (scalarTensorAlgEquiv k K).toAlgHom
        (scalarTensorAlgEquiv k K).toAlgHom)
        (Coalgebra.comul (R := K) (A := K ⊗[k] SymmetricAlgebra k k)
          (1 ⊗ₜ[k] SymmetricAlgebra.ι k k r)) =
      Coalgebra.comul (R := K) (A := SymmetricAlgebra K K)
        (scalarTensorAlgEquiv k K (1 ⊗ₜ[k] SymmetricAlgebra.ι k k r)) := by
  rw [scalarTensorAlgEquiv_tmul_ι]
  rw [TensorProduct.comul_tmul, Bialgebra.comul_one, SymmetricAlgebra.comul_ι]
  simp only [TensorProduct.tmul_add, map_add, Algebra.TensorProduct.one_def,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
    Algebra.TensorProduct.map_tmul]
  have hι : (scalarTensorAlgEquiv k K).toAlgHom
      (1 ⊗ₜ[k] SymmetricAlgebra.ι k k r) =
      SymmetricAlgebra.ι K K (algebraMap k K r) := by
    simpa only [AlgEquiv.coe_toAlgHom, one_smul] using
      scalarTensorAlgEquiv_tmul_ι k K 1 r
  have h_one : (scalarTensorAlgEquiv k K).toAlgHom (1 ⊗ₜ[k] 1) = 1 := by
    exact scalarTensorAlgEquiv_tmul_one k K 1
  rw [hι, h_one, one_smul, SymmetricAlgebra.comul_ι]

private theorem scalarTensorAlgEquiv_map_comp_comul :
    (Algebra.TensorProduct.map (scalarTensorAlgEquiv k K).toAlgHom
        (scalarTensorAlgEquiv k K).toAlgHom).comp
        (Bialgebra.comulAlgHom K (K ⊗[k] SymmetricAlgebra k k)) =
      (Bialgebra.comulAlgHom K (SymmetricAlgebra K K)).comp
        (scalarTensorAlgEquiv k K).toAlgHom := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro s
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Bialgebra.comulAlgHom_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply,
      Bialgebra.comul_one, AlgEquiv.coe_toAlgHom, scalarTensorAlgEquiv_tmul_one,
      AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.one_def,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.map_tmul, map_one]
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro r
    exact scalarTensorAlgEquiv_comul_tmul_ι k K r

/-- **Base change of the additive coordinate bialgebra is the additive coordinate bialgebra over
the new base.** -/
noncomputable def scalarTensorBialgEquiv :
    K ⊗[k] SymmetricAlgebra k k ≃ₐc[K] SymmetricAlgebra K K :=
  BialgEquiv.ofAlgEquiv (scalarTensorAlgEquiv k K)
    (scalarTensorAlgEquiv_counit_comp k K)
    (scalarTensorAlgEquiv_map_comp_comul k K)

/-- The bialgebra equivalence sends a scalar multiple of the base-changed additive coordinate to
the corresponding scalar multiple of the additive coordinate over `K`. -/
@[simp]
theorem scalarTensorBialgEquiv_tmul_ι (s : K) (r : k) :
    scalarTensorBialgEquiv k K (s ⊗ₜ[k] SymmetricAlgebra.ι k k r) =
      s • SymmetricAlgebra.ι K K (algebraMap k K r) := by
  rw [scalarTensorBialgEquiv, BialgEquiv.ofAlgEquiv_apply]
  exact scalarTensorAlgEquiv_tmul_ι k K s r

/-- The bialgebra equivalence identifies the scalar copy of `K` in the tensor product with the
scalar copy of `K` in the target. -/
@[simp]
theorem scalarTensorBialgEquiv_tmul_one (s : K) :
    scalarTensorBialgEquiv k K (s ⊗ₜ[k] 1) = algebraMap K (SymmetricAlgebra K K) s := by
  rw [scalarTensorBialgEquiv, BialgEquiv.ofAlgEquiv_apply]
  exact scalarTensorAlgEquiv_tmul_one k K s

/-- The inverse bialgebra equivalence sends the additive coordinate over `K` to the base-changed
additive coordinate. -/
@[simp]
theorem scalarTensorBialgEquiv_symm_ι (s : K) :
    (scalarTensorBialgEquiv k K).symm (SymmetricAlgebra.ι K K s) =
      s • (1 ⊗ₜ[k] SymmetricAlgebra.ι k k 1) := by
  apply_fun scalarTensorBialgEquiv k K
  simp [Algebra.smul_def]
  simpa [Algebra.smul_def] using map_smul (SymmetricAlgebra.ι K K) s (1 : K)

end TauCeti.AdditiveGroup
