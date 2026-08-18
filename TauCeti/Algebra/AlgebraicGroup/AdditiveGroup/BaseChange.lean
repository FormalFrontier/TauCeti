/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic

/-!
# Base change of additive groups

The vector group attached to a `k`-module `M` is represented by the symmetric bialgebra
`SymmetricAlgebra k M`. Scalar extension of this bialgebra is canonically the symmetric
bialgebra on the scalar extension of `M`:

```text
K ⊗[k] SymmetricAlgebra k M ≃ₐc[K] SymmetricAlgebra K (K ⊗[k] M).
```

The file also records the corresponding functor-of-points calculation: if `A` is a commutative
`K`-algebra, then the convolution monoid of `K`-algebra maps out of the left-hand side is the
additive monoid of `k`-linear maps `M →ₗ[k] A`.

The coordinate result transports the counit and comultiplication, hence is bialgebra-level.
No separate antipode or Hopf-equivalence packaging is asserted here.

The equivalence first restricts a base-changed point along `m ↦ 1 ⊗ ι(m)` using
`AlgHom.baseChangePointsMulEquiv`, then applies `AdditiveGroup.pointsMulEquiv`. The
characteristic lemmas spell out the generator values, the inverse map on scalar multiples of
generators, and the one-dimensional additive group `𝔾ₐ`.

The general coordinate equivalence aligns the bialgebra and functor-of-points presentations used
by the additive-group worked example in the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.AdditiveGroup.scalarTensorBialgEquiv`: scalar extension of a symmetric bialgebra is
  the symmetric bialgebra on the scalar-extended module.
* `TauCeti.AdditiveGroup.scalarTensorBialgEquiv_tmul_ι`: the equivalence on pure-tensor
  generators.
* `TauCeti.AdditiveGroup.scalarTensorBialgEquiv_symm_ι_tmul`: the inverse on pure-tensor
  generators.
* `TauCeti.AdditiveGroup.scalarTensorBialgEquiv_tmul_one`: the equivalence on scalar copies.
* `TauCeti.AdditiveGroup.gaScalarTensorBialgEquiv`: the rank-one specialization for `𝔾ₐ`.
* `TauCeti.AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι`: its forward coordinate formula.
* `TauCeti.AdditiveGroup.gaScalarTensorBialgEquiv_tmul_one`: its formula on scalar copies.
* `TauCeti.AdditiveGroup.gaScalarTensorBialgEquiv_symm_ι`: the inverse formula for the additive
  coordinate.
* `TauCeti.AdditiveGroup.baseChangePointsMulEquiv`: base-changed vector-group points are
  `k`-linear maps `M →ₗ[k] A`.
* `TauCeti.AdditiveGroup.toAdd_baseChangePointsMulEquiv_apply`: the equivalence reads a
  point on `1 ⊗ ι(m)`.
* `TauCeti.AdditiveGroup.baseChangePointsMulEquiv_symm_apply_tmul_ι`: the inverse
  equivalence evaluates scalar multiples of base-changed generators.
* `TauCeti.AdditiveGroup.gaBaseChangePointsMulEquiv`: the base-changed `𝔾ₐ` points are the
  additive monoid of `A`.

## References

The coordinate-bialgebra equivalence follows the API pattern of
`TauCeti.MonoidAlgebra.scalarTensorBialgEquiv` and uses Mathlib's `AlgHom.liftEquiv`,
`SymmetricAlgebra.lift`, and `BialgEquiv.ofAlgEquiv`. The bialgebra structures are from
`Mathlib.RingTheory.Bialgebra.SymmetricAlgebra` and
`Mathlib.RingTheory.Bialgebra.TensorProduct`.
The generic points base-change step is Tau Ceti's `AlgHom.baseChangePointsMulEquiv`; the
vector-group points calculation is Tau Ceti's `AdditiveGroup.pointsMulEquiv`. This specialization
follows the API pattern of `RootsOfUnityGroup.baseChangePointsMulEquiv`,
`SplitTorus.baseChangePointsMulEquiv`, and `DiagonalizableGroup.baseChangePointsMulEquiv`.
-/

public section

open SymmetricAlgebra WithConv
open scoped TensorProduct

namespace TauCeti

namespace AdditiveGroup

universe u v w w'

variable {k : Type u} {K : Type v} {A : Type w} {M : Type w'}
variable [CommSemiring k] [CommSemiring K] [CommSemiring A]
variable [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
variable [AddCommMonoid M] [Module k M]

section CoordinateBialgebra

/-- The algebra map from the scalar extension of the symmetric algebra to the symmetric algebra
on the scalar-extended module. -/
private noncomputable def fromScalarTensor :
    K ⊗[k] SymmetricAlgebra k M →ₐ[K] SymmetricAlgebra K (K ⊗[k] M) :=
  AlgHom.liftEquiv k K (SymmetricAlgebra k M) (SymmetricAlgebra K (K ⊗[k] M)) <|
    SymmetricAlgebra.lift <|
      (SymmetricAlgebra.ι K (K ⊗[k] M)).restrictScalars k ∘ₗ
        TensorProduct.mk k K M 1

/-- The algebra map from the symmetric algebra on the scalar-extended module back to the scalar
extension of the original symmetric algebra. -/
private noncomputable def toScalarTensor :
    SymmetricAlgebra K (K ⊗[k] M) →ₐ[K] K ⊗[k] SymmetricAlgebra k M :=
  SymmetricAlgebra.lift <| LinearMap.baseChange K (SymmetricAlgebra.ι k M)

@[simp]
private theorem fromScalarTensor_tmul_ι (s : K) (m : M) :
    fromScalarTensor (k := k) (K := K) (M := M)
        (s ⊗ₜ[k] SymmetricAlgebra.ι k M m) =
      SymmetricAlgebra.ι K (K ⊗[k] M) (s ⊗ₜ[k] m) := by
  simp only [fromScalarTensor, AlgHom.liftEquiv_tmul,
    SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    TensorProduct.mk_apply]
  rw [← map_smul, TensorProduct.smul_tmul']
  simp only [smul_eq_mul, mul_one]

@[simp]
private theorem toScalarTensor_ι_tmul (s : K) (m : M) :
    toScalarTensor (k := k) (K := K) (M := M)
        (SymmetricAlgebra.ι K (K ⊗[k] M) (s ⊗ₜ[k] m)) =
      s ⊗ₜ[k] SymmetricAlgebra.ι k M m := by
  simp [toScalarTensor]

private theorem toScalarTensor_comp_fromScalarTensor :
    (toScalarTensor (k := k) (K := K) (M := M)).comp
        (fromScalarTensor (k := k) (K := K) (M := M)) = AlgHom.id K _ := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro s
    simp [fromScalarTensor, toScalarTensor, Algebra.smul_def,
      Algebra.TensorProduct.algebraMap_apply]
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    change toScalarTensor (k := k) (K := K) (M := M)
        (fromScalarTensor (k := k) (K := K) (M := M)
          (1 ⊗ₜ[k] SymmetricAlgebra.ι k M m)) =
      1 ⊗ₜ[k] SymmetricAlgebra.ι k M m
    rw [fromScalarTensor_tmul_ι, toScalarTensor_ι_tmul]

private theorem fromScalarTensor_comp_toScalarTensor :
    (fromScalarTensor (k := k) (K := K) (M := M)).comp
        (toScalarTensor (k := k) (K := K) (M := M)) = AlgHom.id K _ := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro z
  change fromScalarTensor (k := k) (K := K) (M := M)
      (toScalarTensor (k := k) (K := K) (M := M)
        (SymmetricAlgebra.ι K (K ⊗[k] M) z)) =
    SymmetricAlgebra.ι K (K ⊗[k] M) z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | tmul s m =>
      rw [toScalarTensor_ι_tmul, fromScalarTensor_tmul_ι]

/-- The underlying algebra equivalence for scalar extension of a symmetric algebra. -/
private noncomputable def scalarTensorAlgEquiv :
    K ⊗[k] SymmetricAlgebra k M ≃ₐ[K] SymmetricAlgebra K (K ⊗[k] M) :=
  AlgEquiv.ofAlgHom
    (fromScalarTensor (k := k) (K := K) (M := M))
    (toScalarTensor (k := k) (K := K) (M := M))
    (fromScalarTensor_comp_toScalarTensor (k := k) (K := K) (M := M))
    (toScalarTensor_comp_fromScalarTensor (k := k) (K := K) (M := M))

@[simp]
private theorem scalarTensorAlgEquiv_tmul_ι (s : K) (m : M) :
    scalarTensorAlgEquiv (k := k) (K := K) (M := M)
        (s ⊗ₜ[k] SymmetricAlgebra.ι k M m) =
      SymmetricAlgebra.ι K (K ⊗[k] M) (s ⊗ₜ[k] m) := by
  exact fromScalarTensor_tmul_ι (k := k) (K := K) (M := M) s m

private theorem scalarTensorAlgEquiv_counit_tmul_ι (m : M) :
    (Bialgebra.counitAlgHom K (SymmetricAlgebra K (K ⊗[k] M)))
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)
          (1 ⊗ₜ[k] SymmetricAlgebra.ι k M m)) =
      (Bialgebra.counitAlgHom K (K ⊗[k] SymmetricAlgebra k M))
        (1 ⊗ₜ[k] SymmetricAlgebra.ι k M m) := by
  rw [scalarTensorAlgEquiv_tmul_ι]
  simpa using SymmetricAlgebra.algebraMapInv_ι
    (R := K) (M := K ⊗[k] M) (1 ⊗ₜ[k] m)

private theorem scalarTensorAlgEquiv_counit_comp :
    (Bialgebra.counitAlgHom K (SymmetricAlgebra K (K ⊗[k] M))).comp
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom =
      Bialgebra.counitAlgHom K (K ⊗[k] SymmetricAlgebra k M) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro s
    change (Bialgebra.counitAlgHom K (SymmetricAlgebra K (K ⊗[k] M)))
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)
          (algebraMap K (K ⊗[k] SymmetricAlgebra k M) s)) =
      (Bialgebra.counitAlgHom K (K ⊗[k] SymmetricAlgebra k M))
        (algebraMap K (K ⊗[k] SymmetricAlgebra k M) s)
    rw [AlgEquiv.commutes (scalarTensorAlgEquiv (k := k) (K := K) (M := M)) s,
      AlgHom.commutes (Bialgebra.counitAlgHom K (SymmetricAlgebra K (K ⊗[k] M))) s,
      AlgHom.commutes (Bialgebra.counitAlgHom K (K ⊗[k] SymmetricAlgebra k M)) s]
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    exact scalarTensorAlgEquiv_counit_tmul_ι (k := k) (K := K) (M := M) m

private theorem scalarTensorAlgEquiv_comul_tmul_ι (m : M) :
    (Algebra.TensorProduct.map
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom)
        (Coalgebra.comul (R := K) (A := K ⊗[k] SymmetricAlgebra k M)
          (1 ⊗ₜ[k] SymmetricAlgebra.ι k M m)) =
      Coalgebra.comul (R := K) (A := SymmetricAlgebra K (K ⊗[k] M))
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)
          (1 ⊗ₜ[k] SymmetricAlgebra.ι k M m)) := by
  rw [scalarTensorAlgEquiv_tmul_ι]
  rw [TensorProduct.comul_tmul, Bialgebra.comul_one, SymmetricAlgebra.comul_ι]
  simp only [TensorProduct.tmul_add, map_add, Algebra.TensorProduct.one_def,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
    Algebra.TensorProduct.map_tmul]
  have hι :
      (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom
          (1 ⊗ₜ[k] SymmetricAlgebra.ι k M m) =
        SymmetricAlgebra.ι K (K ⊗[k] M) (1 ⊗ₜ[k] m) := by
    simpa only [AlgEquiv.coe_toAlgHom] using
      scalarTensorAlgEquiv_tmul_ι (k := k) (K := K) (M := M) 1 m
  have h_one :
      (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom (1 ⊗ₜ[k] 1) = 1 := by
    simpa only [Algebra.TensorProduct.one_def] using
      map_one (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom
  rw [hι, h_one, SymmetricAlgebra.comul_ι]

private theorem scalarTensorAlgEquiv_map_comp_comul :
    (Algebra.TensorProduct.map
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom).comp
        (Bialgebra.comulAlgHom K (K ⊗[k] SymmetricAlgebra k M)) =
      (Bialgebra.comulAlgHom K (SymmetricAlgebra K (K ⊗[k] M))).comp
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro s
    change (Algebra.TensorProduct.map
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom)
        ((Bialgebra.comulAlgHom K (K ⊗[k] SymmetricAlgebra k M))
          (algebraMap K (K ⊗[k] SymmetricAlgebra k M) s)) =
      (Bialgebra.comulAlgHom K (SymmetricAlgebra K (K ⊗[k] M)))
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)
          (algebraMap K (K ⊗[k] SymmetricAlgebra k M) s))
    rw [AlgHom.commutes (Bialgebra.comulAlgHom K (K ⊗[k] SymmetricAlgebra k M)) s,
      AlgHom.commutes (Algebra.TensorProduct.map
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom) s,
      AlgEquiv.commutes (scalarTensorAlgEquiv (k := k) (K := K) (M := M)) s,
      AlgHom.commutes (Bialgebra.comulAlgHom K (SymmetricAlgebra K (K ⊗[k] M))) s]
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    exact scalarTensorAlgEquiv_comul_tmul_ι (k := k) (K := K) (M := M) m

/-- **Symmetric bialgebras commute with scalar extension.**

The equivalence sends `s ⊗ ι(m)` to the generator `ι(s ⊗ m)` of the symmetric algebra on the
scalar-extended module. -/
noncomputable def scalarTensorBialgEquiv :
    K ⊗[k] SymmetricAlgebra k M ≃ₐc[K] SymmetricAlgebra K (K ⊗[k] M) :=
  BialgEquiv.ofAlgEquiv (scalarTensorAlgEquiv (k := k) (K := K) (M := M))
    (scalarTensorAlgEquiv_counit_comp (k := k) (K := K) (M := M))
    (scalarTensorAlgEquiv_map_comp_comul (k := k) (K := K) (M := M))

/-- The scalar-extension equivalence sends `s ⊗ ι(m)` to `ι(s ⊗ m)`. -/
@[simp]
theorem scalarTensorBialgEquiv_tmul_ι (s : K) (m : M) :
    scalarTensorBialgEquiv (k := k) (K := K) (M := M)
        (s ⊗ₜ[k] SymmetricAlgebra.ι k M m) =
      SymmetricAlgebra.ι K (K ⊗[k] M) (s ⊗ₜ[k] m) := by
  exact scalarTensorAlgEquiv_tmul_ι (k := k) (K := K) (M := M) s m

/-- The inverse scalar-extension equivalence sends the generator indexed by `s ⊗ m` to
`s ⊗ ι(m)`. -/
@[simp]
theorem scalarTensorBialgEquiv_symm_ι_tmul (s : K) (m : M) :
    (scalarTensorBialgEquiv (k := k) (K := K) (M := M)).symm
      (SymmetricAlgebra.ι K (K ⊗[k] M) (s ⊗ₜ[k] m)) =
      s ⊗ₜ[k] SymmetricAlgebra.ι k M m := by
  change (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).symm
      (SymmetricAlgebra.ι K (K ⊗[k] M) (s ⊗ₜ[k] m)) = _
  exact toScalarTensor_ι_tmul (k := k) (K := K) (M := M) s m

/-- The scalar-extension equivalence identifies the scalar copy of `K` on both sides. -/
@[simp]
theorem scalarTensorBialgEquiv_tmul_one (s : K) :
    scalarTensorBialgEquiv (k := k) (K := K) (M := M) (s ⊗ₜ[k] 1) =
      algebraMap K (SymmetricAlgebra K (K ⊗[k] M)) s := by
  calc
    _ = scalarTensorBialgEquiv (k := k) (K := K) (M := M)
        (algebraMap K (K ⊗[k] SymmetricAlgebra k M) s) := by
      rw [Algebra.TensorProduct.algebraMap_apply]
      rw [Algebra.algebraMap_self_apply]
    _ = _ := AlgEquiv.commutes
      (scalarTensorBialgEquiv (k := k) (K := K) (M := M) :
        (K ⊗[k] SymmetricAlgebra k M) ≃ₐ[K] SymmetricAlgebra K (K ⊗[k] M)) s

/-- The algebra equivalence on symmetric algebras induced by a linear equivalence. -/
private noncomputable def symmetricAlgebraAlgEquiv {P N : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid N] [Module K N]
    (e : P ≃ₗ[K] N) : SymmetricAlgebra K P ≃ₐ[K] SymmetricAlgebra K N :=
  AlgEquiv.ofAlgHom
    (SymmetricAlgebra.lift (SymmetricAlgebra.ι K N ∘ₗ e.toLinearMap))
    (SymmetricAlgebra.lift (SymmetricAlgebra.ι K P ∘ₗ e.symm.toLinearMap))
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro n
      simp [LinearMap.comp_apply])
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro m
      simp [LinearMap.comp_apply])

@[simp]
private theorem symmetricAlgebraAlgEquiv_ι {P N : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid N] [Module K N]
    (e : P ≃ₗ[K] N) (p : P) :
    symmetricAlgebraAlgEquiv (K := K) e (SymmetricAlgebra.ι K P p) =
      SymmetricAlgebra.ι K N (e p) := by
  simp [symmetricAlgebraAlgEquiv, LinearMap.comp_apply]

@[simp]
private theorem symmetricAlgebraAlgEquiv_symm_ι {P N : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid N] [Module K N]
    (e : P ≃ₗ[K] N) (n : N) :
    (symmetricAlgebraAlgEquiv (K := K) e).symm (SymmetricAlgebra.ι K N n) =
      SymmetricAlgebra.ι K P (e.symm n) := by
  simp [symmetricAlgebraAlgEquiv, LinearMap.comp_apply]

/-- The bialgebra equivalence on symmetric algebras induced by a linear equivalence. -/
private noncomputable def symmetricAlgebraBialgEquiv {P N : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid N] [Module K N] (e : P ≃ₗ[K] N) :
    SymmetricAlgebra K P ≃ₐc[K] SymmetricAlgebra K N :=
  BialgEquiv.ofAlgEquiv (symmetricAlgebraAlgEquiv (K := K) e)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro m
      change (Bialgebra.counitAlgHom K (SymmetricAlgebra K N))
          (symmetricAlgebraAlgEquiv (K := K) e (SymmetricAlgebra.ι K P m)) =
        (Bialgebra.counitAlgHom K (SymmetricAlgebra K P)) (SymmetricAlgebra.ι K P m)
      rw [symmetricAlgebraAlgEquiv_ι]
      exact (SymmetricAlgebra.algebraMapInv_ι _).trans
        (SymmetricAlgebra.algebraMapInv_ι _).symm)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro m
      simp [symmetricAlgebraAlgEquiv, LinearMap.comp_apply, SymmetricAlgebra.comul_ι])

@[simp]
private theorem symmetricAlgebraBialgEquiv_ι {P N : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid N] [Module K N]
    (e : P ≃ₗ[K] N) (p : P) :
    symmetricAlgebraBialgEquiv (K := K) e (SymmetricAlgebra.ι K P p) =
      SymmetricAlgebra.ι K N (e p) :=
  symmetricAlgebraAlgEquiv_ι (K := K) e p

@[simp]
private theorem symmetricAlgebraBialgEquiv_symm_ι {P N : Type*}
    [AddCommMonoid P] [Module K P] [AddCommMonoid N] [Module K N]
    (e : P ≃ₗ[K] N) (n : N) :
    (symmetricAlgebraBialgEquiv (K := K) e).symm (SymmetricAlgebra.ι K N n) =
      SymmetricAlgebra.ι K P (e.symm n) :=
  symmetricAlgebraAlgEquiv_symm_ι (K := K) e n

section GaCoordinateBialgebra

/-- **Base change of the additive coordinate bialgebra is the additive coordinate bialgebra over
the new base.**

This is the rank-one specialization of `scalarTensorBialgEquiv`, transported along
`K ⊗[k] k ≃ K`. -/
noncomputable def gaScalarTensorBialgEquiv :
    K ⊗[k] SymmetricAlgebra k k ≃ₐc[K] SymmetricAlgebra K K :=
  (scalarTensorBialgEquiv (k := k) (K := K) (M := k)).trans <|
    symmetricAlgebraBialgEquiv (K := K)
      (Algebra.TensorProduct.rid k K K).toLinearEquiv

/-- The `𝔾ₐ` coordinate equivalence sends `s ⊗ ι(r)` to
`s • ι(algebraMap k K r)`. -/
@[simp]
theorem gaScalarTensorBialgEquiv_tmul_ι (s : K) (r : k) :
    gaScalarTensorBialgEquiv (k := k) (K := K)
        (s ⊗ₜ[k] SymmetricAlgebra.ι k k r) =
      s • SymmetricAlgebra.ι K K (algebraMap k K r) := by
  rw [gaScalarTensorBialgEquiv, BialgEquiv.trans_apply]
  change symmetricAlgebraBialgEquiv (K := K)
      (Algebra.TensorProduct.rid k K K).toLinearEquiv
        (scalarTensorBialgEquiv (k := k) (K := K) (M := k)
          (s ⊗ₜ[k] SymmetricAlgebra.ι k k r)) = _
  rw [scalarTensorBialgEquiv_tmul_ι, symmetricAlgebraBialgEquiv_ι]
  have hrid : Algebra.TensorProduct.rid k K K (s ⊗ₜ[k] r) = r • s :=
    Algebra.TensorProduct.rid_tmul (R := k) (S := K) (A := K) r s
  change SymmetricAlgebra.ι K K
      (Algebra.TensorProduct.rid k K K (s ⊗ₜ[k] r)) = _
  rw [hrid]
  conv_lhs => rw [Algebra.smul_def, mul_comm]
  change SymmetricAlgebra.ι K K (s • algebraMap k K r) =
    s • SymmetricAlgebra.ι K K (algebraMap k K r)
  exact map_smul (SymmetricAlgebra.ι K K) s (algebraMap k K r)

/-- The `𝔾ₐ` coordinate equivalence identifies the scalar copy of `K` on both sides. -/
@[simp]
theorem gaScalarTensorBialgEquiv_tmul_one (s : K) :
    gaScalarTensorBialgEquiv (k := k) (K := K) (s ⊗ₜ[k] 1) =
      algebraMap K (SymmetricAlgebra K K) s := by
  rw [gaScalarTensorBialgEquiv, BialgEquiv.trans_apply]
  change symmetricAlgebraBialgEquiv (K := K)
      (Algebra.TensorProduct.rid k K K).toLinearEquiv
        (scalarTensorBialgEquiv (k := k) (K := K) (M := k) (s ⊗ₜ[k] 1)) = _
  rw [scalarTensorBialgEquiv_tmul_one]
  exact AlgEquiv.commutes
    (symmetricAlgebraBialgEquiv (K := K)
      (Algebra.TensorProduct.rid k K K).toLinearEquiv :
        SymmetricAlgebra K (K ⊗[k] k) ≃ₐ[K] SymmetricAlgebra K K) s

/-- The inverse `𝔾ₐ` coordinate equivalence sends `ι(s)` to the pure tensor
`s ⊗ ι(1)`. -/
@[simp]
theorem gaScalarTensorBialgEquiv_symm_ι (s : K) :
    (gaScalarTensorBialgEquiv (k := k) (K := K)).symm
        (SymmetricAlgebra.ι K K s) =
      s ⊗ₜ[k] SymmetricAlgebra.ι k k 1 := by
  change (scalarTensorBialgEquiv (k := k) (K := K) (M := k)).symm
      ((symmetricAlgebraBialgEquiv (K := K)
        (Algebra.TensorProduct.rid k K K).toLinearEquiv).symm
          (SymmetricAlgebra.ι K K s)) = _
  rw [symmetricAlgebraBialgEquiv_symm_ι]
  have hrid :
      (Algebra.TensorProduct.rid k K K).toLinearEquiv.symm s = s ⊗ₜ[k] 1 := rfl
  rw [hrid, scalarTensorBialgEquiv_symm_ι_tmul]

end GaCoordinateBialgebra

end CoordinateBialgebra

/-- The `A`-points of the base change `K ⊗[k] SymmetricAlgebra k M` of the vector group on
`M` are the additive monoid of `k`-linear maps `M →ₗ[k] A`.

The source is the convolution monoid of `K`-algebra maps out of the base-changed bialgebra;
the target is written multiplicatively as `Multiplicative (M →ₗ[k] A)` to match `≃*`. -/
noncomputable def baseChangePointsMulEquiv :
    WithConv (K ⊗[k] SymmetricAlgebra k M →ₐ[K] A) ≃* Multiplicative (M →ₗ[k] A) :=
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
      (A := SymmetricAlgebra k M) (R := A)).symm.trans
    (pointsMulEquiv (R := k) (M := M) (A := A))

/-- The base-changed vector-group points equivalence reads a point by evaluating it on the
base-changed generator `1 ⊗ ι(m)`. -/
@[simp]
theorem toAdd_baseChangePointsMulEquiv_apply
    (F : WithConv (K ⊗[k] SymmetricAlgebra k M →ₐ[K] A)) (m : M) :
    Multiplicative.toAdd (baseChangePointsMulEquiv F) m =
      F.ofConv (1 ⊗ₜ[k] ι k M m) := by
  rw [baseChangePointsMulEquiv, MulEquiv.trans_apply, toAdd_pointsMulEquiv_apply,
    AlgHom.baseChangePointsMulEquiv_symm_apply]

/-- The inverse base-changed vector-group points equivalence evaluates scalar multiples of
base-changed generators by scalar multiplication of the corresponding linear-map value. -/
@[simp]
theorem baseChangePointsMulEquiv_symm_apply_tmul_ι
    (φ : Multiplicative (M →ₗ[k] A)) (s : K) (m : M) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (M := M)).symm φ).ofConv
        (s ⊗ₜ[k] ι k M m) =
      s • (Multiplicative.toAdd φ m) := by
  simp [baseChangePointsMulEquiv, pointsMulEquiv_symm_apply]

/-- The inverse base-changed vector-group points equivalence takes the generator indexed by
`m` to the value of the chosen linear map at `m`. -/
theorem baseChangePointsMulEquiv_symm_apply_ι
    (φ : Multiplicative (M →ₗ[k] A)) (m : M) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (M := M)).symm φ).ofConv
        (1 ⊗ₜ[k] ι k M m) =
      Multiplicative.toAdd φ m := by
  rw [baseChangePointsMulEquiv_symm_apply_tmul_ι]
  simp

section Ga

variable {A : Type w} [CommSemiring A]
variable [Algebra K A] [Algebra k A] [IsScalarTower k K A]

/-- The base-changed one-dimensional additive group `𝔾ₐ` has `A`-points the additive monoid
of the value algebra `A`. -/
noncomputable def gaBaseChangePointsMulEquiv :
    WithConv (K ⊗[k] SymmetricAlgebra k k →ₐ[K] A) ≃* Multiplicative A :=
  (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (M := k)).trans
    (AddEquiv.toMultiplicative (LinearMap.ringLmapEquivSelf k k A).toAddEquiv)

/-- The base-changed `𝔾ₐ` points equivalence reads a point by evaluating it on
`1 ⊗ ι(1)`. -/
@[simp]
theorem toAdd_gaBaseChangePointsMulEquiv
    (F : WithConv (K ⊗[k] SymmetricAlgebra k k →ₐ[K] A)) :
    Multiplicative.toAdd (gaBaseChangePointsMulEquiv F) =
      F.ofConv (1 ⊗ₜ[k] ι k k 1) := by
  rw [gaBaseChangePointsMulEquiv]
  simp

/-- The inverse base-changed `𝔾ₐ` points equivalence takes the generator `1 ⊗ ι(1)` to the
chosen value. -/
@[simp]
theorem gaBaseChangePointsMulEquiv_symm_apply_ι (a : Multiplicative A) :
    ((gaBaseChangePointsMulEquiv (k := k) (K := K) (A := A)).symm a).ofConv
        (1 ⊗ₜ[k] ι k k 1) =
      Multiplicative.toAdd a := by
  rw [gaBaseChangePointsMulEquiv, MulEquiv.symm_trans_apply,
    baseChangePointsMulEquiv_symm_apply_ι]
  simp

end Ga

end AdditiveGroup

end TauCeti
