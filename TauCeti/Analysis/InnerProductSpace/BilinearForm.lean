/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.LinearAlgebra.TensorProduct.Symmetric

/-!
# The bilinear form of a tensor on an inner product space

On an inner product space the tensor square `V ⊗[𝕜] V` and the bilinear forms on `V` are the same
size, and the inner product identifies them: a tensor `t` becomes the form

`B_t (v, w) = ⟪t, v ⊗ₜ w⟫`,

`TauCeti.bilinFormOfTensor`. The identification is conjugate-linear in `t`, and in finite
dimensions it is a bijection. It carries the flip `x ⊗ y ↦ y ⊗ x` to the exchange of the two
arguments of a form, so the **symmetric tensors** `TauCeti.symmetricTensors` become the
**symmetric** forms and the **antisymmetric tensors** `TauCeti.antisymmetricTensors` the
**alternating** ones.

Nothing here needs a group or a representation: this is the purely bilinear half of the dictionary
that `TauCeti/RepresentationTheory/Continuous/Square/BilinearForm.lean` makes equivariant for a
unitary representation.

## Main definitions

* `TauCeti.bilinFormOfTensor`: the bilinear form `B_t (v, w) = ⟪t, v ⊗ₜ w⟫` of a tensor.

## Main statements

* `TauCeti.bilinFormOfTensor_injective` and `TauCeti.bilinFormOfTensor_surjective`: the
  identification is injective, and surjective in finite dimensions.
* `TauCeti.isSymm_bilinFormOfTensor_iff` and `TauCeti.isAlt_bilinFormOfTensor_iff`: the form of a
  tensor is symmetric, respectively alternating, exactly when the tensor is symmetric, respectively
  antisymmetric.

## Implementation notes

`TauCeti.bilinFormOfTensor` is conjugate-linear, not linear, so it is bundled as a semilinear map
`V ⊗[𝕜] V →ₛₗ[starRingEnd 𝕜] BilinForm 𝕜 V`; its behaviour on `0`, on sums, on negation and on
differences is then the generic `map_zero`, `map_add`, `map_neg` and `map_sub`. Injectivity comes
from `TensorProduct.ext_iff_inner_right`, and surjectivity in finite dimensions from the Riesz
representation `InnerProductSpace.toDual` applied to the functional `TensorProduct.lift B`; the
bijection is not packaged as a semilinear equivalence because only the two directions are used.

## References

This is the linear-algebra half of the invariant-form dictionary that Layer 6b of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md)
needs for its `frobeniusSchurIndicator_eq_one_iff` and `frobeniusSchurIndicator_eq_neg_one_iff`
targets. The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2,
and T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
Chapter II.
-/

public section

open LinearMap (BilinForm)

open scoped InnerProductSpace TensorProduct

namespace TauCeti

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **The bilinear form of a tensor**: `B_t (v, w) = ⟪t, v ⊗ₜ w⟫`. The inner product is
conjugate-linear in its first argument and linear in its second, so this is bilinear in `(v, w)`
and conjugate-linear in `t`. -/
noncomputable def bilinFormOfTensor : V ⊗[𝕜] V →ₛₗ[starRingEnd 𝕜] BilinForm 𝕜 V where
  toFun t := TensorProduct.curry (innerSL 𝕜 t).toLinearMap
  map_add' t s := by
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    simp
  map_smul' c t := by
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    simp

@[simp]
theorem bilinFormOfTensor_apply (t : V ⊗[𝕜] V) (v w : V) :
    bilinFormOfTensor t v w = ⟪t, v ⊗ₜ[𝕜] w⟫_𝕜 :=
  (rfl)

/-- **A tensor is determined by its form.** -/
theorem bilinFormOfTensor_injective :
    Function.Injective (bilinFormOfTensor : V ⊗[𝕜] V → BilinForm 𝕜 V) := by
  intro s t h
  refine TensorProduct.ext_iff_inner_right.mpr fun a b => ?_
  simpa using DFunLike.congr_fun (DFunLike.congr_fun h a) b

/-- **The form of a tensor vanishes only for the zero tensor.** -/
@[simp]
theorem bilinFormOfTensor_eq_zero_iff {t : V ⊗[𝕜] V} : bilinFormOfTensor t = 0 ↔ t = 0 :=
  map_eq_zero_iff _ bilinFormOfTensor_injective

/-- **The flip of the tensor square exchanges the two arguments of the form.** -/
theorem bilinFormOfTensor_comm_apply (t : V ⊗[𝕜] V) (v w : V) :
    bilinFormOfTensor (TensorProduct.comm 𝕜 V V t) v w = bilinFormOfTensor t w v := by
  rw [bilinFormOfTensor_apply, bilinFormOfTensor_apply, ← TensorProduct.commIsometry_apply,
    (TensorProduct.commIsometry 𝕜 V V).inner_map_eq_flip, TensorProduct.commIsometry_symm]
  simp

/-- **The form of a tensor is symmetric exactly when the tensor is symmetric.** -/
theorem isSymm_bilinFormOfTensor_iff {t : V ⊗[𝕜] V} :
    (bilinFormOfTensor t).IsSymm ↔ t ∈ symmetricTensors 𝕜 V := by
  rw [mem_symmetricTensors, BilinForm.isSymm_def]
  refine ⟨fun h => bilinFormOfTensor_injective ?_, fun h x y => ?_⟩
  · refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    rw [bilinFormOfTensor_comm_apply]
    exact h w v
  · calc bilinFormOfTensor t x y = bilinFormOfTensor (TensorProduct.comm 𝕜 V V t) y x :=
          (bilinFormOfTensor_comm_apply t y x).symm
      _ = bilinFormOfTensor t y x := by rw [h]

/-- **The form of a tensor is alternating exactly when the tensor is antisymmetric.** -/
theorem isAlt_bilinFormOfTensor_iff {t : V ⊗[𝕜] V} :
    (bilinFormOfTensor t).IsAlt ↔ t ∈ antisymmetricTensors 𝕜 V := by
  rw [mem_antisymmetricTensors]
  refine ⟨fun h => bilinFormOfTensor_injective ?_, fun h v => ?_⟩
  · rw [map_neg]
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    rw [bilinFormOfTensor_comm_apply, LinearMap.neg_apply, LinearMap.neg_apply]
    exact (h.neg_eq v w).symm
  · have hvv : bilinFormOfTensor t v v = -bilinFormOfTensor t v v := by
      calc bilinFormOfTensor t v v = bilinFormOfTensor (TensorProduct.comm 𝕜 V V t) v v :=
            (bilinFormOfTensor_comm_apply t v v).symm
        _ = -bilinFormOfTensor t v v := by rw [h, map_neg]; simp
    have h2 : (2 : 𝕜) * bilinFormOfTensor t v v = 0 := by linear_combination hvv
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- **Every bilinear form on a finite-dimensional inner product space is the form of a tensor.**
The preimage is the Riesz representative of the linear functional `TensorProduct.lift B` on the
tensor square. -/
theorem bilinFormOfTensor_surjective [FiniteDimensional 𝕜 V] :
    Function.Surjective (bilinFormOfTensor : V ⊗[𝕜] V → BilinForm 𝕜 V) := by
  intro B
  have hfd : FiniteDimensional 𝕜 (V ⊗[𝕜] V) := Module.Finite.tensorProduct 𝕜 V V
  have hcomplete : CompleteSpace (V ⊗[𝕜] V) := FiniteDimensional.complete 𝕜 _
  refine ⟨(InnerProductSpace.toDual 𝕜 (V ⊗[𝕜] V)).symm
    (LinearMap.toContinuousLinearMap (TensorProduct.lift B)), ?_⟩
  refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
  rw [bilinFormOfTensor_apply, InnerProductSpace.toDual_symm_apply]
  simp

end TauCeti
