/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.LinearAlgebra.TensorProduct.Symmetric

/-!
# The bilinear form of a tensor on an inner product space

On an inner product space the inner product turns a tensor `t : V ⊗[𝕜] V` into a bilinear form on
`V`,

`B_t (v, w) = ⟪t, v ⊗ₜ w⟫`,

`TauCeti.BilinForm.ofTensor`. The construction is conjugate-linear in `t` and always injective, so
a tensor is determined by its form; it is **surjective only in finite dimensions**, where it
therefore identifies the tensor square with all of `BilinForm 𝕜 V`
(`TauCeti.BilinForm.ofTensorEquiv`). In infinite dimensions it is just an injection: the tensor
square is spanned by the finite sums of pure tensors, while a general bilinear form need not be one.

The construction carries the flip `x ⊗ y ↦ y ⊗ x` to the exchange of the two arguments of a form,
so the **symmetric tensors** `TauCeti.symmetricTensors` become the **symmetric** forms and the
**antisymmetric tensors** `TauCeti.antisymmetricTensors` the **alternating** ones.

Nothing here needs a group or a representation: this is the purely bilinear half of the dictionary
that `TauCeti/RepresentationTheory/Continuous/Square/BilinearForm.lean` makes equivariant for a
unitary representation.

## Main definitions

* `TauCeti.BilinForm.ofTensor`: the bilinear form `B_t (v, w) = ⟪t, v ⊗ₜ w⟫` of a tensor.
* `TauCeti.BilinForm.ofTensorEquiv`: in finite dimensions, that construction as a conjugate-linear
  equivalence of the tensor square with the bilinear forms.

## Main statements

* `TauCeti.BilinForm.ofTensor_injective` and `TauCeti.BilinForm.ofTensor_surjective`: the
  construction is injective, and surjective in finite dimensions.
* `TauCeti.BilinForm.isSymm_ofTensor_iff` and `TauCeti.BilinForm.isAlt_ofTensor_iff`: the form of a
  tensor is symmetric, respectively alternating, exactly when the tensor is symmetric, respectively
  antisymmetric.

## Implementation notes

`TauCeti.BilinForm.ofTensor` is conjugate-linear, not linear, so it is bundled as a semilinear map
`V ⊗[𝕜] V →ₛₗ[starRingEnd 𝕜] BilinForm 𝕜 V`; it is the composition of `innerSL` with the currying
`TensorProduct.lcurry`, so its behaviour on `0`, on sums, on negation and on differences is the
generic `map_zero`, `map_add`, `map_neg` and `map_sub`. Injectivity comes from
`TensorProduct.ext_iff_inner_right`; surjectivity in finite dimensions is read off
`TauCeti.BilinForm.ofTensorEquiv`, which is assembled from the Riesz representation
`InnerProductSpace.toDual`, the identification `LinearMap.toContinuousLinearMap` of the linear with
the continuous linear functionals, and the currying `TensorProduct.lift.equiv`.

The two symmetry statements go through Mathlib's flip characterizations
`LinearMap.BilinForm.isSymm_iff_flip` and `LinearMap.isAlt_iff_eq_neg_flip`, so the only geometric
input is `TauCeti.BilinForm.ofTensor_comm`, that the construction intertwines the flip of the
tensor square with the flip of a form.

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

namespace BilinForm

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **The bilinear form of a tensor**: `B_t (v, w) = ⟪t, v ⊗ₜ w⟫`. The inner product is
conjugate-linear in its first argument and linear in its second, so this is bilinear in `(v, w)`
and conjugate-linear in `t`. -/
noncomputable def ofTensor : V ⊗[𝕜] V →ₛₗ[starRingEnd 𝕜] BilinForm 𝕜 V :=
  (TensorProduct.lcurry (RingHom.id 𝕜) V V 𝕜).comp
    ((ContinuousLinearMap.coeLM 𝕜).comp (innerSL 𝕜 (E := V ⊗[𝕜] V)).toLinearMap)

@[simp]
theorem ofTensor_apply (t : V ⊗[𝕜] V) (v w : V) : ofTensor t v w = ⟪t, v ⊗ₜ[𝕜] w⟫_𝕜 :=
  (rfl)

/-- **A tensor is determined by its form.** -/
@[grind inj]
theorem ofTensor_injective : Function.Injective (ofTensor : V ⊗[𝕜] V → BilinForm 𝕜 V) := by
  intro s t h
  refine TensorProduct.ext_iff_inner_right.mpr fun a b => ?_
  simpa using DFunLike.congr_fun (DFunLike.congr_fun h a) b

/-- **The form of a tensor vanishes only for the zero tensor.** -/
@[simp]
theorem ofTensor_eq_zero_iff {t : V ⊗[𝕜] V} : ofTensor t = 0 ↔ t = 0 :=
  map_eq_zero_iff _ ofTensor_injective

/-- **The flip of the tensor square is the flip of the form.** -/
@[simp]
theorem ofTensor_comm (t : V ⊗[𝕜] V) :
    ofTensor (TensorProduct.comm 𝕜 V V t) = BilinForm.flipHom (ofTensor t) := by
  refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
  rw [BilinForm.flip_apply, ofTensor_apply, ofTensor_apply]
  simpa only [TensorProduct.commIsometry_apply, TensorProduct.comm_tmul] using
    (TensorProduct.commIsometry 𝕜 V V).inner_map_map t (w ⊗ₜ[𝕜] v)

/-- **The form of a tensor is symmetric exactly when the tensor is symmetric.** -/
@[simp, grind =]
theorem isSymm_ofTensor_iff {t : V ⊗[𝕜] V} :
    (ofTensor t).IsSymm ↔ t ∈ symmetricTensors 𝕜 V := by
  rw [BilinForm.isSymm_iff_flip, mem_symmetricTensors, ← ofTensor_comm,
    ofTensor_injective.eq_iff]

/-- **The form of a tensor is alternating exactly when the tensor is antisymmetric.** -/
@[simp, grind =]
theorem isAlt_ofTensor_iff {t : V ⊗[𝕜] V} :
    (ofTensor t).IsAlt ↔ t ∈ antisymmetricTensors 𝕜 V := by
  -- `LinearMap.BilinForm.IsAlt` is `LinearMap.IsAlt`, which is where the flip characterization is.
  have halt : (ofTensor t).IsAlt ↔ LinearMap.IsAlt (ofTensor t) := Iff.rfl
  rw [halt, LinearMap.isAlt_iff_eq_neg_flip, mem_antisymmetricTensors,
    ← ofTensor_injective.eq_iff, map_neg, ofTensor_comm]
  exact eq_comm.trans (neg_eq_iff_eq_neg (a := BilinForm.flipHom (ofTensor t)) (b := ofTensor t))

/-- **In finite dimensions the tensor square is the space of bilinear forms**, conjugate-linearly,
through `TauCeti.BilinForm.ofTensor`: the Riesz representation `InnerProductSpace.toDual` identifies
a tensor with a functional on the tensor square, and the currying `TensorProduct.lift.equiv`
identifies such a functional with a bilinear form. -/
noncomputable def ofTensorEquiv [FiniteDimensional 𝕜 V] :
    V ⊗[𝕜] V ≃ₛₗ[starRingEnd 𝕜] BilinForm 𝕜 V :=
  have : FiniteDimensional 𝕜 (V ⊗[𝕜] V) := Module.Finite.tensorProduct 𝕜 V V
  have : CompleteSpace (V ⊗[𝕜] V) := FiniteDimensional.complete 𝕜 _
  (InnerProductSpace.toDual 𝕜 (V ⊗[𝕜] V)).toLinearEquiv.trans
    (LinearMap.toContinuousLinearMap.symm.trans
      (TensorProduct.lift.equiv (RingHom.id 𝕜) V V 𝕜).symm)

@[simp]
theorem ofTensorEquiv_apply [FiniteDimensional 𝕜 V] (t : V ⊗[𝕜] V) :
    ofTensorEquiv t = ofTensor t := by
  refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
  rw [ofTensor_apply]
  simp [ofTensorEquiv]

@[simp]
theorem coe_ofTensorEquiv [FiniteDimensional 𝕜 V] :
    (ofTensorEquiv (𝕜 := 𝕜) (V := V) : V ⊗[𝕜] V →ₛₗ[starRingEnd 𝕜] BilinForm 𝕜 V) = ofTensor :=
  LinearMap.ext ofTensorEquiv_apply

/-- **Every bilinear form on a finite-dimensional inner product space is the form of a tensor**,
because `TauCeti.BilinForm.ofTensorEquiv` is an equivalence. -/
theorem ofTensor_surjective [FiniteDimensional 𝕜 V] :
    Function.Surjective (ofTensor : V ⊗[𝕜] V → BilinForm 𝕜 V) := fun B =>
  ⟨ofTensorEquiv.symm B, by rw [← ofTensorEquiv_apply, LinearEquiv.apply_symm_apply]⟩

end BilinForm

end TauCeti
