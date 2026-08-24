/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Square.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# Invariant tensors and invariant bilinear forms

On an inner product space the tensor square `V ⊗[𝕜] V` and the bilinear forms on `V` are the same
size, and the inner product identifies them: a tensor `t` becomes the form

`B_t (v, w) = ⟪t, v ⊗ₜ w⟫`,

`TauCeti.bilinFormOfTensor`. The identification is conjugate-linear in `t`, and in finite
dimensions it is a bijection. What makes it useful is that it carries all three structures the
Frobenius-Schur trichotomy is stated in:

* the flip `x ⊗ y ↦ y ⊗ x` becomes the exchange of the two arguments of a form, so the **symmetric
  tensors** `TauCeti.symmetricTensors` become the **symmetric** forms and the **antisymmetric
  tensors** `TauCeti.antisymmetricTensors` the **alternating** ones;
* for a **unitary** representation `π`, the invariants of the tensor square `π ⊗ π` become the
  **invariant** forms of `π`, in the sense of `TauCeti.Representation.IsInvariantForm`.

Together these say that the two eigenspaces of the flip that
`TauCeti/RepresentationTheory/Continuous/Square/Invariants.lean` counts are, invariant vector by
invariant vector, the invariant symmetric and the invariant alternating forms. That is the
dictionary the compact-group Frobenius-Schur trichotomy is read off from in
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/InvariantForm.lean`; it is the analytic
counterpart of `TauCeti/LinearAlgebra/BilinearForm/Squares.lean`, which does the same job for
finite groups through the dual of the symmetric and exterior powers rather than through an inner
product.

Nothing here needs a group, a measure, or compactness, so everything is stated over a topological
monoid with `RCLike` scalars, and the purely bilinear half needs no representation at all.
Unitarity is what makes the dictionary equivariant: `π g ⊗ π g` preserves the inner product of the
tensor square, so moving it across `⟪t, v ⊗ₜ w⟫` costs nothing.

## Main definitions

* `TauCeti.bilinFormOfTensor`: the bilinear form `B_t (v, w) = ⟪t, v ⊗ₜ w⟫` of a tensor.

## Main statements

* `TauCeti.bilinFormOfTensor_injective` and `TauCeti.bilinFormOfTensor_surjective`: the
  identification is injective, and surjective in finite dimensions.
* `TauCeti.isSymm_bilinFormOfTensor_iff` and `TauCeti.isAlt_bilinFormOfTensor_iff`: the form of a
  tensor is symmetric, respectively alternating, exactly when the tensor is symmetric, respectively
  antisymmetric.
* `ContRepresentation.isInvariantForm_bilinFormOfTensor_iff`: the form of a tensor is invariant for
  a unitary representation exactly when the tensor is invariant for the tensor square.
* `ContRepresentation.exists_ne_zero_isSymm_isInvariantForm_iff` and
  `ContRepresentation.exists_ne_zero_isAlt_isInvariantForm_iff`: **a nonzero invariant symmetric,
  respectively alternating, form exists exactly when the symmetric, respectively exterior, square
  has a nonzero invariant tensor.**

## Implementation notes

`TauCeti.bilinFormOfTensor` is conjugate-linear, not linear, so it is bundled as a semilinear map
`V ⊗[𝕜] V →ₛₗ[starRingEnd 𝕜] BilinForm 𝕜 V`; its behaviour on `0`, on sums, on negation and on
differences is then the generic `map_zero`, `map_add`, `map_neg` and `map_sub`. Injectivity comes
from `TensorProduct.ext_iff_inner_right`, and surjectivity in finite dimensions from the Riesz
representation `InnerProductSpace.toDual` applied to the functional `TensorProduct.lift B`; the
bijection is not packaged as a semilinear equivalence because only the two directions are used.

## References

This is the invariant-form dictionary that Layer 6b of the
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

section Tensor

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
theorem bilinFormOfTensor_tensorComm_apply (t : V ⊗[𝕜] V) (v w : V) :
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
    rw [bilinFormOfTensor_tensorComm_apply]
    exact h w v
  · calc bilinFormOfTensor t x y = bilinFormOfTensor (TensorProduct.comm 𝕜 V V t) y x :=
          (bilinFormOfTensor_tensorComm_apply t y x).symm
      _ = bilinFormOfTensor t y x := by rw [h]

/-- **The form of a tensor is alternating exactly when the tensor is antisymmetric.** -/
theorem isAlt_bilinFormOfTensor_iff {t : V ⊗[𝕜] V} :
    (bilinFormOfTensor t).IsAlt ↔ t ∈ antisymmetricTensors 𝕜 V := by
  rw [mem_antisymmetricTensors]
  refine ⟨fun h => bilinFormOfTensor_injective ?_, fun h v => ?_⟩
  · rw [map_neg]
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    rw [bilinFormOfTensor_tensorComm_apply, LinearMap.neg_apply, LinearMap.neg_apply]
    exact (h.neg_eq v w).symm
  · have hvv : bilinFormOfTensor t v v = -bilinFormOfTensor t v v := by
      calc bilinFormOfTensor t v v = bilinFormOfTensor (TensorProduct.comm 𝕜 V V t) v v :=
            (bilinFormOfTensor_tensorComm_apply t v v).symm
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

end Tensor

end TauCeti

open TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

section Unitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (π : ContRepresentation 𝕜 G V)

omit [TopologicalSpace G] in
/-- **The form of an invariant tensor is invariant.** Moving `π g ⊗ π g` across the inner product
costs nothing because the representation is unitary. -/
theorem isInvariantForm_bilinFormOfTensor (hπ : IsUnitary π) {t : V ⊗[𝕜] V}
    (ht : t ∈ (tprod π π).invariants) :
    Representation.IsInvariantForm π.toRepresentation (bilinFormOfTensor t) := by
  refine Representation.isInvariantForm_iff.mpr fun g v w => ?_
  have hg : (tprod π π) g (v ⊗ₜ[𝕜] w) = π g v ⊗ₜ[𝕜] π g w := by simp
  calc bilinFormOfTensor t (π g v) (π g w)
      = ⟪(tprod π π) g t, (tprod π π) g (v ⊗ₜ[𝕜] w)⟫_𝕜 := by
        rw [(mem_invariants t).mp ht g, hg, bilinFormOfTensor_apply]
    _ = ⟪t, v ⊗ₜ[𝕜] w⟫_𝕜 := (hπ.tprod hπ).inner_map_map g t (v ⊗ₜ[𝕜] w)
    _ = bilinFormOfTensor t v w := (bilinFormOfTensor_apply t v w).symm

omit [TopologicalSpace G] in
/-- **A tensor whose form is invariant is invariant.** The action operators of a unitary
representation of a monoid on a finite-dimensional space are bijective, so the pure tensors
`π g v ⊗ₜ π g w` still span the tensor square. -/
theorem mem_invariants_of_isInvariantForm_bilinFormOfTensor [FiniteDimensional 𝕜 V]
    (hπ : IsUnitary π) {t : V ⊗[𝕜] V}
    (hB : Representation.IsInvariantForm π.toRepresentation (bilinFormOfTensor t)) :
    t ∈ (tprod π π).invariants := by
  refine (mem_invariants t).mpr fun g => ?_
  have hsurj : Function.Surjective (π g) := by
    have := LinearMap.surjective_of_injective (f := ((π g : V →L[𝕜] V) : V →ₗ[𝕜] V))
      (hπ.injective g)
    simpa using this
  have key : ∀ a b : V, ⟪(tprod π π) g t, a ⊗ₜ[𝕜] b⟫_𝕜 = ⟪t, a ⊗ₜ[𝕜] b⟫_𝕜 := by
    intro a b
    obtain ⟨v, rfl⟩ := hsurj a
    obtain ⟨w, rfl⟩ := hsurj b
    have hg : (tprod π π) g (v ⊗ₜ[𝕜] w) = π g v ⊗ₜ[𝕜] π g w := by simp
    calc ⟪(tprod π π) g t, π g v ⊗ₜ[𝕜] π g w⟫_𝕜
        = ⟪(tprod π π) g t, (tprod π π) g (v ⊗ₜ[𝕜] w)⟫_𝕜 := by rw [hg]
      _ = ⟪t, v ⊗ₜ[𝕜] w⟫_𝕜 := (hπ.tprod hπ).inner_map_map g t (v ⊗ₜ[𝕜] w)
      _ = bilinFormOfTensor t v w := (bilinFormOfTensor_apply t v w).symm
      _ = bilinFormOfTensor t (π g v) (π g w) :=
          (Representation.isInvariantForm_iff.mp hB g v w).symm
      _ = ⟪t, π g v ⊗ₜ[𝕜] π g w⟫_𝕜 := bilinFormOfTensor_apply t _ _
  rw [← sub_eq_zero, ← bilinFormOfTensor_eq_zero_iff]
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply, bilinFormOfTensor_apply, inner_sub_left, key]
  exact sub_self _

omit [TopologicalSpace G] in
/-- **The invariant tensors of the tensor square are the invariant forms.** -/
theorem isInvariantForm_bilinFormOfTensor_iff [FiniteDimensional 𝕜 V] (hπ : IsUnitary π)
    {t : V ⊗[𝕜] V} :
    Representation.IsInvariantForm π.toRepresentation (bilinFormOfTensor t) ↔
      t ∈ (tprod π π).invariants :=
  ⟨mem_invariants_of_isInvariantForm_bilinFormOfTensor π hπ,
    isInvariantForm_bilinFormOfTensor π hπ⟩

omit [TopologicalSpace G] in
/-- Membership in the invariants of the symmetric square, read in the tensor square. -/
theorem mem_invariants_symmetricSquare_iff {x : symmetricTensors 𝕜 V} :
    x ∈ (symmetricSquare π).invariants ↔ (x : V ⊗[𝕜] V) ∈ (tprod π π).invariants := by
  simp only [mem_invariants, Subtype.ext_iff, ← ContinuousLinearMap.coe_coe (symmetricSquare π _),
    symmetricSquare_apply, coe_symmetricTensorsRestrict_apply,
    ContRepresentation.tprod_apply, TensorProduct.mapL_apply]

omit [TopologicalSpace G] in
/-- Membership in the invariants of the exterior square, read in the tensor square. -/
theorem mem_invariants_exteriorSquare_iff {x : antisymmetricTensors 𝕜 V} :
    x ∈ (exteriorSquare π).invariants ↔ (x : V ⊗[𝕜] V) ∈ (tprod π π).invariants := by
  simp only [mem_invariants, Subtype.ext_iff, ← ContinuousLinearMap.coe_coe (exteriorSquare π _),
    exteriorSquare_apply, coe_antisymmetricTensorsRestrict_apply,
    ContRepresentation.tprod_apply, TensorProduct.mapL_apply]

omit [TopologicalSpace G] in
/-- **A nonzero invariant symmetric form is the same thing as a nonzero invariant tensor of the
symmetric square.** -/
theorem exists_ne_zero_isSymm_isInvariantForm_iff [FiniteDimensional 𝕜 V] (hπ : IsUnitary π) :
    (∃ B : BilinForm 𝕜 V,
        Representation.IsInvariantForm π.toRepresentation B ∧ B ≠ 0 ∧ B.IsSymm) ↔
      (symmetricSquare π).invariants ≠ ⊥ := by
  constructor
  · rintro ⟨B, hB, hB0, hsymm⟩
    obtain ⟨t, rfl⟩ := bilinFormOfTensor_surjective B
    have ht : t ∈ symmetricTensors 𝕜 V := isSymm_bilinFormOfTensor_iff.mp hsymm
    refine (Submodule.ne_bot_iff _).mpr ⟨⟨t, ht⟩, ?_, ?_⟩
    · exact (mem_invariants_symmetricSquare_iff π).mpr
        ((isInvariantForm_bilinFormOfTensor_iff π hπ).mp hB)
    · simpa [Subtype.ext_iff] using fun h => hB0 (by rw [h, map_zero])
  · intro h
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp h
    refine ⟨bilinFormOfTensor (x : V ⊗[𝕜] V), ?_, ?_, ?_⟩
    · exact isInvariantForm_bilinFormOfTensor π hπ ((mem_invariants_symmetricSquare_iff π).mp hx)
    · rw [Ne, bilinFormOfTensor_eq_zero_iff]
      exact fun h0 => hx0 (Subtype.ext h0)
    · exact isSymm_bilinFormOfTensor_iff.mpr x.2

omit [TopologicalSpace G] in
/-- **A nonzero invariant alternating form is the same thing as a nonzero invariant tensor of the
exterior square.** -/
theorem exists_ne_zero_isAlt_isInvariantForm_iff [FiniteDimensional 𝕜 V] (hπ : IsUnitary π) :
    (∃ B : BilinForm 𝕜 V,
        Representation.IsInvariantForm π.toRepresentation B ∧ B ≠ 0 ∧ B.IsAlt) ↔
      (exteriorSquare π).invariants ≠ ⊥ := by
  constructor
  · rintro ⟨B, hB, hB0, halt⟩
    obtain ⟨t, rfl⟩ := bilinFormOfTensor_surjective B
    have ht : t ∈ antisymmetricTensors 𝕜 V := isAlt_bilinFormOfTensor_iff.mp halt
    refine (Submodule.ne_bot_iff _).mpr ⟨⟨t, ht⟩, ?_, ?_⟩
    · exact (mem_invariants_exteriorSquare_iff π).mpr
        ((isInvariantForm_bilinFormOfTensor_iff π hπ).mp hB)
    · simpa [Subtype.ext_iff] using fun h => hB0 (by rw [h, map_zero])
  · intro h
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp h
    refine ⟨bilinFormOfTensor (x : V ⊗[𝕜] V), ?_, ?_, ?_⟩
    · exact isInvariantForm_bilinFormOfTensor π hπ ((mem_invariants_exteriorSquare_iff π).mp hx)
    · rw [Ne, bilinFormOfTensor_eq_zero_iff]
      exact fun h0 => hx0 (Subtype.ext h0)
    · exact isAlt_bilinFormOfTensor_iff.mpr x.2

end Unitary

end ContRepresentation
