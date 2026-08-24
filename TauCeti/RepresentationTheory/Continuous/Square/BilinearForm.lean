/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BilinearForm
public import TauCeti.RepresentationTheory.Continuous.Square.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# Invariant tensors and invariant bilinear forms

On an inner product space the inner product identifies the tensor square `V ⊗[𝕜] V` with the
bilinear forms on `V`: a tensor `t` becomes the form `B_t (v, w) = ⟪t, v ⊗ₜ w⟫`,
`TauCeti.bilinFormOfTensor`, built in
`TauCeti/Analysis/InnerProductSpace/BilinearForm.lean` together with its injectivity, its
surjectivity in finite dimensions and the fact that it carries the symmetric tensors to the
symmetric forms and the antisymmetric tensors to the alternating ones.

This file makes that identification **equivariant**: for a **unitary** representation `π`, the
invariants of the tensor square `π ⊗ π` become the invariant forms of `π`, in the sense of
`TauCeti.Representation.IsInvariantForm`. Together with the symmetry dictionary this says that the
two eigenspaces of the flip that
`TauCeti/RepresentationTheory/Continuous/Square/Invariants.lean` counts are, invariant vector by
invariant vector, the invariant symmetric and the invariant alternating forms. That is the
dictionary the compact-group Frobenius-Schur trichotomy is read off from in
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/InvariantForm.lean`; it is the analytic
counterpart of `TauCeti/LinearAlgebra/BilinearForm/Squares.lean`, which does the same job for
finite groups through the dual of the symmetric and exterior powers rather than through an inner
product.

Nothing here needs a group, a measure, or compactness, so everything is stated over a topological
monoid with `RCLike` scalars. Unitarity is what makes the dictionary equivariant: `π g ⊗ π g`
preserves the inner product of the tensor square, so moving it across `⟪t, v ⊗ₜ w⟫` costs nothing.

## Main statements

* `ContRepresentation.isInvariantForm_bilinFormOfTensor_iff`: the form of a tensor is invariant for
  a unitary representation exactly when the tensor is invariant for the tensor square.
* `ContRepresentation.exists_ne_zero_isSymm_isInvariantForm_iff` and
  `ContRepresentation.exists_ne_zero_isAlt_isInvariantForm_iff`: **a nonzero invariant symmetric,
  respectively alternating, form exists exactly when the symmetric, respectively exterior, square
  has a nonzero invariant tensor.**

## Implementation notes

The last two statements are two readings of one argument, which is why they are both deduced from
the private `ContRepresentation.exists_ne_zero_isInvariantForm_iff`, stated for an arbitrary
subrepresentation of the tensor square cut out by a property of the corresponding forms.

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
/-- A nonzero invariant form with a property `P` is the same thing as a nonzero invariant tensor of
the subrepresentation of the tensor square that `P` cuts out. Both squares are such a
subrepresentation, for `P = IsSymm` and for `P = IsAlt`. -/
private theorem exists_ne_zero_isInvariantForm_iff [FiniteDimensional 𝕜 V] (hπ : IsUnitary π)
    {W : Submodule 𝕜 (V ⊗[𝕜] V)} {σ : ContRepresentation 𝕜 G W}
    (hσ : ∀ x : W, x ∈ σ.invariants ↔ (x : V ⊗[𝕜] V) ∈ (tprod π π).invariants)
    {P : BilinForm 𝕜 V → Prop} (hP : ∀ t : V ⊗[𝕜] V, P (bilinFormOfTensor t) ↔ t ∈ W) :
    (∃ B : BilinForm 𝕜 V,
        Representation.IsInvariantForm π.toRepresentation B ∧ B ≠ 0 ∧ P B) ↔
      σ.invariants ≠ ⊥ := by
  constructor
  · rintro ⟨B, hB, hB0, hPB⟩
    obtain ⟨t, rfl⟩ := bilinFormOfTensor_surjective B
    refine (Submodule.ne_bot_iff _).mpr ⟨⟨t, (hP t).mp hPB⟩, ?_, ?_⟩
    · exact (hσ _).mpr ((isInvariantForm_bilinFormOfTensor_iff π hπ).mp hB)
    · simpa [Subtype.ext_iff] using fun h => hB0 (by rw [h, map_zero])
  · intro h
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp h
    refine ⟨bilinFormOfTensor (x : V ⊗[𝕜] V), ?_, ?_, ?_⟩
    · exact isInvariantForm_bilinFormOfTensor π hπ ((hσ x).mp hx)
    · rw [Ne, bilinFormOfTensor_eq_zero_iff]
      exact fun h0 => hx0 (Subtype.ext h0)
    · exact (hP _).mpr x.2

omit [TopologicalSpace G] in
/-- **A nonzero invariant symmetric form is the same thing as a nonzero invariant tensor of the
symmetric square.** -/
theorem exists_ne_zero_isSymm_isInvariantForm_iff [FiniteDimensional 𝕜 V] (hπ : IsUnitary π) :
    (∃ B : BilinForm 𝕜 V,
        Representation.IsInvariantForm π.toRepresentation B ∧ B ≠ 0 ∧ B.IsSymm) ↔
      (symmetricSquare π).invariants ≠ ⊥ :=
  exists_ne_zero_isInvariantForm_iff π hπ (fun _ => mem_invariants_symmetricSquare_iff π)
    fun _ => isSymm_bilinFormOfTensor_iff

omit [TopologicalSpace G] in
/-- **A nonzero invariant alternating form is the same thing as a nonzero invariant tensor of the
exterior square.** -/
theorem exists_ne_zero_isAlt_isInvariantForm_iff [FiniteDimensional 𝕜 V] (hπ : IsUnitary π) :
    (∃ B : BilinForm 𝕜 V,
        Representation.IsInvariantForm π.toRepresentation B ∧ B ≠ 0 ∧ B.IsAlt) ↔
      (exteriorSquare π).invariants ≠ ⊥ :=
  exists_ne_zero_isInvariantForm_iff π hπ (fun _ => mem_invariants_exteriorSquare_iff π)
    fun _ => isAlt_bilinFormOfTensor_iff

end Unitary

end ContRepresentation
