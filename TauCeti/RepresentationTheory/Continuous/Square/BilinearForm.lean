/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BilinearForm
public import TauCeti.RepresentationTheory.Continuous.Square.Basic
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# Invariant tensors and invariant bilinear forms

On an inner product space the inner product turns a tensor `t` of the tensor square `V ⊗[𝕜] V` into
the bilinear form `B_t (v, w) = ⟪t, v ⊗ₜ w⟫`, `TauCeti.BilinForm.ofTensor`, built in
`TauCeti/Analysis/InnerProductSpace/BilinearForm.lean` together with its injectivity, its
surjectivity **in finite dimensions** -- only there is it an identification of the tensor square
with all of `BilinForm 𝕜 V` -- and the fact that it carries the symmetric tensors to the symmetric
forms and the antisymmetric tensors to the alternating ones.

This file makes that construction **equivariant**: for a **unitary** representation `π`, the
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

Nothing here needs a topology on `G`, a measure, compactness, or even inverses: the acting object
is a monoid. Unitarity is what makes the dictionary equivariant: `π g ⊗ π g` preserves the inner
product of the tensor square, so moving it across `⟪t, v ⊗ₜ w⟫` costs nothing. That an invariant
*form* comes from an invariant *tensor* needs in addition that the pure tensors `π g v ⊗ₜ π g w`
still span, which is why the converse asks that every action operator be surjective. That
hypothesis is free in the two situations it is used in: a group representation satisfies it in
every dimension (`Representation.apply_bijective`), and a unitary one satisfies it whenever `V` is
finite-dimensional (`TauCeti.ContRepresentation.IsUnitary.surjective`), which is how the results
below that need `TauCeti.BilinForm.ofTensor_surjective` anyway discharge it.

## Main definitions

* `ContRepresentation.invariantsEquivInvariantForms`: in finite dimensions, the invariants of the
  tensor square **are** the invariant forms, conjugate-linearly.
* `ContRepresentation.symmetricSquareInvariantsEquivSymmetricInvariantForms` and
  `ContRepresentation.exteriorSquareInvariantsEquivAlternatingInvariantForms`: the same for the two
  squares, whose invariants are the invariant **symmetric**, respectively **alternating**, forms.

## Main statements

* `ContRepresentation.isInvariantForm_ofTensor` and
  `ContRepresentation.isInvariantForm_ofTensor_iff`: the form of a tensor is invariant for a unitary
  representation as soon as the tensor is invariant for the tensor square, and exactly then once
  the action operators are surjective.
* `ContRepresentation.map_ofTensor_invariants`: the same statement for the two spaces, rather than
  vector by vector.
* `ContRepresentation.exists_isInvariantForm_isSymm_ne_zero_iff` and
  `ContRepresentation.exists_isInvariantForm_isAlt_ne_zero_iff`: **a nonzero invariant symmetric,
  respectively alternating, form exists exactly when the symmetric, respectively exterior, square
  has a nonzero invariant tensor.**

## Implementation notes

The last two statements are two readings of one argument, which is why they are both deduced from
the private `ContRepresentation.exists_isInvariantForm_ne_zero_iff`, stated for an arbitrary
subrepresentation of the tensor square cut out by a property of the corresponding forms. The two
equivalences for the squares are read off the same shape, from the private
`ContRepresentation.invariantsEquivOfMemIff`.

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

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (π : ContRepresentation 𝕜 G V)

/-- **The form of an invariant tensor is invariant.** Moving `π g ⊗ π g` across the inner product
costs nothing because the representation is unitary. -/
theorem isInvariantForm_ofTensor (hπ : IsUnitary π) {t : V ⊗[𝕜] V}
    (ht : t ∈ (tprod π π).invariants) :
    Representation.IsInvariantForm π.toRepresentation (BilinForm.ofTensor t) := by
  refine Representation.isInvariantForm_iff.mpr fun g v w => ?_
  have hg : (tprod π π) g (v ⊗ₜ[𝕜] w) = π g v ⊗ₜ[𝕜] π g w := by simp
  calc BilinForm.ofTensor t (π g v) (π g w)
      = ⟪(tprod π π) g t, (tprod π π) g (v ⊗ₜ[𝕜] w)⟫_𝕜 := by
        rw [(mem_invariants t).mp ht g, hg, BilinForm.ofTensor_apply]
    _ = ⟪t, v ⊗ₜ[𝕜] w⟫_𝕜 := (hπ.tprod hπ).inner_map_map g t (v ⊗ₜ[𝕜] w)
    _ = BilinForm.ofTensor t v w := (BilinForm.ofTensor_apply t v w).symm

/-- **A tensor whose form is invariant is invariant**, as soon as every action operator is
surjective, so that the pure tensors `π g v ⊗ₜ π g w` still span the tensor square. -/
private theorem mem_invariants_of_isInvariantForm_ofTensor (hπ : IsUnitary π)
    (hsurj : ∀ g : G, Function.Surjective (π g)) {t : V ⊗[𝕜] V}
    (hB : Representation.IsInvariantForm π.toRepresentation (BilinForm.ofTensor t)) :
    t ∈ (tprod π π).invariants := by
  refine (mem_invariants t).mpr fun g => ?_
  have key : ∀ a b : V, ⟪(tprod π π) g t, a ⊗ₜ[𝕜] b⟫_𝕜 = ⟪t, a ⊗ₜ[𝕜] b⟫_𝕜 := by
    intro a b
    obtain ⟨v, rfl⟩ := hsurj g a
    obtain ⟨w, rfl⟩ := hsurj g b
    have hg : (tprod π π) g (v ⊗ₜ[𝕜] w) = π g v ⊗ₜ[𝕜] π g w := by simp
    calc ⟪(tprod π π) g t, π g v ⊗ₜ[𝕜] π g w⟫_𝕜
        = ⟪(tprod π π) g t, (tprod π π) g (v ⊗ₜ[𝕜] w)⟫_𝕜 := by rw [hg]
      _ = ⟪t, v ⊗ₜ[𝕜] w⟫_𝕜 := (hπ.tprod hπ).inner_map_map g t (v ⊗ₜ[𝕜] w)
      _ = BilinForm.ofTensor t v w := (BilinForm.ofTensor_apply t v w).symm
      _ = BilinForm.ofTensor t (π g v) (π g w) :=
          (Representation.isInvariantForm_iff.mp hB g v w).symm
      _ = ⟪t, π g v ⊗ₜ[𝕜] π g w⟫_𝕜 := BilinForm.ofTensor_apply t _ _
  rw [← sub_eq_zero, ← BilinForm.ofTensor_eq_zero_iff]
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply, BilinForm.ofTensor_apply, inner_sub_left, key]
  exact sub_self _

/-- **The form of a tensor is invariant exactly when the tensor is invariant.** This is a statement
about one tensor at a time; that *every* invariant form is the form of an invariant tensor is
`TauCeti.ContRepresentation.map_ofTensor_invariants`, which needs finite dimensions. The
surjectivity hypothesis holds for a group representation in every dimension, and for a unitary
representation of any monoid in finite dimensions
(`TauCeti.ContRepresentation.IsUnitary.surjective`). -/
@[simp, grind =]
theorem isInvariantForm_ofTensor_iff (hπ : IsUnitary π)
    (hsurj : ∀ g : G, Function.Surjective (π g)) {t : V ⊗[𝕜] V} :
    Representation.IsInvariantForm π.toRepresentation (BilinForm.ofTensor t) ↔
      t ∈ (tprod π π).invariants :=
  ⟨mem_invariants_of_isInvariantForm_ofTensor π hπ hsurj, isInvariantForm_ofTensor π hπ⟩

/-- **The invariant tensors of the tensor square are exactly the invariant forms**, as submodules:
the image of the invariants under `TauCeti.BilinForm.ofTensor` is
`TauCeti.Representation.invariantForms`. -/
theorem map_ofTensor_invariants [FiniteDimensional 𝕜 V] (hπ : IsUnitary π) :
    Submodule.map (BilinForm.ofTensor : V ⊗[𝕜] V →ₛₗ[starRingEnd 𝕜] BilinForm 𝕜 V)
        (tprod π π).invariants = Representation.invariantForms π.toRepresentation := by
  refine Submodule.ext fun B => ⟨?_, fun hB => ?_⟩
  · rintro ⟨t, ht, rfl⟩
    exact Representation.mem_invariantForms.mpr (isInvariantForm_ofTensor π hπ ht)
  · obtain ⟨t, rfl⟩ := BilinForm.ofTensor_surjective B
    exact ⟨t, (isInvariantForm_ofTensor_iff π hπ hπ.surjective).mp
      (Representation.mem_invariantForms.mp hB), rfl⟩

/-- **The invariants of the tensor square are the invariant forms**, conjugate-linearly: the
equivalence `TauCeti.BilinForm.ofTensorEquiv` restricted to the invariants. -/
noncomputable def invariantsEquivInvariantForms [FiniteDimensional 𝕜 V] (hπ : IsUnitary π) :
    (tprod π π).invariants ≃ₛₗ[starRingEnd 𝕜]
      Representation.invariantForms π.toRepresentation :=
  (BilinForm.ofTensorEquiv.submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (by rw [BilinForm.coe_ofTensorEquiv]; exact map_ofTensor_invariants π hπ))

@[simp]
theorem coe_invariantsEquivInvariantForms_apply [FiniteDimensional 𝕜 V] (hπ : IsUnitary π)
    (t : (tprod π π).invariants) :
    (invariantsEquivInvariantForms π hπ t : BilinForm 𝕜 V) =
      BilinForm.ofTensor (t : V ⊗[𝕜] V) := by
  simp [invariantsEquivInvariantForms]

/-- The invariant forms with a property `P` are the image of the invariants of the subrepresentation
of the tensor square that `P` cuts out. Both squares are such a subrepresentation, for `P = IsSymm`
and for `P = IsAlt`. -/
private theorem map_ofTensor_map_subtype_invariants [FiniteDimensional 𝕜 V] (hπ : IsUnitary π)
    {W : Submodule 𝕜 (V ⊗[𝕜] V)} {σ : ContRepresentation 𝕜 G W}
    (hσ : ∀ x : W, x ∈ σ.invariants ↔ (x : V ⊗[𝕜] V) ∈ (tprod π π).invariants)
    {P : BilinForm 𝕜 V → Prop} (hP : ∀ t : V ⊗[𝕜] V, P (BilinForm.ofTensor t) ↔ t ∈ W)
    {S : Submodule 𝕜 (BilinForm 𝕜 V)}
    (hS : ∀ B : BilinForm 𝕜 V,
      B ∈ S ↔ Representation.IsInvariantForm π.toRepresentation B ∧ P B) :
    Submodule.map (BilinForm.ofTensor : V ⊗[𝕜] V →ₛₗ[starRingEnd 𝕜] BilinForm 𝕜 V)
        (Submodule.map W.subtype σ.invariants) = S := by
  refine Submodule.ext fun B => ⟨?_, fun hB => ?_⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact (hS _).mpr ⟨isInvariantForm_ofTensor π hπ ((hσ x).mp hx), (hP _).mpr x.2⟩
  · obtain ⟨hBinv, hPB⟩ := (hS B).mp hB
    obtain ⟨t, rfl⟩ := BilinForm.ofTensor_surjective B
    exact ⟨t, ⟨⟨t, (hP t).mp hPB⟩,
      (hσ _).mpr ((isInvariantForm_ofTensor_iff π hπ hπ.surjective).mp hBinv), rfl⟩, rfl⟩

/-- The invariants of such a subrepresentation, conjugate-linearly, as the invariant forms with the
property `P` that cuts it out. -/
private noncomputable def invariantsEquivOfMemIff [FiniteDimensional 𝕜 V] (hπ : IsUnitary π)
    {W : Submodule 𝕜 (V ⊗[𝕜] V)} {σ : ContRepresentation 𝕜 G W}
    (hσ : ∀ x : W, x ∈ σ.invariants ↔ (x : V ⊗[𝕜] V) ∈ (tprod π π).invariants)
    {P : BilinForm 𝕜 V → Prop} (hP : ∀ t : V ⊗[𝕜] V, P (BilinForm.ofTensor t) ↔ t ∈ W)
    {S : Submodule 𝕜 (BilinForm 𝕜 V)}
    (hS : ∀ B : BilinForm 𝕜 V,
      B ∈ S ↔ Representation.IsInvariantForm π.toRepresentation B ∧ P B) :
    σ.invariants ≃ₛₗ[starRingEnd 𝕜] S :=
  ((Submodule.equivMapOfInjective W.subtype (Submodule.injective_subtype W)
    σ.invariants).trans (BilinForm.ofTensorEquiv.submoduleMap _)).trans
      (LinearEquiv.ofEq _ _ (by
        rw [BilinForm.coe_ofTensorEquiv]
        exact map_ofTensor_map_subtype_invariants π hπ hσ hP hS))

/-- The form underlying an invariant tensor of such a subrepresentation, which is what the two
`@[simp]` lemmas below record for the two squares. -/
private theorem coe_invariantsEquivOfMemIff_apply [FiniteDimensional 𝕜 V] (hπ : IsUnitary π)
    {W : Submodule 𝕜 (V ⊗[𝕜] V)} {σ : ContRepresentation 𝕜 G W}
    (hσ : ∀ x : W, x ∈ σ.invariants ↔ (x : V ⊗[𝕜] V) ∈ (tprod π π).invariants)
    {P : BilinForm 𝕜 V → Prop} (hP : ∀ t : V ⊗[𝕜] V, P (BilinForm.ofTensor t) ↔ t ∈ W)
    {S : Submodule 𝕜 (BilinForm 𝕜 V)}
    (hS : ∀ B : BilinForm 𝕜 V,
      B ∈ S ↔ Representation.IsInvariantForm π.toRepresentation B ∧ P B)
    (x : σ.invariants) :
    (invariantsEquivOfMemIff π hπ hσ hP hS x : BilinForm 𝕜 V) =
      BilinForm.ofTensor ((x : W) : V ⊗[𝕜] V) := by
  simp [invariantsEquivOfMemIff]

/-- **The invariants of the symmetric square are the invariant symmetric forms**,
conjugate-linearly: the equivalence `TauCeti.BilinForm.ofTensorEquiv` restricted to them. -/
noncomputable def symmetricSquareInvariantsEquivSymmetricInvariantForms [FiniteDimensional 𝕜 V]
    (hπ : IsUnitary π) :
    (symmetricSquare π).invariants ≃ₛₗ[starRingEnd 𝕜]
      Representation.symmetricInvariantForms π.toRepresentation :=
  invariantsEquivOfMemIff π hπ (fun _ => mem_invariants_symmetricSquare_iff π)
    (fun _ => BilinForm.isSymm_ofTensor_iff) fun _ => Representation.mem_symmetricInvariantForms

@[simp]
theorem coe_symmetricSquareInvariantsEquivSymmetricInvariantForms_apply [FiniteDimensional 𝕜 V]
    (hπ : IsUnitary π) (x : (symmetricSquare π).invariants) :
    (symmetricSquareInvariantsEquivSymmetricInvariantForms π hπ x : BilinForm 𝕜 V) =
      BilinForm.ofTensor ((x : symmetricTensors 𝕜 V) : V ⊗[𝕜] V) :=
  coe_invariantsEquivOfMemIff_apply π hπ _ _ _ x

/-- **The invariants of the exterior square are the invariant alternating forms**,
conjugate-linearly: the equivalence `TauCeti.BilinForm.ofTensorEquiv` restricted to them. -/
noncomputable def exteriorSquareInvariantsEquivAlternatingInvariantForms [FiniteDimensional 𝕜 V]
    (hπ : IsUnitary π) :
    (exteriorSquare π).invariants ≃ₛₗ[starRingEnd 𝕜]
      Representation.alternatingInvariantForms π.toRepresentation :=
  invariantsEquivOfMemIff π hπ (fun _ => mem_invariants_exteriorSquare_iff π)
    (fun _ => BilinForm.isAlt_ofTensor_iff) fun _ => Representation.mem_alternatingInvariantForms

@[simp]
theorem coe_exteriorSquareInvariantsEquivAlternatingInvariantForms_apply [FiniteDimensional 𝕜 V]
    (hπ : IsUnitary π) (x : (exteriorSquare π).invariants) :
    (exteriorSquareInvariantsEquivAlternatingInvariantForms π hπ x : BilinForm 𝕜 V) =
      BilinForm.ofTensor ((x : antisymmetricTensors 𝕜 V) : V ⊗[𝕜] V) :=
  coe_invariantsEquivOfMemIff_apply π hπ _ _ _ x

/-- A nonzero invariant form with a property `P` is the same thing as a nonzero invariant tensor of
the subrepresentation of the tensor square that `P` cuts out. Both squares are such a
subrepresentation, for `P = IsSymm` and for `P = IsAlt`. -/
private theorem exists_isInvariantForm_ne_zero_iff [FiniteDimensional 𝕜 V] (hπ : IsUnitary π)
    {W : Submodule 𝕜 (V ⊗[𝕜] V)} {σ : ContRepresentation 𝕜 G W}
    (hσ : ∀ x : W, x ∈ σ.invariants ↔ (x : V ⊗[𝕜] V) ∈ (tprod π π).invariants)
    {P : BilinForm 𝕜 V → Prop} (hP : ∀ t : V ⊗[𝕜] V, P (BilinForm.ofTensor t) ↔ t ∈ W) :
    (∃ B : BilinForm 𝕜 V,
        Representation.IsInvariantForm π.toRepresentation B ∧ P B ∧ B ≠ 0) ↔
      σ.invariants ≠ ⊥ := by
  constructor
  · rintro ⟨B, hB, hPB, hB0⟩
    obtain ⟨t, rfl⟩ := BilinForm.ofTensor_surjective B
    refine (Submodule.ne_bot_iff _).mpr ⟨⟨t, (hP t).mp hPB⟩, ?_, ?_⟩
    · exact (hσ _).mpr ((isInvariantForm_ofTensor_iff π hπ hπ.surjective).mp hB)
    · simpa [Subtype.ext_iff] using fun h => hB0 (by rw [h, map_zero])
  · intro h
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp h
    refine ⟨BilinForm.ofTensor (x : V ⊗[𝕜] V), ?_, ?_, ?_⟩
    · exact isInvariantForm_ofTensor π hπ ((hσ x).mp hx)
    · exact (hP _).mpr x.2
    · rw [Ne, BilinForm.ofTensor_eq_zero_iff]
      exact fun h0 => hx0 (Subtype.ext h0)

/-- **A nonzero invariant symmetric form is the same thing as a nonzero invariant tensor of the
symmetric square.** -/
theorem exists_isInvariantForm_isSymm_ne_zero_iff [FiniteDimensional 𝕜 V] (hπ : IsUnitary π) :
    (∃ B : BilinForm 𝕜 V,
        Representation.IsInvariantForm π.toRepresentation B ∧ B.IsSymm ∧ B ≠ 0) ↔
      (symmetricSquare π).invariants ≠ ⊥ :=
  exists_isInvariantForm_ne_zero_iff π hπ (fun _ => mem_invariants_symmetricSquare_iff π)
    fun _ => BilinForm.isSymm_ofTensor_iff

/-- **A nonzero invariant alternating form is the same thing as a nonzero invariant tensor of the
exterior square.** -/
theorem exists_isInvariantForm_isAlt_ne_zero_iff [FiniteDimensional 𝕜 V] (hπ : IsUnitary π) :
    (∃ B : BilinForm 𝕜 V,
        Representation.IsInvariantForm π.toRepresentation B ∧ B.IsAlt ∧ B ≠ 0) ↔
      (exteriorSquare π).invariants ≠ ⊥ :=
  exists_isInvariantForm_ne_zero_iff π hπ (fun _ => mem_invariants_exteriorSquare_iff π)
    fun _ => BilinForm.isAlt_ofTensor_iff

end ContRepresentation
