/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
import TauCeti.Algebra.AlgebraicGroup.Tangent.Dimension
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation

/-!
# The conormal sequence of a closed affine subgroup

Let `I` be a Hopf ideal of a commutative Hopf algebra `H`. The quotient map `H ⟶ H/I` induces a
surjection on augmentation cotangent spaces. Its kernel is the image of `I` in the ambient
cotangent space, the conormal space of the corresponding closed subgroup at the identity. Thus
there is a short exact sequence over any commutative base ring

`N* ⟶ Tₑ*G ⟶ Tₑ*V(I) ⟶ 0`.

Dualizing recovers the injective differential constructed in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent`. In finite dimension, rank-nullity gives
`dim Lie(V(I)) + dim N* = dim Lie(G)`. This is the closed-subgroup conormal and dimension tool
needed in Layer 2 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.HopfIdeal.conormalSubspace`: the image of the defining Hopf ideal in the ambient
  augmentation cotangent space.
* `TauCeti.HopfIdeal.quotientCotangentMap`: the map on cotangent spaces induced by the quotient.
* `TauCeti.HopfIdeal.quotientCotangentMap_toCotangent`: the quotient map on an augmentation-ideal
  representative.
* `TauCeti.HopfIdeal.cotangentLinearEquiv_comp_quotientCotangentMap`: dualizing the cotangent map
  gives the differential of the closed-subgroup inclusion.
* `TauCeti.HopfIdeal.quotientCotangentMap_surjective`: right exactness of the conormal sequence.
* `TauCeti.HopfIdeal.ker_quotientCotangentMap`: its kernel is the conormal subspace.
* `TauCeti.HopfIdeal.finrank_quotientLie_add_finrank_conormal`: the resulting dimension formula.
* `TauCeti.HopfIdeal.finrank_quotientLie_le`: the resulting closed-subgroup dimension bound.

## References

J. S. Milne, *Algebraic Groups* (2017), §10.a; the conormal sequence is the cotangent-space
form of the tangent inclusion of a closed subgroup. The implementation uses Mathlib's general
`Ideal.mapCotangent` exactness API.
-/

public section

namespace TauCeti

namespace HopfIdeal

universe u v w

variable {k : Type u} {H : Type v}

section Ring

variable [CommRing k] [CommRing H] [HopfAlgebra k H]

/-- A Hopf ideal is contained in the augmentation ideal. -/
private theorem toIdeal_le_augmentationIdeal (I : HopfIdeal k H) :
    I.toIdeal ≤ Bialgebra.AugmentationIdeal k H := by
  have hI := toIdeal_le_toIdeal.mpr I.le_augmentation
  rw [augmentation_toIdeal] at hI
  exact hI

/-- The image of a closed subgroup's defining Hopf ideal in the ambient augmentation cotangent
space. This is the conormal space at the identity, equivalently
`I / (I ∩ (ker ε)²)` embedded in `(ker ε) / (ker ε)²`. -/
noncomputable def conormalSubspace (I : HopfIdeal k H) :
    Submodule k (Bialgebra.CotangentSpace k H) :=
  (I.toIdeal.restrictScalars k).map (Bialgebra.cotangentMap k H)

/-- Membership in the conormal subspace means being represented by an element of the defining
Hopf ideal. -/
@[simp]
theorem mem_conormalSubspace_iff (I : HopfIdeal k H)
    (x : Bialgebra.CotangentSpace k H) :
    x ∈ conormalSubspace I ↔
      ∃ y : H, y ∈ I.toIdeal ∧ Bialgebra.cotangentMap k H y = x := by
  rw [conormalSubspace, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

/-- The quotient map carries the augmentation ideal of `H` into the augmentation ideal of
`H/I`. -/
private theorem augmentationIdeal_le_comap_quotient (I : HopfIdeal k H) :
    Bialgebra.AugmentationIdeal k H ≤
      (Bialgebra.AugmentationIdeal k (H ⧸ I.toIdeal)).comap
        (algebraMap H (H ⧸ I.toIdeal)) := by
  intro x hx
  rw [Bialgebra.AugmentationIdeal, Ideal.mem_comap, RingHom.mem_ker]
  simpa [Bialgebra.AugmentationIdeal, RingHom.mem_ker] using hx

/-- The map on augmentation cotangent spaces induced by the quotient `H ⟶ H/I`. -/
noncomputable def quotientCotangentMap (I : HopfIdeal k H) :
    Bialgebra.CotangentSpace k H →ₗ[k]
      Bialgebra.CotangentSpace k (H ⧸ I.toIdeal) :=
  (Ideal.mapCotangent
      (Bialgebra.AugmentationIdeal k H)
      (Bialgebra.AugmentationIdeal k (H ⧸ I.toIdeal))
      (Algebra.ofId H (H ⧸ I.toIdeal))
      (by
        intro x hx
        rw [Ideal.mem_comap, Algebra.ofId_apply]
        exact augmentationIdeal_le_comap_quotient I hx)).restrictScalars k

/-- The quotient cotangent map sends the class of an augmentation-ideal element to the class of
its image in the quotient. -/
@[simp]
theorem quotientCotangentMap_toCotangent (I : HopfIdeal k H)
    (x : Bialgebra.AugmentationIdeal k H) :
    quotientCotangentMap I
        ((Bialgebra.AugmentationIdeal k H).toCotangent x) =
      (Bialgebra.AugmentationIdeal k (H ⧸ I.toIdeal)).toCotangent
        ⟨algebraMap H (H ⧸ I.toIdeal) x, by
          have hx : Coalgebra.counit (R := k) (x : H) = 0 := x.property
          rw [Bialgebra.AugmentationIdeal, RingHom.mem_ker]
          simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            Ideal.Quotient.algebraMap_eq, Bialgebra.counitAlgHom_apply,
            Bialgebra.Quotient.counit_mk] using hx⟩ := by
  rw [quotientCotangentMap, LinearMap.restrictScalars_apply,
    Ideal.mapCotangent_toCotangent]
  apply (Bialgebra.AugmentationIdeal k (H ⧸ I.toIdeal)).toCotangent.congr_arg
  ext
  exact Algebra.ofId_apply (H ⧸ I.toIdeal) (x : H)

/-- The quotient cotangent map sends the first-order displacement of `x` to the first-order
displacement of its quotient class. -/
theorem quotientCotangentMap_cotangentMap (I : HopfIdeal k H) (x : H) :
    quotientCotangentMap I (Bialgebra.cotangentMap k H x) =
      Bialgebra.cotangentMap k (H ⧸ I.toIdeal) (Ideal.Quotient.mkₐ k I.toIdeal x) := by
  rw [Bialgebra.cotangentMap_apply, quotientCotangentMap_toCotangent,
    Bialgebra.cotangentMap_apply]
  apply (Bialgebra.AugmentationIdeal k (H ⧸ I.toIdeal)).toCotangent.congr_arg
  -- Both the quotient counit and its algebra map compute on representatives definitionally.
  rfl

/-- Under cotangent duality, precomposition by the quotient cotangent map is the differential
of the closed-subgroup inclusion. -/
@[simp]
theorem cotangentLinearEquiv_comp_quotientCotangentMap
    {B : Type w} [CommRing B] [Algebra k B] (I : HopfIdeal k H)
    (f : Bialgebra.CotangentSpace k (H ⧸ I.toIdeal) →ₗ[k] B) :
    quotientLieHom (B := B) I
        (Derivation.cotangentLinearEquiv (R := k) (A := H ⧸ I.toIdeal) (B := B) f) =
      Derivation.cotangentLinearEquiv (R := k) (A := H) (B := B)
        (f.comp (quotientCotangentMap I)) := by
  apply Derivation.ext
  intro x
  apply (Bialgebra.CounitAlgebra.algEquivSelf k H B).injective
  rw [quotientLieHom_apply_apply,
    Derivation.cotangentLinearEquiv_apply_apply,
    Derivation.cotangentLinearEquiv_apply_apply, LinearMap.comp_apply,
    quotientCotangentMap_cotangentMap]
  exact congrArg
    (fun b : B => Bialgebra.CounitAlgebra.algEquivSelf k H B
      (b : Bialgebra.CounitAlgebra k H B))
    (Bialgebra.CounitAlgebra.algEquivSelf_apply k (H ⧸ I.toIdeal) B
      (f (Bialgebra.cotangentMap k (H ⧸ I.toIdeal)
        (Ideal.Quotient.mkₐ k I.toIdeal x)) :
          Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) B))

/-- The augmentation ideal of the quotient pulls back to the augmentation ideal of `H`. -/
private theorem comap_augmentationIdeal_quotient (I : HopfIdeal k H) :
    (Bialgebra.AugmentationIdeal k (H ⧸ I.toIdeal)).comap
        (algebraMap H (H ⧸ I.toIdeal)) =
      Bialgebra.AugmentationIdeal k H := by
  apply le_antisymm
  · intro x hx
    rw [Bialgebra.AugmentationIdeal, RingHom.mem_ker]
    simpa [Bialgebra.AugmentationIdeal, Ideal.mem_comap, RingHom.mem_ker] using hx
  · exact augmentationIdeal_le_comap_quotient I

/-- The map from the ambient cotangent space to the closed subgroup's cotangent space is
surjective. -/
theorem quotientCotangentMap_surjective (I : HopfIdeal k H) :
    Function.Surjective (quotientCotangentMap I) := by
  exact Ideal.mapCotangent_surjective_of_comap_eq
    (Ideal.Quotient.mkₐ_surjective H I.toIdeal)
    (by
      rw [comap_augmentationIdeal_quotient, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
      exact (sup_eq_right.mpr (toIdeal_le_augmentationIdeal I)).symm)

/-- The kernel of the quotient cotangent map is exactly the conormal subspace, giving the
exact conormal sequence of a closed affine subgroup at the identity. -/
theorem ker_quotientCotangentMap (I : HopfIdeal k H) :
    LinearMap.ker (quotientCotangentMap I) = conormalSubspace I := by
  rw [quotientCotangentMap, LinearMap.ker_restrictScalars]
  rw [Ideal.mapCotangent_ker_of_surjective
    (Ideal.Quotient.mkₐ_surjective H I.toIdeal)
    (by
      rw [comap_augmentationIdeal_quotient, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
      exact (sup_eq_right.mpr (toIdeal_le_augmentationIdeal I)).symm)]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [conormalSubspace]
    refine ⟨(x : H), ?_, ?_⟩
    · have h := (Ideal.mem_inf.mp (Submodule.mem_comap.mp hx)).1
      rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] at h
      exact (Submodule.restrictScalars_mem k I.toIdeal (x : H)).mpr h
    · rw [Bialgebra.cotangentMap_augmentation]
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ I.toIdeal :=
      (Submodule.restrictScalars_mem k I.toIdeal x).mp hx
    refine ⟨⟨x, toIdeal_le_augmentationIdeal I hx'⟩, ?_, ?_⟩
    · exact Submodule.mem_comap.mpr
        (Ideal.mem_inf.mpr ⟨by simpa only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker],
          toIdeal_le_augmentationIdeal I hx'⟩)
    · exact (Bialgebra.cotangentMap_augmentation
        (R := k) (A := H) ⟨x, toIdeal_le_augmentationIdeal I hx'⟩).symm

end Ring

section Field

variable [Field k] [CommRing H] [HopfAlgebra k H]

/-- In finite dimension, the dimension of the closed subgroup's cotangent space plus its
conormal dimension is the dimension of the ambient cotangent space. -/
theorem finrank_quotientCotangent_add_finrank_conormal (I : HopfIdeal k H)
    [FiniteDimensional k (Bialgebra.CotangentSpace k H)] :
    Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ I.toIdeal)) +
        Module.finrank k (conormalSubspace I) =
      Module.finrank k (Bialgebra.CotangentSpace k H) := by
  rw [← LinearMap.finrank_range_add_finrank_ker (quotientCotangentMap I),
    ker_quotientCotangentMap]
  rw [LinearMap.range_eq_top.mpr (quotientCotangentMap_surjective I),
    finrank_top]

/-- For a finite-dimensional ambient cotangent space, the Lie algebra dimension of a closed
subgroup plus its conormal dimension is the Lie algebra dimension of the ambient group. -/
theorem finrank_quotientLie_add_finrank_conormal (I : HopfIdeal k H)
    [FiniteDimensional k (Bialgebra.CotangentSpace k H)] :
    Module.finrank k
          (Derivation k (H ⧸ I.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)) +
        Module.finrank k (conormalSubspace I) =
      Module.finrank k
        (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  have hquotient :
      Module.finrank k
          (Derivation k (H ⧸ I.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)) =
        Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ I.toIdeal)) :=
    Derivation.finrank_eq_finrank_cotangentSpace
      (k := k) (H := H ⧸ I.toIdeal)
  have hambient :
      Module.finrank k
          (Derivation k H (Bialgebra.CounitAlgebra k H k)) =
        Module.finrank k (Bialgebra.CotangentSpace k H) :=
    Derivation.finrank_eq_finrank_cotangentSpace (k := k) (H := H)
  rw [hquotient, hambient]
  exact finrank_quotientCotangent_add_finrank_conormal I

/-- The Lie dimension of a closed subgroup is at most the Lie dimension of the ambient affine
group when the ambient cotangent space is finite-dimensional. -/
theorem finrank_quotientLie_le (I : HopfIdeal k H)
    [FiniteDimensional k (Bialgebra.CotangentSpace k H)] :
    Module.finrank k
        (Derivation k (H ⧸ I.toIdeal)
          (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)) ≤
      Module.finrank k
        (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  have h := finrank_quotientLie_add_finrank_conormal I
  omega

end Field

end HopfIdeal

end TauCeti
