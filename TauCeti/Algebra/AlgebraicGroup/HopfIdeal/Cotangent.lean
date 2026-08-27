/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.Algebra.HopfAlgebra.Kernel
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
* `TauCeti.HopfIdeal.quotientLieHom_surjective_iff_conormalSubspace_eq_bot`: the
  closed-subgroup differential is onto exactly when its conormal space vanishes.
* `TauCeti.HopfIdeal.conormalSubspace_eq_bot_iff_toIdeal_le_sq_augmentationIdeal`: conormal
  vanishing means that the defining ideal has no linear term at the identity.
* `TauCeti.HopfIdeal.finrank_quotientLie_add_finrank_conormal`: the resulting dimension formula.
* `TauCeti.HopfIdeal.finrank_quotientLie_le`: the resulting closed-subgroup dimension bound.
* `TauCeti.HopfIdeal.finrank_quotientLie_antitone`: inclusion of closed subgroups cannot increase
  Lie dimension.

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

/-- Enlarging the defining Hopf ideal enlarges the conormal space of the corresponding closed
subgroup at the identity. -/
theorem conormalSubspace_mono {I J : HopfIdeal k H} (hIJ : I ≤ J) :
    conormalSubspace I ≤ conormalSubspace J := by
  rw [conormalSubspace, conormalSubspace]
  exact Submodule.map_mono (Submodule.restrictScalars_mono k
    (HopfIdeal.toIdeal_le_toIdeal.mpr hIJ))

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

/-- A closed subgroup has zero conormal space at the identity exactly when every element of its
defining ideal vanishes to second order there. -/
@[simp]
theorem conormalSubspace_eq_bot_iff_toIdeal_le_sq_augmentationIdeal
    (I : HopfIdeal k H) :
    conormalSubspace I = ⊥ ↔
      I.toIdeal ≤ Bialgebra.AugmentationIdeal k H ^ 2 := by
  constructor
  · intro hconormal x hx
    have hxconormal : Bialgebra.cotangentMap k H x ∈ conormalSubspace I :=
      (mem_conormalSubspace_iff I _).2 ⟨x, hx, rfl⟩
    rw [hconormal, Submodule.mem_bot] at hxconormal
    let x' : Bialgebra.AugmentationIdeal k H :=
      ⟨x, toIdeal_le_augmentationIdeal I hx⟩
    rw [Bialgebra.cotangentMap_augmentation (x := x')] at hxconormal
    exact
      ((Bialgebra.AugmentationIdeal k H).toCotangent_eq_zero x').1 hxconormal
  · intro hsquare
    apply le_bot_iff.1
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_conormalSubspace_iff I y).1 hy
    let x' : Bialgebra.AugmentationIdeal k H :=
      ⟨x, toIdeal_le_augmentationIdeal I hx⟩
    rw [Bialgebra.cotangentMap_augmentation (x := x'), Submodule.mem_bot,
      Ideal.toCotangent_eq_zero]
    exact hsquare hx

end Ring

section Field

variable [Field k] [CommRing H] [HopfAlgebra k H]

/-- The differential of a closed-subgroup inclusion is surjective exactly when the subgroup has
zero conormal space at the identity. Equivalently, the inclusion is an infinitesimal equality at
the identity. -/
theorem quotientLieHom_surjective_iff_conormalSubspace_eq_bot
    (I : HopfIdeal k H) :
    Function.Surjective (quotientLieHom (B := k) I) ↔
      conormalSubspace I = ⊥ := by
  constructor
  · intro hsurjective
    rw [← ker_quotientCotangentMap, LinearMap.ker_eq_bot,
      ← LinearMap.dualMap_surjective_iff]
    intro f
    obtain ⟨d, hd⟩ := hsurjective
      (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) f)
    refine ⟨(Derivation.cotangentLinearEquiv
      (R := k) (A := H ⧸ I.toIdeal) (B := k)).symm d, ?_⟩
    apply (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).injective
    rw [LinearMap.dualMap_apply',
      ← cotangentLinearEquiv_comp_quotientCotangentMap,
      (Derivation.cotangentLinearEquiv
        (R := k) (A := H ⧸ I.toIdeal) (B := k)).apply_symm_apply]
    exact hd
  · intro hconormal
    have hinjective : Function.Injective (quotientCotangentMap I) := by
      rw [← LinearMap.ker_eq_bot, ker_quotientCotangentMap]
      exact hconormal
    have hdual : Function.Surjective (quotientCotangentMap I).dualMap :=
      LinearMap.dualMap_surjective_of_injective hinjective
    intro d
    obtain ⟨f, hf⟩ := hdual
      ((Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).symm d)
    refine ⟨Derivation.cotangentLinearEquiv
      (R := k) (A := H ⧸ I.toIdeal) (B := k) f, ?_⟩
    rw [cotangentLinearEquiv_comp_quotientCotangentMap,
      ← LinearMap.dualMap_apply', hf,
      (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).apply_symm_apply]

/-- The kernel of a surjective Hopf-algebra morphism has zero conormal space when the
differential of the morphism is surjective. -/
theorem conormalSubspace_ker_eq_bot_of_surjective_of_derivationCompLieHom_surjective
    {K : Type w} [CommRing K] [HopfAlgebra k K] (f : H →ₐc[k] K)
    (hf : Function.Surjective f)
    (hdf : Function.Surjective (derivationCompLieHom (B := k) f)) :
    conormalSubspace (ker f) = ⊥ := by
  have hkerOf : conormalSubspace (kerOfSurjective f hf) = ⊥ := by
    apply
      (quotientLieHom_surjective_iff_conormalSubspace_eq_bot
        (kerOfSurjective f hf)).1
    intro d
    obtain ⟨e, he⟩ := hdf d
    refine ⟨derivationCompLieHom (B := k) (kerLiftBialgHom f hf) e, ?_⟩
    -- `quotientLieHom` is not exposed, so rewrite it through its public application lemma.
    have hquotient :
        quotientLieHom (B := k) (kerOfSurjective f hf) =
          derivationCompLieHom (B := k)
            (Bialgebra.Quotient.mkBialgHom (kerOfSurjective f hf).toIdeal) := by
      ext d x
      rw [quotientLieHom_apply_apply, derivationCompLieHom_apply, derivationComp_apply]
      exact Bialgebra.CounitAlgebra.algEquivSelf_apply
        k (H ⧸ (kerOfSurjective f hf).toIdeal) k
        (d (Ideal.Quotient.mkₐ k (kerOfSurjective f hf).toIdeal x))
    rw [hquotient]
    calc
      derivationCompLieHom (B := k)
          (Bialgebra.Quotient.mkBialgHom (kerOfSurjective f hf).toIdeal)
          (derivationCompLieHom (B := k) (kerLiftBialgHom f hf) e) =
        ((derivationCompLieHom (B := k)
            (Bialgebra.Quotient.mkBialgHom (kerOfSurjective f hf).toIdeal)).comp
          (derivationCompLieHom (B := k) (kerLiftBialgHom f hf))) e := rfl
      _ = derivationCompLieHom (B := k)
          ((kerLiftBialgHom f hf).comp
            (Bialgebra.Quotient.mkBialgHom (kerOfSurjective f hf).toIdeal)) e := by
        rw [derivationCompLieHom_comp]
      _ = derivationCompLieHom (B := k) f e := by
        rw [kerLiftBialgHom_comp_mkBialgHom]
      _ = d := he
  simpa only [kerOfSurjective_eq_ker] using hkerOf

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

/-- Lie dimension is antitone in the defining Hopf ideal: if `I ≤ J`, then the closed subgroup
cut out by `J` is contained in the one cut out by `I`, so its Lie dimension is no larger. -/
theorem finrank_quotientLie_antitone
    [FiniteDimensional k (Bialgebra.CotangentSpace k H)] :
    Antitone fun I : HopfIdeal k H ↦
      Module.finrank k
        (Derivation k (H ⧸ I.toIdeal)
          (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)) := by
  intro I J hIJ
  dsimp only
  have hI := finrank_quotientLie_add_finrank_conormal I
  have hJ := finrank_quotientLie_add_finrank_conormal J
  have hconormal : Module.finrank k (conormalSubspace I) ≤
      Module.finrank k (conormalSubspace J) :=
    Submodule.finrank_mono (conormalSubspace_mono hIJ)
  omega

end Field

end HopfIdeal

end TauCeti
