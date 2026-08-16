/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation

/-!
# Translations of the identity component

Right translation by a `k`-rational point induces a homeomorphism of the prime spectrum. This file
proves that a point in the connected component of the counit translates that component onto itself
and preserves its defining idempotent and ideal.

## Main declarations

* `rightTranslationHomeomorph_image_connectedComponent_augmentationPoint_eq_self`: a point in the
  identity component translates that component to itself.
* `map_rightTranslationAlgEquiv_connectedComponentIdeal_eq_self`: translation by an
  identity-component point fixes its defining ideal.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 6.7.

This is the translation prerequisite for Layer 3, "Identity component `G°` and component group
`π₀(G)`", of the ReductiveGroups roadmap.  The next step uses these automorphisms to prove
that multiplication carries the product of the identity component with itself into the identity
component, giving comultiplication closure of its defining ideal.
-/

public section

open AlgebraicGeometry

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [_root_.HopfAlgebra k H]

/-- Right translation transports the connected component of a point to the connected component
of its translate. -/
theorem rightTranslationHomeomorph_image_connectedComponent
    (g : WithConv (H →ₐ[k] k)) (x : Spec (CommRingCat.of H)) :
    rightTranslationHomeomorph g '' connectedComponent x =
      connectedComponent (rightTranslationHomeomorph g x) := by
  simpa only [connectedComponentIn_univ,
    Set.image_univ_of_surjective (rightTranslationHomeomorph g).surjective] using
    (rightTranslationHomeomorph g).image_connectedComponentIn
      (s := Set.univ) (x := x) (Set.mem_univ x)

/-- A point in the identity component right-translates that component onto itself. -/
theorem rightTranslationHomeomorph_image_connectedComponent_augmentationPoint_eq_self
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    rightTranslationHomeomorph g ''
        connectedComponent (Bialgebra.augmentationPoint k H) =
      connectedComponent (Bialgebra.augmentationPoint k H) := by
  rw [rightTranslationHomeomorph_image_connectedComponent,
    rightTranslationHomeomorph_apply, AlgEquiv.toRingEquiv_toRingHom,
    comap_rightTranslationAlgEquiv_augmentationPoint]
  exact (connectedComponent_eq hg).symm

variable [LocallyConnectedSpace (PrimeSpectrum H)]

private theorem connectedComponentIdempotent_kernelPoint_eq_augmentationPoint
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    PrimeSpectrum.connectedComponentIdempotent (AlgHom.kernelPoint g.ofConv) =
      PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H) := by
  let p : PrimeSpectrum H := AlgHom.kernelPoint g.ofConv
  let e : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  -- `Spec (CommRingCat.of H)` has `PrimeSpectrum H` as its reducible carrier.
  change PrimeSpectrum.connectedComponentIdempotent p =
    PrimeSpectrum.connectedComponentIdempotent e
  change p ∈ connectedComponent e at hg
  apply (PrimeSpectrum.eq_connectedComponentIdempotent_iff
    (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent p) e).mpr
  rw [PrimeSpectrum.basicOpen_connectedComponentIdempotent]
  exact (connectedComponent_eq hg).symm

private theorem connectedComponentIdeal_kernelPoint_eq_augmentationPoint
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    PrimeSpectrum.connectedComponentIdeal (AlgHom.kernelPoint g.ofConv) =
      PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) := by
  let p : PrimeSpectrum H := AlgHom.kernelPoint g.ofConv
  let e : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  have h := connectedComponentIdempotent_kernelPoint_eq_augmentationPoint g hg
  -- Reduce the two `Spec` point abbreviations once, then use the named idempotent equality.
  change PrimeSpectrum.connectedComponentIdempotent p =
    PrimeSpectrum.connectedComponentIdempotent e at h
  change PrimeSpectrum.connectedComponentIdeal p = PrimeSpectrum.connectedComponentIdeal e
  apply Ideal.ext
  intro x
  rw [PrimeSpectrum.mem_connectedComponentIdeal_iff,
    PrimeSpectrum.mem_connectedComponentIdeal_iff, h]

/-- The inverse coordinate-algebra automorphism of translation by an identity-component point
fixes the idempotent selecting the identity component. -/
@[simp]
theorem rightTranslationAlgEquiv_symm_connectedComponentIdempotent_eq_self
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    (rightTranslationAlgEquiv g).symm
        (PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H)) =
      PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H) := by
  have he : PrimeSpectrum.comap
      ((rightTranslationAlgEquiv g).toRingEquiv : H →+* H)
        (Bialgebra.augmentationPoint k H) =
      AlgHom.kernelPoint g.ofConv :=
    comap_rightTranslationAlgEquiv_augmentationPoint g
  calc
    (rightTranslationAlgEquiv g).symm
        (PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H)) =
      PrimeSpectrum.connectedComponentIdempotent
        (PrimeSpectrum.comap
          (((rightTranslationAlgEquiv g).symm.toRingEquiv).symm : H →+* H)
            (Bialgebra.augmentationPoint k H)) :=
      PrimeSpectrum.map_connectedComponentIdempotent
        (rightTranslationAlgEquiv g).symm.toRingEquiv (Bialgebra.augmentationPoint k H)
    _ = PrimeSpectrum.connectedComponentIdempotent
        (PrimeSpectrum.comap
          ((rightTranslationAlgEquiv g).toRingEquiv : H →+* H)
            (Bialgebra.augmentationPoint k H)) := by
      rw [AlgEquiv.symm_toRingEquiv, RingEquiv.symm_symm]
    _ = PrimeSpectrum.connectedComponentIdempotent (AlgHom.kernelPoint g.ofConv) :=
      congrArg PrimeSpectrum.connectedComponentIdempotent he
    _ = PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H) :=
      connectedComponentIdempotent_kernelPoint_eq_augmentationPoint g hg

/-- The coordinate-algebra automorphism of translation by an identity-component point fixes the
idempotent selecting the identity component. -/
@[simp]
theorem rightTranslationAlgEquiv_connectedComponentIdempotent_eq_self
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    rightTranslationAlgEquiv g
        (PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H)) =
      PrimeSpectrum.connectedComponentIdempotent (Bialgebra.augmentationPoint k H) := by
  have h := congrArg (rightTranslationAlgEquiv g)
    (rightTranslationAlgEquiv_symm_connectedComponentIdempotent_eq_self g hg)
  simpa using h.symm

/-- Translation by a point in the identity component fixes the ideal cutting out that
component. -/
@[simp]
theorem map_rightTranslationAlgEquiv_connectedComponentIdeal_eq_self
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) :
    Ideal.map (rightTranslationAlgEquiv g)
        (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)) =
      PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) := by
  let φ : H ≃+* H := (rightTranslationAlgEquiv g).toRingEquiv
  let p : PrimeSpectrum H := AlgHom.kernelPoint g.ofConv
  let e : PrimeSpectrum H := Bialgebra.augmentationPoint k H
  let I : Ideal H := PrimeSpectrum.connectedComponentIdeal e
  -- Reduce the algebra-equivalence and `Spec` wrappers once; the proof below stays in the generic
  -- ring-equivalence and prime-spectrum API.
  change Ideal.map φ I = I
  have he : PrimeSpectrum.comap (φ : H →+* H) e = p := by
    change PrimeSpectrum.comap
        ((rightTranslationAlgEquiv g).toRingEquiv : H →+* H)
          (Bialgebra.augmentationPoint k H) =
      AlgHom.kernelPoint g.ofConv
    exact comap_rightTranslationAlgEquiv_augmentationPoint g
  have hp : PrimeSpectrum.connectedComponentIdeal p = I := by
    change PrimeSpectrum.connectedComponentIdeal (AlgHom.kernelPoint g.ofConv) =
      PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)
    exact connectedComponentIdeal_kernelPoint_eq_augmentationPoint g hg
  have hsymm : Ideal.map φ.symm I = I := by
    calc
      Ideal.map φ.symm I =
          PrimeSpectrum.connectedComponentIdeal
            (PrimeSpectrum.comap (φ.symm.symm : H →+* H) e) :=
        PrimeSpectrum.map_connectedComponentIdeal φ.symm e
      _ = PrimeSpectrum.connectedComponentIdeal (PrimeSpectrum.comap (φ : H →+* H) e) := by
        rw [RingEquiv.symm_symm]
      _ = PrimeSpectrum.connectedComponentIdeal p :=
        congrArg PrimeSpectrum.connectedComponentIdeal he
      _ = I := hp
  calc
    Ideal.map φ I = Ideal.map φ (Ideal.map φ.symm I) := by rw [hsymm]
    _ = Ideal.map ((φ : H →+* H).comp (φ.symm : H →+* H)) I :=
      Ideal.map_map (φ.symm : H →+* H) (φ : H →+* H)
    _ = I := by simp

/-- Membership in the identity-component ideal is invariant under translation by a point of the
identity component. -/
@[simp]
theorem rightTranslationAlgEquiv_mem_connectedComponentIdeal_iff
    (g : WithConv (H →ₐ[k] k))
    (hg : AlgHom.kernelPoint g.ofConv ∈
      connectedComponent (Bialgebra.augmentationPoint k H)) {x : H} :
    rightTranslationAlgEquiv g x ∈
        PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) ↔
      x ∈ PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) := by
  have hmap := map_rightTranslationAlgEquiv_connectedComponentIdeal_eq_self g hg
  calc
    rightTranslationAlgEquiv g x ∈
          PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) ↔
        rightTranslationAlgEquiv g x ∈
          Ideal.map (rightTranslationAlgEquiv g)
            (PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)) := by
      rw [hmap]
    _ ↔ x ∈ PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) :=
      Ideal.apply_mem_of_equiv_iff
        (I := PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H))
        (f := (rightTranslationAlgEquiv g).toRingEquiv) (x := x)

end TauCeti.HopfAlgebra
