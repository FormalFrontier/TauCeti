/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.Comultiplication
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic

/-!
# The identity-component affine group scheme

Let `H` be a finite-type commutative Hopf algebra over an algebraically closed field.  The ideal
cutting out the connected component of the counit point is a Hopf ideal.  This file takes its
quotient Hopf algebra and packages the corresponding Hopf spectrum as the identity-component
affine group scheme `G⁰`.

The underlying prime spectrum is canonically homeomorphic to the connected component of the
augmentation point in `Spec H`.  The morphism `G⁰ ⟶ G` is the closed immersion induced by the
quotient coordinate map.  On rational points its image consists exactly of the points whose
kernel belongs to the augmentation point's connected component.

The construction here is over an algebraically closed ground field.  Descent to an arbitrary
field, compatibility with geometric base change, and the finite étale component group are
separate parts of the roadmap.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.identityComponent`: the quotient coordinate Hopf algebra of
  the identity component.
* `TauCeti.FiniteTypeCommHopfAlgCat.identityComponentSpec`: its affine group scheme.
* `TauCeti.FiniteTypeCommHopfAlgCat.identityComponentSpecι`: the canonical closed immersion into
  the ambient affine group scheme.
* `TauCeti.FiniteTypeCommHopfAlgCat.identityComponentPrimeSpectrumHomeomorph`: the identification
  of its spectrum with the augmentation point's connected component.
* `TauCeti.FiniteTypeCommHopfAlgCat.identityComponentPointsHom`: the inclusion on points.
* `TauCeti.FiniteTypeCommHopfAlgCat.mem_range_identityComponentPointsHom_iff`: the corresponding
  characterization on rational points.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 6.7.

This advances Layer 3, "Identity component `G⁰` and component group `π₀(G)`", of the
ReductiveGroups roadmap by constructing `G⁰` over an algebraically closed field.  Descent,
geometric base-change compatibility, and construction of `π₀(G)` remain.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The finite-type coordinate Hopf algebra of the identity component.

It is the quotient by the Hopf ideal cutting out the connected component of the counit point. -/
noncomputable abbrev identityComponent (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    FiniteTypeCommHopfAlgCat.{u, u} k :=
  quotient H (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))

/-- The coordinate morphism from an affine group to its identity component.  Contravariantly,
this is the inclusion of the identity-component group scheme into the ambient group scheme. -/
noncomputable abbrev identityComponentCoordinateMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) : H ⟶ identityComponent H :=
  mkQuotient H (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))

/-- The kernel of the identity-component coordinate morphism is the ideal cutting out the
connected component of the augmentation point. -/
theorem identityComponentCoordinateMap_ker
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    RingHom.ker (toBialgHom (identityComponentCoordinateMap H)).toAlgHom.toRingHom =
      PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) := by
  rw [mkQuotient_ker, HopfAlgebra.identityComponentHopfIdeal_toIdeal]

/-- The prime spectrum of the identity-component coordinate algebra is canonically
homeomorphic to the connected component of the augmentation point. -/
noncomputable def identityComponentPrimeSpectrumHomeomorph
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    PrimeSpectrum (identityComponent H) ≃ₜ
      (connectedComponent (Bialgebra.augmentationPoint k H) : Set (PrimeSpectrum H)) := by
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let _ : LocallyConnectedSpace (PrimeSpectrum H) := inferInstance
  -- Expose the finite-type and Hopf-algebra quotient wrappers at their common carrier.
  change PrimeSpectrum
      (H ⧸ (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal) ≃ₜ _
  exact (PrimeSpectrum.quotientHomeomorphZeroLocus
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal).trans
      (Homeomorph.setCongr (by
        rw [HopfAlgebra.identityComponentHopfIdeal_toIdeal]
        exact PrimeSpectrum.zeroLocus_connectedComponentIdeal
          (Bialgebra.augmentationPoint k H)))

/-- After coercion to the ambient prime spectrum, the identity-component homeomorphism sends a
point to its contraction along the identity-component coordinate map. -/
@[simp]
theorem identityComponentPrimeSpectrumHomeomorph_apply_coe
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (x : PrimeSpectrum (identityComponent H)) :
    (identityComponentPrimeSpectrumHomeomorph H x : PrimeSpectrum H) =
      PrimeSpectrum.comap
        (toBialgHom (identityComponentCoordinateMap H)).toAlgHom.toRingHom x := by
  simp only [identityComponentPrimeSpectrumHomeomorph, id_eq, Homeomorph.trans_apply]
  change (PrimeSpectrum.quotientHomeomorphZeroLocus
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal x :
      PrimeSpectrum H) = _
  exact PrimeSpectrum.quotientHomeomorphZeroLocus_apply_coe _ x

/-- The spectrum of the identity-component coordinate algebra is connected. -/
noncomputable instance connectedSpace_identityComponent
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ConnectedSpace (PrimeSpectrum (identityComponent H)) := by
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let _ : LocallyConnectedSpace (PrimeSpectrum H) := inferInstance
  -- Expose the finite-type and Hopf-algebra quotient wrappers at their common carrier.
  change ConnectedSpace (PrimeSpectrum
    (H ⧸ (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal))
  rw [HopfAlgebra.identityComponentHopfIdeal_toIdeal]
  exact PrimeSpectrum.connectedSpace_quotient_connectedComponentIdeal
    (Bialgebra.augmentationPoint k H)

/-- The identity-component affine group scheme represented by `identityComponent H`. -/
noncomputable abbrev identityComponentSpec
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Grp (Over (Spec (CommRingCat.of k))) :=
  CommHopfAlgCat.quotientSpec H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))

/-- The canonical morphism from the identity-component affine group scheme to the ambient
affine group scheme. -/
noncomputable abbrev identityComponentSpecι
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    identityComponentSpec H ⟶
      (hopfSpec (CommRingCat.of k)).obj (op H.obj) :=
  CommHopfAlgCat.quotientSpecι H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))

/-- The canonical inclusion of the identity-component affine group scheme is a closed
immersion. -/
instance isClosedImmersion_identityComponentSpecι
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsClosedImmersion (identityComponentSpecι H).hom.hom.left :=
  CommHopfAlgCat.isClosedImmersion_quotientSpecι H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))

/-- The scheme underlying the identity-component group scheme has connected carrier. -/
noncomputable instance connectedSpace_identityComponentSpec
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ConnectedSpace (identityComponentSpec H).X.left := by
  -- `hopfSpec` reaches the ordinary spectrum through several categorical wrappers.
  change ConnectedSpace (PrimeSpectrum (identityComponent H))
  infer_instance

/-- On underlying topological spaces, the identity-component inclusion is contraction along the
quotient coordinate map. -/
theorem identityComponentSpecι_apply
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : (identityComponentSpec H).X.left) :
    (identityComponentSpecι H).hom.hom.left x =
      PrimeSpectrum.comap
        (toBialgHom (identityComponentCoordinateMap H)).toAlgHom.toRingHom x := by
  rw [identityComponentSpecι, CommHopfAlgCat.quotientSpecι_def]
  rfl

/-- The image of the identity-component inclusion on underlying topological spaces is exactly
the connected component of the augmentation point. -/
theorem range_identityComponentSpecι
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Set.range (identityComponentSpecι H).hom.hom.left =
      connectedComponent (Bialgebra.augmentationPoint k H) := by
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let _ : LocallyConnectedSpace (PrimeSpectrum H) := inferInstance
  let f := (toBialgHom (identityComponentCoordinateMap H)).toAlgHom.toRingHom
  have hf : Function.Surjective f :=
    Ideal.Quotient.mkₐ_surjective k
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal
  have hker : RingHom.ker f =
      PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H) := by
    dsimp only [f]
    exact identityComponentCoordinateMap_ker H
  -- Expose the ordinary spectra underlying `hopfSpec` before applying the ring-theoretic range
  -- theorem for a surjective coordinate map.
  change Set.range (fun x : PrimeSpectrum (identityComponent H) ↦
      (identityComponentSpecι H).hom.hom.left x) =
    (connectedComponent (Bialgebra.augmentationPoint k H) : Set (PrimeSpectrum H))
  have hmap : Set.range (fun x : PrimeSpectrum (identityComponent H) ↦
      (identityComponentSpecι H).hom.hom.left x) =
      Set.range (PrimeSpectrum.comap f) :=
    congrArg Set.range (funext fun x ↦ identityComponentSpecι_apply H x)
  have hrange : Set.range (PrimeSpectrum.comap f) =
      PrimeSpectrum.zeroLocus (RingHom.ker f) :=
    range_comap_of_surjective _ f hf
  have hzero : PrimeSpectrum.zeroLocus (RingHom.ker f) =
      (connectedComponent (Bialgebra.augmentationPoint k H) : Set (PrimeSpectrum H)) := by
    rw [hker]
    exact PrimeSpectrum.zeroLocus_connectedComponentIdeal
      (Bialgebra.augmentationPoint k H)
  exact hmap.trans (hrange.trans hzero)

/-- The canonical inclusion from the identity component to the ambient group on `A`-points. -/
noncomputable abbrev identityComponentPointsHom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k) :
    HopfAlgebra.points (R := k) (H := identityComponent H) A ⟶
      HopfAlgebra.points (R := k) (H := H) A :=
  CommHopfAlgCat.quotientPointsHom H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) A

/-- A rational point of the ambient affine group lies in the image of the identity-component
points exactly when its kernel point belongs to the connected component of the augmentation
point. -/
theorem mem_range_identityComponentPointsHom_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    g ∈ Set.range (identityComponentPointsHom H (CommAlgCat.of k k)) ↔
      AlgHom.kernelPoint g.ofConv ∈
        connectedComponent (Bialgebra.augmentationPoint k H) := by
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let _ : LocallyConnectedSpace (PrimeSpectrum H) := inferInstance
  rw [CommHopfAlgCat.mem_range_quotientPointsHom_iff]
  let I := PrimeSpectrum.connectedComponentIdeal (Bialgebra.augmentationPoint k H)
  have hcomponent : PrimeSpectrum.zeroLocus (I : Set H) =
      connectedComponent (Bialgebra.augmentationPoint k H) :=
    PrimeSpectrum.zeroLocus_connectedComponentIdeal (Bialgebra.augmentationPoint k H)
  constructor
  · intro hg
    have hz : AlgHom.kernelPoint g.ofConv ∈ PrimeSpectrum.zeroLocus (I : Set H) := by
      exact (PrimeSpectrum.mem_zeroLocus (AlgHom.kernelPoint g.ofConv) (I : Set H)).mpr <|
        fun h hh ↦ by
          rw [AlgHom.kernelPoint_asIdeal]
          exact RingHom.mem_ker.mpr <|
            hg h (HopfAlgebra.mem_identityComponentHopfIdeal.mpr hh)
    exact hcomponent ▸ hz
  · intro hg h hh
    have hz : AlgHom.kernelPoint g.ofConv ∈ PrimeSpectrum.zeroLocus (I : Set H) :=
      hcomponent.symm ▸ hg
    have hz' : (I : Set H) ⊆ (AlgHom.kernelPoint g.ofConv).asIdeal :=
      (PrimeSpectrum.mem_zeroLocus (AlgHom.kernelPoint g.ofConv) (I : Set H)).mp hz
    have hker : h ∈ RingHom.ker (g.ofConv : H →+* k) := by
      rw [← AlgHom.kernelPoint_asIdeal]
      exact hz' (HopfAlgebra.mem_identityComponentHopfIdeal.mp hh)
    exact RingHom.mem_ker.mp hker

end TauCeti.FiniteTypeCommHopfAlgCat
