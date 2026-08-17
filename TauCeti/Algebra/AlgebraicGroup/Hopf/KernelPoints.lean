/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.HopfAlgebra.Kernel

/-!
# Points of kernel quotients

For a surjective morphism of Hopf algebras `f : H →ₐc[R] K`, the quotient by the Hopf-ideal
kernel is bialgebra-equivalent to `K`. This file transports that first isomorphism theorem to
functors of points: for every commutative `R`-algebra `A`, the convolution group of `A`-points
of `H ⧸ ker f` is multiplicatively equivalent to the convolution group of `A`-points of `K`.

The characteristic compatibility says that including an `A`-point of `H ⧸ ker f` back into
the ambient `H`-points is the same as first identifying it with a `K`-point and then
pre-composing along `f`. This compatibility with the closed-subgroup inclusion assumes the
source Hopf algebra `H` is commutative.

## Main declarations

* `TauCeti.HopfIdeal.quotientKerPointsMulEquiv`: the equivalence between points of the
  kernel quotient and points of the codomain.
* `TauCeti.HopfIdeal.quotientKerPointsMulEquiv_apply`: its action by pre-composition with the
  inverse quotient-kernel equivalence.
* `TauCeti.HopfIdeal.quotientKerPointsMulEquiv_symm_apply`: its inverse action by
  pre-composition with the kernel quotient equivalence.
* `TauCeti.HopfIdeal.quotientKerPointsMulEquiv_mapValue`: naturality in the value algebra.
* `TauCeti.HopfIdeal.mapValue_quotientKerPointsMulEquiv_symm_apply`: inverse naturality in the
  value algebra.
* `TauCeti.HopfIdeal.quotientPointsHom_quotientKerPointsMulEquiv_symm_apply`: compatibility of
  the inverse equivalence with the quotient-points inclusion.
* `TauCeti.HopfIdeal.quotientPointsHom_quotientKerPointsMulEquiv_apply`: the corresponding
  compatibility for an arbitrary point of the kernel quotient.

## References

This is a Layer 3 prerequisite for `TauCetiRoadmap/ReductiveGroups/README.md`, "Hopf ideals
↔ closed subgroup schemes", specifically the kernels part of the Hopf-ideal dictionary. It
uses the first isomorphism theorem `TauCeti.HopfIdeal.kerLiftBialgEquiv` and the
contravariant points functoriality `TauCeti.AlgHom.mapDomainMulEquiv`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w x

namespace HopfIdeal

variable {R : Type u} [CommRing R]
variable {H : Type v} {K : Type w}

section RingSource

variable [Ring H] [Ring K] [HopfAlgebra R H] [HopfAlgebra R K]

/-- The points of the quotient by the Hopf-ideal kernel of a surjective Hopf algebra
morphism are the points of its codomain.

Contravariantly, this is induced by the bialgebra equivalence
`H ⧸ ker f ≃ₐc[R] K` from the Hopf-algebra first isomorphism theorem. -/
noncomputable def quotientKerPointsMulEquiv (f : H →ₐc[R] K)
    (hf : Function.Surjective f) (A : CommAlgCat.{x} R) :
    WithConv (H ⧸ (ker f hf).toIdeal →ₐ[R] A) ≃* WithConv (K →ₐ[R] A) :=
  (AlgHom.mapDomainMulEquiv (A := A) (kerLiftBialgEquiv f hf)).symm

/-- The quotient-kernel point equivalence acts by pre-composition with the inverse
bialgebra equivalence `K ≃ₐc[R] H ⧸ ker f`. -/
theorem quotientKerPointsMulEquiv_apply (f : H →ₐc[R] K)
    (hf : Function.Surjective f) (A : CommAlgCat.{x} R)
    (g : WithConv (H ⧸ (ker f hf).toIdeal →ₐ[R] A)) :
    quotientKerPointsMulEquiv f hf A g =
      AlgHom.mapDomain (A := A)
        ((kerLiftBialgEquiv f hf).symm : K →ₐc[R] H ⧸ (ker f hf).toIdeal) g := by
  rw [quotientKerPointsMulEquiv, AlgHom.mapDomainMulEquiv_symm_apply]

/-- The inverse quotient-kernel point equivalence acts by pre-composition with the
bialgebra equivalence `H ⧸ ker f ≃ₐc[R] K`. -/
theorem quotientKerPointsMulEquiv_symm_apply (f : H →ₐc[R] K)
    (hf : Function.Surjective f) (A : CommAlgCat.{x} R)
    (g : WithConv (K →ₐ[R] A)) :
    (quotientKerPointsMulEquiv f hf A).symm g =
      AlgHom.mapDomain (A := A)
        (kerLiftBialgEquiv f hf : H ⧸ (ker f hf).toIdeal →ₐc[R] K) g := by
  rw [quotientKerPointsMulEquiv, MulEquiv.symm_symm, AlgHom.mapDomainMulEquiv_apply]

/-- The quotient-kernel point equivalence is natural in the value algebra. -/
theorem quotientKerPointsMulEquiv_mapValue {B : Type*} [CommRing B] [Algebra R B]
    (f : H →ₐc[R] K) (hf : Function.Surjective f) (A : CommAlgCat.{x} R)
    (χ : A →ₐ[R] B) (g : WithConv (H ⧸ (ker f hf).toIdeal →ₐ[R] A)) :
    quotientKerPointsMulEquiv f hf (CommAlgCat.of R B)
        (AlgHom.mapValue (H := H ⧸ (ker f hf).toIdeal) χ g) =
      AlgHom.mapValue (H := K) χ (quotientKerPointsMulEquiv f hf A g) := by
  rw [quotientKerPointsMulEquiv_apply, quotientKerPointsMulEquiv_apply]
  exact DFunLike.congr_fun
    (AlgHom.mapValue_mapDomain
      ((kerLiftBialgEquiv f hf).symm : K →ₐc[R] H ⧸ (ker f hf).toIdeal) χ) g

/-- The inverse quotient-kernel point equivalence is natural in the value algebra. -/
theorem mapValue_quotientKerPointsMulEquiv_symm_apply {B : Type*} [CommRing B] [Algebra R B]
    (f : H →ₐc[R] K) (hf : Function.Surjective f) (A : CommAlgCat.{x} R)
    (χ : A →ₐ[R] B) (g : WithConv (K →ₐ[R] A)) :
    AlgHom.mapValue (H := H ⧸ (ker f hf).toIdeal) χ
        ((quotientKerPointsMulEquiv f hf A).symm g) =
      (quotientKerPointsMulEquiv f hf (CommAlgCat.of R B)).symm
        (AlgHom.mapValue (H := K) χ g) := by
  rw [quotientKerPointsMulEquiv_symm_apply, quotientKerPointsMulEquiv_symm_apply]
  exact (DFunLike.congr_fun
    (AlgHom.mapValue_mapDomain
      (kerLiftBialgEquiv f hf : H ⧸ (ker f hf).toIdeal →ₐc[R] K) χ) g).symm

end RingSource

section CommSource

variable [CommRing H] [Ring K] [HopfAlgebra R H] [HopfAlgebra R K]

/-- Including the quotient point attached to a `K`-point back into ambient `H`-points is
pre-composition along the original surjective Hopf algebra morphism. -/
theorem quotientPointsHom_quotientKerPointsMulEquiv_symm_apply (f : H →ₐc[R] K)
    (hf : Function.Surjective f) (A : CommAlgCat.{x} R)
    (g : HopfAlgebra.points (R := R) (H := K) A) :
    CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H) (ker f hf) A
        ((quotientKerPointsMulEquiv f hf A).symm g) =
      AlgHom.mapDomain f g := by
  ext h
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply, quotientKerPointsMulEquiv_symm_apply,
    AlgHom.mapDomain_apply_apply, kerLiftBialgEquiv_toBialgHom, kerLiftBialgHom_mk]
  rw [AlgHom.mapDomain_apply_apply]

/-- Pointwise form of `quotientPointsHom_quotientKerPointsMulEquiv_symm_apply`. -/
theorem quotientPointsHom_quotientKerPointsMulEquiv_symm_apply_apply
    (f : H →ₐc[R] K) (hf : Function.Surjective f) (A : CommAlgCat.{x} R)
    (g : HopfAlgebra.points (R := R) (H := K) A) (h : H) :
    (CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H) (ker f hf) A
        ((quotientKerPointsMulEquiv f hf A).symm g)).ofConv h = g.ofConv (f h) := by
  rw [quotientPointsHom_quotientKerPointsMulEquiv_symm_apply, AlgHom.mapDomain_apply_apply]

/-- For an arbitrary point of `H ⧸ ker f`, the quotient-points inclusion agrees with first
identifying it as a `K`-point and then pre-composing along `f`. -/
theorem quotientPointsHom_quotientKerPointsMulEquiv_apply (f : H →ₐc[R] K)
    (hf : Function.Surjective f) (A : CommAlgCat.{x} R)
    (g : HopfAlgebra.points (R := R) (H := H ⧸ (ker f hf).toIdeal) A) :
    CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H) (ker f hf) A g =
      AlgHom.mapDomain f (quotientKerPointsMulEquiv f hf A g) := by
  convert quotientPointsHom_quotientKerPointsMulEquiv_symm_apply f hf A
    (quotientKerPointsMulEquiv f hf A g)
  exact (MulEquiv.symm_apply_apply (quotientKerPointsMulEquiv f hf A) g).symm

/-- Pointwise form of `quotientPointsHom_quotientKerPointsMulEquiv_apply`. -/
theorem quotientPointsHom_quotientKerPointsMulEquiv_apply_apply (f : H →ₐc[R] K)
    (hf : Function.Surjective f) (A : CommAlgCat.{x} R)
    (g : HopfAlgebra.points (R := R) (H := H ⧸ (ker f hf).toIdeal) A) (h : H) :
    (CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H) (ker f hf) A g).ofConv h =
      (quotientKerPointsMulEquiv f hf A g).ofConv (f h) := by
  rw [quotientPointsHom_quotientKerPointsMulEquiv_apply, AlgHom.mapDomain_apply_apply]

end CommSource

end HopfIdeal

end TauCeti
