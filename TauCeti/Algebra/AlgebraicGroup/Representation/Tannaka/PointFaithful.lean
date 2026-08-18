/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ScalarExtension
public import TauCeti.Algebra.Coalgebra.Comodule.PointSeparation

/-!
# Faithfulness of point automorphisms

An algebra-valued point of a Hopf algebra acts naturally on the scalar extension of every
comodule. This file proves that the resulting natural automorphism determines the point.

For all comodules, it is enough to inspect the regular comodule: its matrix coefficients generate
the whole Hopf algebra. For finitely generated comodules over a principal ideal domain, the
fundamental theorem of coalgebras replaces the generally infinite regular comodule by its finite
restricted subcomodules. Consequently, the point action on the finite scalar-extension functor is
faithful. Over a field this is the injectivity half of Tannakian reconstruction for affine group
schemes.

## Main declarations

* `TauCeti.Tannaka.pointNatIsoHom_injective`: point automorphisms on all comodules determine the
  point.
* `TauCeti.Tannaka.fgPointNatIsoHom_injective`: point automorphisms on finitely generated
  comodules determine the point over a principal ideal domain.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 4.5 and 9.4.
* M. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open CategoryTheory

namespace TauCeti.Tannaka

universe u v x

section AllComodules

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [HopfAlgebra R H]
variable (A : Type x) [CommSemiring A] [Algebra R A]

/-- The action of algebra-valued points on the scalar-extension functor of all comodules is
faithful. Equality of natural automorphisms on the regular comodule forces equality of the points
on its matrix coefficients, which generate `H`. -/
theorem pointNatIsoHom_injective :
    Function.Injective (pointNatIsoHom R H A :
      WithConv (H →ₐ[R] A) →*
        Aut (ComoduleCat.scalarExtensionFunctor.{u, v, v, x} R H A)) := by
  intro g h hgh
  let M : ComoduleCat.{u, v, v} R H := ComoduleCat.regular R H
  have happ := congrArg
    (fun a : Aut (ComoduleCat.scalarExtensionFunctor.{u, v, v, x} R H A) =>
      a.hom.app M) hgh
  rw [pointNatIsoHom_apply, pointNatIso_hom_app,
    pointNatIsoHom_apply, pointNatIso_hom_app] at happ
  rw [cancel_epi] at happ
  rw [cancel_mono] at happ
  apply WithConv.ofConv_injective
  apply Comodule.eq_of_endOfPoint_eq_of_matrixCoefficientSubalgebra_eq_top
    (M := H) g.ofConv h.ofConv
  · simpa only [M, LinearEquiv.toModuleIsoₛ_hom, SemimoduleCat.hom_ofHom,
      Comodule.pointsAction_toLinearMap] using congrArg SemimoduleCat.Hom.hom happ
  · exact Comodule.regular_matrixCoefficientSubalgebra_eq_top

end AllComodules

section FiniteComodules

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (H : Type v) [Semiring H] [HopfAlgebra R H] [Module.Free R H]
variable (A : Type x) [CommSemiring A] [Algebra R A]

/-- The action of algebra-valued points on the scalar-extension functor of finitely generated
comodules is faithful over a principal ideal domain when the Hopf algebra is free as a module.

In particular this applies over a field. The finite restricted regular comodules jointly separate
points, so equality of the natural automorphisms implies equality of the original algebra maps. -/
theorem fgPointNatIsoHom_injective :
    Function.Injective (fgPointNatIsoHom R H A :
      WithConv (H →ₐ[R] A) →*
        Aut (FGComoduleCat.scalarExtensionFunctor.{u, v, v, x} R H A)) := by
  intro g h hgh
  apply WithConv.ofConv_injective
  apply Comodule.eq_of_forall_finiteSubcoalgebra_endOfPoint_eq g.ofConv h.ofConv
  intro D hD
  have hDreg : Module.Finite R D.toRegularSubcomodule.toSubmodule := by
    rw [Subcoalgebra.toRegularSubcomodule_toSubmodule]
    exact hD
  let M : FGComoduleCat.{u, v, v} R H :=
    ⟨ComoduleCat.of R H D.toRegularSubcomodule, hDreg⟩
  have happ := congrArg
    (fun a : Aut (FGComoduleCat.scalarExtensionFunctor.{u, v, v, x} R H A) =>
      a.hom.app M) hgh
  rw [fgPointNatIsoHom_hom_app, fgPointNatIsoHom_hom_app] at happ
  rw [cancel_epi] at happ
  rw [cancel_mono] at happ
  simpa only [M, LinearEquiv.toModuleIsoₛ_hom, SemimoduleCat.hom_ofHom,
    Comodule.pointsAction_toLinearMap] using congrArg SemimoduleCat.Hom.hom happ

end FiniteComodules

end TauCeti.Tannaka
