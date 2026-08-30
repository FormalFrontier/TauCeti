/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Basic
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Local equations for Cartier divisors

A Cartier divisor on an integral scheme is a section of the quotient sheaf
`𝒦_X^× / 𝒪_X^×`. This file extracts the local-equation description from that quotient:
every section is locally represented by a nonzero rational function, and two representatives
differ by a unique regular unit.

## Main declarations

* `Scheme.exists_local_equation` lifts a Cartier-divisor section to a rational unit on a
  neighbourhood of any chosen point;
* `Scheme.CartierDivisor.exists_local_equation_cover` chooses local equations on an open cover
  indexed by the points of the scheme;
* `Scheme.toCartierDivisorSheaf_app_eq_iff` characterizes equality of two representatives by
  their difference coming from a regular unit;
* `Scheme.CartierDivisor.existsUnique_transitionUnit` applies that characterization on the
  overlap of two local equations of a global Cartier divisor.

The local equations and their transition units are the gluing data used to construct the
invertible sheaf `𝒪_X(D)`. This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A,
item "Cartier divisors; the dictionaries `Cartier ≃ line bundles` and (smooth curve)
`Weil ≃ Cartier`". The construction follows Hartshorne, *Algebraic Geometry*, II.6, and the
Stacks Project, *Divisors*, Tag 02AR. No formalization is vendored: local lifting is Mathlib's
characterization of epimorphisms of sheaves as locally surjective maps, while the transition-unit
criterion uses left exactness of sections and the cokernel exact sequence.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- Every local Cartier-divisor section has a rational equation near each point of its domain.

The representative is a section of `𝒦_X^×` on a smaller open neighbourhood, and its image in
`𝒦_X^× / 𝒪_X^×` is the restriction of the given Cartier-divisor section. -/
theorem exists_local_equation {U : X.Opens}
    (D : ((cartierDivisorSheaf X).obj.obj (op U) : Type u)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ f : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ),
        ((toCartierDivisorSheaf X).hom.app (op V)).hom f = D |_ V := by
  have hlocal : TopCat.Presheaf.IsLocallySurjective (toCartierDivisorSheaf X).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi (toCartierDivisorSheaf X)).mpr inferInstance
  obtain ⟨V, hVU, ⟨f, hf⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (toCartierDivisorSheaf X).hom).mp hlocal
      U D x hx
  exact ⟨V, hVU, hxV, f, hf⟩

/-- Two rational-unit sections have the same image in the Cartier-divisor sheaf exactly when
their difference is the image of a regular unit.

The unit is unique by `toRationalUnitSheaf_app_injective`; the explicit existence-and-uniqueness
form is `existsUnique_regularUnit_sub_of_toCartierDivisorSheaf_app_eq`. Multiplication and
division of units are written as addition and subtraction because the unit sheaves are regarded
as sheaves of additive commutative groups. -/
theorem toCartierDivisorSheaf_app_eq_iff {U : X.Opens}
    (f g : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ)) :
    ((toCartierDivisorSheaf X).hom.app (op U)).hom f =
        ((toCartierDivisorSheaf X).hom.app (op U)).hom g ↔
      ∃ r : Additive (((X.presheaf.obj (op U)) : Type u)ˣ),
        ((toRationalUnitSheaf X).hom.app (op U)).hom r = f - g := by
  constructor
  · intro h
    let S : ShortComplex (TopCat.Sheaf AddCommGrpCat X) :=
      ShortComplex.mk (toRationalUnitSheaf X) (toCartierDivisorSheaf X)
        (toRationalUnitSheaf_comp_toCartierDivisorSheaf X)
    have hS : S.Exact := exact_toRationalUnitSheaf_toCartierDivisorSheaf X
    have hzero : ((toCartierDivisorSheaf X).hom.app (op U)).hom (f - g) = 0 :=
      (map_sub _ f g).trans (sub_eq_zero.mpr h)
    exact _root_.TopCat.Sheaf.sections_exact_of_left_exact hS (inferInstance : Mono S.f)
      (f - g) hzero
  · rintro ⟨r, hr⟩
    have hcomp := toRationalUnitSheaf_comp_toCartierDivisorSheaf X
    have happ := congrArg (fun k ↦ k.hom.app (op U)) hcomp
    have hrzero := ConcreteCategory.congr_hom happ r
    have hq_sub : ((toCartierDivisorSheaf X).hom.app (op U)).hom (f - g) = 0 :=
      (congrArg ((toCartierDivisorSheaf X).hom.app (op U)).hom hr.symm).trans hrzero
    apply sub_eq_zero.mp
    exact (map_sub _ f g).symm.trans hq_sub

/-- If two rational-unit sections represent the same Cartier divisor, there is a unique regular
unit whose image is their difference. In multiplicative notation, this says their ratio is a
unique regular unit. -/
theorem existsUnique_regularUnit_sub_of_toCartierDivisorSheaf_app_eq {U : X.Opens}
    (f g : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (h : ((toCartierDivisorSheaf X).hom.app (op U)).hom f =
      ((toCartierDivisorSheaf X).hom.app (op U)).hom g) :
    ∃! r : Additive (((X.presheaf.obj (op U)) : Type u)ˣ),
      ((toRationalUnitSheaf X).hom.app (op U)).hom r = f - g := by
  obtain ⟨r, hr⟩ := (toCartierDivisorSheaf_app_eq_iff X f g).mp h
  exact ⟨r, hr, fun s hs ↦ toRationalUnitSheaf_app_injective X U (hs.trans hr.symm)⟩

namespace CartierDivisor

/-- A global Cartier divisor admits an open cover carrying rational local equations.

The cover is indexed by the points of `X`, with the open indexed by `x` chosen to contain `x`.
The displayed supremum records that these opens cover the whole scheme. -/
theorem exists_local_equation_cover (D : CartierDivisor X) :
    ∃ (U : X → X.Opens)
      (f : ∀ x, Additive (((rationalFunctionsRing X).presheaf.obj (op (U x)))ˣ)),
      (∀ x, x ∈ U x) ∧ (⨆ x, U x) = ⊤ ∧ ∀ x,
        ((toCartierDivisorSheaf X).hom.app (op (U x))).hom (f x) = D |_ (U x) := by
  choose U _ hxU f hf using fun x ↦ exists_local_equation X D x (by simp)
  refine ⟨U, f, hxU, ?_, hf⟩
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hxU x⟩

/-- Two local equations of a global Cartier divisor determine a unique regular transition unit
on their overlap.

In multiplicative notation the displayed difference is the ratio `f / g`. The uniqueness is
what makes the transition functions satisfy the cocycle identity in the subsequent construction
of `𝒪_X(D)`. -/
theorem existsUnique_transitionUnit (D : CartierDivisor X) {U V : X.Opens}
    (f : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (g : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ))
    (hf : ((toCartierDivisorSheaf X).hom.app (op U)).hom f = D |_ U)
    (hg : ((toCartierDivisorSheaf X).hom.app (op V)).hom g = D |_ V) :
    ∃! r : Additive (((X.presheaf.obj (op (U ⊓ V))) : Type u)ˣ),
      ((toRationalUnitSheaf X).hom.app (op (U ⊓ V))).hom r =
        f |_ (U ⊓ V) - g |_ (U ⊓ V) := by
  apply existsUnique_regularUnit_sub_of_toCartierDivisorSheaf_app_eq X
  calc
    _ = (((toCartierDivisorSheaf X).hom.app (op U)).hom f) |_ (U ⊓ V) :=
      TopCat.Presheaf.map_restrict (toCartierDivisorSheaf X).hom inf_le_left f
    _ = (D |_ U) |_ (U ⊓ V) := congrArg (fun s ↦ s |_ (U ⊓ V)) hf
    _ = D |_ (U ⊓ V) := TopCat.Presheaf.restrict_restrict _ _ _
    _ = (D |_ V) |_ (U ⊓ V) := (TopCat.Presheaf.restrict_restrict _ _ _).symm
    _ = (((toCartierDivisorSheaf X).hom.app (op V)).hom g) |_ (U ⊓ V) :=
      congrArg (fun s ↦ s |_ (U ⊓ V)) hg.symm
    _ = _ := (TopCat.Presheaf.map_restrict
      (toCartierDivisorSheaf X).hom inf_le_right g).symm

end CartierDivisor

end Scheme

end

end AlgebraicGeometry

end TauCeti
