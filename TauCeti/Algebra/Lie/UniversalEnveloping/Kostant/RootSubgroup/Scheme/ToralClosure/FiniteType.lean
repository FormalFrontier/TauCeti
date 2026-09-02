/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.BaseChange
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.BaseChange.Basic

/-!
# The toral Kostant carrier as a finite-type group scheme

The toral Kostant closure is presented as a quotient of the coordinate Hopf algebra of a general
linear group. This file records the finite-type structure of that quotient and of all its base
changes. In particular, it supplies the finite-type commutative Hopf algebra on which the
reductivity and root-datum stages of the Chevalley--Demazure construction are formulated.

For a commutative ring `A`, the specialized carrier is kept in the same presentation used by
`kostantToralBaseChangeIdeal`: first base-change the ambient general-linear coordinate algebra,
then quotient by the base-changed toral ideal. The finite-type version of
`kostantToralBaseChangeIso` identifies this presentation with the base change of the quotient over
`ℤ`. Its spectrum is therefore a locally finite-type closed subgroup scheme of the base-changed
general-linear group scheme.

No smoothness, flatness, or reductivity is asserted here. Those are the remaining substantive
properties needed to identify a specialized carrier as a split reductive group.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantToralFiniteTypeCoordinateHopfAlgebra`: the generic
  toral carrier bundled as a finite-type commutative Hopf algebra over `ℤ`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralFiniteTypeSpecialization`: the corresponding
  specialized quotient over a commutative ring.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralFiniteTypeBaseChangeIso`: the finite-type
  identification between the base change of the generic carrier and the specialization.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralBaseChangeGroupScheme`: the specialized affine
  group scheme, locally of finite type over its base.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralBaseChangeGroupSchemeι`: its closed immersion
  into the base-changed general-linear group scheme.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralBaseChangeGroupSchemePullbackIso`: its
  identification with the scheme-theoretic base change of the toral group scheme over `ℤ`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* B. Conrad, *Reductive Group Schemes*, §1.

This advances the finite-type and base-change parts of the pinned Chevalley--Demazure construction
in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. That construction is consumed by
milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Finite κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)

/-! ## The finite-type carrier over `ℤ` -/

/-- The coordinate Hopf algebra of the toral Kostant closure, bundled with its finite-type
property. It is a quotient of the finite-type coordinate Hopf algebra of `GLₙ`. -/
noncomputable def kostantToralFiniteTypeCoordinateHopfAlgebra :
    FiniteTypeCommHopfAlgCat ℤ :=
  FiniteTypeCommHopfAlgCat.quotient
    -- Not `GeneralLinear.finiteTypeCoordinateHopfAlgebra`: its body is not exposed, so its
    -- underlying object matches the coordinate Hopf algebra only propositionally here, and the
    -- toral defining ideal would not typecheck against it. The ambient bundle is rebuilt around
    -- the recorded finite-type instance, keeping its object definitionally in place.
    (⟨GeneralLinear.coordinateHopfAlgebra ℤ n,
      inferInstanceAs (Algebra.FiniteType ℤ (GeneralLinear.coordinateHopfAlgebra ℤ n))⟩ :
      FiniteTypeCommHopfAlgCat ℤ)
    (kostantToralDefiningIdeal e h ρ M hM hnil b wt)

/-- The underlying object of the finite-type package is the coordinate Hopf algebra already used
to define the toral Kostant group scheme. -/
@[simp]
theorem kostantToralFiniteTypeCoordinateHopfAlgebra_obj :
    (kostantToralFiniteTypeCoordinateHopfAlgebra e h ρ M hM hnil b wt).obj =
      CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt) :=
  (rfl)

/-! ## Finite-type specialization -/

variable (A : Type v) [CommRing A]

/-- The specialized toral carrier, in the quotient presentation obtained by base-changing the
ambient general-linear coordinate Hopf algebra and its defining ideal. -/
noncomputable def kostantToralFiniteTypeSpecialization :
    FiniteTypeCommHopfAlgCat A :=
  FiniteTypeCommHopfAlgCat.quotient
    -- The base-changed ambient bundle is likewise rebuilt around the finite-type instance
    -- inherited by scalar extension, keeping the object `kostantToralBaseChangeIdeal` is
    -- stated for definitionally in place.
    (⟨CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n),
      inferInstanceAs (Algebra.FiniteType A
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n)))⟩ :
      FiniteTypeCommHopfAlgCat A)
    (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A)

/-- The object underlying the finite-type specialization is the specialized quotient coordinate
Hopf algebra. -/
@[simp]
theorem kostantToralFiniteTypeSpecialization_obj :
    (kostantToralFiniteTypeSpecialization e h ρ M hM hnil b wt A).obj =
      CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
        (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A) :=
  (rfl)

/-- The base change of the generic toral carrier is canonically the specialized finite-type
carrier. This is `kostantToralBaseChangeIso` lifted to the finite-type full subcategory. -/
noncomputable def kostantToralFiniteTypeBaseChangeIso :
    FiniteTypeCommHopfAlgCat.baseChange (K := A)
        (kostantToralFiniteTypeCoordinateHopfAlgebra e h ρ M hM hnil b wt) ≅
      kostantToralFiniteTypeSpecialization e h ρ M hM hnil b wt A :=
  FiniteTypeCommHopfAlgCat.baseChangeIsoOfObjIso
    (kostantToralFiniteTypeCoordinateHopfAlgebra_obj e h ρ M hM hnil b wt)
    (kostantToralFiniteTypeSpecialization_obj e h ρ M hM hnil b wt A)
    (kostantToralBaseChangeIso e h ρ M hM hnil b wt A).symm

/-- The underlying commutative-Hopf-algebra isomorphism of the finite-type comparison is the
previously constructed quotient/base-change comparison. -/
@[simp]
theorem kostantToralFiniteTypeBaseChangeIso_hom :
    (kostantToralFiniteTypeBaseChangeIso e h ρ M hM hnil b wt A).hom.hom =
      (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := A))
          (kostantToralFiniteTypeCoordinateHopfAlgebra_obj e h ρ M hM hnil b wt)) ≪≫
        (kostantToralBaseChangeIso e h ρ M hM hnil b wt A).symm ≪≫
        eqToIso (kostantToralFiniteTypeSpecialization_obj e h ρ M hM hnil b wt A).symm).hom :=
  FiniteTypeCommHopfAlgCat.baseChangeIsoOfObjIso_hom
    (kostantToralFiniteTypeCoordinateHopfAlgebra_obj e h ρ M hM hnil b wt)
    (kostantToralFiniteTypeSpecialization_obj e h ρ M hM hnil b wt A)
    (kostantToralBaseChangeIso e h ρ M hM hnil b wt A).symm

/-! ## The specialized finite-type group scheme -/

/-- The affine group scheme represented by the specialized toral carrier. -/
noncomputable abbrev kostantToralBaseChangeGroupScheme :
    Grp (Over (Spec (CommRingCat.of A))) :=
  CommHopfAlgCat.quotientSpec
    (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
    (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A)

/-- The specialized toral carrier is locally of finite type over its base. -/
instance locallyOfFiniteType_kostantToralBaseChangeGroupScheme :
    LocallyOfFiniteType
      (kostantToralBaseChangeGroupScheme e h ρ M hM hnil b wt A).X.hom :=
  FiniteTypeCommHopfAlgCat.locallyOfFiniteType_quotientSpec
    (⟨CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n),
      inferInstanceAs (Algebra.FiniteType A
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n)))⟩ :
      FiniteTypeCommHopfAlgCat A)
    (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A)

/-- The closed-subgroup inclusion of the specialized toral carrier into the base-changed
general-linear group scheme. Unfolding this abbreviation exposes `CommHopfAlgCat.quotientSpecι`,
so instance search finds `CommHopfAlgCat.isClosedImmersion_quotientSpecι` for its underlying
scheme morphism. -/
noncomputable abbrev kostantToralBaseChangeGroupSchemeι :
    kostantToralBaseChangeGroupScheme e h ρ M hM hnil b wt A ⟶
      (hopfSpec (CommRingCat.of A)).obj
        (Opposite.op
          (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))) :=
  CommHopfAlgCat.quotientSpecι
    (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
    (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A)

/-! ## The specialized carrier as a scheme-theoretic base change -/

section Pullback

variable (A : Type) [CommRing A]

/-- **The specialized toral group scheme is the base change of the toral group scheme over
`ℤ`.**

`AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso` identifies the pullback of a Hopf spectrum along
`Spec A ⟶ Spec ℤ` with the Hopf spectrum of the scalar extension of its coordinate Hopf algebra,
and `kostantToralBaseChangeIso`, whose finite-type form is
`kostantToralFiniteTypeBaseChangeIso`, identifies that scalar extension with the specialized
quotient presentation. Smoothness, flatness or reductivity of the specialized carrier may
therefore be transported along this isomorphism.

The base ring is a `Type` because the Hopf-spectrum base-change comparison requires the two base
rings to lie in the same universe, and the carrier being specialized lives over `ℤ`. -/
noncomputable def kostantToralBaseChangeGroupSchemePullbackIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ A)))).mapGrp.obj
        (kostantToralGroupScheme e h ρ M hM hnil b wt) ≅
      kostantToralBaseChangeGroupScheme e h ρ M hM hnil b wt A :=
  AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt)) ≪≫
    (hopfSpec (CommRingCat.of A)).mapIso
      (kostantToralBaseChangeIso e h ρ M hM hnil b wt A).op

/-- The base-change comparison of group schemes is the Hopf-spectrum base-change comparison
followed by the spectrum of the specialized quotient identification. -/
@[simp]
theorem kostantToralBaseChangeGroupSchemePullbackIso_hom :
    (kostantToralBaseChangeGroupSchemePullbackIso e h ρ M hM hnil b wt A).hom =
      (AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso
          (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
            (kostantToralDefiningIdeal e h ρ M hM hnil b wt))).hom ≫
        (hopfSpec (CommRingCat.of A)).map
          (kostantToralBaseChangeIso e h ρ M hM hnil b wt A).hom.op := by
  rw [kostantToralBaseChangeGroupSchemePullbackIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom]

end Pullback

end TauCeti.UniversalEnvelopingAlgebra
