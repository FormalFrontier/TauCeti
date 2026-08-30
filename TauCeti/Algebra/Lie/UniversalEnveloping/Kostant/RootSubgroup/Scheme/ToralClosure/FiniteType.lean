/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.BaseChange

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
  identification between specialization and base change of the generic carrier.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralBaseChangeGroupScheme`: the specialized affine
  group scheme, locally of finite type over its base.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralBaseChangeGroupSchemeι`: its closed immersion
  into the base-changed general-linear group scheme.

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
  ⟨CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
      (kostantToralDefiningIdeal e h ρ M hM hnil b wt),
    inferInstanceAs (Algebra.FiniteType ℤ
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt)))⟩

/-- The underlying object of the finite-type package is the coordinate Hopf algebra already used
to define the toral Kostant group scheme. -/
@[simp]
theorem kostantToralFiniteTypeCoordinateHopfAlgebra_obj :
    (kostantToralFiniteTypeCoordinateHopfAlgebra e h ρ M hM hnil b wt).obj =
      CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt) :=
  (rfl)

/-- The structural morphism of the toral Kostant group scheme is locally of finite type. -/
instance locallyOfFiniteType_kostantToralGroupScheme :
    LocallyOfFiniteType (kostantToralGroupScheme e h ρ M hM hnil b wt).X.hom := by
  let H : FiniteTypeCommHopfAlgCat ℤ :=
    ⟨GeneralLinear.coordinateHopfAlgebra ℤ n,
      (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
  exact FiniteTypeCommHopfAlgCat.locallyOfFiniteType_quotientSpec
    H
    (kostantToralDefiningIdeal e h ρ M hM hnil b wt)

/-- The toral Kostant group scheme is affine. -/
instance isAffine_kostantToralGroupScheme :
    IsAffine (kostantToralGroupScheme e h ρ M hM hnil b wt).X.left := by
  rw [hopfSpec_obj_X_left]
  exact isAffine_Spec _

/-! ## Finite-type specialization -/

variable (A : Type v) [CommRing A]

/-- The specialized toral carrier, in the quotient presentation obtained by base-changing the
ambient general-linear coordinate Hopf algebra and its defining ideal. -/
noncomputable def kostantToralFiniteTypeSpecialization :
    FiniteTypeCommHopfAlgCat A :=
  ⟨CommHopfAlgCat.quotient
      (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
      (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A),
    inferInstanceAs (Algebra.FiniteType A
      (CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
        (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A)))⟩

/-- The object underlying the finite-type specialization is the specialized quotient coordinate
Hopf algebra. -/
@[simp]
theorem kostantToralFiniteTypeSpecialization_obj :
    (kostantToralFiniteTypeSpecialization e h ρ M hM hnil b wt A).obj =
      CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
        (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A) :=
  (rfl)

/-- The specialized finite-type carrier is canonically the base change of the generic toral
carrier. This is `kostantToralBaseChangeIso` lifted to the finite-type full subcategory. -/
noncomputable def kostantToralFiniteTypeBaseChangeIso :
    kostantToralFiniteTypeSpecialization e h ρ M hM hnil b wt A ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := A)
        (kostantToralFiniteTypeCoordinateHopfAlgebra e h ρ M hM hnil b wt) :=
  ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty A) <|
    eqToIso (kostantToralFiniteTypeSpecialization_obj e h ρ M hM hnil b wt A) ≪≫
      kostantToralBaseChangeIso e h ρ M hM hnil b wt A ≪≫
      eqToIso (congrArg (CommHopfAlgCat.baseChange (K := A))
        (kostantToralFiniteTypeCoordinateHopfAlgebra_obj e h ρ M hM hnil b wt)).symm

/-- The underlying commutative-Hopf-algebra isomorphism of the finite-type comparison is the
previously constructed quotient/base-change comparison. -/
@[simp]
theorem kostantToralFiniteTypeBaseChangeIso_hom :
    (kostantToralFiniteTypeBaseChangeIso e h ρ M hM hnil b wt A).hom.hom =
      (eqToIso (kostantToralFiniteTypeSpecialization_obj e h ρ M hM hnil b wt A) ≪≫
        kostantToralBaseChangeIso e h ρ M hM hnil b wt A ≪≫
        eqToIso (congrArg (CommHopfAlgCat.baseChange (K := A))
          (kostantToralFiniteTypeCoordinateHopfAlgebra_obj e h ρ M hM hnil b wt)).symm).hom :=
  (rfl)

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
      (kostantToralBaseChangeGroupScheme e h ρ M hM hnil b wt A).X.hom := by
  let H : FiniteTypeCommHopfAlgCat A :=
    ⟨CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n),
      (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
  exact FiniteTypeCommHopfAlgCat.locallyOfFiniteType_quotientSpec
    H
    (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A)

/-- The specialized toral Kostant group scheme is affine. -/
instance isAffine_kostantToralBaseChangeGroupScheme :
    IsAffine (kostantToralBaseChangeGroupScheme e h ρ M hM hnil b wt A).X.left := by
  rw [hopfSpec_obj_X_left]
  exact isAffine_Spec _

/-- The closed-subgroup inclusion of the specialized toral carrier into the base-changed
general-linear group scheme. -/
noncomputable def kostantToralBaseChangeGroupSchemeι :
    kostantToralBaseChangeGroupScheme e h ρ M hM hnil b wt A ⟶
      (hopfSpec (CommRingCat.of A)).obj
        (Opposite.op
          (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))) :=
  CommHopfAlgCat.quotientSpecι
    (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
    (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A)

/-- The specialized closed-subgroup inclusion is the spectrum of the specialized quotient
coordinate map. -/
theorem kostantToralBaseChangeGroupSchemeι_def :
    kostantToralBaseChangeGroupSchemeι e h ρ M hM hnil b wt A =
      CommHopfAlgCat.quotientSpecι
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
        (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A) :=
  (rfl)

/-- The specialized toral carrier is a closed subgroup scheme of the base-changed general-linear
group scheme. -/
instance isClosedImmersion_kostantToralBaseChangeGroupSchemeι :
    IsClosedImmersion
      (kostantToralBaseChangeGroupSchemeι e h ρ M hM hnil b wt A).hom.hom.left := by
  exact CommHopfAlgCat.isClosedImmersion_quotientSpecι _ _

end TauCeti.UniversalEnvelopingAlgebra
