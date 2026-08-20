/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Torsor

/-!
# The fppf quotient by the center

Let `H` be the coordinate Hopf algebra of an affine group over a field. The center is a normal
closed subgroup, so the general fppf quotient construction gives the center quotient `G / Z(G)`
as a group object in fppf sheaves. This file names that quotient and its canonical projection.

The projection is an epimorphism and is locally surjective for the fppf topology. Its kernel-pair
square is the torsor square for the action of the center on `G`. The sheaf quotient is the correct
first construction of `G / Z(G)`: no representability claim is made here. For a reductive group,
representability and the proof that the represented quotient is the adjoint form remain separate.

Before sheafification, the construction is the ordinary quotient `G(A) / Z(G)(A)` on every
commutative value algebra `A`. Its projection has kernel exactly the universally central points.

## Main declarations

* `TauCeti.CommHopfAlgCat.centerQuotientFppfSheaf`: the fppf sheaf quotient `G / Z(G)`.
* `TauCeti.CommHopfAlgCat.centerQuotientFppfProjection`: the canonical projection to the center
  quotient.
* `TauCeti.CommHopfAlgCat.centerPointwiseQuotientMk_ker`: the pointwise projection has kernel
  `Z(G)(A)`.
* `TauCeti.CommHopfAlgCat.centerQuotientFppfHomEquiv`: the universal property inherited from
  fppf sheafification.
* `TauCeti.CommHopfAlgCat.isLocallySurjective_centerQuotientFppfProjection`: local surjectivity
  of the projection.
* `TauCeti.CommHopfAlgCat.isPullback_centerQuotientFppfTorsor`: the center-torsor kernel-pair
  square.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§5 and 19.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 14.

This advances Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap toward
the adjoint form by constructing the required quotient by `Z(G)` in fppf sheaves.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k]

/-- The defining Hopf ideal of the center is normal. -/
theorem isNormal_centerDefiningIdeal (H : _root_.CommHopfAlgCat.{v} k) :
    (centerDefiningIdeal H).IsNormal :=
  (isCentral_centerDefiningIdeal H).isNormal

section Pointwise

variable (H : _root_.CommHopfAlgCat.{v} k) (A : CommAlgCat.{v} k)

/-- Locally expose normality of the represented center on points. -/
local instance centerPointsSubgroupNormal : (centerPointsSubgroup H A).Normal :=
  quotientPointsSubgroup_normal H (centerDefiningIdeal H)
    (isNormal_centerDefiningIdeal H) A

/-- The pointwise center quotient `G(A) / Z(G)(A)`.

The fppf center quotient is obtained by assembling these groups into a presheaf and
sheafifying. -/
noncomputable abbrev centerPointwiseQuotient : GrpCat.{v} :=
  pointwiseQuotientGroup H (centerDefiningIdeal H) (isNormal_centerDefiningIdeal H) A

/-- Locally expose the group structure carried by the bundled pointwise center quotient. -/
noncomputable local instance centerPointwiseQuotientGroup :
    Group (centerPointwiseQuotient H A) :=
  (centerPointwiseQuotient H A).str

/-- The quotient homomorphism from `G(A)` to `G(A) / Z(G)(A)`. -/
noncomputable def centerPointwiseQuotientMk :
    HopfAlgebra.points (R := k) (H := H) A ⟶ centerPointwiseQuotient H A :=
  pointwiseQuotientMk H (centerDefiningIdeal H) (isNormal_centerDefiningIdeal H) A

/-- The pointwise center-quotient projection sends a point to its ordinary quotient class. -/
@[simp]
theorem centerPointwiseQuotientMk_apply
    (g : HopfAlgebra.points (R := k) (H := H) A) :
    centerPointwiseQuotientMk H A g = QuotientGroup.mk' (centerPointsSubgroup H A) g := by
  rw [centerPointwiseQuotientMk]
  exact pointwiseQuotientMk_apply H (centerDefiningIdeal H)
    (isNormal_centerDefiningIdeal H) A g

/-- The kernel of `G(A) ⟶ G(A) / Z(G)(A)` is exactly the center of the point group. -/
theorem centerPointwiseQuotientMk_ker :
    (centerPointwiseQuotientMk H A).hom.ker = HopfAlgebra.center k H A := by
  exact (pointwiseQuotientMk_ker H (centerDefiningIdeal H)
    (isNormal_centerDefiningIdeal H) A).trans (centerPointsSubgroup_eq_center H A)

/-- A point maps to the identity in `G(A) / Z(G)(A)` exactly when it is universally central. -/
@[simp]
theorem centerPointwiseQuotientMk_eq_one_iff_isCentralPoint
    (g : HopfAlgebra.points (R := k) (H := H) A) :
    centerPointwiseQuotientMk H A g = 1 ↔ HopfAlgebra.IsCentralPoint g := by
  exact (pointwiseQuotientMk_eq_one_iff H (centerDefiningIdeal H)
    (isNormal_centerDefiningIdeal H) A g).trans (mem_centerPointsSubgroup_iff H A g)

/-- The projection from points to their center quotient is surjective. -/
theorem centerPointwiseQuotientMk_surjective :
    Function.Surjective (centerPointwiseQuotientMk H A) := by
  rw [centerPointwiseQuotientMk]
  exact pointwiseQuotientMk_surjective H (centerDefiningIdeal H)
    (isNormal_centerDefiningIdeal H) A

end Pointwise

/-- The fppf sheaf quotient `G / Z(G)` of an affine group by its center.

This is the sheafification of the pointwise quotient presheaf. It does not assert that the
quotient is represented by a scheme. -/
noncomputable abbrev centerQuotientFppfSheaf (H : _root_.CommHopfAlgCat.{u} k) :=
  fppfQuotientSheaf H (centerDefiningIdeal H) (isNormal_centerDefiningIdeal H)

/-- The canonical morphism from an affine group's fppf sheaf of points to its center quotient. -/
noncomputable def centerQuotientFppfProjection (H : _root_.CommHopfAlgCat.{u} k) :
    pointsFppfGroupObject H ⟶ centerQuotientFppfSheaf H :=
  fppfQuotientProjection H (centerDefiningIdeal H) (isNormal_centerDefiningIdeal H)

/-- The center-quotient projection is the general fppf quotient projection for the center's
defining ideal. -/
theorem centerQuotientFppfProjection_def (H : _root_.CommHopfAlgCat.{u} k) :
    centerQuotientFppfProjection H =
      fppfQuotientProjection H (centerDefiningIdeal H) (isNormal_centerDefiningIdeal H) := by
  rw [centerQuotientFppfProjection]

/-- Maps from the center quotient to an fppf sheaf group are equivalent to maps from the
pointwise center quotient into its underlying presheaf. -/
noncomputable def centerQuotientFppfHomEquiv (H : _root_.CommHopfAlgCat.{u} k)
    (F : Grp (Sheaf (CommAlgCat.fppfTopology k) (Type (u + 1)))) :
    (centerQuotientFppfSheaf H ⟶ F) ≃
      (pointwiseQuotientPresheafGrp H (centerDefiningIdeal H)
          (isNormal_centerDefiningIdeal H) ⟶ fppfGroupObjectToPresheaf F) :=
  fppfQuotientHomEquiv H (centerDefiningIdeal H) (isNormal_centerDefiningIdeal H) F

/-- A map from the pointwise center quotient into the underlying presheaf of an fppf sheaf group
extends uniquely to the fppf center quotient. -/
noncomputable def centerQuotientFppfLift (H : _root_.CommHopfAlgCat.{u} k)
    (F : Grp (Sheaf (CommAlgCat.fppfTopology k) (Type (u + 1))))
    (f : pointwiseQuotientPresheafGrp H (centerDefiningIdeal H)
      (isNormal_centerDefiningIdeal H) ⟶ fppfGroupObjectToPresheaf F) :
    centerQuotientFppfSheaf H ⟶ F :=
  (centerQuotientFppfHomEquiv H F).symm f

/-- The projection to the fppf center quotient is an epimorphism. -/
instance instEpiCenterQuotientFppfProjection (H : _root_.CommHopfAlgCat.{u} k) :
    Epi (centerQuotientFppfProjection H) := by
  rw [centerQuotientFppfProjection]
  infer_instance

/-- Every section of the fppf center quotient lifts to an ambient-group section after an fppf
cover. -/
theorem isLocallySurjective_centerQuotientFppfProjection
    (H : _root_.CommHopfAlgCat.{u} k) :
    Sheaf.IsLocallySurjective (centerQuotientFppfProjection H).hom.hom := by
  rw [centerQuotientFppfProjection]
  exact isLocallySurjective_fppfQuotientProjection H (centerDefiningIdeal H)
    (isNormal_centerDefiningIdeal H)

/-- The right action of the center on the ambient fppf sheaf of points. -/
noncomputable abbrev centerQuotientFppfTorsorAction
    (H : _root_.CommHopfAlgCat.{u} k) :=
  fppfQuotientTorsorAction H (centerDefiningIdeal H)

/-- The kernel pair of `G ⟶ G / Z(G)` is `G × Z(G)` via `(g, z) ↦ (g, gz)`. Together with
local surjectivity, this exhibits the projection as an fppf torsor under the center. -/
theorem isPullback_centerQuotientFppfTorsor (H : _root_.CommHopfAlgCat.{u} k) :
    IsPullback
      (CartesianMonoidalCategory.fst _ _)
      (centerQuotientFppfTorsorAction H)
      (centerQuotientFppfProjection H).hom.hom
      (centerQuotientFppfProjection H).hom.hom := by
  rw [centerQuotientFppfProjection]
  exact isPullback_fppfQuotientTorsor H (centerDefiningIdeal H)
    (isNormal_centerDefiningIdeal H)

end TauCeti.CommHopfAlgCat
