/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Maximal
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction

/-!
# The solvable radical of an affine group

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field. A connected
normal smooth solvable closed subgroup is represented contravariantly by a normal Hopf ideal `I`
whose quotient `H/I` is geometrically connected, smooth, and has a solvable group of geometric
points. The maximal-dimension construction and product closure show that one such ideal is
contained in every other one. This file chooses that unique ideal and packages its quotient as the
solvable radical of `H`.

The order on Hopf ideals reverses inclusion of represented closed subgroups. Thus
`solvableRadicalDefiningIdeal_le` says precisely that every connected normal smooth solvable
closed subgroup lies in the solvable radical. The chosen ideal is canonical because this
universal property determines it uniquely.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal`: the Hopf ideal cutting out
  the solvable radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_le`: the radical's defining
  ideal is below every candidate ideal.
* `TauCeti.FiniteTypeCommHopfAlgCat.eq_solvableRadicalDefiningIdeal_iff`: the choice-free
  universal property characterizing the radical's defining ideal.
* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadical`: the coordinate Hopf algebra of the
  solvable radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalSpec`: its affine group scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

The packaging and characteristic API follow the existing formal construction in
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction`, with solvability replacing
unipotence.

This completes the solvable-radical construction in Layer 6, "Reductive and semisimple groups",
of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The Hopf ideal cutting out the solvable radical of a finite-type affine group.

It is the unique solvable-radical candidate contained in every other candidate. Since Hopf-ideal
order reverses closed-subgroup inclusion, its represented subgroup is the greatest connected
normal smooth solvable closed subgroup. -/
noncomputable def solvableRadicalDefiningIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) : HopfIdeal k H :=
  Classical.choose
    (HopfIdeal.exists_isSolvableRadicalCandidate_maximal_finrank_quotientLie H)

/-- The defining ideal of the solvable radical cuts out a connected normal smooth solvable
closed subgroup. -/
theorem isSolvableRadicalCandidate_solvableRadicalDefiningIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    HopfIdeal.IsSolvableRadicalCandidate H (solvableRadicalDefiningIdeal H) := by
  rw [solvableRadicalDefiningIdeal]
  exact (Classical.choose_spec
    (HopfIdeal.exists_isSolvableRadicalCandidate_maximal_finrank_quotientLie H)).1

/-- Every connected normal smooth solvable closed subgroup is contained in the solvable radical.

Contravariantly, this says that the radical's defining Hopf ideal is contained in the ideal
cutting out the given subgroup. -/
theorem solvableRadicalDefiningIdeal_le (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (I : HopfIdeal k H) (hI : HopfIdeal.IsSolvableRadicalCandidate H I) :
    solvableRadicalDefiningIdeal H ≤ I := by
  apply (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H).le_of_finrank_maximal
  · rw [solvableRadicalDefiningIdeal]
    exact (Classical.choose_spec
      (HopfIdeal.exists_isSolvableRadicalCandidate_maximal_finrank_quotientLie H)).2
  · exact hI

/-- A Hopf ideal is the defining ideal of the solvable radical exactly when it is a candidate
contained in every other candidate. This is the choice-free universal property of the radical. -/
theorem eq_solvableRadicalDefiningIdeal_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (I : HopfIdeal k H) :
    I = solvableRadicalDefiningIdeal H ↔
      HopfIdeal.IsSolvableRadicalCandidate H I ∧
        ∀ J : HopfIdeal k H, HopfIdeal.IsSolvableRadicalCandidate H J → I ≤ J := by
  constructor
  · rintro rfl
    exact ⟨isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H,
      solvableRadicalDefiningIdeal_le H⟩
  · rintro ⟨hI, hleast⟩
    exact le_antisymm
      (hleast _ (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H))
      (solvableRadicalDefiningIdeal_le H I hI)

/-- The solvable radical is trivial exactly when every solvable-radical candidate is the identity
subgroup. -/
theorem solvableRadicalDefiningIdeal_eq_augmentation_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    solvableRadicalDefiningIdeal H = HopfIdeal.augmentation k H ↔
      ∀ I : HopfIdeal k H, HopfIdeal.IsSolvableRadicalCandidate H I →
        I = HopfIdeal.augmentation k H := by
  constructor
  · intro hrad I hI
    apply le_antisymm (HopfIdeal.le_augmentation k H I)
    rw [← hrad]
    exact solvableRadicalDefiningIdeal_le H I hI
  · intro h
    exact h _ (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H)

/-- The solvable radical contains the unipotent radical. In coordinate rings, this inclusion is
the reverse inequality between their defining Hopf ideals. -/
theorem solvableRadicalDefiningIdeal_le_unipotentRadicalDefiningIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    solvableRadicalDefiningIdeal H ≤ unipotentRadicalDefiningIdeal H :=
  solvableRadicalDefiningIdeal_le H _
    (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H).isSolvableRadicalCandidate

/-- The finite-type coordinate Hopf algebra of the solvable radical. -/
noncomputable abbrev solvableRadical (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    FiniteTypeCommHopfAlgCat.{u, u} k :=
  quotient H (solvableRadicalDefiningIdeal H)

/-- The coordinate morphism from an affine group to its solvable radical. Contravariantly, this
is the inclusion of the solvable radical into the ambient group. -/
noncomputable def solvableRadicalCoordinateMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) : H ⟶ solvableRadical H :=
  mkQuotient H (solvableRadicalDefiningIdeal H)

/-- The kernel of the solvable-radical coordinate morphism is its defining ideal. -/
@[simp]
theorem solvableRadicalCoordinateMap_ker
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    RingHom.ker
        (↑(↑(toBialgHom (solvableRadicalCoordinateMap H)) :
            H →ₐ[k] solvableRadical H) : H →+* solvableRadical H) =
      (solvableRadicalDefiningIdeal H).toIdeal := by
  simpa only [solvableRadicalCoordinateMap, AlgHom.toRingHom_eq_coe] using
    mkQuotient_ker H (solvableRadicalDefiningIdeal H)

/-- The coordinate Hopf algebra of the solvable radical is geometrically connected. -/
theorem geometricallyConnected_solvableRadical
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    geometricallyConnectedCommHopfAlgProperty k (solvableRadical H).obj :=
  (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H).geometricallyConnected

/-- The coordinate Hopf algebra of the solvable radical is smooth. -/
theorem smooth_solvableRadical (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Algebra.Smooth k (solvableRadical H) :=
  (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H).smooth

/-- The geometric points of the solvable radical form a solvable group. -/
theorem geometricallySolvable_solvableRadical (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    geometricallySolvablePointsCommHopfAlgProperty k (solvableRadical H).obj :=
  (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H).geometricallySolvable

/-- The defining ideal of the solvable radical is normal. -/
theorem isNormal_solvableRadicalDefiningIdeal (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (solvableRadicalDefiningIdeal H).IsNormal :=
  (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H).isNormal

/-- The affine group scheme represented by the solvable radical's coordinate algebra. -/
noncomputable abbrev solvableRadicalSpec (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Grp (Over (Spec (CommRingCat.of k))) :=
  CommHopfAlgCat.quotientSpec H.obj (solvableRadicalDefiningIdeal H)

/-- The canonical inclusion of the solvable radical into the ambient affine group scheme. -/
noncomputable abbrev solvableRadicalSpecι (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    solvableRadicalSpec H ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).obj (op H.obj) :=
  CommHopfAlgCat.quotientSpecι H.obj (solvableRadicalDefiningIdeal H)

/-- The inclusion of a candidate subgroup into the solvable radical. -/
noncomputable def solvableRadicalSpecMapOfCandidate
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H)
    (hI : HopfIdeal.IsSolvableRadicalCandidate H I) :
    CommHopfAlgCat.quotientSpec H.obj I ⟶ solvableRadicalSpec H :=
  CommHopfAlgCat.quotientSpecMapOfLe H.obj (solvableRadicalDefiningIdeal_le H I hI)

/-- A candidate's inclusion into the radical followed by the radical's ambient inclusion is the
candidate's ambient inclusion. -/
@[simp]
theorem solvableRadicalSpecMapOfCandidate_comp_solvableRadicalSpecι
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H)
    (hI : HopfIdeal.IsSolvableRadicalCandidate H I) :
    solvableRadicalSpecMapOfCandidate H I hI ≫ solvableRadicalSpecι H =
      CommHopfAlgCat.quotientSpecι H.obj I :=
  CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι H.obj
    (solvableRadicalDefiningIdeal_le H I hI)

/-- The inclusion of the solvable radical is a closed immersion. -/
instance isClosedImmersion_solvableRadicalSpecι
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsClosedImmersion (solvableRadicalSpecι H).hom.hom.left :=
  inferInstance

end FiniteTypeCommHopfAlgCat

end

end TauCeti
