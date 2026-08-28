/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Maximal

/-!
# The unipotent radical of an affine group

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field. A connected
normal smooth unipotent closed subgroup is represented contravariantly by a normal Hopf ideal `I`
whose quotient `H/I` is geometrically connected, smooth, and geometrically unipotent. The
maximal-dimension construction and its product theorem show that one such ideal is contained in
every other one. This file chooses that unique ideal and packages its quotient as the unipotent
radical of `H`.

The order on Hopf ideals reverses inclusion of represented closed subgroups. Thus
`unipotentRadicalDefiningIdeal_le` says precisely that every connected normal smooth unipotent
closed subgroup lies in the unipotent radical. The chosen ideal is canonical because this
universal property determines it uniquely.

Over a nonperfect field this construction is the `k`-unipotent radical: no claim is made that it
commutes with extension to an algebraic closure. Applying the construction directly to the
geometric fibre gives the geometric unipotent radical.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal`: the Hopf ideal cutting out
  the unipotent radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_le`: the radical's defining
  ideal is below every candidate ideal, so every candidate subgroup lies in the radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.eq_unipotentRadicalDefiningIdeal_iff`: the choice-free
  universal property characterizing the radical's defining ideal.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_iff`: the
  radical is trivial exactly when every candidate subgroup is trivial.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical`: the coordinate Hopf algebra of the
  unipotent radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalSpec`: its affine group scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and §§6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.

This completes the construction target in Layer 5, "The unipotent radical", of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The Hopf ideal cutting out the `k`-unipotent radical of a finite-type affine group.

It is the unique unipotent-radical candidate contained in every other candidate. Since Hopf-ideal
order reverses closed-subgroup inclusion, its represented subgroup is the greatest connected
normal smooth unipotent closed subgroup defined over `k`. -/
noncomputable def unipotentRadicalDefiningIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) : HopfIdeal k H :=
  Classical.choose
    (HopfIdeal.exists_isUnipotentRadicalCandidate_maximal_finrank_quotientLie H)

/-- The defining ideal of the unipotent radical cuts out a connected normal smooth unipotent
closed subgroup. -/
theorem isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    HopfIdeal.IsUnipotentRadicalCandidate H (unipotentRadicalDefiningIdeal H) := by
  rw [unipotentRadicalDefiningIdeal]
  exact (Classical.choose_spec
    (HopfIdeal.exists_isUnipotentRadicalCandidate_maximal_finrank_quotientLie H)).1

/-- Every connected normal smooth unipotent closed subgroup is contained in the unipotent
radical.

Contravariantly, this says that the radical's defining Hopf ideal is contained in the ideal
cutting out the given subgroup. -/
theorem unipotentRadicalDefiningIdeal_le (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (I : HopfIdeal k H) (hI : HopfIdeal.IsUnipotentRadicalCandidate H I) :
    unipotentRadicalDefiningIdeal H ≤ I := by
  apply (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H).le_of_finrank_maximal
  · rw [unipotentRadicalDefiningIdeal]
    exact (Classical.choose_spec
      (HopfIdeal.exists_isUnipotentRadicalCandidate_maximal_finrank_quotientLie H)).2
  · exact hI

/-- A Hopf ideal is the defining ideal of the unipotent radical exactly when it is a candidate
contained in every other candidate. This is the choice-free universal property of the radical. -/
theorem eq_unipotentRadicalDefiningIdeal_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (I : HopfIdeal k H) :
    I = unipotentRadicalDefiningIdeal H ↔
      HopfIdeal.IsUnipotentRadicalCandidate H I ∧
        ∀ J : HopfIdeal k H, HopfIdeal.IsUnipotentRadicalCandidate H J → I ≤ J := by
  constructor
  · rintro rfl
    exact ⟨isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H,
      unipotentRadicalDefiningIdeal_le H⟩
  · rintro ⟨hI, hleast⟩
    exact le_antisymm
      (hleast _ (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H))
      (unipotentRadicalDefiningIdeal_le H I hI)

/-- The unipotent radical is trivial exactly when every unipotent-radical candidate is the
identity subgroup. -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalDefiningIdeal H = HopfIdeal.augmentation k H ↔
      ∀ I : HopfIdeal k H, HopfIdeal.IsUnipotentRadicalCandidate H I →
        I = HopfIdeal.augmentation k H := by
  constructor
  · intro hrad I hI
    apply le_antisymm (HopfIdeal.le_augmentation k H I)
    rw [← hrad]
    exact unipotentRadicalDefiningIdeal_le H I hI
  · intro h
    exact h _ (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H)

/-- The finite-type coordinate Hopf algebra of the unipotent radical. -/
noncomputable abbrev unipotentRadical (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    FiniteTypeCommHopfAlgCat.{u, u} k :=
  quotient H (unipotentRadicalDefiningIdeal H)

/-- The coordinate morphism from an affine group to its unipotent radical. Contravariantly, this
is the inclusion of the unipotent radical into the ambient group. -/
noncomputable def unipotentRadicalCoordinateMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) : H ⟶ unipotentRadical H :=
  mkQuotient H (unipotentRadicalDefiningIdeal H)

/-- The unipotent-radical coordinate morphism is the canonical quotient morphism. -/
lemma unipotentRadicalCoordinateMap_def
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalCoordinateMap H = mkQuotient H (unipotentRadicalDefiningIdeal H) :=
  (rfl)

/-- The kernel of the unipotent-radical coordinate morphism is its defining ideal. -/
@[simp]
theorem unipotentRadicalCoordinateMap_ker
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    RingHom.ker
        (↑(↑(toBialgHom (unipotentRadicalCoordinateMap H)) :
            H →ₐ[k] unipotentRadical H) : H →+* unipotentRadical H) =
      (unipotentRadicalDefiningIdeal H).toIdeal := by
  simpa only [unipotentRadicalCoordinateMap, AlgHom.toRingHom_eq_coe] using
    mkQuotient_ker H (unipotentRadicalDefiningIdeal H)

/-- The coordinate Hopf algebra of the unipotent radical is geometrically connected. -/
theorem geometricallyConnected_unipotentRadical
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    geometricallyConnectedCommHopfAlgProperty k (unipotentRadical H).obj :=
  (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H).geometricallyConnected

/-- The coordinate Hopf algebra of the unipotent radical is smooth and geometrically
unipotent. -/
theorem smoothUnipotent_unipotentRadical (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    smoothUnipotentCommHopfAlgProperty k (unipotentRadical H) :=
  (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H).smoothUnipotent

/-- The defining ideal of the unipotent radical is normal. -/
theorem isNormal_unipotentRadicalDefiningIdeal (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (unipotentRadicalDefiningIdeal H).IsNormal :=
  (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H).isNormal

/-- The affine group scheme represented by the unipotent radical's coordinate algebra. -/
noncomputable abbrev unipotentRadicalSpec (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Grp (Over (Spec (CommRingCat.of k))) :=
  CommHopfAlgCat.quotientSpec H.obj (unipotentRadicalDefiningIdeal H)

/-- The canonical inclusion of the unipotent radical into the ambient affine group scheme. -/
noncomputable abbrev unipotentRadicalSpecι (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalSpec H ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of k)).obj (op H.obj) :=
  CommHopfAlgCat.quotientSpecι H.obj (unipotentRadicalDefiningIdeal H)

/-- The inclusion of a candidate subgroup into the unipotent radical. -/
noncomputable def unipotentRadicalSpecMapOfCandidate
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H)
    (hI : HopfIdeal.IsUnipotentRadicalCandidate H I) :
    CommHopfAlgCat.quotientSpec H.obj I ⟶ unipotentRadicalSpec H :=
  CommHopfAlgCat.quotientSpecMapOfLe H.obj (unipotentRadicalDefiningIdeal_le H I hI)

/-- A candidate's inclusion into the radical followed by the radical's ambient inclusion is the
candidate's ambient inclusion. -/
@[simp]
theorem unipotentRadicalSpecMapOfCandidate_comp_unipotentRadicalSpecι
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H)
    (hI : HopfIdeal.IsUnipotentRadicalCandidate H I) :
    unipotentRadicalSpecMapOfCandidate H I hI ≫ unipotentRadicalSpecι H =
      CommHopfAlgCat.quotientSpecι H.obj I :=
  CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι H.obj
    (unipotentRadicalDefiningIdeal_le H I hI)

/-- The inclusion of the unipotent radical is a closed immersion. -/
instance isClosedImmersion_unipotentRadicalSpecι
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsClosedImmersion (unipotentRadicalSpecι H).hom.hom.left :=
  inferInstance

end FiniteTypeCommHopfAlgCat

end

end TauCeti
