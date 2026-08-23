/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality

/-!
# Order of Hopf-ideal quotient point subgroups

A Hopf ideal `I` cuts out, on every value algebra `A`, the subgroup of ambient points
`H(A)` which vanish on `I`. This file records the elementary order behavior of this
construction: if `I ≤ J`, then every point which kills `J` also kills `I`, so the subgroup
cut out by `J` is contained in the subgroup cut out by `I`.

This is the point-level order bookkeeping for the Layer 3 ReductiveGroups roadmap item
"Hopf ideals ↔ closed subgroup schemes". Larger Hopf ideals correspond contravariantly to
smaller closed subgroup functors, and the inclusion is compatible with functoriality in the
value algebra.

## Main declarations

* `CommHopfAlgCat.quotientPointsSubgroup_antitone`: the cut-out point subgroup is antitone in
  the Hopf ideal.
* `CommHopfAlgCat.quotientPointsSubgroup_sup`: the point subgroup cut out by a join of Hopf
  ideals is the intersection of the point subgroups cut out by the joinands.
* `CommHopfAlgCat.quotientPointsSubgroupInclusion`: the bundled natural inclusion between
  subgroup functors induced by `I ≤ J`.
* `CommHopfAlgCat.mapQuotientPointsSubgroup_inclusion_apply`: these inclusions commute with
  post-composition in the value algebra.

## References

This uses the vanishing characterization of quotient points from
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic` and the naturality API from
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The point subgroup cut out by a Hopf ideal is antitone in the Hopf ideal:
larger ideals impose more vanishing equations. -/
theorem quotientPointsSubgroup_antitone (H : _root_.CommHopfAlgCat.{v} R)
    (A : CommAlgCat.{w} R) :
    Antitone fun I : HopfIdeal R H => quotientPointsSubgroup H I A := by
  intro I J hIJ g hg
  rw [mem_quotientPointsSubgroup_iff] at hg ⊢
  intro h hh
  exact hg h (hIJ hh)

/-- If `I ≤ J`, then the point subgroup cut out by `J` is contained in the point subgroup
cut out by `I`. -/
theorem quotientPointsSubgroup_le_of_le (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup H J A ≤ quotientPointsSubgroup H I A :=
  quotientPointsSubgroup_antitone H A hIJ

/-- Rewriting form of `quotientPointsSubgroup_le_of_le` as a membership implication. -/
theorem mem_quotientPointsSubgroup_of_le (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) (A : CommAlgCat.{w} R)
    {g : HopfAlgebra.points (R := R) (H := H) A}
    (hg : g ∈ quotientPointsSubgroup H J A) :
    g ∈ quotientPointsSubgroup H I A :=
  quotientPointsSubgroup_le_of_le H hIJ A hg

/-- If `I = J`, then the point subgroups cut out by `I` and `J` are equal. -/
theorem quotientPointsSubgroup_eq_of_eq (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I = J) (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup H I A = quotientPointsSubgroup H J A := by
  subst hIJ
  rfl

/-- The point subgroup cut out by the zero Hopf ideal is the full ambient point group. -/
@[simp]
theorem quotientPointsSubgroup_bot (H : _root_.CommHopfAlgCat.{v} R)
    (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup H (⊥ : HopfIdeal R H) A = ⊤ := by
  ext g
  constructor
  · intro _
    exact Subgroup.mem_top g
  · intro _
    rw [mem_quotientPointsSubgroup_iff]
    intro h hh
    rw [HopfIdeal.mem_bot.mp hh, map_zero]

/-- The point subgroup cut out by a join of Hopf ideals is the intersection of the point
subgroups cut out by the joinands: a point vanishes on `I ⊔ J` exactly when it vanishes on
`I` and on `J`. -/
theorem quotientPointsSubgroup_sup (H : _root_.CommHopfAlgCat.{v} R)
    (I J : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup H (I ⊔ J) A =
      quotientPointsSubgroup H I A ⊓ quotientPointsSubgroup H J A := by
  refine le_antisymm
    (le_inf (quotientPointsSubgroup_le_of_le H le_sup_left A)
      (quotientPointsSubgroup_le_of_le H le_sup_right A))
    fun g hg => ?_
  obtain ⟨hI, hJ⟩ := Subgroup.mem_inf.mp hg
  rw [mem_quotientPointsSubgroup_iff] at hI hJ ⊢
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := HopfIdeal.mem_sup.mp hx
  rw [map_add, hI y hy, hJ z hz, add_zero]

/-- The subgroup inclusions associated to `I ≤ J` commute with maps of value algebras. -/
@[simp]
theorem mapQuotientPointsSubgroup_inclusion_apply
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    {A B : CommAlgCat.{w} R} (χ : A ⟶ B) (g : quotientPointsSubgroup H J A) :
    mapQuotientPointsSubgroup H I χ
        (Subgroup.inclusion (quotientPointsSubgroup_le_of_le H hIJ A) g) =
      Subgroup.inclusion (quotientPointsSubgroup_le_of_le H hIJ B)
        (mapQuotientPointsSubgroup H J χ g) := by
  apply Subtype.ext
  rw [coe_mapQuotientPointsSubgroup_apply, Subgroup.coe_inclusion, Subgroup.coe_inclusion,
    coe_mapQuotientPointsSubgroup_apply]

/-- The natural inclusion of subgroup functors associated to `I ≤ J`. -/
@[expose] noncomputable def quotientPointsSubgroupInclusion
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    quotientPointsSubgroupFunctor (R := R) H J ⟶
      quotientPointsSubgroupFunctor (R := R) H I where
  app A := GrpCat.ofHom (Subgroup.inclusion (quotientPointsSubgroup_le_of_le H hIJ A))
  naturality {A B} χ := by
    simp only [quotientPointsSubgroupFunctor_obj, quotientPointsSubgroupFunctor_map]
    rw [← GrpCat.ofHom_comp, ← GrpCat.ofHom_comp]
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact mapQuotientPointsSubgroup_inclusion_apply H hIJ χ g

/-- The component of `quotientPointsSubgroupInclusion` is the subgroup inclusion. -/
@[simp]
lemma quotientPointsSubgroupInclusion_app
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J)
    (A : CommAlgCat.{w} R) :
    (quotientPointsSubgroupInclusion (R := R) H hIJ).app A =
      GrpCat.ofHom (Subgroup.inclusion (quotientPointsSubgroup_le_of_le H hIJ A)) :=
  rfl

/-- The inclusion associated to reflexivity is the identity natural transformation. -/
@[simp]
lemma quotientPointsSubgroupInclusion_refl
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    quotientPointsSubgroupInclusion (R := R) H (le_refl I) =
      𝟙 (quotientPointsSubgroupFunctor (R := R) H I) := by
  ext A g
  exact SubgroupClass.inclusion_self g

/-- Inclusions of quotient point subgroup functors compose along transitive ideal inclusions. -/
@[simp]
lemma quotientPointsSubgroupInclusion_comp
    (H : _root_.CommHopfAlgCat.{v} R) {I J K : HopfIdeal R H}
    (hIJ : I ≤ J) (hJK : J ≤ K) :
    quotientPointsSubgroupInclusion (R := R) H hJK ≫
        quotientPointsSubgroupInclusion (R := R) H hIJ =
      quotientPointsSubgroupInclusion (R := R) H (hIJ.trans hJK) := by
  ext A g
  exact SubgroupClass.inclusion_inclusion
    (quotientPointsSubgroup_le_of_le H hJK A)
    (quotientPointsSubgroup_le_of_le H hIJ A) g

end CommHopfAlgCat

end TauCeti
