/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.Algebra.HopfAlgebra.GroupLike.FiniteGeneration

import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

/-!
# The essential image of diagonalizable coordinate Hopf algebras

Over a field `k`, a finite-type commutative Hopf algebra is the coordinate algebra of a
diagonalizable group exactly when its group-like elements span the whole carrier. This file
identifies that intrinsic object property with the essential image of
`DiagonalizableGroup.coordinateRingFunctor` and packages the resulting equivalence of categories.

The proof reconstructs a group-like-spanned Hopf algebra `H` from its group of group-like elements.
The canonical evaluation map `k[GroupLike k H] → H` is a bialgebra equivalence: spanning gives
surjectivity, while linear independence of group-like elements over a field gives injectivity.
Finite type then implies that `GroupLike k H` is finitely generated. Conversely, the standard
basis elements of every group algebra are group-like and span, and this property is invariant
under bialgebra equivalence.

All categories and carriers in the equivalence lie in the universe of `k`. Applying `Spec`, and
the resulting scheme-side anti-equivalence, are outside the scope of this file.

## Main declarations

* `TauCeti.MonoidAlgebra.groupLikeSetSpan_eq_top`: the group-like elements of a group algebra span.
* `TauCeti.GroupLike.groupLikeSetSpan_eq_top_iff_of_bialgEquiv`: group-like spanning is invariant
  under bialgebra equivalence.
* `TauCeti.DiagonalizableGroup.groupLikeSpannedProperty`: the intrinsic object property on
  finite-type commutative Hopf algebras.
* `TauCeti.DiagonalizableGroup.essImage_coordinateRingFunctor`: the essential image of the
  coordinate-ring functor is the group-like-spanned property.
* `TauCeti.DiagonalizableGroup.GroupLikeSpannedCommHopfAlgCat`: the corresponding full
  subcategory.
* `TauCeti.DiagonalizableGroup.coordinateRingEquivalence`: the equivalence from finitely generated
  commutative groups to group-like-spanned finite-type commutative Hopf algebras.

## References

See Milne, *Algebraic Groups*, Proposition 4.23 and Definition 12.7 with Theorems 12.8--12.9.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

namespace MonoidAlgebra

/-- The group-like elements of a monoid algebra span the whole algebra: every standard basis
element is group-like, and the standard basis spans. -/
theorem groupLikeSetSpan_eq_top (R : Type u) (G : Type v) [CommSemiring R] [Monoid G] :
    Subcoalgebra.groupLikeSetSpan (R := R) (C := _root_.MonoidAlgebra R G) Set.univ = ⊤ := by
  apply Subcoalgebra.ext
  intro x
  rw [Subcoalgebra.mem_groupLikeSetSpan]
  constructor
  · intro
    exact Subcoalgebra.mem_top x
  · intro
    have hbasis :
        Submodule.span R
            (Set.range (fun g : G ↦ _root_.MonoidAlgebra.single g (1 : R))) = ⊤ := by
      rw [show Set.range (fun g : G ↦ _root_.MonoidAlgebra.single g (1 : R)) =
          Set.range (_root_.MonoidAlgebra.basis G R) by
        ext y
        constructor <;> rintro ⟨g, rfl⟩
        · exact ⟨g, (_root_.MonoidAlgebra.basis_apply R g).symm⟩
        · exact ⟨g, _root_.MonoidAlgebra.basis_apply R g⟩]
      exact (_root_.MonoidAlgebra.basis G R).span_eq
    have hx : x ∈ Submodule.span R
        (Set.range (fun g : G ↦ _root_.MonoidAlgebra.single g (1 : R))) := by
      rw [hbasis]
      exact Submodule.mem_top
    apply (Submodule.span_mono ?_) hx
    rintro _ ⟨g, rfl⟩
    exact ⟨⟨_root_.MonoidAlgebra.single g 1,
      TauCeti.MonoidAlgebra.isGroupLikeElem_single_one R g⟩, Set.mem_univ _, rfl⟩

end MonoidAlgebra

namespace GroupLike

/-- A bialgebra equivalence preserves the property that the group-like elements span the whole
carrier. -/
theorem groupLikeSetSpan_eq_top_iff_of_bialgEquiv
    (R : Type u) (A : Type v) (B : Type w) [CommSemiring R]
    [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]
    (e : A ≃ₐc[R] B) :
    Subcoalgebra.groupLikeSetSpan (R := R) (C := A) Set.univ = ⊤ ↔
      Subcoalgebra.groupLikeSetSpan (R := R) (C := B) Set.univ = ⊤ := by
  let f : A ≃ₗ[R] B := e.toCoalgEquiv.toLinearEquiv
  have hgroupLike :
      f '' Set.range (_root_.GroupLike.val (R := R) (A := A)) =
        Set.range (_root_.GroupLike.val (R := R) (A := B)) := by
    ext b
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨⟨e g, g.isGroupLikeElem_val.map e⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      refine ⟨e.symm (g : B), ⟨⟨e.symm (g : B), ?_⟩, rfl⟩, ?_⟩
      · exact g.isGroupLikeElem_val.map e.symm
      · exact e.apply_symm_apply (g : B)
  constructor
  · intro hA
    have hA' :
        Submodule.span R
            (Set.range (_root_.GroupLike.val (R := R) (A := A))) = ⊤ := by
      have h := congrArg Subcoalgebra.toSubmodule hA
      simpa only [Subcoalgebra.groupLikeSetSpan_toSubmodule,
        Subcoalgebra.top_toSubmodule, Set.image_univ] using h
    have hB' :
        Submodule.span R
            (Set.range (_root_.GroupLike.val (R := R) (A := B))) = ⊤ := by
      rw [← hgroupLike, Submodule.span_image_linearEquiv, hA', Submodule.map_top,
        LinearEquiv.range]
    apply Subcoalgebra.ext
    intro b
    rw [Subcoalgebra.mem_groupLikeSetSpan]
    simp [hB']
  · intro hB
    have hB' :
        Submodule.span R
            (Set.range (_root_.GroupLike.val (R := R) (A := B))) = ⊤ := by
      have h := congrArg Subcoalgebra.toSubmodule hB
      simpa only [Subcoalgebra.groupLikeSetSpan_toSubmodule,
        Subcoalgebra.top_toSubmodule, Set.image_univ] using h
    have hA' :
        Submodule.span R
            (Set.range (_root_.GroupLike.val (R := R) (A := A))) = ⊤ := by
      apply Submodule.map_injective_of_injective (f := f.toLinearMap) f.injective
      calc
        (Submodule.span R
            (Set.range (_root_.GroupLike.val (R := R) (A := A)))).map f.toLinearMap =
            Submodule.span R
              (f '' Set.range (_root_.GroupLike.val (R := R) (A := A))) :=
          Submodule.map_span f.toLinearMap _
        _ = Submodule.span R
              (Set.range (_root_.GroupLike.val (R := R) (A := B))) := by rw [hgroupLike]
        _ = ⊤ := hB'
        _ = (⊤ : Submodule R A).map f.toLinearMap := by
          rw [Submodule.map_top, LinearEquiv.range]
    apply Subcoalgebra.ext
    intro a
    rw [Subcoalgebra.mem_groupLikeSetSpan]
    simp [hA']

end GroupLike

namespace DiagonalizableGroup

variable (k : Type u) [Field k]

/-- The object property selecting finite-type commutative Hopf algebras whose group-like elements
span the whole carrier. -/
@[expose] def groupLikeSpannedProperty :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  fun H ↦ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ = ⊤

/-- Membership in the group-like-spanned object property. -/
@[simp]
theorem groupLikeSpannedProperty_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    groupLikeSpannedProperty k H ↔
      Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ = ⊤ :=
  Iff.rfl

/-- The essential image of the finite-type diagonalizable coordinate-ring functor consists
exactly of the finite-type commutative Hopf algebras spanned by their group-like elements. -/
theorem essImage_coordinateRingFunctor :
    (coordinateRingFunctor k).essImage = groupLikeSpannedProperty k := by
  funext H
  apply propext
  constructor
  · rintro ⟨G, ⟨e⟩⟩
    let e' : ((coordinateRingFunctor k).obj G).obj ≅ H.obj :=
      (finiteTypeCommHopfAlgProperty k).ι.mapIso e
    exact (TauCeti.GroupLike.groupLikeSetSpan_eq_top_iff_of_bialgEquiv k
      ((coordinateRingFunctor k).obj G) H (_root_.CommHopfAlgCat.ofIso e')).mp
        (TauCeti.MonoidAlgebra.groupLikeSetSpan_eq_top k G)
  · intro hH
    letI : Group.FG (_root_.GroupLike k H) :=
      TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top k H
        (inferInstanceAs (Algebra.FiniteType k H)) hH
    let G : FGCommGrpCat.{u} := FGCommGrpCat.of (_root_.GroupLike k H)
    have hspan :
        Submodule.span k
            (Set.range (_root_.GroupLike.val (R := k) (A := H))) = ⊤ := by
      have h := congrArg Subcoalgebra.toSubmodule hH
      simpa only [Subcoalgebra.groupLikeSetSpan_toSubmodule,
        Subcoalgebra.top_toSubmodule, Set.image_univ] using h
    let e : _root_.CommHopfAlgCat.of k (_root_.MonoidAlgebra k (_root_.GroupLike k H)) ≅
        H.obj :=
      _root_.CommHopfAlgCat.isoMk
          (TauCeti.GroupLike.evaluationBialgEquiv k H hspan) ≪≫
        _root_.CommHopfAlgCat.ofIsoSelf H.obj
    exact ⟨G, ⟨ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty k) e⟩⟩

/-- The property of being spanned by group-like elements is invariant under isomorphisms of
finite-type commutative Hopf algebras. -/
instance groupLikeSpannedProperty_isClosedUnderIsomorphisms :
    (groupLikeSpannedProperty k).IsClosedUnderIsomorphisms := by
  rw [← essImage_coordinateRingFunctor k]
  infer_instance

/-- The category of finite-type commutative Hopf algebras spanned by their group-like elements. -/
abbrev GroupLikeSpannedCommHopfAlgCat :=
  (groupLikeSpannedProperty k).FullSubcategory

/-- Finitely generated commutative groups are equivalent to finite-type commutative Hopf
algebras spanned by their group-like elements, via the group-algebra coordinate-ring functor. -/
noncomputable def coordinateRingEquivalence :
    FGCommGrpCat.{u} ≌ GroupLikeSpannedCommHopfAlgCat k :=
  (coordinateRingFunctor k).toEssImage.asEquivalence.trans
    (ObjectProperty.fullSubcategoryCongr (essImage_coordinateRingFunctor k))

/-- The forward functor of `coordinateRingEquivalence`, followed by the inclusion into all
finite-type commutative Hopf algebras, is the coordinate-ring functor. -/
noncomputable def coordinateRingEquivalence.functorCompιIso :
    (coordinateRingEquivalence k).functor ⋙ (groupLikeSpannedProperty k).ι ≅
      coordinateRingFunctor k := by
  change (((coordinateRingFunctor k).toEssImage ⋙
      ObjectProperty.ιOfLE (essImage_coordinateRingFunctor k).le) ⋙
        (groupLikeSpannedProperty k).ι) ≅ coordinateRingFunctor k
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (coordinateRingFunctor k).toEssImage
      (ObjectProperty.ιOfLECompιIso _) ≪≫
    (coordinateRingFunctor k).toEssImageCompι

end DiagonalizableGroup

end TauCeti
