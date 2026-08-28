/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic
import Mathlib.CategoryTheory.Sites.CoversTop.Over

/-!
# Local trivializations of invertible sheaves

An invertible sheaf is locally free on a one-element basis. This file turns the
singleton-indexed free presentations in `SheafOfModules.IsInvertible` into the standard
geometric formulation: on every member of a cover, the sheaf is isomorphic to the free sheaf
on `PUnit`.

The structure `SheafOfModules.LocalTrivializations M` records such a cover and its
trivializing isomorphisms. The two formulations are equivalent:

* `LocalGeneratorsData.IsInvertible.trivializationIso` standardizes each rank-one free
  presentation;
* `LocalTrivializations.ofIso` transports a local trivialization atlas along an isomorphism;
* `LocalTrivializations.isInvertible` recovers the local-generator formulation;
* `LocalTrivializations.ofIsInvertible` constructs local trivializations from an invertible
  sheaf;
* `LocalTrivializations.nonempty_iff_isInvertible` characterizes invertibility by the existence
  of local trivializations;
* `LocalTrivializations.CommonRefinement` records a cover refining two local trivialization
  atlases, and `LocalTrivializations.commonRefinement` constructs one.

This supplies the local-triviality interface for
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a scheme; the
Picard group `Pic X` under `⊗`". It is the form needed to prove that tensor products and duals
of invertible sheaves remain invertible. The common-refinement construction here supplies the
cover-theoretic step for tensor-product closure. The construction reuses Mathlib's free-sheaf
functor, `LocalGeneratorsData`, and the transitivity lemma for covers in over-categories; no
formalization is vendored.
-/

public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

/-- A local trivialization atlas for a sheaf of modules. It consists of a cover of the terminal
object and, over every member of the cover, an isomorphism from the standard free rank-one
sheaf to the restriction of `M`. -/
structure LocalTrivializations (M : SheafOfModules.{u} R) where
  /-- The indexing type of the trivializing cover. -/
  I : Type u₁
  /-- The objects of the trivializing cover. -/
  X : I → C
  /-- The chosen objects cover the terminal object. -/
  coversTop : J.CoversTop X
  /-- The isomorphism from the standard free rank-one sheaf to `M` on each member of the
  cover. -/
  iso (i : I) :
    _root_.SheafOfModules.free (R := R.over (X i)) PUnit ≅ M.over (X i)

namespace LocalGeneratorsData.IsInvertible

/-- A rank-one free presentation on a member of a cover, standardized to an isomorphism from
the free sheaf on `PUnit`. -/
def trivializationIso {q : SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.IsInvertible q) (i : q.I) :
    _root_.SheafOfModules.free (R := R.over (q.X i)) PUnit ≅ M.over (q.X i) := by
  letI : Nonempty (q.generators i).I := hq.basisNonempty i
  letI : Subsingleton (q.generators i).I := hq.basisSubsingleton i
  exact
    ((_root_.SheafOfModules.freeFunctor (R := R.over (q.X i))).mapIso
      Equiv.punitOfNonemptyOfSubsingleton.symm.toIso).trans
      (@asIso _ _ _ _ (q.generators i).π (hq.isLocallyFreeData.isIso i))

/-- The forward map of the standardized trivialization is the relabelling of the free basis,
followed by the original local free presentation. -/
@[simp]
lemma trivializationIso_hom {q : SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.IsInvertible q) (i : q.I) : (hq.trivializationIso i).hom =
      (_root_.SheafOfModules.freeFunctor (R := R.over (q.X i))).map
        (@Equiv.punitOfNonemptyOfSubsingleton (q.generators i).I
          (hq.basisNonempty i) (hq.basisSubsingleton i)).symm.toIso.hom ≫
        (q.generators i).π :=
  by
    simp only [trivializationIso, Iso.trans_hom, Functor.mapIso_hom]
    -- the residual goal is `(asIso (q.generators i).π).hom = (q.generators i).π`; `asIso_hom`
    -- no longer rewrites under the composition after the bump, and `asIso` stores its `hom`
    -- field as the given morphism, so this is definitional.
    rfl

end LocalGeneratorsData.IsInvertible

namespace LocalTrivializations

/-- A common refinement of two local trivialization atlases.

The objects in the refined cover carry arrows to one member of each original cover. The arrows
are retained explicitly because they are the data used to restrict the two trivializing
isomorphisms to the common cover. -/
structure CommonRefinement (t : LocalTrivializations M) (s : LocalTrivializations N) where
  /-- The indexing type of the common refinement. -/
  I : Type u₁
  /-- The objects in the common refinement. -/
  X : I → C
  /-- The member of the first atlas above each refined object. -/
  leftIndex : I → t.I
  /-- The arrow from each refined object to its member of the first atlas. -/
  left : ∀ i, X i ⟶ t.X (leftIndex i)
  /-- The member of the second atlas above each refined object. -/
  rightIndex : I → s.I
  /-- The arrow from each refined object to its member of the second atlas. -/
  right : ∀ i, X i ⟶ s.X (rightIndex i)
  /-- The sieve generated by the refined objects covers every object. -/
  coversTop : J.CoversTop X

private lemma coversTop_of_sieve (t : LocalTrivializations M) (s : LocalTrivializations N)
    (i : t.I) :
    (J.over (t.X i)).CoversTop
      (fun z : {Z : Over (t.X i) // Sieve.ofObjects s.X (t.X i) Z.hom} ↦ z.1) := by
  intro W
  rw [J.mem_over_iff]
  refine J.superset_covering ?_
    (J.pullback_stable W.hom (s.coversTop (t.X i)))
  intro V f hf
  rw [Sieve.overEquiv_iff, Sieve.mem_ofObjects_iff]
  let Z : Over (t.X i) := Over.mk (f ≫ W.hom)
  exact ⟨⟨Z, hf⟩, ⟨𝟙 Z⟩⟩

/-- Construct a common refinement of any two local trivialization atlases.

For a member of the first cover, use the pullback along it of the sieve generated by the second
cover. The resulting family is a cover on the corresponding over-category, and
`CoversTop.over` combines these covers with the first atlas. -/
noncomputable def commonRefinement (t : LocalTrivializations M) (s : LocalTrivializations N) :
    CommonRefinement t s := by
  let I' (i : t.I) := {Z : Over (t.X i) // Sieve.ofObjects s.X (t.X i) Z.hom}
  let Y (i : t.I) (z : I' i) := z.1.left
  let K := Σ i, I' i
  let i' : K → t.I := Sigma.fst
  let j' : (k : K) → s.I :=
    fun k => ((Sieve.mem_ofObjects_iff s.X k.2.1.hom).mp k.2.2).choose
  let g' : (k : K) → Y k.1 k.2 ⟶ s.X (j' k) :=
    fun k => ((Sieve.mem_ofObjects_iff s.X k.2.1.hom).mp k.2.2).choose_spec.some
  let Z : K → C := fun k => Y k.1 k.2
  let I := Set.range Z
  let X : I → C := fun k => Z k.2.choose
  exact
    { I := I
      X := X
      leftIndex := fun k => i' k.2.choose
      left := fun k => k.2.choose.2.1.hom
      rightIndex := fun k => j' k.2.choose
      right := fun k => g' k.2.choose
      coversTop := by
        intro A
        refine J.superset_covering (fun W hW H ↦ ?_)
          (CoversTop.over t.coversTop (fun i => coversTop_of_sieve t s i) A)
        obtain ⟨k, ⟨hk⟩⟩ := (Sieve.mem_ofObjects_iff Z hW).mp H
        exact ⟨⟨Z k, ⟨k, rfl⟩⟩, ⟨hk ≫ eqToHom (by grind)⟩⟩ }

/-- Transport local trivializations along an isomorphism of sheaves of modules. -/
def ofIso (t : LocalTrivializations M) (e : M ≅ N) : LocalTrivializations N where
  I := t.I
  X := t.X
  coversTop := t.coversTop
  iso i := t.iso i ≪≫ (SheafOfModules.overFunctor R (t.X i)).mapIso e

/-- Transporting local trivializations preserves the indexing type. -/
@[simp]
lemma ofIso_I (t : LocalTrivializations M) (e : M ≅ N) : (t.ofIso e).I = t.I := (rfl)

/-- Transporting local trivializations preserves the covering objects. -/
@[simp]
lemma ofIso_X (t : LocalTrivializations M) (e : M ≅ N) :
    (t.ofIso e).X = fun i ↦ t.X ((ofIso_I t e).mp i) := (rfl)

/-- The transported trivializations are obtained by composing with the restricted isomorphism. -/
@[simp]
lemma ofIso_iso (t : LocalTrivializations M) (e : M ≅ N) (i : (t.ofIso e).I) : (t.ofIso e).iso i =
      cast (by rw [ofIso_X])
        (t.iso ((ofIso_I t e).mp i) ≪≫
          (SheafOfModules.overFunctor R (t.X ((ofIso_I t e).mp i))).mapIso e) := (rfl)

/-- Local trivializations exhibit a sheaf as invertible. -/
theorem isInvertible (t : LocalTrivializations M) : IsInvertible M := by
  let q : SheafOfModules.LocalGeneratorsData.{u₁} M :=
    { I := t.I
      X := t.X
      coversTop := t.coversTop
      generators i :=
        (_root_.SheafOfModules.free.generatingSections
          (R := R.over (t.X i)) PUnit).ofEpi (t.iso i).hom }
  refine ⟨q, ?_⟩
  refine
    { isLocallyFreeData :=
        { isIso := by
            -- `q` uses the atlas's cover and the standard free generators, so unfold that local
            -- witness to express its isomorphism condition directly in terms of `t`.
            change ∀ i : t.I, IsIso
              ((_root_.SheafOfModules.free.generatingSections
                (R := R.over (t.X i)) PUnit).ofEpi (t.iso i).hom).π
            intro i
            rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
            simpa only [_root_.SheafOfModules.free.generatingSections_π, Category.id_comp] using
              inferInstanceAs (IsIso (t.iso i).hom) }
      basisNonempty := fun i ↦ ?_
      basisSubsingleton := fun i ↦ ?_ }
  · simpa only [_root_.SheafOfModules.GeneratingSections.ofEpi_I,
      _root_.SheafOfModules.free.generatingSections_I] using
      inferInstanceAs (Nonempty PUnit)
  · simpa only [_root_.SheafOfModules.GeneratingSections.ofEpi_I,
      _root_.SheafOfModules.free.generatingSections_I] using
      inferInstanceAs (Subsingleton PUnit)

/-- Every invertible sheaf admits local trivializations by the standard free rank-one sheaf. -/
def ofIsInvertible (M : SheafOfModules.{u} R) [hM : IsInvertible M] :
    LocalTrivializations M := by
  let q := hM.exists_isInvertible.choose
  let hq := hM.exists_isInvertible.choose_spec
  exact
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      iso i := hq.trivializationIso i }

/-- A sheaf of modules is invertible exactly when it admits a local trivialization atlas by
the standard free rank-one sheaf. -/
theorem nonempty_iff_isInvertible :
    Nonempty (LocalTrivializations M) ↔ IsInvertible M := by
  constructor
  · rintro ⟨t⟩
    exact t.isInvertible
  · intro hM
    let := hM
    exact ⟨ofIsInvertible M⟩

end LocalTrivializations

end SheafOfModules

end

end TauCeti
