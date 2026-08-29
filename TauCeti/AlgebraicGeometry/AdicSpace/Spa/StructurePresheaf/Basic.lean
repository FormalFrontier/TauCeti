/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.CompleteSeparated.RefinementCategory
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Limits

/-!
# The presentation-indexed limit behind the structure presheaf

Wedhorn §8.1 assigns `A⟨T/s⟩` to the rational subset `R(T/s)` and extends the assignment to an
arbitrary open `V ⊆ Spa(A,A⁺)` by the limit over the rational subsets contained in `V`. This file
constructs that limit **indexed by presentations rather than by rational subsets**, and makes it a
presheaf. It is deliberately not named for `𝒪_X`: see *What this is not, yet* below.

The index is `PresentationIndex`: a presentation together with a proof that the rational subset it
presents lies in `V`, ordered by refinement. `RefinementCategory` already makes the assignment
`p ↦ A⟨p.num / p.den⟩` functorial on presentations, so the diagram is obtained by restricting that
functor along the forgetful map, and the value is its limit — which exists because
`CompleteSeparatedTopCommRingCat` has all small limits.

## Main definitions

* `TauCeti.ValuationSpectrum.PresentationIndex` : the index category for an open — presentations
  whose numerator ideal is open, so that the basic open they present really is a rational subset.
* `TauCeti.ValuationSpectrum.presentationIndexDiagram` : the diagram it indexes.
* `TauCeti.ValuationSpectrum.presentationLimit` : the limit itself.
* `TauCeti.ValuationSpectrum.presentationLimitMap` : the restriction morphism of a containment.
* `TauCeti.ValuationSpectrum.presentationLimitPresheaf` : the presheaf they assemble into.

## Main results

* `TauCeti.ValuationSpectrum.presentationLimit_hom_ext` : two morphisms into the limit agree as
  soon as their projections do.
* `TauCeti.ValuationSpectrum.presentationLimitMap_comp_π` : restriction is reindexing —
  restricting and then projecting is projecting at the same presentation.
* `TauCeti.ValuationSpectrum.presentationLimitMap_refl` and
  `TauCeti.ValuationSpectrum.presentationLimitMap_comp` : the two functor laws, as normal forms
  for a restriction map along `le_refl` and for a composite of two restriction maps.

## Why the index is presentations and not subsets

`A⟨T/s⟩` is built from the data `(T, s)`, and two presentations of the *same* rational subset give
canonically isomorphic but not equal rings. Indexing the limit by presentations rather than by
subsets avoids having to choose one.

## What this is not, yet

The presheaf built here is **not identified with Wedhorn's `𝒪_X`**, and is named for what it is
rather than for what it is expected to become. Wedhorn indexes by rational *subsets* `U ⊆ V`, which
presupposes that `𝒪_X(U)` is well defined; here the index is presentations, so the value depends a
priori on presentation data. Two results close the gap, and neither is yet available outright:

* refinement maps between two presentations of the *same* rational subset are isomorphisms, so that
  `p ↦ A⟨p.num / p.den⟩` descends to a function of the subset. The isomorphism is supplied by
  `TauCeti.ValuationSpectrum.presentationRingEquivOfEq`, but only for coordinate rings whose
  denominators are invertible in each other's coordinate ring and whose plus subrings are open —
  Wedhorn asks for neither, so the descent is not yet unconditional; and
* the presentation index is then cofinal in the subset index, so the two limits agree.

Until both are available unconditionally, no result here may be read as computing `𝒪_X(V)`, and
in particular nothing here shows the value on a rational open `U` is `A_U`. What *is* established
is self-contained: the limit exists, restriction along a containment is reindexing, and the two
functor laws hold.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.

## Provenance

The idea of indexing the limit by presentations, and the refinement relation ordering them, were
adapted from AINTLIB (Apache-2.0), commit `37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`,
`projects/AdicSpaces/Adic spaces/StructurePresheafLimit.lean`. The Lean here is written against this
repository's own `RefinementCategory` and `PairOfDefinition.Presentation` API; no code was copied.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory CategoryTheory.Limits _root_.TopologicalSpace TauCeti.Huber

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **The index of the limit**: presentations whose numerator ideal is open and whose rational
subset lies in `V`.

The openness of `Ideal.span pres.num` is what makes `R(pres.num / pres.den)` a *rational* subset
in Wedhorn's sense rather than a general basic open — it is the defining condition of
`TauCeti.ValuationSpectrum.spaRationalFamily`. Carrying it as a field of the index restricts the
diagram to admissible presentations; because it is a field, every object supplies its own proof
and the refinement morphisms carry no preservation obligation. -/
structure PresentationIndex {P : PairOfDefinition A} (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) where
  /-- The presentation. -/
  pres : P.Presentation
  /-- Its numerator ideal is open, so the subset it presents is rational. -/
  isOpen_span : IsOpen (Ideal.span (pres.num : Set A) : Set A)
  /-- Its rational subset is contained in `V`. -/
  le_open : spaBasicOpen Aplus pres.num pres.den ≤ V

variable {P : PairOfDefinition A} {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

/-- Refinement of the underlying presentations orders the index. -/
instance : Preorder (PresentationIndex (P := P) Aplus V) :=
  Preorder.lift PresentationIndex.pres

omit [IsTopologicalRing A] in
/-- **An index is its presentation.** The other two fields are propositions, so they are
proof-irrelevant and carry no information: equality of indices reduces to equality of the
underlying presentations. -/
@[ext]
theorem PresentationIndex.ext {i j : PresentationIndex (P := P) Aplus V} (h : i.pres = j.pres) :
    i = j := by
  cases i
  cases j
  subst h
  rfl

/-- Forgetting the containment is a functor to the category of all presentations. -/
private def presentationIndexInclusion (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    PresentationIndex (P := P) Aplus V ⥤ P.Presentation where
  obj i := i.pres
  map h := homOfLE h.le

/-- **The diagram the limit is taken over**: each admissible presentation refining `V` contributes
`A⟨T/s⟩`, and a refinement contributes its restriction morphism. -/
noncomputable def presentationIndexDiagram (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    PresentationIndex (P := P) Aplus V ⥤ CompleteSeparatedTopCommRingCat.{v} :=
  presentationIndexInclusion Aplus V ⋙ P.presentationFunctor

/-- **The limit over the presentations refining `V`**, `lim_{R(T/s) ⊆ V} A⟨T/s⟩` — Wedhorn §8.1's
formula for `𝒪_X(V)`, but indexed by presentations rather than by rational subsets. The limit
exists because `CompleteSeparatedTopCommRingCat` has all small limits. This is *not* shown to be
`𝒪_X(V)`; see the module docstring. -/
noncomputable def presentationLimit (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    CompleteSeparatedTopCommRingCat.{v} :=
  limit (presentationIndexDiagram (P := P) Aplus V)

/-- Restricting the containment reindexes the diagram: a presentation refining `W` refines `V`
whenever `W ≤ V`. -/
def presentationIndexRestrict {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    PresentationIndex (P := P) Aplus W ⥤ PresentationIndex (P := P) Aplus V where
  obj i := ⟨i.pres, i.isOpen_span, i.le_open.trans h⟩
  map f := homOfLE f.le

/-- **The restriction morphism of a containment `W ≤ V`**: the limit over the presentations
refining `V` maps to the limit over the smaller index, by reindexing. -/
noncomputable def presentationLimitMap {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    presentationLimit (P := P) Aplus V ⟶ presentationLimit (P := P) Aplus W :=
  limit.pre (presentationIndexDiagram (P := P) Aplus V) (presentationIndexRestrict (P := P) h)

/-! ### The projection, and the restriction normal forms

`presentationLimit` is a `limit`, so Mathlib's `limit.w`, `limit.lift` and `limit.lift_π` are its
interface and are not restated here. Two names do have to exist. `presentationLimitπ` is
load-bearing rather than cosmetic: `presentationLimitMap`'s codomain is `presentationLimit W`, and
because that definition is sealed the elaborator will not identify it with `limit (diagram W)`, so
`limit.π` cannot be written at the use site — it reports *"definitions were not unfolded because
their definition is not exposed"*. `presentationLimit_hom_ext` follows it: `limit.hom_ext` leaves
goals spelled with `limit.π`, which the restriction lemmas below then fail to rewrite.
-/

/-- **The projection of `presentationLimit` at an index.** -/
noncomputable def presentationLimitπ (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (i : PresentationIndex (P := P) Aplus V) :
    presentationLimit (P := P) Aplus V ⟶ (presentationIndexDiagram (P := P) Aplus V).obj i :=
  limit.π _ i

/-- **Projections are compatible with refinement**: projecting then restricting along a refinement
is projecting at the finer index. -/
-- These three are not restatements of Mathlib's limit API for their own sake: `presentationLimit`
-- is sealed, so a consumer in another module cannot apply `limit.w`, `limit.lift` or `limit.lift_π`
-- to it at all. They are the only access to the universal property from outside this file.
@[simp]
theorem presentationLimitπ_comp_map {i j : PresentationIndex (P := P) Aplus V} (h : i ⟶ j) :
    presentationLimitπ (P := P) Aplus V i ≫ (presentationIndexDiagram (P := P) Aplus V).map h =
      presentationLimitπ (P := P) Aplus V j :=
  limit.w _ h

/-- **The universal property**: a cone over the diagram factors through the limit. -/
noncomputable def presentationLimitLift (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (s : Cone (presentationIndexDiagram (P := P) Aplus V)) :
    s.pt ⟶ presentationLimit (P := P) Aplus V :=
  limit.lift _ s

/-- **The lift is a factorisation**: composing it with a projection recovers the cone leg. -/
@[simp]
theorem presentationLimitLift_comp_π (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (s : Cone (presentationIndexDiagram (P := P) Aplus V))
    (i : PresentationIndex (P := P) Aplus V) :
    presentationLimitLift (P := P) Aplus V s ≫ presentationLimitπ (P := P) Aplus V i = s.π.app i :=
  limit.lift_π _ _

/-- **Extensionality**: maps into the limit agree when their projections do. -/
-- Tagged `@[ext]` because `presentationLimit` is sealed, so `ext` cannot reach `limit.hom_ext`
-- through it from another module.
@[ext]
theorem presentationLimit_hom_ext {W : CompleteSeparatedTopCommRingCat.{v}}
    {f g : W ⟶ presentationLimit (P := P) Aplus V}
    (h : ∀ i, f ≫ presentationLimitπ (P := P) Aplus V i =
      g ≫ presentationLimitπ (P := P) Aplus V i) : f = g :=
  limit.hom_ext h

/-- **Restricting an index does not change what the diagram sends it to.** -/
-- This is the object half of the reindexing characterisation, and what lets the index functors
-- stay sealed: the two objects are definitionally equal, and naming that equality here means no
-- consumer has to see a body to use it.
theorem presentationIndexDiagram_obj_restrict {V W : Opens ↥(spa Aplus)} (h : W ≤ V)
    (i : PresentationIndex (P := P) Aplus W) :
    (presentationIndexDiagram (P := P) Aplus V).obj ((presentationIndexRestrict (P := P) h).obj i) =
      (presentationIndexDiagram (P := P) Aplus W).obj i := (rfl)

/-- **Restriction is reindexing**: restricting to `W` and then projecting at an index of `W` is
projecting at the same presentation viewed as an index of `V`, transported along
`presentationIndexDiagram_obj_restrict`. -/
-- The transport is the price of keeping the index functors sealed; it is `eqToHom` of a
-- `rfl`-equality, so `simp` discharges it at every use site.
@[simp]
theorem presentationLimitMap_comp_π {V W : Opens ↥(spa Aplus)} (h : W ≤ V)
    (i : PresentationIndex (P := P) Aplus W) :
    presentationLimitMap (P := P) h ≫ presentationLimitπ (P := P) Aplus W i =
      presentationLimitπ (P := P) Aplus V ((presentationIndexRestrict (P := P) h).obj i) ≫
        eqToHom (presentationIndexDiagram_obj_restrict (P := P) h i) :=
  limit.pre_π _ _ _

/-- **Restricting along `le_refl` is the identity.** -/
@[simp]
theorem presentationLimitMap_refl (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    presentationLimitMap (P := P) (le_refl V) = 𝟙 (presentationLimit (P := P) Aplus V) := by
  apply limit.hom_ext
  intro j
  -- `presentationIndexRestrict (le_refl V)` is only definitionally the identity functor, so
  -- `limit.pre_π`'s index does not match syntactically and `rw` reports no occurrence.
  erw [limit.pre_π, Category.id_comp]
  rfl

/-- **Successive restrictions compose** to the restriction along the transitive containment. -/
@[simp]
theorem presentationLimitMap_comp {U V W : Opens ↥(spa Aplus)} (h₁ : W ≤ V) (h₂ : U ≤ W) :
    presentationLimitMap (P := P) h₁ ≫ presentationLimitMap (P := P) h₂ =
      presentationLimitMap (P := P) (h₂.trans h₁) := by
  refine presentationLimit_hom_ext (P := P) fun j => ?_
  -- The last step needs `erw`: the two sides land in `(diagram W).obj i` and
  -- `(diagram V).obj ((restrict h₁).obj i)`, which are definitionally but not syntactically equal.
  simp only [Category.assoc, presentationLimitMap_comp_π]
  erw [presentationLimitMap_comp_π]
  rfl

/-- **The presheaf `V ↦ presentationLimit V`** on `Spa(A,A⁺)`, valued in
`CompleteSeparatedTopCommRingCat`. Both functor laws are reindexing identities for the limit:
restricting along `le_refl` is the identity on the index, and restricting twice is restricting
once. Wedhorn §8.1's `𝒪_X` is this presheaf only once presentation-independence is available. -/
-- This definition is sealed, as are the three index functors above. Two consequences worth
-- naming, because they are what the evaluation lemmas below look like: `_obj` closes with
-- `(rfl)` rather than `rfl`, the parentheses letting the elaborator postpone a defeq check the
-- sealed body would otherwise refuse; and `_map` cannot be stated bare at all, since its sides
-- live in `(presheaf).obj V ⟶ (presheaf).obj W` and `presentationLimit V.unop ⟶
-- presentationLimit W.unop`, equal only definitionally. It carries `eqToHom` transports built
-- from `_obj`. Both transports are `eqToHom` of `rfl`-equalities, so `simp` removes them at the
-- use site and no consumer sees a body.
noncomputable def presentationLimitPresheaf (P : PairOfDefinition A) (Aplus : Subring A) :
    (Opens ↥(spa Aplus))ᵒᵖ ⥤ CompleteSeparatedTopCommRingCat.{v} where
  obj V := presentationLimit (P := P) Aplus V.unop
  map h := presentationLimitMap (P := P) (leOfHom h.unop)
  map_id V := presentationLimitMap_refl (P := P) Aplus V.unop
  map_comp f g := (presentationLimitMap_comp (P := P) (leOfHom f.unop) (leOfHom g.unop)).symm


/-- Evaluating the presheaf on an open is the limit over that open. -/
@[simp]
theorem presentationLimitPresheaf_obj (P : PairOfDefinition A) (Aplus : Subring A)
    (V : (Opens ↥(spa Aplus))ᵒᵖ) :
    (presentationLimitPresheaf P Aplus).obj V = presentationLimit (P := P) Aplus V.unop :=
  (rfl)

/-- The presheaf's action on a containment is the reindexing map. -/
@[simp]
theorem presentationLimitPresheaf_map (P : PairOfDefinition A) (Aplus : Subring A)
    {V W : (Opens ↥(spa Aplus))ᵒᵖ} (h : V ⟶ W) :
    (presentationLimitPresheaf P Aplus).map h =
      eqToHom (presentationLimitPresheaf_obj P Aplus V) ≫
        presentationLimitMap (P := P) (leOfHom h.unop) ≫
          eqToHom (presentationLimitPresheaf_obj P Aplus W).symm :=
  (rfl)

end

end TauCeti.ValuationSpectrum
