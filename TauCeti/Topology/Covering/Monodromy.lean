/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Covering.Category
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality

/-!
# The monodromy functor on covering spaces

For a fixed topological space `X`, a covering space over `X` determines its monodromy functor from
the fundamental groupoid of `X` to types. A map of covering spaces restricts on every fibre and
therefore induces a natural transformation of monodromy functors. This file assembles those object-
and morphism-level constructions into a functor on `TauCeti.CoveringSpace X`.

The resulting functor is faithful: a map over `X` is determined by all of its restrictions to the
fibres. Fullness and the characterization of its essential image are the remaining topological
content of the classification of covering spaces by fundamental-groupoid actions.

## Main declarations

* `TauCeti.CoveringSpace.monodromyFunctor`: the functor from covering spaces over `X` to functors
  from the fundamental groupoid of `X` to types.
* `TauCeti.CoveringSpace.monodromyFunctor_map_app`: the natural transformation induced by a map of
  covering spaces, evaluated at a base point.
* `TauCeti.CoveringSpace.monodromyFunctor_faithful`: monodromy is faithful on maps of covers.

## References

This is the functor-construction step in Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`. It reuses Mathlib's object-level
`IsCoveringMap.monodromyFunctor` and Tau Ceti's functoriality of monodromy under maps of covering
spaces.
-/

public section

open CategoryTheory

universe u

namespace TauCeti.CoveringSpace

variable {X : TopCat.{u}}

/-- Monodromy as a functor from covering spaces over `X` to functors from the fundamental
groupoid of `X` to types.

A covering space is sent to its own monodromy functor, and a map of covering spaces to the natural
transformation restricting that map to every fibre. The definition is exposed, so downstream files
may unfold its object and morphism values; the intended interface for doing so is
`monodromyFunctor_obj` and `monodromyFunctor_map_app` rather than the record fields. -/
@[expose] noncomputable def monodromyFunctor (X : TopCat.{u}) :
    CoveringSpace X ⥤ (FundamentalGroupoid X ⥤ Type u) where
  obj p := p.isCoveringMap_proj.monodromyFunctor
  map {p q} f := IsCoveringMap.monodromyNatTrans p.isCoveringMap_proj q.isCoveringMap_proj
    f.hom.left.hom (proj_hom_comp_hom_left_hom f)
  map_id p := by
    simp
  map_comp {p q r} f g := by
    simpa using IsCoveringMap.monodromyNatTrans_comp p.isCoveringMap_proj
      q.isCoveringMap_proj r.isCoveringMap_proj f.hom.left.hom g.hom.left.hom
      (proj_hom_comp_hom_left_hom f) (proj_hom_comp_hom_left_hom g)

@[simp]
theorem monodromyFunctor_obj (p : CoveringSpace X) :
    (monodromyFunctor X).obj p = p.isCoveringMap_proj.monodromyFunctor :=
  rfl

/-- At a base point, the natural transformation assigned by monodromy is the restriction of the
underlying map of total spaces to the corresponding fibre. -/
@[simp]
theorem monodromyFunctor_map_app {p q : CoveringSpace X} (f : p ⟶ q) (x : X) :
    ((monodromyFunctor X).map f).app (FundamentalGroupoid.mk x) =
      ↾(IsCoveringMap.fiberMap f.hom.left.hom (proj_hom_comp_hom_left_hom f) x) := by
  exact IsCoveringMap.monodromyNatTrans_app p.isCoveringMap_proj q.isCoveringMap_proj
    f.hom.left.hom (proj_hom_comp_hom_left_hom f) x

/-- The monodromy functor is faithful: a map of covering spaces is determined by its restrictions
to all fibres. -/
instance monodromyFunctor_faithful (X : TopCat.{u}) : (monodromyFunctor X).Faithful where
  map_injective {p q} f g h := by
    apply ObjectProperty.hom_ext
    ext e
    have happ := NatTrans.congr_app h (FundamentalGroupoid.mk (p.proj e))
    rw [monodromyFunctor_map_app, monodromyFunctor_map_app] at happ
    let e' : p.proj ⁻¹' {p.proj e} := ⟨e, rfl⟩
    have happ := ConcreteCategory.congr_hom happ e'
    calc
      f.hom.left e =
          (IsCoveringMap.fiberMap f.hom.left.hom (proj_hom_comp_hom_left_hom f) (p.proj e) e' :
            (q : TopCat)) :=
        (IsCoveringMap.fiberMap_apply_coe f.hom.left.hom (proj_hom_comp_hom_left_hom f)
          (p.proj e) e').symm
      _ = IsCoveringMap.fiberMap g.hom.left.hom (proj_hom_comp_hom_left_hom g) (p.proj e) e' := by
        exact Subtype.ext_iff.mp happ
      _ = g.hom.left e :=
        IsCoveringMap.fiberMap_apply_coe g.hom.left.hom (proj_hom_comp_hom_left_hom g)
          (p.proj e) e'

end TauCeti.CoveringSpace
