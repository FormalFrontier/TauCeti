/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.Basic
public import TauCeti.RepresentationTheory.Quiver.Reflection.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option

/-!
# The `D₄` quiver

The `D₄` quiver has a central vertex and three outer vertices, with one arrow running from each
outer vertex into the centre. Its underlying graph is the simply-laced Dynkin diagram `D₄`, the
smallest one that is not of type `A`, which makes it the standard test of the positive-root count
beyond type `A`.

This file constructs the quiver and its combinatorics: the centre is a sink and the outer vertices
are sources, so the quiver is acyclic and its only nontrivial paths are the three arrows. The
dimension of its path algebra is computed in `TauCeti.RepresentationTheory.Quiver.D4.PathAlgebra`,
and its Euler and Tits forms, with the twelve positive roots they cut out, in
`TauCeti.RepresentationTheory.Quiver.D4.EulerForm`.

## Main definitions

* `TauCeti.Quiver.D4`: the vertex type, with constructors `center` and `outer`, and a `Quiver`
  instance whose only arrows are the three `outer i ⟶ center`.
* `TauCeti.Quiver.D4.vertexEquiv`: the vertices as `Option (Fin 3)`, the centre being `none`.
* `TauCeti.Quiver.D4.arrow` and `TauCeti.Quiver.D4.arrowPath`: the arrow attached to an outer
  vertex, and the length-one path it traces.

## Main results

* `TauCeti.Quiver.D4.isSink_center` and `TauCeti.Quiver.D4.isSource_outer`: the centre is a sink
  and each outer vertex is a source.
* `TauCeti.Quiver.D4.isAcyclic`: the quiver is acyclic, since all of its arrows run the same way.
* `TauCeti.Quiver.D4.instUniquePathOuterCenter`: the only path from an outer vertex to the centre
  is the arrow there, so the quiver has seven paths in all.

## References

This file supplies the vertex and arrow data of the “`D₄` quiver” worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, alongside the generalized
Kronecker quiver of `TauCeti.RepresentationTheory.Quiver.Kronecker.Basic`. See Derksen--Weyman,
*An Introduction to Quiver Representations*, and Assem--Simson--Skowroński, *Elements of the
Representation Theory of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

namespace Quiver

/-- The `D₄` quiver: a central vertex together with three outer vertices, with one arrow from each
outer vertex into the centre. Its underlying graph is the Dynkin diagram `D₄`. -/
inductive D4 : Type
  | /-- The central vertex, the head of every arrow. -/ center : D4
  | /-- The `i`-th outer vertex, the tail of the `i`-th arrow. -/ outer (i : Fin 3) : D4
  deriving DecidableEq

namespace D4

/-! ### The four vertices -/

/-- The vertices of the `D₄` quiver as `Option (Fin 3)`: the centre is `none`, and the `i`-th outer
vertex is `some i`. -/
def vertexEquiv : D4 ≃ Option (Fin 3) where
  toFun
    | .center => none
    | .outer i => some i
  invFun
    | none => center
    | some i => outer i
  left_inv v := by cases v <;> rfl
  right_inv o := by cases o <;> rfl

@[simp]
theorem vertexEquiv_center : vertexEquiv center = none :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `vertexEquiv` to be `@[expose]`.
  (rfl)

@[simp]
theorem vertexEquiv_outer (i : Fin 3) : vertexEquiv (outer i) = some i := (rfl)

@[simp]
theorem vertexEquiv_symm_none : vertexEquiv.symm none = center := (rfl)

@[simp]
theorem vertexEquiv_symm_some (i : Fin 3) : vertexEquiv.symm (some i) = outer i := (rfl)

instance : Fintype D4 := Fintype.ofEquiv _ vertexEquiv.symm

@[simp]
theorem card_eq_four : Fintype.card D4 = 4 := by
  rw [Fintype.card_congr vertexEquiv]
  simp

/-- A sum over the vertices of `D₄` splits into the value at the centre and a sum over the three
outer vertices. -/
@[simp]
theorem sum_univ {M : Type*} [AddCommMonoid M] (f : D4 → M) :
    ∑ v, f v = f center + ∑ i, f (outer i) := by
  rw [Fintype.sum_equiv vertexEquiv f (fun o => f (vertexEquiv.symm o)) (by simp),
    Fintype.sum_option]
  simp

/-- A function on the vertices vanishes exactly when all four of its values do. -/
theorem eq_zero_iff {M : Type*} [Zero M] {f : D4 → M} :
    f = 0 ↔ f center = 0 ∧ ∀ i, f (outer i) = 0 := by
  refine ⟨fun h => h ▸ ⟨rfl, fun _ => rfl⟩, fun h => funext fun v => ?_⟩
  cases v
  · exact h.1
  · exact h.2 _

/-! ### The three arrows -/

instance : _root_.Quiver.{1} D4 where
  Hom a b :=
    match a, b with
    | .outer _, .center => PUnit
    | _, _ => PEmpty

/-- The arrow running from the `i`-th outer vertex into the centre. -/
def arrow (i : Fin 3) : outer i ⟶ center := PUnit.unit

instance instUniqueHomOuterCenter (i : Fin 3) : Unique (outer i ⟶ center) :=
  inferInstanceAs (Unique PUnit)

instance : IsEmpty (center ⟶ center) := inferInstanceAs (IsEmpty PEmpty)

instance (i : Fin 3) : IsEmpty (center ⟶ outer i) := inferInstanceAs (IsEmpty PEmpty)

instance (i j : Fin 3) : IsEmpty (outer i ⟶ outer j) := inferInstanceAs (IsEmpty PEmpty)

/-- No arrow leaves the centre. -/
theorem isEmpty_hom_from_center (b : D4) : IsEmpty (center ⟶ b) := by
  cases b <;> infer_instance

/-- No arrow ends at an outer vertex. -/
theorem isEmpty_hom_to_outer (a : D4) (i : Fin 3) : IsEmpty (a ⟶ outer i) := by
  cases a <;> infer_instance

/-- The centre is a sink: every arrow of `D₄` ends there. -/
theorem isSink_center : IsSink center :=
  (IsSink_def _).mpr isEmpty_hom_from_center

/-- Each outer vertex is a source: every arrow of `D₄` starts at one. -/
theorem isSource_outer (i : Fin 3) : IsSource (outer i) :=
  (IsSource_def _).mpr fun a => isEmpty_hom_to_outer a i

instance instFintypeHom : ∀ a b : D4, Fintype (a ⟶ b)
  | .center, .center => Fintype.ofIsEmpty
  | .center, .outer _ => Fintype.ofIsEmpty
  | .outer _, .center => inferInstanceAs (Fintype PUnit)
  | .outer _, .outer _ => Fintype.ofIsEmpty

/-! ### The paths -/

/-- The only closed path at the centre is the trivial one, the centre being a sink. -/
theorem path_center_center_eq_nil (p : Path center center) : p = Path.nil :=
  isSink_center.path_self_eq_nil p

/-- The only closed path at an outer vertex is the trivial one, an outer vertex being a source. -/
theorem path_outer_outer_eq_nil (i : Fin 3) (p : Path (outer i) (outer i)) : p = Path.nil :=
  (isSource_outer i).path_self_eq_nil p

/-- The `D₄` quiver is acyclic: all of its arrows run into the centre. -/
theorem isAcyclic : Quiver.IsAcyclic D4 :=
  isAcyclic_def.mpr fun a p => by
    cases a
    · exact path_center_center_eq_nil p
    · exact path_outer_outer_eq_nil _ p

instance : Unique (Path center center) where
  default := Path.nil
  uniq := path_center_center_eq_nil

instance instUniquePathOuterSelf (i : Fin 3) : Unique (Path (outer i) (outer i)) where
  default := Path.nil
  uniq := path_outer_outer_eq_nil i

instance (i : Fin 3) : IsEmpty (Path center (outer i)) :=
  ⟨fun p => by simpa using isSink_center.eq_of_path p⟩

/-- There is no path between two distinct outer vertices: a path out of an outer vertex reaches
the centre and stops there. -/
theorem isEmpty_path_outer_outer {i j : Fin 3} (h : i ≠ j) : IsEmpty (Path (outer i) (outer j)) :=
  ⟨fun p => h (by simpa using (isSource_outer j).eq_of_path p)⟩

/-- The length-one path traced by the arrow at an outer vertex. -/
def arrowPath (i : Fin 3) : Path (outer i) center := (arrow i).toPath

/-- The only path from an outer vertex to the centre is the arrow there: that arrow is the only
one leaving the vertex, and nothing can be appended to it because the centre is a sink. -/
instance instUniquePathOuterCenter (i : Fin 3) : Unique (Path (outer i) center) where
  default := arrowPath i
  uniq p := by
    cases p with
    | @cons b _ q e =>
        cases b with
        | center => exact (isEmpty_hom_from_center _).elim e
        | outer j =>
            obtain rfl : i = j := by simpa using (isSource_outer j).eq_of_path q
            rw [path_outer_outer_eq_nil _ q, Subsingleton.elim e (arrow i)]
            rfl

instance instFintypePath : ∀ a b : D4, Fintype (Path a b)
  | .center, .center => Unique.fintype
  | .center, .outer _ => Fintype.ofIsEmpty
  | .outer _, .center => Unique.fintype
  | .outer i, .outer j =>
      if h : i = j then by subst h; exact Unique.fintype
      else @Fintype.ofIsEmpty _ (isEmpty_path_outer_outer h)

/-- The only path between two outer vertices is the trivial one at a single vertex. The other
three path counts of `D₄` are read off by `simp` from the `Unique` and `IsEmpty` instances
above. -/
@[simp]
theorem card_path_outer_outer (i j : Fin 3) :
    Fintype.card (Path (outer i) (outer j)) = if i = j then 1 else 0 := by
  split
  · next h => subst h; exact Fintype.card_unique
  · next h => exact Fintype.card_eq_zero_iff.mpr (isEmpty_path_outer_outer h)

end D4

end Quiver

end TauCeti
