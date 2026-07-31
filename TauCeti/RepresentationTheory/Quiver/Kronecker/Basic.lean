/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.Basic
public import TauCeti.RepresentationTheory.Quiver.Reflection.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# The generalized Kronecker quiver

The generalized Kronecker quiver has two vertices, a source and a target, and one arrow from the
source to the target for each element of an arrow type `A`. Taking `A = Fin 2` gives the
*Kronecker quiver* `• ⇉ •`, the smallest connected acyclic quiver that is not of Dynkin type and
hence the boundary case of Gabriel's theorem; `A = Fin 1` gives the `A₂` quiver `• → •`. (Dropping
acyclicity there would be wrong: the one-loop quiver of
`TauCeti.RepresentationTheory.Quiver.PathAlgebra` is connected, smaller, and not of Dynkin type.)

This file constructs the quiver and classifies its paths: it is acyclic, and its only nontrivial
paths are the arrows themselves. The dimension of its path algebra is computed in
`TauCeti.RepresentationTheory.Quiver.Kronecker.PathAlgebra`, and its Euler and Tits forms in
`TauCeti.RepresentationTheory.Quiver.Kronecker.EulerForm`.

## Main definitions

* `TauCeti.Quiver.Kronecker A`: the vertex type, with constructors `src` and `tgt` and a `Quiver`
  instance whose only arrows are `src ⟶ tgt`, indexed by `A`.
* `TauCeti.Quiver.Kronecker.arrow`: the arrow attached to an element of the arrow type.
* `TauCeti.Quiver.Kronecker.vertexEquiv`: the two vertices as indices in `Fin 2`, the target first.
* `TauCeti.Quiver.Kronecker.pathEquivArrow`: the paths from `src` to `tgt` are the arrows.

## Main results

* `TauCeti.Quiver.Kronecker.isAcyclic`: the quiver is acyclic, since all of its arrows run the
  same way.
* `TauCeti.Quiver.Kronecker.card_path_src_tgt`: there are as many paths from the source to the
  target as there are arrows.

## References

This file supplies the “Kronecker quiver” worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, alongside the one-loop
quiver of `TauCeti.RepresentationTheory.Quiver.PathAlgebra`. See Derksen--Weyman, *An Introduction
to Quiver Representations*, and Assem--Simson--Skowroński, *Elements of the Representation Theory
of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe v w

namespace Quiver

/-- The generalized Kronecker quiver on an arrow type `A`: two vertices, a source `src` and a
target `tgt`, with one arrow `src ⟶ tgt` for each element of `A` and no other arrows. The classical
Kronecker quiver `• ⇉ •` is the case `A = Fin 2`, and the `A₂` quiver `• → •` is the case
`A = Fin 1`. -/
inductive Kronecker (A : Type v) : Type
  | /-- The source vertex, the tail of every arrow. -/ src : Kronecker A
  | /-- The target vertex, the head of every arrow. -/ tgt : Kronecker A

namespace Kronecker

variable {A : Type v}

instance : _root_.Quiver.{v} (Kronecker A) where
  Hom a b :=
    match a, b with
    | .src, .tgt => A
    | _, _ => PEmpty

/-! ### The two vertices -/

/-- The source and the target are distinct vertices. -/
theorem src_ne_tgt : (src : Kronecker A) ≠ tgt := by simp

-- The `deriving DecidableEq` handler would ask for `[DecidableEq A]`, which the two constructors
-- plainly do not need.
instance : DecidableEq (Kronecker A)
  | .src, .src => isTrue rfl
  | .src, .tgt => isFalse src_ne_tgt
  | .tgt, .src => isFalse src_ne_tgt.symm
  | .tgt, .tgt => isTrue rfl

instance : Fintype (Kronecker A) where
  elems := {(src : Kronecker A), tgt}
  complete x := by cases x <;> simp

/-- The vertex type is the pair `{src, tgt}`. -/
theorem univ_eq : (Finset.univ : Finset (Kronecker A)) = {(src : Kronecker A), tgt} :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would expose the body of the `Fintype` instance.
  (rfl)

@[simp]
theorem card_eq_two : Fintype.card (Kronecker A) = 2 := by
  rw [Fintype.card, univ_eq, Finset.card_pair src_ne_tgt]

/-- A sum over the two vertices is the sum of its two values. -/
@[simp]
theorem sum_univ {M : Type w} [AddCommMonoid M] (f : Kronecker A → M) :
    ∑ v, f v = f src + f tgt := by
  rw [univ_eq, Finset.sum_pair src_ne_tgt]

/-- A function on the vertices vanishes exactly when both of its values do. -/
theorem eq_zero_iff {M : Type w} [Zero M] {f : Kronecker A → M} :
    f = 0 ↔ f src = 0 ∧ f tgt = 0 := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => funext fun v => ?_⟩
  cases v
  · exact h.1
  · exact h.2

/-- The two vertices as indices in `Fin 2`, **the target first**: `tgt` is `0` and `src` is `1`.

The order is the one that makes the path algebra upper triangular rather than lower triangular. In
`TauCeti.RepresentationTheory.Quiver.Kronecker.UpperTriangular` a path is sent to the matrix unit
in the row of its target and the column of its source, because an arrow acts on a left module from
its source to its target; so the arrows, all of which run from `src` to `tgt`, occupy entries above
the diagonal exactly when `tgt` comes first. -/
def vertexEquiv : Kronecker A ≃ Fin 2 where
  toFun
    | .src => 1
    | .tgt => 0
  invFun i := if i = 0 then tgt else src
  left_inv v := by cases v <;> rfl
  right_inv
    | 0 => rfl
    | 1 => rfl

@[simp]
theorem vertexEquiv_src : vertexEquiv (src : Kronecker A) = 1 :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `vertexEquiv` to be `@[expose]`.
  (rfl)

@[simp]
theorem vertexEquiv_tgt : vertexEquiv (tgt : Kronecker A) = 0 := (rfl)

@[simp]
theorem vertexEquiv_symm_zero : vertexEquiv.symm (0 : Fin 2) = (tgt : Kronecker A) := (rfl)

@[simp]
theorem vertexEquiv_symm_one : vertexEquiv.symm (1 : Fin 2) = (src : Kronecker A) := (rfl)

/-! ### The arrows -/

/-- The arrow of the generalized Kronecker quiver indexed by an element of the arrow type. The
arrows from the source to the target are exactly the elements of the arrow type, and the
identification is definitional. -/
def arrow (a : A) : (src : Kronecker A) ⟶ tgt := a

/-- The arrows from the source to the target are the elements of the arrow type, and `arrow` is
that identification. This is not `@[simp]`: rewriting `arrow a` to `a` would erase the named
constructor from every goal, leaving `toPath_arrow` and the `pathEquivArrow` lemmas below unable to
fire. -/
theorem arrow_def (a : A) : arrow a = (a : (src : Kronecker A) ⟶ tgt) :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `arrow` to be `@[expose]`.
  (rfl)

instance : IsEmpty ((src : Kronecker A) ⟶ src) := inferInstanceAs (IsEmpty PEmpty)

instance : IsEmpty ((tgt : Kronecker A) ⟶ src) := inferInstanceAs (IsEmpty PEmpty)

instance : IsEmpty ((tgt : Kronecker A) ⟶ tgt) := inferInstanceAs (IsEmpty PEmpty)

/-- No arrow ends at the source vertex. -/
theorem isEmpty_hom_to_src (a : Kronecker A) : IsEmpty (a ⟶ (src : Kronecker A)) := by
  cases a <;> infer_instance

/-- No arrow starts at the target vertex. -/
theorem isEmpty_hom_from_tgt (b : Kronecker A) : IsEmpty ((tgt : Kronecker A) ⟶ b) := by
  cases b <;> infer_instance

/-- The source vertex is a source. -/
theorem isSource_src : IsSource (src : Kronecker A) :=
  (IsSource_def _).mpr isEmpty_hom_to_src

/-- The target vertex is a sink. -/
theorem isSink_tgt : IsSink (tgt : Kronecker A) :=
  (IsSink_def _).mpr isEmpty_hom_from_tgt

instance instFiniteHom [Finite A] : ∀ a b : Kronecker A, Finite (a ⟶ b)
  | .src, .src => inferInstanceAs (Finite PEmpty)
  | .src, .tgt => inferInstanceAs (Finite A)
  | .tgt, .src => inferInstanceAs (Finite PEmpty)
  | .tgt, .tgt => inferInstanceAs (Finite PEmpty)

instance instFintypeHom [Fintype A] : ∀ a b : Kronecker A, Fintype (a ⟶ b)
  | .src, .src => Fintype.ofIsEmpty
  | .src, .tgt => inferInstanceAs (Fintype A)
  | .tgt, .src => Fintype.ofIsEmpty
  | .tgt, .tgt => Fintype.ofIsEmpty

/-- There are as many arrows from the source to the target as there are elements of the arrow
type. -/
@[simp]
theorem card_hom_src_tgt [Fintype A] :
    Fintype.card ((src : Kronecker A) ⟶ tgt) = Fintype.card A :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would expose the bodies of the `Quiver` and `Fintype` instances.
  (rfl)

/-! ### The paths -/

/-- The only closed path at the source vertex is the trivial one. -/
theorem path_src_src_eq_nil (p : Path (src : Kronecker A) src) : p = Path.nil := by
  cases p with
  | nil => rfl
  | cons _ e => exact (isEmpty_hom_to_src _).elim e

/-- The only closed path at the target vertex is the trivial one. -/
theorem path_tgt_tgt_eq_nil (p : Path (tgt : Kronecker A) tgt) : p = Path.nil := by
  cases p with
  | cons q e =>
      have h := isSink_tgt.eq_of_path q
      subst h
      exact (isEmpty_hom_from_tgt _).elim e
  | nil => rfl

/-- The generalized Kronecker quiver is acyclic: all of its arrows run the same way. -/
theorem isAcyclic : Quiver.IsAcyclic (Kronecker A) :=
  isAcyclic_def.mpr fun a p => by
    cases a
    · exact path_src_src_eq_nil p
    · exact path_tgt_tgt_eq_nil p

instance : Unique (Path (src : Kronecker A) src) where
  default := Path.nil
  uniq := path_src_src_eq_nil

instance : Unique (Path (tgt : Kronecker A) tgt) where
  default := Path.nil
  uniq := path_tgt_tgt_eq_nil

instance : IsEmpty (Path (tgt : Kronecker A) src) :=
  ⟨fun p => src_ne_tgt (isSink_tgt.eq_of_path p).symm⟩

/-- The length-one path traced by an arrow of the generalized Kronecker quiver. -/
def arrowPath (a : A) : Path (src : Kronecker A) tgt := (arrow a).toPath

/-- The length-one path of an arrow is the path that arrow traces. -/
@[simp]
theorem toPath_arrow (a : A) : (arrow a).toPath = arrowPath a := (rfl)

/-- Distinct arrows trace distinct paths. -/
theorem arrowPath_injective : Function.Injective (arrowPath (A := A)) := by
  intro a b h
  simpa [arrowPath, arrow, Hom.toPath] using h

/-- Every path from the source to the target is a single arrow. -/
theorem arrowPath_surjective : Function.Surjective (arrowPath (A := A)) := by
  intro p
  cases p with
  | @cons b _ q e =>
      cases b with
      | src => exact ⟨e, by rw [path_src_src_eq_nil q]; rfl⟩
      | tgt => exact (isEmpty_hom_from_tgt _).elim e

/-- The paths from the source to the target of the generalized Kronecker quiver are its arrows. -/
noncomputable def pathEquivArrow : Path (src : Kronecker A) tgt ≃ A :=
  (Equiv.ofBijective arrowPath ⟨arrowPath_injective, arrowPath_surjective⟩).symm

/-- The inverse of the classification sends an arrow to the path it traces; the two are the same
construction, so this holds definitionally. -/
@[simp]
theorem pathEquivArrow_symm_apply (a : A) : pathEquivArrow.symm a = arrowPath a :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `pathEquivArrow` to be `@[expose]`; the three lemmas here are the whole interface.
  (rfl)

/-- The classification sends the path traced by an arrow back to that arrow. -/
@[simp]
theorem pathEquivArrow_arrowPath (a : A) : pathEquivArrow (arrowPath a) = a := by
  rw [← pathEquivArrow_symm_apply, Equiv.apply_symm_apply]

/-- Every path from the source to the target is traced by the arrow it classifies. -/
@[simp]
theorem arrowPath_pathEquivArrow (p : Path (src : Kronecker A) tgt) :
    arrowPath (pathEquivArrow p) = p := by
  rw [← pathEquivArrow_symm_apply, Equiv.symm_apply_apply]

noncomputable instance instFintypePath [Fintype A] : ∀ a b : Kronecker A, Fintype (Path a b)
  | .src, .src => Unique.fintype
  | .src, .tgt => Fintype.ofEquiv A pathEquivArrow.symm
  | .tgt, .src => Fintype.ofIsEmpty
  | .tgt, .tgt => Unique.fintype

/-- There are as many paths from the source to the target as there are arrows: by
`pathEquivArrow`, each such path is a single arrow. -/
@[simp]
theorem card_path_src_tgt [Fintype A] :
    Fintype.card (Path (src : Kronecker A) tgt) = Fintype.card A :=
  Fintype.card_congr pathEquivArrow

end Kronecker

end Quiver

end TauCeti
