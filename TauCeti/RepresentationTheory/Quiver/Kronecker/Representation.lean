/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.Basic

/-!
# Representations of the generalized Kronecker quiver

A representation of the generalized Kronecker quiver is a pair of vector spaces together with one
linear map between them for each arrow: no two arrows compose, so the only paths are the identities
and the arrows themselves. This file builds such a representation from that datum, as
`TauCeti.kroneckerRep`, computes its two vertex spaces and the action of each arrow, and records
that a morphism between two representations of the quiver is its two components.

The representation type of the quiver -- infinite as soon as there are two arrows -- is
`TauCeti.RepresentationTheory.Quiver.Kronecker.FiniteRepType`, which builds its Jordan blocks with
the definition below.

## Main definitions

* `TauCeti.kroneckerRep`: the representation of the generalized Kronecker quiver with prescribed
  vertex spaces and a prescribed linear map along each arrow.

## Main results

* `TauCeti.kroneckerRep_map_arrowPath`: the arrow indexed by `a` acts by the prescribed map.
* `TauCeti.kronecker_hom_ext`: a morphism of representations of the generalized Kronecker quiver is
  determined by its two components.

## Implementation notes

`TauCeti.kroneckerRep` carries `@[expose]`, for the reason the loop-quiver file
`TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType` records: a functor built by
`CategoryTheory.Paths.lift` reveals its value on objects only through its definition. The
obstruction is at the level of *statements*, not of proofs, so no characteristic lemma can remove
it: without `@[expose]`, already `kroneckerRep_map_arrowPath` fails to elaborate, `f a : M ⟶ N` not
being accepted where `(kroneckerRep k M N f).obj Quiver.Kronecker.src ⟶
(kroneckerRep k M N f).obj Quiver.Kronecker.tgt` is expected.

## References

This is the representation-level part of the “Kronecker quiver” worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Derksen--Weyman, *An
Introduction to Quiver Representations*, and Assem--Simson--Skowroński, *Elements of the
Representation Theory of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v t

variable {k : Type u} [Field k] {A : Type v}

variable (k) in
/-- **A representation of the generalized Kronecker quiver**: a vector space `M` at the source, a
vector space `N` at the target, and a linear map `f a : M ⟶ N` along the arrow indexed by `a`. No
two arrows compose, so the only paths are the identities and the arrows themselves, and this is the
whole datum. -/
@[expose]
def kroneckerRep (M N : ModuleCat.{t} k) (f : A → (M ⟶ N)) :
    QuiverRep k (Quiver.Kronecker A) :=
  Paths.lift
    { obj := fun a ↦ match a with
        | .src => M
        | .tgt => N
      map := fun {a b} e ↦ match a, b, e with
        | .src, .tgt, e => f e
        | .src, .src, e => isEmptyElim e
        | .tgt, .src, e => isEmptyElim e
        | .tgt, .tgt, e => isEmptyElim e }

variable (M N : ModuleCat.{t} k) (f : A → (M ⟶ N))

@[simp]
theorem kroneckerRep_obj_src :
    (kroneckerRep k M N f).obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) = M :=
  rfl

@[simp]
theorem kroneckerRep_obj_tgt :
    (kroneckerRep k M N f).obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) = N :=
  rfl

/-- The arrow indexed by `a` acts on `TauCeti.kroneckerRep` by `f a`. -/
@[simp]
theorem kroneckerRep_map_arrowPath (a : A) :
    (kroneckerRep k M N f).map (Quiver.Kronecker.arrowPath a) = f a := by
  rw [← Quiver.Kronecker.toPath_arrow]
  exact (Paths.lift_toPath _ (Quiver.Kronecker.arrow a)).trans
    (congrArg f (Quiver.Kronecker.arrow_def a))

/-- **A morphism of representations of the generalized Kronecker quiver is determined by its two
components.** The quiver has two vertices, so a natural transformation is a pair of linear maps. -/
theorem kronecker_hom_ext {ρ σ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)} {e e' : ρ ⟶ σ}
    (hsrc : e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) =
      e'.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
    (htgt : e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) =
      e'.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))) : e = e' := by
  refine NatTrans.ext (funext fun w ↦ ?_)
  cases w
  · exact hsrc
  · exact htgt

end TauCeti
