/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.Basic
public import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# Representations of the generalized Kronecker quiver

A representation of the generalized Kronecker quiver is a pair of vector spaces together with one
linear map between them for each arrow: no two arrows compose, so the only paths are the identities
and the arrows themselves. This file builds such a representation from that datum, as
`TauCeti.kroneckerRep`, computes its two vertex spaces and the action of each arrow, and identifies
the morphisms between two such representations with the pairs of linear maps making a commuting
square along every arrow. The same identification for representations that are *not* presented by
`TauCeti.kroneckerRep` is `TauCeti.kroneckerHom`, with its isomorphism version
`TauCeti.kroneckerIso`.

The representation type of the quiver -- infinite as soon as there are two arrows -- is
`TauCeti.RepresentationTheory.Quiver.Kronecker.FiniteRepType`, which builds its Jordan blocks with
the definition below.

## Main definitions

* `TauCeti.kroneckerRep`: the representation of the generalized Kronecker quiver with prescribed
  vertex spaces and a prescribed linear map along each arrow.
* `TauCeti.kroneckerRepHom`: the morphism between two such representations attached to a pair of
  linear maps making a commuting square along every arrow.
* `TauCeti.kroneckerHom` and `TauCeti.kroneckerIso`: the same, for two arbitrary representations of
  the generalized Kronecker quiver rather than two presented by `TauCeti.kroneckerRep`, built from
  a linear map -- an isomorphism, for `TauCeti.kroneckerIso` -- at each vertex intertwining the
  action of every arrow.

## Main results

* `TauCeti.kroneckerRep_map_arrowPath`: the arrow indexed by `a` acts by the prescribed map.
* `TauCeti.kroneckerRep_hom_ext`: a morphism of representations of the generalized Kronecker quiver
  is determined by its two components.
* `TauCeti.kroneckerRepHom_eta`: conversely, every morphism between two representations built by
  `TauCeti.kroneckerRep` is the one attached to its two components. Together with
  `TauCeti.kroneckerRep_hom_ext` this is the promised identification, mirroring the pair
  `TauCeti.oneLoopRepHom_oneLoopRepScalar` / `TauCeti.oneLoopRep_hom_ext` of the loop quiver.
* `TauCeti.kroneckerHom_eta`: the same for two arbitrary representations, every morphism between
  them being `TauCeti.kroneckerHom` of its two components.

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

section Rep

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

end Rep

/-- **A morphism of representations of the generalized Kronecker quiver is determined by its two
components.** The quiver has two vertices, so a natural transformation is a pair of linear maps. -/
@[ext]
theorem kroneckerRep_hom_ext {ρ σ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)} {e e' : ρ ⟶ σ}
    (hsrc : e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) =
      e'.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
    (htgt : e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) =
      e'.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))) : e = e' := by
  refine NatTrans.ext (funext fun w ↦ ?_)
  cases w
  · exact hsrc
  · exact htgt

section Hom

variable {M N M' N' : ModuleCat.{t} k} {f : A → (M ⟶ N)} {f' : A → (M' ⟶ N')}

/-- **The morphism of representations of the generalized Kronecker quiver attached to a commuting
square along every arrow**: a linear map at each of the two vertices, intertwining the two actions
of each arrow. Together with `TauCeti.kroneckerRep_hom_ext` and `TauCeti.kroneckerRepHom_eta` this
identifies the morphisms `kroneckerRep k M N f ⟶ kroneckerRep k M' N' f'` with such pairs. -/
def kroneckerRepHom (g : M ⟶ M') (h : N ⟶ N') (w : ∀ a, f a ≫ h = g ≫ f' a) :
    kroneckerRep k M N f ⟶ kroneckerRep k M' N' f' :=
  Paths.liftNatTrans
    (fun v ↦ match v with
      | Quiver.Kronecker.src => g
      | Quiver.Kronecker.tgt => h)
    fun {a b} e ↦ match a, b, e with
      | .src, .tgt, e => by
          have hl : (kroneckerRep k M N f).map (Quiver.Hom.toPath e) = f e :=
            Paths.lift_toPath _ e
          have hr : (kroneckerRep k M' N' f').map (Quiver.Hom.toPath e) = f' e :=
            Paths.lift_toPath _ e
          rw [hl, hr]
          exact w e
      | .src, .src, e => isEmptyElim e
      | .tgt, .src, e => isEmptyElim e
      | .tgt, .tgt, e => isEmptyElim e

@[simp]
theorem kroneckerRepHom_app_src (g : M ⟶ M') (h : N ⟶ N') (w : ∀ a, f a ≫ h = g ≫ f' a) :
    (kroneckerRepHom g h w).app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) = g :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `kroneckerRepHom` to be `@[expose]`.
  (rfl)

@[simp]
theorem kroneckerRepHom_app_tgt (g : M ⟶ M') (h : N ⟶ N') (w : ∀ a, f a ≫ h = g ≫ f' a) :
    (kroneckerRepHom g h w).app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) = h := (rfl)

/-- **The two components of a morphism make a commuting square along every arrow**, by naturality
along the path of that arrow. -/
theorem kroneckerRep_hom_naturality (e : kroneckerRep k M N f ⟶ kroneckerRep k M' N' f') (a : A) :
    f a ≫ e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) =
      e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) ≫ f' a := by
  have hnat := e.naturality (Quiver.Kronecker.arrowPath a)
  rwa [kroneckerRep_map_arrowPath, kroneckerRep_map_arrowPath] at hnat

/-- **Every morphism between representations of the generalized Kronecker quiver is the one
attached to its two components.** This is the converse of `TauCeti.kroneckerRep_hom_ext`: the two
together identify such morphisms with the commuting squares. -/
theorem kroneckerRepHom_eta (e : kroneckerRep k M N f ⟶ kroneckerRep k M' N' f') :
    kroneckerRepHom (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
      (e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))
      (kroneckerRep_hom_naturality e) = e :=
  kroneckerRep_hom_ext (kroneckerRepHom_app_src _ _ _) (kroneckerRepHom_app_tgt _ _ _)

end Hom

section HomOfComponents

variable {ρ σ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)}
  (p : ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) ⟶
    σ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
  (q : ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) ⟶
    σ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))

/-- **The morphism of representations of the generalized Kronecker quiver attached to a linear map
at each vertex intertwining the action of every arrow**, the form of `TauCeti.kroneckerRepHom` for
representations that are not presented by `TauCeti.kroneckerRep`. -/
def kroneckerHom (w : ∀ a, ρ.map (Quiver.Kronecker.arrowPath a) ≫ q
    = p ≫ σ.map (Quiver.Kronecker.arrowPath a)) : ρ ⟶ σ :=
  Paths.liftNatTrans
    (fun v ↦ match v with
      | Quiver.Kronecker.src => p
      | Quiver.Kronecker.tgt => q)
    fun {a b} e ↦ match a, b, e with
      | .src, .tgt, e => by
          have hw := w e
          rwa [← Quiver.Kronecker.toPath_arrow, Quiver.Kronecker.arrow_def] at hw
      | .src, .src, e => isEmptyElim e
      | .tgt, .src, e => isEmptyElim e
      | .tgt, .tgt, e => isEmptyElim e

/-- At the source, `TauCeti.kroneckerHom` is the prescribed linear map. -/
@[simp]
theorem kroneckerHom_app_src (w : ∀ a, ρ.map (Quiver.Kronecker.arrowPath a) ≫ q
    = p ≫ σ.map (Quiver.Kronecker.arrowPath a)) :
    (kroneckerHom p q w).app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) = p :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `kroneckerHom` to be `@[expose]`.
  (rfl)

/-- At the target, `TauCeti.kroneckerHom` is the prescribed linear map. -/
@[simp]
theorem kroneckerHom_app_tgt (w : ∀ a, ρ.map (Quiver.Kronecker.arrowPath a) ≫ q
    = p ≫ σ.map (Quiver.Kronecker.arrowPath a)) :
    (kroneckerHom p q w).app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) = q := (rfl)

/-- **Every morphism of representations of the generalized Kronecker quiver is the one attached to
its two components**, the form of `TauCeti.kroneckerRepHom_eta` for representations that are not
presented by `TauCeti.kroneckerRep`: the commuting square along an arrow is naturality along the
path of that arrow. -/
theorem kroneckerHom_eta (e : ρ ⟶ σ) :
    kroneckerHom (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
      (e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))
      (fun a ↦ e.naturality (Quiver.Kronecker.arrowPath a)) = e :=
  kroneckerRep_hom_ext (kroneckerHom_app_src _ _ _) (kroneckerHom_app_tgt _ _ _)

end HomOfComponents

section IsoOfComponents

variable {ρ σ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)}
  (g : ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))
    ≅ σ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
  (h : ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))
    ≅ σ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))

/-- **Two representations of the generalized Kronecker quiver with isomorphic vertex spaces
intertwining every arrow are isomorphic**, the isomorphism version of `TauCeti.kroneckerHom`. -/
def kroneckerIso (w : ∀ a, ρ.map (Quiver.Kronecker.arrowPath a) ≫ h.hom
    = g.hom ≫ σ.map (Quiver.Kronecker.arrowPath a)) : ρ ≅ σ :=
  Paths.liftNatIso
    (fun v ↦ match v with
      | Quiver.Kronecker.src => g
      | Quiver.Kronecker.tgt => h)
    fun {a b} e ↦ match a, b, e with
      | .src, .tgt, e => by
          have hw := w e
          rwa [← Quiver.Kronecker.toPath_arrow, Quiver.Kronecker.arrow_def] at hw
      | .src, .src, e => isEmptyElim e
      | .tgt, .src, e => isEmptyElim e
      | .tgt, .tgt, e => isEmptyElim e

/-- At the source, `TauCeti.kroneckerIso` is the prescribed isomorphism. -/
@[simp]
theorem kroneckerIso_hom_app_src (w : ∀ a, ρ.map (Quiver.Kronecker.arrowPath a) ≫ h.hom
    = g.hom ≫ σ.map (Quiver.Kronecker.arrowPath a)) :
    (kroneckerIso g h w).hom.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) = g.hom :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `kroneckerIso` to be `@[expose]`.
  (rfl)

/-- At the target, `TauCeti.kroneckerIso` is the prescribed isomorphism. -/
@[simp]
theorem kroneckerIso_hom_app_tgt (w : ∀ a, ρ.map (Quiver.Kronecker.arrowPath a) ≫ h.hom
    = g.hom ≫ σ.map (Quiver.Kronecker.arrowPath a)) :
    (kroneckerIso g h w).hom.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) = h.hom :=
  (rfl)

/-- At the source, the inverse of `TauCeti.kroneckerIso` is the prescribed inverse. -/
@[simp]
theorem kroneckerIso_inv_app_src (w : ∀ a, ρ.map (Quiver.Kronecker.arrowPath a) ≫ h.hom
    = g.hom ≫ σ.map (Quiver.Kronecker.arrowPath a)) :
    (kroneckerIso g h w).inv.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) = g.inv :=
  (rfl)

/-- At the target, the inverse of `TauCeti.kroneckerIso` is the prescribed inverse. -/
@[simp]
theorem kroneckerIso_inv_app_tgt (w : ∀ a, ρ.map (Quiver.Kronecker.arrowPath a) ≫ h.hom
    = g.hom ≫ σ.map (Quiver.Kronecker.arrowPath a)) :
    (kroneckerIso g h w).inv.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) = h.inv :=
  (rfl)

end IsoOfComponents

end TauCeti
