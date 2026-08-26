/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Rank
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.RepresentationTheory.Quiver.Kronecker.Representation
public import TauCeti.RepresentationTheory.Quiver.Representation.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Representation.Simple

/-!
# The three indecomposable representations of the `A₂` quiver

The `A₂` quiver `• → •` is the generalized Kronecker quiver on a one-element arrow type. This file
classifies its finite-dimensional indecomposable representations: there are exactly three, the two
vertex simples `S₁ = (k → 0)` and `S₂ = (0 → k)` and the vertex projective
`P₁ = kQ·e₁ = (k →^{id} k)`, of dimension vectors `(1,0)`, `(0,1)` and `(1,1)` -- the three
positive roots of `A₂`. In particular the `A₂` quiver has **finite representation type**, the
positive half of Gabriel's dichotomy at the smallest Dynkin diagram, mirroring
`TauCeti.not_isFiniteRepType_kronecker` on the other side of the boundary.

The proof needs no reflection functor and no Krull-Schmidt theory. Indecomposability of an object
in a category where idempotents split is exactly the triviality of its idempotent endomorphisms
(`TauCeti.indecomposable_iff_idempotent_eq_zero_or_id`), and an endomorphism of a representation of
the generalized Kronecker quiver is a pair of endomorphisms of the two vertex spaces intertwining
the action of every arrow. Feeding three linear projections into that dichotomy settles the
classification:

* the projection onto the kernel of the arrow, paired with `0` at the target, forces the arrow to
  be **injective** once the target is nonzero;
* the projection onto a complement of the range of the arrow, paired with `0` at the source, forces
  it to be **surjective** once the source is nonzero;
* with the arrow then invertible, conjugating an arbitrary idempotent of the source through it
  produces an intertwining pair, so the source -- and hence the target -- has no proper nonzero
  subspace and is a **line**.

Finite-dimensionality is therefore a conclusion, not a hypothesis: an indecomposable
representation of the `A₂` quiver is automatically finite-dimensional.

## Main definitions

* `TauCeti.kroneckerRepSelfIso`: every representation of the generalized Kronecker quiver is the
  one that `TauCeti.kroneckerRep` builds from its own vertex spaces and arrow actions.
* `TauCeti.kroneckerRepIso` and `TauCeti.kroneckerIso`: an isomorphism of representations of the
  generalized Kronecker quiver from a commuting square of isomorphisms, for representations
  presented by `TauCeti.kroneckerRep` and for arbitrary ones.
* `TauCeti.kroneckerEnd`: the endomorphism of an arbitrary representation of the generalized
  Kronecker quiver attached to an endomorphism of each vertex space intertwining every arrow.

## Main results

* `TauCeti.eq_zero_or_eq_id_of_indecomposable_kronecker`: an indecomposable representation of the
  generalized Kronecker quiver admits no nontrivial intertwining pair of idempotents.
* `TauCeti.ker_map_arrowPath_eq_bot`, `TauCeti.range_map_arrowPath_eq_top` and
  `TauCeti.isIso_map_arrowPath`: over the `A₂` quiver the arrow of an indecomposable
  representation with two nonzero vertex spaces is an isomorphism.
* `TauCeti.finrank_src_eq_one_of_isZero_tgt`, `TauCeti.finrank_tgt_eq_one_of_isZero_src`,
  `TauCeti.finrank_src_eq_one_of_not_isZero` and `TauCeti.finrank_tgt_eq_one_of_not_isZero`: the
  nonzero vertex spaces of an indecomposable representation are lines.
* `TauCeti.nonempty_iso_of_indecomposable_kronecker`: **every indecomposable representation of the
  `A₂` quiver is `S₁`, `S₂` or `P₁`.**
* `TauCeti.isFiniteRepType_kronecker`: **the `A₂` quiver has finite representation type.**

## Implementation notes

`TauCeti.kroneckerEnd` builds a natural transformation of an arbitrary representation directly from
its two components, rather than transporting `TauCeti.kroneckerRepHom` along
`TauCeti.kroneckerRepSelfIso`: the latter is the same morphism, but reading off its components asks
`simp` to rewrite `NatTrans.comp_app` at a vertex of `CategoryTheory.Paths`, where the motive is
not type-correct at the transparency `simp` uses. `TauCeti.kroneckerRepHom` remains the constructor
for morphisms *between* two representations, which `TauCeti.kroneckerEnd` does not supply.

The classification is stated for an arrow type in `Type`, not in an arbitrary universe. That is
what puts the three comparison objects in the same universe as the representation: the vertex
simple `TauCeti.simpleRep` puts the base field itself at its vertex, while `TauCeti.indecProjRep`
puts the paths of the quiver into a `Finsupp`, and only for a `Type`-valued arrow type do the two
land in one universe. The supporting layers -- the reconstruction isomorphism, the endomorphism
constructor, and the idempotent dichotomy -- carry an arbitrary arrow universe, and the
`[Unique A]` hypothesis is spelled only where a single arrow is genuinely used.

## References

This supplies the representation-level half of the "`A₂` quiver" worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose path-algebra half is
`TauCeti.RepresentationTheory.Quiver.Kronecker.UpperTriangular`, together with the finite
representation type asked for in its Layer 5. See Assem--Simson--Skowroński, *Elements of the
Representation Theory of Associative Algebras I*, Ch. II and VII, and Schiffler, *Quiver
Representations*, Ch. 2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v t

variable {k : Type u} [Field k]

section GeneralizedKronecker

variable {A : Type v}

/-- Every representation of the generalized Kronecker quiver is the one built from its own data. -/
def kroneckerRepSelfIso (ρ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)) :
    ρ ≅ kroneckerRep k (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
      (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))
      (fun a ↦ ρ.map (Quiver.Kronecker.arrowPath a)) :=
  NatIso.ofComponents
    (fun v ↦ match v with
      | Quiver.Kronecker.src => Iso.refl _
      | Quiver.Kronecker.tgt => Iso.refl _)
    (by
      rintro (_ | _) (_ | _) p
      · rw [Quiver.Kronecker.path_src_src_eq_nil p]
        simp
      · obtain ⟨a, rfl⟩ := Quiver.Kronecker.arrowPath_surjective p
        simp
      · exact isEmptyElim
          (α := Quiver.Path (Quiver.Kronecker.tgt : Quiver.Kronecker A) Quiver.Kronecker.src) p
      · rw [Quiver.Kronecker.path_tgt_tgt_eq_nil p]
        simp)

/-- The reconstruction isomorphism is the identity at the source. -/
@[simp]
theorem kroneckerRepSelfIso_hom_app_src (ρ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)) :
    (kroneckerRepSelfIso ρ).hom.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))
      = 𝟙 _ := (rfl)

/-- The reconstruction isomorphism is the identity at the target. -/
@[simp]
theorem kroneckerRepSelfIso_hom_app_tgt (ρ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)) :
    (kroneckerRepSelfIso ρ).hom.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))
      = 𝟙 _ := (rfl)

/-- The inverse of the reconstruction isomorphism is the identity at the source. -/
@[simp]
theorem kroneckerRepSelfIso_inv_app_src (ρ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)) :
    (kroneckerRepSelfIso ρ).inv.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))
      = 𝟙 _ := (rfl)

/-- The inverse of the reconstruction isomorphism is the identity at the target. -/
@[simp]
theorem kroneckerRepSelfIso_inv_app_tgt (ρ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)) :
    (kroneckerRepSelfIso ρ).inv.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))
      = 𝟙 _ := (rfl)

section Iso

variable {M N M' N' : ModuleCat.{t} k} {f : A → (M ⟶ N)} {f' : A → (M' ⟶ N')}

/-- An isomorphism of representations of the generalized Kronecker quiver from a commuting square
of isomorphisms. -/
def kroneckerRepIso (g : M ≅ M') (h : N ≅ N') (w : ∀ a, f a ≫ h.hom = g.hom ≫ f' a) :
    kroneckerRep k M N f ≅ kroneckerRep k M' N' f' :=
  NatIso.ofComponents
    (fun v ↦ match v with
      | Quiver.Kronecker.src => g
      | Quiver.Kronecker.tgt => h)
    (by
      rintro (_ | _) (_ | _) p
      · rw [Quiver.Kronecker.path_src_src_eq_nil p]
        simp
      · obtain ⟨a, rfl⟩ := Quiver.Kronecker.arrowPath_surjective p
        simpa using w a
      · exact isEmptyElim
          (α := Quiver.Path (Quiver.Kronecker.tgt : Quiver.Kronecker A) Quiver.Kronecker.src) p
      · rw [Quiver.Kronecker.path_tgt_tgt_eq_nil p]
        simp)

/-- At the source, `TauCeti.kroneckerRepIso` is the prescribed isomorphism. -/
@[simp]
theorem kroneckerRepIso_hom_app_src (g : M ≅ M') (h : N ≅ N')
    (w : ∀ a, f a ≫ h.hom = g.hom ≫ f' a) :
    (kroneckerRepIso g h w).hom.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))
      = g.hom := (rfl)

/-- At the target, `TauCeti.kroneckerRepIso` is the prescribed isomorphism. -/
@[simp]
theorem kroneckerRepIso_hom_app_tgt (g : M ≅ M') (h : N ≅ N')
    (w : ∀ a, f a ≫ h.hom = g.hom ≫ f' a) :
    (kroneckerRepIso g h w).hom.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))
      = h.hom := (rfl)

end Iso

section IsoOfComponents

variable {ρ σ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)}

/-- **Two representations of the generalized Kronecker quiver with isomorphic vertex spaces
intertwining every arrow are isomorphic**, the isomorphism version of `TauCeti.kroneckerRepHom`
for representations that are not presented by `TauCeti.kroneckerRep`. -/
def kroneckerIso
    (g : ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))
      ≅ σ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
    (h : ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))
      ≅ σ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))
    (w : ∀ a, ρ.map (Quiver.Kronecker.arrowPath a) ≫ h.hom
      = g.hom ≫ σ.map (Quiver.Kronecker.arrowPath a)) : ρ ≅ σ :=
  kroneckerRepSelfIso ρ ≪≫ kroneckerRepIso g h w ≪≫ (kroneckerRepSelfIso σ).symm

end IsoOfComponents

section Endomorphism

variable {ρ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)}

/-- **The endomorphism of a representation of the generalized Kronecker quiver attached to an
endomorphism of each vertex space intertwining the action of every arrow.** -/
def kroneckerEnd
    (p : ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) ⟶
      ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
    (q : ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) ⟶
      ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))
    (w : ∀ a, ρ.map (Quiver.Kronecker.arrowPath a) ≫ q
      = p ≫ ρ.map (Quiver.Kronecker.arrowPath a)) : ρ ⟶ ρ where
  app v := match v with
    | Quiver.Kronecker.src => p
    | Quiver.Kronecker.tgt => q
  naturality := by
    rintro (_ | _) (_ | _) e
    · rw [Quiver.Kronecker.path_src_src_eq_nil e]
      simp
    · obtain ⟨a, rfl⟩ := Quiver.Kronecker.arrowPath_surjective e
      exact w a
    · exact isEmptyElim
        (α := Quiver.Path (Quiver.Kronecker.tgt : Quiver.Kronecker A) Quiver.Kronecker.src) e
    · rw [Quiver.Kronecker.path_tgt_tgt_eq_nil e]
      simp

variable {p : ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) ⟶
    ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))}
  {q : ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) ⟶
    ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))}
  {w : ∀ a, ρ.map (Quiver.Kronecker.arrowPath a) ≫ q
    = p ≫ ρ.map (Quiver.Kronecker.arrowPath a)}

include w in
/-- At the source, `TauCeti.kroneckerEnd` is the prescribed endomorphism of the source space. -/
@[simp]
theorem kroneckerEnd_app_src :
    (kroneckerEnd p q w).app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) = p := (rfl)

include w in
/-- At the target, `TauCeti.kroneckerEnd` is the prescribed endomorphism of the target space. -/
@[simp]
theorem kroneckerEnd_app_tgt :
    (kroneckerEnd p q w).app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) = q := (rfl)

include w in
/-- **An indecomposable representation of the generalized Kronecker quiver admits no nontrivial
pair of intertwining idempotents.** -/
theorem eq_zero_or_eq_id_of_indecomposable_kronecker (hind : Indecomposable ρ)
    (hp : p ≫ p = p) (hq : q ≫ q = q) :
    (p = 0 ∧ q = 0) ∨ (p = 𝟙 _ ∧ q = 𝟙 _) := by
  have hidem : kroneckerEnd p q w ≫ kroneckerEnd p q w = kroneckerEnd p q w := by
    refine NatTrans.ext (funext fun x ↦ ?_)
    cases x
    · exact hp
    · exact hq
  rcases idempotent_eq_zero_or_id_of_indecomposable hind hidem with h | h
  · exact Or.inl ⟨congrArg (fun e : ρ ⟶ ρ ↦
        e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))) h,
      congrArg (fun e : ρ ⟶ ρ ↦
        e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))) h⟩
  · exact Or.inr ⟨congrArg (fun e : ρ ⟶ ρ ↦
        e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))) h,
      congrArg (fun e : ρ ⟶ ρ ↦
        e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))) h⟩

end Endomorphism

section Structure

/-- A module carrying no idempotent endomorphism other than `0` and the identity, and not itself
zero, is a line: its submodules are only `⊥` and `⊤`, so it is a simple module. -/
private theorem finrank_eq_one_of_trivial_idempotent (M : ModuleCat.{t} k) (hM : ¬ IsZero M)
    (h : ∀ pr : ↥M →ₗ[k] ↥M, pr ∘ₗ pr = pr → pr = 0 ∨ pr = LinearMap.id) :
    Module.finrank k M = 1 := by
  have hnt : Nontrivial ↥M :=
    not_subsingleton_iff_nontrivial.mp fun hs ↦ hM (ModuleCat.isZero_iff_subsingleton.mpr hs)
  rw [← isSimpleModule_iff_finrank_eq_one, isSimpleModule_iff]
  refine ⟨fun W ↦ ?_⟩
  obtain ⟨C, hC⟩ := W.exists_isCompl
  rcases h (W.projection C hC) (Submodule.isIdempotentElem_projection hC) with h0 | h1
  · exact Or.inl (by rw [← Submodule.range_projection hC, h0, LinearMap.range_zero])
  · exact Or.inr (by rw [← Submodule.range_projection hC, h1, LinearMap.range_id])

variable {ρ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)} [Unique A]

omit [Unique A] in
/-- A representation of the generalized Kronecker quiver whose two vertex spaces both vanish is a
zero object. -/
private theorem isZero_of_isZero_obj
    (hsrc : IsZero (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))))
    (htgt : IsZero (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))) : IsZero ρ := by
  refine (IsZero.iff_id_eq_zero ρ).mpr (NatTrans.ext (funext fun x ↦ ?_))
  cases x
  · exact (IsZero.iff_id_eq_zero _).mp hsrc
  · exact (IsZero.iff_id_eq_zero _).mp htgt

omit [Unique A] in
/-- **A vertex space of an indecomposable representation of the generalized Kronecker quiver whose
partner vanishes is a line.** With the target zero, every idempotent of the source intertwines
every arrow trivially, so indecomposability leaves only `0` and the identity. -/
theorem finrank_src_eq_one_of_isZero_tgt (hind : Indecomposable ρ)
    (htgt : IsZero (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))) :
    Module.finrank k (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))) = 1 := by
  refine finrank_eq_one_of_trivial_idempotent _ (fun hsrc ↦ hind.1 (isZero_of_isZero_obj hsrc htgt))
    fun pr hpr ↦ ?_
  have hw : ∀ a : A, ρ.map (Quiver.Kronecker.arrowPath a) ≫
      (0 : ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) ⟶
        ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))
      = ModuleCat.ofHom pr ≫ ρ.map (Quiver.Kronecker.arrowPath a) :=
    fun _ ↦ htgt.eq_of_tgt _ _
  rcases eq_zero_or_eq_id_of_indecomposable_kronecker (w := hw) hind
    (ModuleCat.hom_ext hpr) (zero_comp) with ⟨h0, -⟩ | ⟨h1, -⟩
  · exact Or.inl (by simpa using congrArg ModuleCat.Hom.hom h0)
  · exact Or.inr (by simpa using congrArg ModuleCat.Hom.hom h1)

omit [Unique A] in
/-- The mirror of `TauCeti.finrank_src_eq_one_of_isZero_tgt`: with the source zero, the target of
an indecomposable representation of the generalized Kronecker quiver is a line. -/
theorem finrank_tgt_eq_one_of_isZero_src (hind : Indecomposable ρ)
    (hsrc : IsZero (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))) :
    Module.finrank k (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))) = 1 := by
  refine finrank_eq_one_of_trivial_idempotent _ (fun htgt ↦ hind.1 (isZero_of_isZero_obj hsrc htgt))
    fun pr hpr ↦ ?_
  have hw : ∀ a : A, ρ.map (Quiver.Kronecker.arrowPath a) ≫ ModuleCat.ofHom pr
      = (0 : ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) ⟶
        ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
        ≫ ρ.map (Quiver.Kronecker.arrowPath a) :=
    fun _ ↦ hsrc.eq_of_src _ _
  rcases eq_zero_or_eq_id_of_indecomposable_kronecker (w := hw) hind zero_comp
    (ModuleCat.hom_ext hpr) with ⟨-, h0⟩ | ⟨-, h1⟩
  · exact Or.inl (by simpa using congrArg ModuleCat.Hom.hom h0)
  · exact Or.inr (by simpa using congrArg ModuleCat.Hom.hom h1)

/-- **The arrow of an indecomposable representation of the `A₂` quiver with both vertex spaces
nonzero is injective.** The projection onto its kernel, paired with `0` at the target, is an
idempotent pair; the identity is excluded because the target does not vanish. -/
theorem ker_map_arrowPath_eq_bot (hind : Indecomposable ρ)
    (htgt : ¬ IsZero (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))) :
    LinearMap.ker (ρ.map (Quiver.Kronecker.arrowPath (default : A))).hom = ⊥ := by
  obtain ⟨C, hC⟩ :=
    (LinearMap.ker (ρ.map (Quiver.Kronecker.arrowPath (default : A))).hom).exists_isCompl
  have hw : ∀ a : A, ρ.map (Quiver.Kronecker.arrowPath a) ≫
      (0 : ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) ⟶
        ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))
      = ModuleCat.ofHom
          ((LinearMap.ker (ρ.map (Quiver.Kronecker.arrowPath (default : A))).hom).projection C hC)
        ≫ ρ.map (Quiver.Kronecker.arrowPath a) := by
    intro a
    obtain rfl : a = default := Subsingleton.elim a default
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    simpa using (Submodule.projection_apply_mem hC x).symm
  rcases eq_zero_or_eq_id_of_indecomposable_kronecker (w := hw) hind
    (ModuleCat.hom_ext (Submodule.isIdempotentElem_projection hC)) zero_comp with
    ⟨h0, -⟩ | ⟨-, h1⟩
  · have hpr : (LinearMap.ker (ρ.map (Quiver.Kronecker.arrowPath (default : A))).hom).projection
        C hC = 0 := by simpa using congrArg ModuleCat.Hom.hom h0
    rw [← Submodule.range_projection hC, hpr, LinearMap.range_zero]
  · exact absurd ((IsZero.iff_id_eq_zero _).mpr h1.symm) htgt

/-- **The arrow of an indecomposable representation of the `A₂` quiver with both vertex spaces
nonzero is surjective**, the mirror of `TauCeti.ker_map_arrowPath_eq_bot`: the projection onto a
complement of its range, paired with `0` at the source, is an idempotent pair. -/
theorem range_map_arrowPath_eq_top (hind : Indecomposable ρ)
    (hsrc : ¬ IsZero (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))) :
    LinearMap.range (ρ.map (Quiver.Kronecker.arrowPath (default : A))).hom = ⊤ := by
  obtain ⟨D, hD⟩ :=
    (LinearMap.range (ρ.map (Quiver.Kronecker.arrowPath (default : A))).hom).exists_isCompl
  have hw : ∀ a : A, ρ.map (Quiver.Kronecker.arrowPath a) ≫
      ModuleCat.ofHom (D.projection
        (LinearMap.range (ρ.map (Quiver.Kronecker.arrowPath (default : A))).hom) hD.symm)
      = (0 : ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) ⟶
        ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
        ≫ ρ.map (Quiver.Kronecker.arrowPath a) := by
    intro a
    obtain rfl : a = default := Subsingleton.elim a default
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    simp [Submodule.projection_apply_of_mem_right hD.symm (LinearMap.mem_range_self _ x)]
  rcases eq_zero_or_eq_id_of_indecomposable_kronecker (w := hw) hind zero_comp
    (ModuleCat.hom_ext (Submodule.isIdempotentElem_projection hD.symm)) with
    ⟨-, h0⟩ | ⟨h1, -⟩
  · have hpr : D.projection
        (LinearMap.range (ρ.map (Quiver.Kronecker.arrowPath (default : A))).hom) hD.symm = 0 := by
      simpa using congrArg ModuleCat.Hom.hom h0
    have := Submodule.ker_projection hD.symm
    rw [hpr, LinearMap.ker_zero] at this
    exact this.symm
  · exact absurd ((IsZero.iff_id_eq_zero _).mpr h1.symm) hsrc

/-- **The arrow of an indecomposable representation of the `A₂` quiver with both vertex spaces
nonzero is an isomorphism**, by `TauCeti.ker_map_arrowPath_eq_bot` and
`TauCeti.range_map_arrowPath_eq_top`. -/
theorem isIso_map_arrowPath (hind : Indecomposable ρ)
    (hsrc : ¬ IsZero (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))))
    (htgt : ¬ IsZero (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))) :
    IsIso (ρ.map (Quiver.Kronecker.arrowPath (default : A))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨LinearMap.ker_eq_bot.mp (ker_map_arrowPath_eq_bot hind htgt),
    LinearMap.range_eq_top.mp (range_map_arrowPath_eq_top hind hsrc)⟩

/-- **Both vertex spaces of an indecomposable representation of the `A₂` quiver with neither of
them zero are lines.** Conjugating an idempotent of the source through the arrow -- an isomorphism
by `TauCeti.isIso_map_arrowPath` -- produces an intertwining idempotent pair. -/
theorem finrank_src_eq_one_of_not_isZero (hind : Indecomposable ρ)
    (hsrc : ¬ IsZero (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))))
    (htgt : ¬ IsZero (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))) :
    Module.finrank k (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))) = 1 := by
  have harr := isIso_map_arrowPath hind hsrc htgt
  refine finrank_eq_one_of_trivial_idempotent _ hsrc fun pr hpr ↦ ?_
  have h2 : ModuleCat.ofHom pr ≫ ModuleCat.ofHom pr = ModuleCat.ofHom pr := ModuleCat.hom_ext hpr
  have hw : ∀ a : A, ρ.map (Quiver.Kronecker.arrowPath a) ≫
      (inv (ρ.map (Quiver.Kronecker.arrowPath (default : A))) ≫ ModuleCat.ofHom pr
        ≫ ρ.map (Quiver.Kronecker.arrowPath (default : A)))
      = ModuleCat.ofHom pr ≫ ρ.map (Quiver.Kronecker.arrowPath a) := by
    intro a
    obtain rfl : a = default := Subsingleton.elim a default
    rw [IsIso.hom_inv_id_assoc]
  rcases eq_zero_or_eq_id_of_indecomposable_kronecker (w := hw) hind h2
    (by
      simp only [ModuleCat.of_coe, Category.assoc, IsIso.hom_inv_id_assoc, IsIso.eq_inv_comp]
      rw [← Category.assoc, h2]) with ⟨h0, -⟩ | ⟨h1, -⟩
  · exact Or.inl (by simpa using congrArg ModuleCat.Hom.hom h0)
  · exact Or.inr (by simpa using congrArg ModuleCat.Hom.hom h1)

/-- The companion of `TauCeti.finrank_src_eq_one_of_not_isZero` at the target vertex: the arrow is
an isomorphism, so it carries the dimension of the source to the dimension of the target. -/
theorem finrank_tgt_eq_one_of_not_isZero (hind : Indecomposable ρ)
    (hsrc : ¬ IsZero (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))))
    (htgt : ¬ IsZero (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))) :
    Module.finrank k (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))) = 1 := by
  have harr := isIso_map_arrowPath hind hsrc htgt
  rw [← (asIso (ρ.map (Quiver.Kronecker.arrowPath (default : A)))).toLinearEquiv.finrank_eq]
  exact finrank_src_eq_one_of_not_isZero hind hsrc htgt

end Structure

end GeneralizedKronecker

section A2

variable {A : Type} [Unique A]

/-- Two lines over `k` are isomorphic in `ModuleCat k`. -/
private noncomputable def isoOfFinrankEqOne {M N : ModuleCat.{u} k}
    (hM : Module.finrank k M = 1) (hN : Module.finrank k N = 1) : M ≅ N :=
  have : Module.Finite k (M : Type u) := Module.finite_of_finrank_eq_succ hM
  have : Module.Finite k (N : Type u) := Module.finite_of_finrank_eq_succ hN
  (LinearEquiv.ofFinrankEq (M : Type u) (N : Type u) (hM.trans hN.symm)).toModuleIso

/-- A line is not a zero object. -/
private theorem not_isZero_of_finrank_eq_one {M : ModuleCat.{u} k}
    (h : Module.finrank k M = 1) : ¬ IsZero M := fun hz ↦ by
  have : Subsingleton (M : Type u) := ModuleCat.isZero_iff_subsingleton.mp hz
  simp [Module.finrank_zero_of_subsingleton] at h

omit [Unique A] in
/-- The vertex simple `Sᵢ` is a line at `i`. -/
private theorem finrank_simpleRep_obj_self (i : Quiver.Kronecker A) :
    Module.finrank k ((simpleRep k (Quiver.Kronecker A) i).obj (i : Paths (Quiver.Kronecker A)))
      = 1 := by
  rw [simpleRep_obj_self]
  exact Module.finrank_self k

omit [Unique A] in
/-- The projective `P₁` of the `A₂` quiver is a line at the source: the trivial path is the only
path from the source to itself. -/
private theorem finrank_indecProjRep_obj_src :
    Module.finrank k ((indecProjRep k (Quiver.Kronecker A) Quiver.Kronecker.src).obj
      (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))) = 1 := by
  have h := dimVector_indecProjRep (k := k) Quiver.Kronecker.src
    (Quiver.Kronecker.src : Quiver.Kronecker A)
  rw [dimVector_apply] at h
  rw [Paths.of_obj] at h
  rw [h, Nat.card_unique]

/-- The projective `P₁` of the `A₂` quiver is a line at the target: its single arrow is the only
path from the source to the target. -/
private theorem finrank_indecProjRep_obj_tgt :
    Module.finrank k ((indecProjRep k (Quiver.Kronecker A) Quiver.Kronecker.src).obj
      (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))) = 1 := by
  have h := dimVector_indecProjRep (k := k) Quiver.Kronecker.src
    (Quiver.Kronecker.tgt : Quiver.Kronecker A)
  rw [dimVector_apply] at h
  rw [Paths.of_obj] at h
  rw [h, Nat.card_congr Quiver.Kronecker.pathEquivArrow, Nat.card_unique]

/-- **The `A₂` quiver has exactly three indecomposable representations**: the two vertex simples
`S₁`, `S₂` and the projective `P₁ = kQ·e₁`, of dimension vectors `(1,0)`, `(0,1)` and `(1,1)` --
the three positive roots of `A₂`.

No finite-dimensionality is assumed: it is a conclusion. If the target vanishes, every idempotent
of the source intertwines the arrow, so the source is a line and the representation is `S₁`;
mirror-image if the source vanishes. Otherwise the arrow is injective and surjective, because the
projections onto its kernel and onto a complement of its range extend to idempotent endomorphisms,
so conjugation through it turns an idempotent of the source into an intertwining pair and both
vertex spaces are lines. -/
theorem nonempty_iso_of_indecomposable_kronecker (ρ : QuiverRep k (Quiver.Kronecker A))
    (hind : Indecomposable ρ) :
    Nonempty (ρ ≅ simpleRep k (Quiver.Kronecker A) Quiver.Kronecker.src) ∨
      Nonempty (ρ ≅ simpleRep k (Quiver.Kronecker A) Quiver.Kronecker.tgt) ∨
      Nonempty (ρ ≅ indecProjRep k (Quiver.Kronecker A) Quiver.Kronecker.src) := by
  by_cases htgt : IsZero (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))
  · refine Or.inl ⟨kroneckerIso
      (isoOfFinrankEqOne (finrank_src_eq_one_of_isZero_tgt hind htgt)
        (finrank_simpleRep_obj_self Quiver.Kronecker.src))
      (htgt.iso (isZero_simpleRep_obj Quiver.Kronecker.src_ne_tgt.symm))
      fun _ ↦ (isZero_simpleRep_obj Quiver.Kronecker.src_ne_tgt.symm).eq_of_tgt _ _⟩
  by_cases hsrc : IsZero (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
  · refine Or.inr (Or.inl ⟨kroneckerIso
      (hsrc.iso (isZero_simpleRep_obj Quiver.Kronecker.src_ne_tgt))
      (isoOfFinrankEqOne (finrank_tgt_eq_one_of_isZero_src hind hsrc)
        (finrank_simpleRep_obj_self Quiver.Kronecker.tgt))
      fun _ ↦ hsrc.eq_of_src _ _⟩)
  refine Or.inr (Or.inr ⟨?_⟩)
  have harr : IsIso (ρ.map (Quiver.Kronecker.arrowPath (default : A))) :=
    isIso_map_arrowPath hind hsrc htgt
  have hP : IsIso ((indecProjRep k (Quiver.Kronecker A) Quiver.Kronecker.src).map
      (Quiver.Kronecker.arrowPath (default : A))) :=
    isIso_map_arrowPath (indecomposable_indecProjRep_of_isAcyclic Quiver.Kronecker.isAcyclic _)
      (not_isZero_of_finrank_eq_one finrank_indecProjRep_obj_src)
      (not_isZero_of_finrank_eq_one finrank_indecProjRep_obj_tgt)
  set g := isoOfFinrankEqOne (finrank_src_eq_one_of_not_isZero hind hsrc htgt)
    finrank_indecProjRep_obj_src
  refine kroneckerIso g
    ((asIso (ρ.map (Quiver.Kronecker.arrowPath (default : A)))).symm ≪≫ g ≪≫
      asIso ((indecProjRep k (Quiver.Kronecker A) Quiver.Kronecker.src).map
        (Quiver.Kronecker.arrowPath (default : A)))) fun a ↦ ?_
  obtain rfl : a = default := Subsingleton.elim a default
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, IsIso.hom_inv_id_assoc]

/-- **The `A₂` quiver has finite representation type**, the positive half of Gabriel's dichotomy
for the smallest Dynkin quiver: by `TauCeti.nonempty_iso_of_indecomposable_kronecker` its
finite-dimensional indecomposables fall into three isomorphism classes.

Contrast `TauCeti.not_isFiniteRepType_kronecker`: as soon as a second arrow is added the Kronecker
quiver leaves Dynkin type and acquires infinitely many indecomposables. -/
theorem isFiniteRepType_kronecker (k : Type u) [Field k] (A : Type) [Unique A] :
    IsFiniteRepType.{u, 0, 0, u} k (Quiver.Kronecker A) := by
  rw [isFiniteRepType_iff]
  have hS : ∀ i : Quiver.Kronecker A,
      IsFinDim k (Quiver.Kronecker A) (simpleRep k (Quiver.Kronecker A) i) ∧
        Indecomposable (simpleRep k (Quiver.Kronecker A) i) :=
    fun i ↦ ⟨isFinDim_iff.mpr fun v ↦ finiteDimensional_simpleRep_obj i v,
      indecomposable_of_simple _⟩
  have hP : IsFinDim k (Quiver.Kronecker A)
        (indecProjRep k (Quiver.Kronecker A) Quiver.Kronecker.src) ∧
      Indecomposable (indecProjRep k (Quiver.Kronecker A) Quiver.Kronecker.src) :=
    ⟨isFinDim_iff.mpr fun v ↦ by cases v <;> exact finiteDimensional_indecProjRep_obj _ _,
      indecomposable_indecProjRep_of_isAcyclic Quiver.Kronecker.isAcyclic _⟩
  refine Finite.of_surjective (α := Fin 3) (fun i ↦ toSkeleton (match i with
    | 0 => ⟨_, hS Quiver.Kronecker.src⟩
    | 1 => ⟨_, hS Quiver.Kronecker.tgt⟩
    | _ => ⟨_, hP⟩)) fun x ↦ ?_
  rcases nonempty_iso_of_indecomposable_kronecker ((fromSkeleton _).obj x).obj
    ((fromSkeleton _).obj x).property.2 with h | h | h
  · obtain ⟨e⟩ := h
    exact ⟨0, by
      rw [← toSkeleton_fromSkeleton_obj x]
      exact toSkeleton_eq_toSkeleton_iff.mpr ⟨ObjectProperty.isoMk _ e.symm⟩⟩
  · obtain ⟨e⟩ := h
    exact ⟨1, by
      rw [← toSkeleton_fromSkeleton_obj x]
      exact toSkeleton_eq_toSkeleton_iff.mpr ⟨ObjectProperty.isoMk _ e.symm⟩⟩
  · obtain ⟨e⟩ := h
    exact ⟨2, by
      rw [← toSkeleton_fromSkeleton_obj x]
      exact toSkeleton_eq_toSkeleton_iff.mpr ⟨ObjectProperty.isoMk _ e.symm⟩⟩

end A2

end TauCeti
