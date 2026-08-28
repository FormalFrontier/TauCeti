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

The list is exact, not merely exhaustive: the three dimension vectors are distinct, so the three
representations are pairwise non-isomorphic, and the skeleton of the finite-dimensional
indecomposables is counted by `Fin 3`.

## Main results

* `TauCeti.eq_zero_or_eq_id_of_indecomposable_kronecker`: an indecomposable representation of the
  generalized Kronecker quiver admits no nontrivial intertwining pair of idempotents.
* `TauCeti.ker_map_arrowPath_eq_bot`, `TauCeti.range_map_arrowPath_eq_top` and
  `TauCeti.isIso_map_arrowPath`: over the `A₂` quiver the arrow of an indecomposable
  representation is injective as soon as its target is nonzero and surjective as soon as its
  source is, hence an isomorphism when neither vertex space vanishes.
* `TauCeti.finrank_src_eq_one_of_isZero_tgt`, `TauCeti.finrank_tgt_eq_one_of_isZero_src`,
  `TauCeti.finrank_src_eq_one_of_not_isZero` and `TauCeti.finrank_tgt_eq_one_of_not_isZero`: the
  nonzero vertex spaces of an indecomposable representation are lines.
* `TauCeti.nonempty_iso_simpleRep_src_or_simpleRep_tgt_or_indecProjRep_of_indecomposable_kronecker`:
  **every indecomposable representation of the `A₂` quiver is `S₁`, `S₂` or `P₁`.**
* `TauCeti.not_nonempty_simpleRep_indecProjRep_iso`: a vertex simple of the `A₂` quiver is not
  `P₁`, which with `TauCeti.not_nonempty_simpleRep_iso` makes the three pairwise non-isomorphic.
* `TauCeti.card_skeleton_indecomposable_kronecker`: **the `A₂` quiver has exactly three
  finite-dimensional indecomposable representations up to isomorphism.**

The finite representation type read off that count is
`TauCeti.isFiniteRepType_kronecker`, in
`TauCeti.RepresentationTheory.Quiver.Kronecker.FiniteRepType` beside its negative counterpart.

## Implementation notes

The pair of a linear map at each vertex intertwining every arrow is turned into a morphism of
representations by `TauCeti.kroneckerHom`, in
`TauCeti.RepresentationTheory.Quiver.Kronecker.Representation`, and into an isomorphism by
`TauCeti.kroneckerIso` there: neither needs indecomposability, so neither lives here.

The classification is stated for an arrow type in `Type`, not in an arbitrary universe. That is
what puts the three comparison objects in the same universe as the representation: the vertex
simple `TauCeti.simpleRep` puts the base field itself at its vertex, while `TauCeti.indecProjRep`
puts the paths of the quiver into a `Finsupp`, and only for a `Type`-valued arrow type do the two
land in one universe. The idempotent dichotomy and the structure results below carry an arbitrary
arrow universe, and the `[Unique A]` hypothesis is spelled only where a single arrow is genuinely
used.

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

section Endomorphism

variable {ρ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)}
  {p : ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) ⟶
    ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))}
  {q : ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) ⟶
    ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))}

/-- **An indecomposable representation of the generalized Kronecker quiver admits no nontrivial
pair of intertwining idempotents.** The intertwining hypothesis is explicit: it is not determined
by the idempotency hypotheses, which name only `p` and `q`. -/
theorem eq_zero_or_eq_id_of_indecomposable_kronecker (hind : Indecomposable ρ)
    (w : ∀ a, ρ.map (Quiver.Kronecker.arrowPath a) ≫ q
      = p ≫ ρ.map (Quiver.Kronecker.arrowPath a))
    (hp : p ≫ p = p) (hq : q ≫ q = q) :
    (p = 0 ∧ q = 0) ∨ (p = 𝟙 _ ∧ q = 𝟙 _) := by
  -- `CategoryTheory.NatTrans.comp_app`, `CategoryTheory.NatTrans.app_zero` and
  -- `CategoryTheory.NatTrans.id_app` are applied as terms rather than rewritten: at a vertex of
  -- `CategoryTheory.Paths` the motive of such a rewrite is not type-correct at the transparency
  -- `rw` and `simp` use.
  have hidem : kroneckerHom p q w ≫ kroneckerHom p q w = kroneckerHom p q w :=
    kroneckerRep_hom_ext
      ((NatTrans.comp_app _ _ _).trans (by rw [kroneckerHom_app_src]; exact hp))
      ((NatTrans.comp_app _ _ _).trans (by rw [kroneckerHom_app_tgt]; exact hq))
  have hsrc : ∀ e : ρ ⟶ ρ, kroneckerHom p q w = e →
      p = e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) :=
    fun _ h ↦ (kroneckerHom_app_src p q w).symm.trans (congrArg (fun e : ρ ⟶ ρ ↦
      e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))) h)
  have htgt : ∀ e : ρ ⟶ ρ, kroneckerHom p q w = e →
      q = e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) :=
    fun _ h ↦ (kroneckerHom_app_tgt p q w).symm.trans (congrArg (fun e : ρ ⟶ ρ ↦
      e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))) h)
  rcases idempotent_eq_zero_or_id_of_indecomposable hind hidem with h | h
  · exact Or.inl ⟨(hsrc _ h).trans (NatTrans.app_zero _), (htgt _ h).trans (NatTrans.app_zero _)⟩
  · exact Or.inr ⟨(hsrc _ h).trans (NatTrans.id_app _ _), (htgt _ h).trans (NatTrans.id_app _ _)⟩

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
    (htgt : IsZero (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))) : IsZero ρ :=
  Functor.isZero ρ fun x ↦ by cases x; exacts [hsrc, htgt]

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
  rcases eq_zero_or_eq_id_of_indecomposable_kronecker hind hw
    (ModuleCat.hom_ext hpr) zero_comp with ⟨h0, -⟩ | ⟨h1, -⟩
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
  rcases eq_zero_or_eq_id_of_indecomposable_kronecker hind hw zero_comp
    (ModuleCat.hom_ext hpr) with ⟨-, h0⟩ | ⟨-, h1⟩
  · exact Or.inl (by simpa using congrArg ModuleCat.Hom.hom h0)
  · exact Or.inr (by simpa using congrArg ModuleCat.Hom.hom h1)

/-- **The arrow of an indecomposable representation of the `A₂` quiver whose target vertex space is
nonzero is injective.** The projection onto its kernel, paired with `0` at the target, is an
idempotent pair; the identity is excluded because the target does not vanish. Nothing is assumed at
the source, so this is stronger than the case of two nonzero vertex spaces. -/
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
  rcases eq_zero_or_eq_id_of_indecomposable_kronecker hind hw
    (ModuleCat.hom_ext (Submodule.isIdempotentElem_projection hC)) zero_comp with
    ⟨h0, -⟩ | ⟨-, h1⟩
  · have hpr : (LinearMap.ker (ρ.map (Quiver.Kronecker.arrowPath (default : A))).hom).projection
        C hC = 0 := by simpa using congrArg ModuleCat.Hom.hom h0
    rw [← Submodule.range_projection hC, hpr, LinearMap.range_zero]
  · exact absurd ((IsZero.iff_id_eq_zero _).mpr h1.symm) htgt

/-- **The arrow of an indecomposable representation of the `A₂` quiver whose source vertex space is
nonzero is surjective**, the mirror of `TauCeti.ker_map_arrowPath_eq_bot`: the projection onto a
complement of its range, paired with `0` at the source, is an idempotent pair, and the identity is
excluded because the source does not vanish. Nothing is assumed at the target, so this too is
stronger than the case of two nonzero vertex spaces. -/
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
  rcases eq_zero_or_eq_id_of_indecomposable_kronecker hind hw zero_comp
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

/-- **A nonzero source vertex space of an indecomposable representation of the `A₂` quiver is a
line**; for the target vertex space see `TauCeti.finrank_tgt_eq_one_of_not_isZero`. With the target
zero this is `TauCeti.finrank_src_eq_one_of_isZero_tgt`; otherwise the arrow is an isomorphism by
`TauCeti.isIso_map_arrowPath`, and conjugating an idempotent of the source through it produces an
intertwining idempotent pair. -/
theorem finrank_src_eq_one_of_not_isZero (hind : Indecomposable ρ)
    (hsrc : ¬ IsZero (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))) :
    Module.finrank k (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))) = 1 := by
  by_cases htgt : IsZero (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))
  · exact finrank_src_eq_one_of_isZero_tgt hind htgt
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
  rcases eq_zero_or_eq_id_of_indecomposable_kronecker hind hw h2
    (by
      simp only [ModuleCat.of_coe, Category.assoc, IsIso.hom_inv_id_assoc, IsIso.eq_inv_comp]
      rw [← Category.assoc, h2]) with ⟨h0, -⟩ | ⟨h1, -⟩
  · exact Or.inl (by simpa using congrArg ModuleCat.Hom.hom h0)
  · exact Or.inr (by simpa using congrArg ModuleCat.Hom.hom h1)

/-- **A nonzero target vertex space of an indecomposable representation of the `A₂` quiver is a
line**, the companion of `TauCeti.finrank_src_eq_one_of_not_isZero`. With the source zero this is
`TauCeti.finrank_tgt_eq_one_of_isZero_src`; otherwise the arrow is an isomorphism, so it carries
the dimension of the source to the dimension of the target. -/
theorem finrank_tgt_eq_one_of_not_isZero (hind : Indecomposable ρ)
    (htgt : ¬ IsZero (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)))) :
    Module.finrank k (ρ.obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))) = 1 := by
  by_cases hsrc : IsZero (ρ.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
  · exact finrank_tgt_eq_one_of_isZero_src hind hsrc
  have harr := isIso_map_arrowPath hind hsrc htgt
  rw [← (asIso (ρ.map (Quiver.Kronecker.arrowPath (default : A)))).toLinearEquiv.finrank_eq]
  exact finrank_src_eq_one_of_not_isZero hind hsrc

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

/-- **Every indecomposable representation of the `A₂` quiver is one of the three**: the two vertex
simples `S₁`, `S₂` and the projective `P₁ = kQ·e₁`, of dimension vectors `(1,0)`, `(0,1)` and
`(1,1)` -- the three positive roots of `A₂`. That the three are pairwise non-isomorphic, so that
this list is exact rather than merely exhaustive, is
`TauCeti.not_nonempty_simpleRep_indecProjRep_iso` together with
`TauCeti.not_nonempty_simpleRep_iso`; the resulting count is
`TauCeti.card_skeleton_indecomposable_kronecker`.

No finite-dimensionality is assumed: it is a conclusion. If the target vanishes, every idempotent
of the source intertwines the arrow, so the source is a line and the representation is `S₁`;
mirror-image if the source vanishes. Otherwise the arrow is injective and surjective, because the
projections onto its kernel and onto a complement of its range extend to idempotent endomorphisms,
so conjugation through it turns an idempotent of the source into an intertwining pair and both
vertex spaces are lines. -/
theorem nonempty_iso_simpleRep_src_or_simpleRep_tgt_or_indecProjRep_of_indecomposable_kronecker
    (ρ : QuiverRep k (Quiver.Kronecker A)) (hind : Indecomposable ρ) :
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
  set g := isoOfFinrankEqOne (finrank_src_eq_one_of_not_isZero hind hsrc)
    finrank_indecProjRep_obj_src
  refine kroneckerIso g
    ((asIso (ρ.map (Quiver.Kronecker.arrowPath (default : A)))).symm ≪≫ g ≪≫
      asIso ((indecProjRep k (Quiver.Kronecker A) Quiver.Kronecker.src).map
        (Quiver.Kronecker.arrowPath (default : A)))) fun a ↦ ?_
  obtain rfl : a = default := Subsingleton.elim a default
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, IsIso.hom_inv_id_assoc]

/-- **A vertex simple of the `A₂` quiver is not the projective `P₁`**: the vertex where `Sᵢ`
vanishes is one where `P₁` is a line, `P₁` having dimension vector `(1,1)`. With
`TauCeti.not_nonempty_simpleRep_iso` this makes the three representations of the classification
`TauCeti.nonempty_iso_simpleRep_src_or_simpleRep_tgt_or_indecProjRep_of_indecomposable_kronecker`
pairwise non-isomorphic. -/
theorem not_nonempty_simpleRep_indecProjRep_iso (i : Quiver.Kronecker A) :
    ¬ Nonempty (simpleRep k (Quiver.Kronecker A) i ≅
      indecProjRep k (Quiver.Kronecker A) Quiver.Kronecker.src) := by
  rintro ⟨e⟩
  have h := congrFun (dimVector_eq_of_iso e)
  cases i with
  | src =>
    have h1 := h Quiver.Kronecker.tgt
    rw [dimVector_simpleRep, dimVector_indecProjRep, Pi.single_apply,
      ite_eq_right Quiver.Kronecker.src_ne_tgt.symm,
      Nat.card_congr Quiver.Kronecker.pathEquivArrow, Nat.card_unique] at h1
    exact zero_ne_one h1
  | tgt =>
    have h1 := h Quiver.Kronecker.src
    rw [dimVector_simpleRep, dimVector_indecProjRep, Pi.single_apply,
      ite_eq_right Quiver.Kronecker.src_ne_tgt, Nat.card_unique] at h1
    exact zero_ne_one h1

variable (k A) in
/-- The three indecomposable representations of the `A₂` quiver, listed by `Fin 3`. -/
private noncomputable def indecRep (i : Fin 3) : QuiverRep k (Quiver.Kronecker A) :=
  match i with
  | 0 => simpleRep k (Quiver.Kronecker A) Quiver.Kronecker.src
  | 1 => simpleRep k (Quiver.Kronecker A) Quiver.Kronecker.tgt
  | _ => indecProjRep k (Quiver.Kronecker A) Quiver.Kronecker.src

/-- Each of the three is a finite-dimensional indecomposable: the vertex simples because a simple
object is indecomposable, the projective by `TauCeti.indecomposable_indecProjRep_of_isAcyclic`. -/
private theorem isFinDim_and_indecomposable_indecRep (i : Fin 3) :
    IsFinDim k (Quiver.Kronecker A) (indecRep k A i) ∧ Indecomposable (indecRep k A i) := by
  have hS : ∀ j : Quiver.Kronecker A,
      IsFinDim k (Quiver.Kronecker A) (simpleRep k (Quiver.Kronecker A) j) ∧
        Indecomposable (simpleRep k (Quiver.Kronecker A) j) :=
    fun j ↦ ⟨isFinDim_iff.mpr fun v ↦ finiteDimensional_simpleRep_obj j v,
      indecomposable_of_simple _⟩
  have hP : IsFinDim k (Quiver.Kronecker A)
        (indecProjRep k (Quiver.Kronecker A) Quiver.Kronecker.src) ∧
      Indecomposable (indecProjRep k (Quiver.Kronecker A) Quiver.Kronecker.src) :=
    ⟨isFinDim_iff.mpr fun v ↦ by cases v <;> exact finiteDimensional_indecProjRep_obj _ _,
      indecomposable_indecProjRep_of_isAcyclic Quiver.Kronecker.isAcyclic _⟩
  fin_cases i
  · exact hS Quiver.Kronecker.src
  · exact hS Quiver.Kronecker.tgt
  · exact hP

variable (k A) in
/-- The isomorphism classes of the three indecomposable representations of the `A₂` quiver. -/
private noncomputable def indecClass (i : Fin 3) :
    Skeleton (ObjectProperty.FullSubcategory (fun M : QuiverRep k (Quiver.Kronecker A) ↦
      IsFinDim k (Quiver.Kronecker A) M ∧ Indecomposable M)) :=
  toSkeleton ⟨indecRep k A i, isFinDim_and_indecomposable_indecRep i⟩

/-- The three classes exhaust the skeleton: this is the classification. -/
private theorem indecClass_surjective : Function.Surjective (indecClass k A) := by
  intro x
  have key : ∀ i : Fin 3, Nonempty (((fromSkeleton _).obj x).obj ≅ indecRep k A i) →
      indecClass k A i = x := by
    rintro i ⟨e⟩
    rw [← toSkeleton_fromSkeleton_obj x]
    exact toSkeleton_eq_toSkeleton_iff.mpr ⟨ObjectProperty.isoMk _ e.symm⟩
  rcases nonempty_iso_simpleRep_src_or_simpleRep_tgt_or_indecProjRep_of_indecomposable_kronecker
    ((fromSkeleton _).obj x).obj ((fromSkeleton _).obj x).property.2 with h | h | h
  · exact ⟨0, key 0 h⟩
  · exact ⟨1, key 1 h⟩
  · exact ⟨2, key 2 h⟩

/-- The three classes are distinct: an equality of classes is an isomorphism of representations,
which the two non-isomorphism results rule out off the diagonal. -/
private theorem indecClass_injective : Function.Injective (indecClass k A) := by
  have hSS := not_nonempty_simpleRep_iso (k := k) (Q := Quiver.Kronecker A)
    Quiver.Kronecker.src_ne_tgt
  have hSP := not_nonempty_simpleRep_indecProjRep_iso (k := k) (A := A)
  intro i j hij
  have hiso : Nonempty (indecRep k A i ≅ indecRep k A j) :=
    (ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso _ _ _).mp hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | exact absurd hiso hSS
      | exact absurd (hiso.map Iso.symm) hSS
      | exact absurd hiso (hSP _)
      | exact absurd (hiso.map Iso.symm) (hSP _)

/-- **The `A₂` quiver has exactly three finite-dimensional indecomposable representations up to
isomorphism**: the classification
`TauCeti.nonempty_iso_simpleRep_src_or_simpleRep_tgt_or_indecProjRep_of_indecomposable_kronecker`
exhibits `S₁`, `S₂` and `P₁` as an exhaustive list, and their dimension vectors `(1,0)`, `(0,1)` and
`(1,1)` keep them pairwise non-isomorphic, so the skeleton is counted by `Fin 3`. -/
theorem card_skeleton_indecomposable_kronecker (k : Type u) [Field k] (A : Type) [Unique A] :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, 0, 0, u} k (Quiver.Kronecker A) ↦
        IsFinDim k (Quiver.Kronecker A) M ∧ Indecomposable M))) = 3 := by
  rw [← Nat.card_eq_of_bijective (indecClass k A) ⟨indecClass_injective, indecClass_surjective⟩,
    Nat.card_eq_fintype_card, Fintype.card_fin]

end A2

end TauCeti
