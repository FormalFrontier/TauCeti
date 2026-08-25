/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Projective.Cover
public import TauCeti.RepresentationTheory.Quiver.Representation.Comparison

/-!
# The vertex projective is the projective cover of the vertex simple

For a vertex `i` of a quiver `Q` the surjection `Pᵢ ↠ Sᵢ` of
`TauCeti.RepresentationTheory.Quiver.Representation.Comparison` exhibits the vertex simple as a
quotient of the vertex projective. This file proves that as soon as the trivial path is the only
path `i → i`, that surjection is a *projective cover*: it is an essential epimorphism, so nothing
smaller than `Pᵢ` maps onto `Sᵢ`.

Some such hypothesis is genuinely needed. For the quiver with one vertex and one loop the path
algebra is `k[X]`, the kernel of `Pᵢ ↠ Sᵢ` is the ideal `(X)`, and `(X) + (X - 1) = k[X]` with
`(X - 1)` proper, so that kernel is not superfluous and `Pᵢ ↠ Sᵢ` is not a cover. The hypothesis
used below is the *local* one, `∀ p : Quiver.Path i i, p = Quiver.Path.nil`: what it buys is that
the vertex space `(Pᵢ)ᵢ` is the *line* through the basis vector of the trivial path
(`TauCeti.exists_eq_smul_indecProjRepBasis_nil`), and a morphism `g : X ⟶ Pᵢ` whose composite with
`Pᵢ ↠ Sᵢ` is onto must then hit that basis vector exactly, not merely up to the kernel. Cycles
elsewhere in `Q` are irrelevant to the cover at `i`, so acyclicity of the whole quiver is a
sufficient uniform hypothesis rather than a necessary one: a proof carrying
`hQ : TauCeti.Quiver.IsAcyclic Q` instantiates every result below by passing `hQ.eq_nil`.

Hitting it is already enough, with no hypothesis on `Q` at all: `Pᵢ` is *generated* by the basis
vector of the trivial path, so a morphism into `Pᵢ` whose image contains it is a **split**
epimorphism. That half of the argument is quiver-independent structure theory of `Pᵢ` and lives
upstream, beside the universal property it is a corollary of, in
`TauCeti.RepresentationTheory.Quiver.Representation.Projective.Basic`
(`TauCeti.isSplitEpi_of_app_eq_indecProjRepBasis_nil`, together with the line lemma and
`TauCeti.eq_id_of_app_indecProjRepBasis_nil_eq_self`). The essential-epimorphism statement below
is the composite of that generation lemma with the line lemma.

Two consequences package the cover: the comparison morphism admits no endomorphism of `Pᵢ` over
`Sᵢ` other than the identity (rigidity), and every projective representation mapping onto `Sᵢ`
has `Pᵢ` as a direct summand (minimality). They stand in different relations to the general
theory. Rigidity *sharpens* it: `TauCeti.IsEssentialEpi.isIso_of_comp_eq` concludes only that such
an endomorphism is an isomorphism, while here it is the identity. Minimality is an instantiation
rather than a sharpening — the general split-factorization statement
`TauCeti.IsEssentialEpi.exists_comp_eq_and_isSplitEpi` read at `Pᵢ ↠ Sᵢ`. Uniqueness — that any
two projective covers of `Sᵢ` are isomorphic over `Sᵢ`, so `Pᵢ` is *the* projective cover of
`Sᵢ` — is the general categorical statement
`TauCeti.IsEssentialEpi.exists_iso`, instantiated here at `Pᵢ ↠ Sᵢ`.

The cover is stated in the category of representations, not through the module-level
`TauCeti.IsProjectiveCover`. It is the categorical reading of the *same* condition: over an
additive group `TauCeti.isProjectiveCover_iff_forall_surjective` says that the projective covers
of a module are exactly the essential epimorphisms onto it from a projective module, and that is
what is proved here for `Pᵢ ↠ Sᵢ`. Transporting the statement across
`TauCeti.quiverRepEquivalence` to a literal `TauCeti.IsProjectiveCover` of `kQ`-modules would need
two further bridges — the identification of the image of `Pᵢ` with the left ideal `kQ · eᵢ`, and
the comparison of an essential epimorphism of `ModuleCat` with a superfluous kernel — and neither
is built here.

Every statement here compares `Pᵢ` with `Sᵢ`, so every statement here takes the field in the
universe `max v w` of the vertices and the arrows: that is the restriction under which the two
objects lie in a common category at all, and the implementation notes of
`TauCeti.RepresentationTheory.Quiver.Representation.Comparison` document it. The generation
lemmas mention only `Pᵢ` and carry no such restriction, which is a second reason they live
upstream in `TauCeti.RepresentationTheory.Quiver.Representation.Projective.Basic` rather than
here.

## Main results

* `TauCeti.eq_indecProjRepBasis_nil_of_app_eq_simpleRepGenerator` and
  `TauCeti.exists_app_eq_indecProjRepBasis_nil`: with no nontrivial path `i → i`, `Pᵢ ↠ Sᵢ`
  separates that basis vector from the rest of `(Pᵢ)ᵢ`, so a morphism into `Pᵢ` that is onto `Sᵢ`
  after composing with it hits the basis vector.
* `TauCeti.isSplitEpi_of_epi_comp_indecProjRepToSimpleRep` and
  `TauCeti.epi_of_epi_comp_indecProjRepToSimpleRep`: **`Pᵢ ↠ Sᵢ` is an essential epimorphism** —
  in the sharper form that every `g : X ⟶ Pᵢ` whose composite with it is an epimorphism is
  already a *split* epimorphism — so `Pᵢ` is the projective cover of `Sᵢ`.
* `TauCeti.eq_id_of_comp_indecProjRepToSimpleRep_eq_self`: the cover is rigid — an endomorphism of
  `Pᵢ` commuting with it is the identity.
* `TauCeti.isEssentialEpi_indecProjRepToSimpleRep`: the cover packaged as a
  `TauCeti.IsEssentialEpi`, the form the general theory consumes.
* `TauCeti.exists_comp_indecProjRepToSimpleRep_eq_and_isSplitEpi`: the cover is minimal — every
  projective representation mapping onto `Sᵢ` retracts onto `Pᵢ`, by a retraction that factors the
  given map through the cover.
* `TauCeti.exists_iso_indecProjRep`: **the cover is unique** — every projective cover of `Sᵢ` is
  isomorphic to `Pᵢ` over `Sᵢ`.

## References

This implements the "`Pᵢ = ` projective cover of `Sᵢ`" clause of the "projective covers and
injective envelopes" bullet of Layer 3 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, for a vertex simple at a
vertex carrying no nontrivial closed path — in particular for every vertex of an acyclic quiver.

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), I.5 and III.2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v w

variable (k : Type (max v w)) {Q : Type v} [Field k] [Quiver.{w} Q]

/-- **`Pᵢ ↠ Sᵢ` pins down the basis vector of the trivial path**: with no nontrivial path
`i → i`, it is the only vector of `(Pᵢ)ᵢ` sent to the generator of the line `(Sᵢ)ᵢ`. With a cycle
at `i` this fails: any vector differing from it by a path of positive length `i → i` has the same
image. -/
theorem eq_indecProjRepBasis_nil_of_app_eq_simpleRepGenerator {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil)
    {v : (indecProjRep k Q i).obj i}
    (hv : (indecProjRepToSimpleRep k i).app ((Paths.of Q).obj i) v = simpleRepGenerator k i) :
    v = indecProjRepBasis k i i Quiver.Path.nil := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_indecProjRepBasis_nil k i h v
  -- The component is a `ModuleCat` morphism read through `ConcreteCategory.hom`, which `rw` alone
  -- cannot see past, so the scalar is pulled out by hand.
  have hsmul : (indecProjRepToSimpleRep k i).app ((Paths.of Q).obj i)
        (c • indecProjRepBasis k i i Quiver.Path.nil)
      = c • (indecProjRepToSimpleRep k i).app ((Paths.of Q).obj i)
        (indecProjRepBasis k i i Quiver.Path.nil) :=
    map_smul _ c _
  rw [hsmul, indecProjRepToSimpleRep_app_nil] at hv
  have hc : c = 1 := by
    have hval := congrArg (simpleRepSelfEquiv k i) hv
    rwa [map_smul, simpleRepSelfEquiv_apply_generator, smul_eq_mul, mul_one] at hval
  rw [hc, one_smul]

/-- With no nontrivial path `i → i`, a morphism `g : X ⟶ Pᵢ` whose composite with `Pᵢ ↠ Sᵢ` is an
epimorphism hits the basis vector of the trivial path. Epimorphisms of representations are
surjective vertex by vertex, so the generator of `(Sᵢ)ᵢ` has a preimage, and
`TauCeti.eq_indecProjRepBasis_nil_of_app_eq_simpleRepGenerator` identifies its image in
`(Pᵢ)ᵢ`. -/
theorem exists_app_eq_indecProjRepBasis_nil {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil) {X : QuiverRep k Q}
    (g : X ⟶ indecProjRep k Q i) (hg : Epi (g ≫ indecProjRepToSimpleRep k i)) :
    ∃ x : X.obj ((Paths.of Q).obj i),
      g.app ((Paths.of Q).obj i) x = indecProjRepBasis k i i Quiver.Path.nil := by
  have hepi : Epi ((g ≫ indecProjRepToSimpleRep k i).app ((Paths.of Q).obj i)) :=
    (NatTrans.epi_iff_epi_app _).1 hg _
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).1 hepi (simpleRepGenerator k i)
  exact ⟨y, eq_indecProjRepBasis_nil_of_app_eq_simpleRepGenerator k h hy⟩

/-- **`Pᵢ ↠ Sᵢ` is an essential epimorphism, in the strong split form**: with no nontrivial path
`i → i`, a morphism into `Pᵢ` that becomes an epimorphism after composing with it is already a
split epimorphism. This is the projective-cover property of `Pᵢ` in its sharpest form: the
composite already being onto `Sᵢ` forces `g` to have a section, so `Pᵢ` is a direct summand of
every source that covers `Sᵢ` through it. -/
theorem isSplitEpi_of_epi_comp_indecProjRepToSimpleRep {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil)
    {X : QuiverRep k Q} (g : X ⟶ indecProjRep k Q i)
    (hg : Epi (g ≫ indecProjRepToSimpleRep k i)) : IsSplitEpi g := by
  obtain ⟨x, hx⟩ := exists_app_eq_indecProjRepBasis_nil k h g hg
  exact isSplitEpi_of_app_eq_indecProjRepBasis_nil k g hx

/-- **`Pᵢ` is the projective cover of `Sᵢ` when the trivial path is the only path `i → i`**:
`Pᵢ ↠ Sᵢ` is an epimorphism from a projective object (`TauCeti.epi_indecProjRepToSimpleRep`,
`TauCeti.projective_indecProjRep`) that is *essential*, a morphism into `Pᵢ` being an epimorphism
as soon as its composite with the cover is. -/
theorem epi_of_epi_comp_indecProjRepToSimpleRep {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil)
    {X : QuiverRep k Q} (g : X ⟶ indecProjRep k Q i)
    (hg : Epi (g ≫ indecProjRepToSimpleRep k i)) : Epi g := by
  have hsplit : IsSplitEpi g := isSplitEpi_of_epi_comp_indecProjRepToSimpleRep k h g hg
  infer_instance

/-- **The cover is rigid**: with no nontrivial path `i → i`, an endomorphism of `Pᵢ` commuting
with `Pᵢ ↠ Sᵢ` is the identity, not merely an isomorphism; in particular `Pᵢ ↠ Sᵢ` admits no
automorphism over `Sᵢ` other than the identity. This is sharper than what an arbitrary projective
cover gives, `TauCeti.IsEssentialEpi.isIso_of_comp_eq` concluding only that such an endomorphism is
an isomorphism. -/
theorem eq_id_of_comp_indecProjRepToSimpleRep_eq_self {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil)
    (f : indecProjRep k Q i ⟶ indecProjRep k Q i)
    (hf : f ≫ indecProjRepToSimpleRep k i = indecProjRepToSimpleRep k i) :
    f = 𝟙 (indecProjRep k Q i) := by
  refine eq_id_of_app_indecProjRepBasis_nil_eq_self k f
    (eq_indecProjRepBasis_nil_of_app_eq_simpleRepGenerator k h ?_)
  rw [← indecProjRepHomEquiv_apply, ← indecProjRepHomEquiv_comp, hf,
    indecProjRepHomEquiv_apply, indecProjRepToSimpleRep_app_nil]

/-- **`Pᵢ ↠ Sᵢ` is a projective cover**, packaged as a `TauCeti.IsEssentialEpi`: it is an
epimorphism (`TauCeti.epi_indecProjRepToSimpleRep`) and essential
(`TauCeti.epi_of_epi_comp_indecProjRepToSimpleRep`). Together with
`TauCeti.projective_indecProjRep` this is the hypothesis the general theory of projective covers
consumes. -/
theorem isEssentialEpi_indecProjRepToSimpleRep {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil) :
    IsEssentialEpi (indecProjRepToSimpleRep k i) where
  epi := inferInstance
  epi_of_epi_comp g hg := epi_of_epi_comp_indecProjRepToSimpleRep k h g hg

/-- **The cover is minimal**: with no nontrivial path `i → i`, every projective representation
mapping onto `Sᵢ` retracts onto `Pᵢ`, so `Pᵢ` is a direct summand of it. The retraction is
produced over the given map, factoring it through the cover. This is the general minimality
statement `TauCeti.IsEssentialEpi.exists_comp_eq_and_isSplitEpi` read at `Pᵢ ↠ Sᵢ`. -/
theorem exists_comp_indecProjRepToSimpleRep_eq_and_isSplitEpi {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil)
    {X : QuiverRep k Q} [Projective X] (f : X ⟶ simpleRep k Q i) (hf : Epi f) :
    ∃ g : X ⟶ indecProjRep k Q i, g ≫ indecProjRepToSimpleRep k i = f ∧ IsSplitEpi g :=
  (isEssentialEpi_indecProjRepToSimpleRep k h).exists_comp_eq_and_isSplitEpi hf

/-- **The projective cover of `Sᵢ` is `Pᵢ`, uniquely.** With no nontrivial path `i → i`, every
projective cover of the vertex simple `Sᵢ` — every essential epimorphism onto it from a projective
representation — is isomorphic to `Pᵢ ↠ Sᵢ` by an isomorphism over `Sᵢ`. This is what makes `Pᵢ`
*the* projective cover of `Sᵢ`, and it is the general uniqueness statement
`TauCeti.IsEssentialEpi.exists_iso` read at the vertex cover. -/
theorem exists_iso_indecProjRep {i : Q} (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil)
    {X : QuiverRep k Q} [Projective X] {π : X ⟶ simpleRep k Q i} (hπ : IsEssentialEpi π) :
    ∃ e : indecProjRep k Q i ≅ X, e.hom ≫ π = indecProjRepToSimpleRep k i :=
  (isEssentialEpi_indecProjRepToSimpleRep k h).exists_iso hπ

end TauCeti
