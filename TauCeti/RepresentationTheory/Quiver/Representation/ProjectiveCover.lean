/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
epimorphism (`TauCeti.isSplitEpi_of_app_eq_indecProjRepBasis_nil`). The splitting is written down
by the universal property of `Pᵢ`: the element hitting the basis vector is exactly the datum a
morphism *out of* `Pᵢ` needs, and the two composites are the identity because an endomorphism of
`Pᵢ` fixing that basis vector is the identity (`TauCeti.eq_id_of_app_indecProjRepBasis_nil`). The
essential-epimorphism statement is the composite of that generation lemma with the line lemma
above.

Two consequences package the cover: the comparison morphism admits no endomorphism of `Pᵢ` over
`Sᵢ` other than the identity (uniqueness), and every projective representation mapping onto `Sᵢ`
has `Pᵢ` as a direct summand (minimality).

The cover is stated in the category of representations, not through the module-level
`TauCeti.IsProjectiveCover`. It is the categorical reading of the *same* condition: over an
additive group `TauCeti.isProjectiveCover_iff_forall_surjective` says that the projective covers
of a module are exactly the essential epimorphisms onto it from a projective module, and that is
what is proved here for `Pᵢ ↠ Sᵢ`. Transporting the statement across
`TauCeti.quiverRepEquivalence` to a literal `TauCeti.IsProjectiveCover` of `kQ`-modules would need
two further bridges — the identification of the image of `Pᵢ` with the left ideal `kQ · eᵢ`, and
the comparison of an essential epimorphism of `ModuleCat` with a superfluous kernel — and neither
is built here.

## Main results

* `TauCeti.exists_eq_smul_indecProjRepBasis_nil`: when the trivial path is the only path `i → i`,
  `(Pᵢ)ᵢ` is the line spanned by the basis vector of that path.
* `TauCeti.eq_id_of_app_indecProjRepBasis_nil`: an endomorphism of `Pᵢ` fixing that basis vector
  is the identity, and `TauCeti.isSplitEpi_of_app_eq_indecProjRepBasis_nil`: a morphism into `Pᵢ`
  hitting it is a split epimorphism. Neither needs any hypothesis on `Q`.
* `TauCeti.eq_indecProjRepBasis_nil_of_app_eq_simpleRepGenerator` and
  `TauCeti.exists_app_eq_indecProjRepBasis_nil`: with no nontrivial path `i → i`, `Pᵢ ↠ Sᵢ`
  separates that basis vector from the rest of `(Pᵢ)ᵢ`, so a morphism into `Pᵢ` that is onto `Sᵢ`
  after composing with it hits the basis vector.
* `TauCeti.isSplitEpi_of_epi_comp_indecProjRepToSimpleRep` and
  `TauCeti.epi_of_epi_comp_indecProjRepToSimpleRep`: **`Pᵢ ↠ Sᵢ` is an essential epimorphism** —
  in the sharper form that every `g : X ⟶ Pᵢ` whose composite with it is an epimorphism is
  already a *split* epimorphism — so `Pᵢ` is the projective cover of `Sᵢ`.
* `TauCeti.eq_id_of_comp_indecProjRepToSimpleRep`: the cover is rigid — an endomorphism of `Pᵢ`
  commuting with it is the identity.
* `TauCeti.exists_isSplitEpi_of_epi_to_simpleRep`: the cover is minimal — every projective
  representation mapping onto `Sᵢ` retracts onto `Pᵢ`.

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

universe u v w

section Generation

variable (k : Type u) {Q : Type v} [Field k] [Quiver.{w} Q]

/-- **`(Pᵢ)ᵢ` is a line when the trivial path is the only path `i → i`**: it is then spanned by
the basis vector of that path. This is the one place the hypothesis on `Q` enters the projective
cover below, and it fails for the one-loop quiver, where `(Pᵢ)ᵢ` is `k[X]`. Only closed paths at
`i` matter, so an acyclic `Q` supplies the hypothesis as `hQ.eq_nil`. -/
theorem exists_eq_smul_indecProjRepBasis_nil (i : Q)
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil) (v : (indecProjRep k Q i).obj i) :
    ∃ c : k, v = c • indecProjRepBasis k i i Quiver.Path.nil := by
  have hrange : Set.range ⇑(indecProjRepBasis k i i)
      = {indecProjRepBasis k i i Quiver.Path.nil} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨Quiver.Path.nil, rfl⟩, ?_⟩
    rintro _ ⟨p, rfl⟩
    rw [h p]
  have hmem : v ∈ Submodule.span k {indecProjRepBasis k i i Quiver.Path.nil} := by
    rw [← hrange, (indecProjRepBasis k i i).span_eq]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨c, hc.symm⟩

/-- **An endomorphism of `Pᵢ` fixing the basis vector of the trivial path is the identity.** A
morphism out of `Pᵢ` is determined by the image of that basis vector
(`TauCeti.indecProjRepHom_app_nil_self`), and the identity is the morphism attached to the basis
vector itself. -/
theorem eq_id_of_app_indecProjRepBasis_nil {i : Q} (f : indecProjRep k Q i ⟶ indecProjRep k Q i)
    (hf : f.app ((Paths.of Q).obj i) (indecProjRepBasis k i i Quiver.Path.nil)
      = indecProjRepBasis k i i Quiver.Path.nil) :
    f = 𝟙 (indecProjRep k Q i) :=
  calc f = indecProjRepHom i (indecProjRep k Q i)
        (f.app ((Paths.of Q).obj i) (indecProjRepBasis k i i Quiver.Path.nil)) :=
        (indecProjRepHom_app_nil_self f).symm
    _ = indecProjRepHom i (indecProjRep k Q i) (indecProjRepBasis k i i Quiver.Path.nil) := by
        rw [hf]
    _ = 𝟙 (indecProjRep k Q i) := indecProjRepHom_app_nil_self (𝟙 (indecProjRep k Q i))

/-- **`Pᵢ` is generated by the basis vector of the trivial path**: a morphism into `Pᵢ` whose
image at `i` contains that basis vector is a *split* epimorphism. The splitting is the morphism
that the universal property of `Pᵢ` attaches to a preimage, and the composite is the identity by
`TauCeti.eq_id_of_app_indecProjRepBasis_nil`. No hypothesis on the quiver is needed. -/
theorem isSplitEpi_of_app_eq_indecProjRepBasis_nil {i : Q} {X : QuiverRep k Q}
    (g : X ⟶ indecProjRep k Q i) {x : X.obj ((Paths.of Q).obj i)}
    (hx : g.app ((Paths.of Q).obj i) x = indecProjRepBasis k i i Quiver.Path.nil) :
    IsSplitEpi g := by
  refine IsSplitEpi.mk' ⟨indecProjRepHom i X x, eq_id_of_app_indecProjRepBasis_nil k _ ?_⟩
  -- Composition of morphisms of representations is componentwise, and componentwise it is
  -- composition of linear maps, so the value at the basis vector is the value of `g` at `x`.
  have happ : (indecProjRepHom i X x ≫ g).app ((Paths.of Q).obj i)
        (indecProjRepBasis k i i Quiver.Path.nil)
      = g.app ((Paths.of Q).obj i) ((indecProjRepHom i X x).app ((Paths.of Q).obj i)
        (indecProjRepBasis k i i Quiver.Path.nil)) := rfl
  rw [happ, indecProjRepHom_app_nil, hx]

end Generation

section Cover

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
with `Pᵢ ↠ Sᵢ` is the identity, not merely an isomorphism. This is the uniqueness half of "the"
projective cover, in its sharpest form: `Pᵢ ↠ Sᵢ` admits no automorphism over `Sᵢ` at all. -/
theorem eq_id_of_comp_indecProjRepToSimpleRep {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil)
    (f : indecProjRep k Q i ⟶ indecProjRep k Q i)
    (hf : f ≫ indecProjRepToSimpleRep k i = indecProjRepToSimpleRep k i) :
    f = 𝟙 (indecProjRep k Q i) := by
  refine eq_id_of_app_indecProjRepBasis_nil k f
    (eq_indecProjRepBasis_nil_of_app_eq_simpleRepGenerator k h ?_)
  have happ : (f ≫ indecProjRepToSimpleRep k i).app ((Paths.of Q).obj i)
        (indecProjRepBasis k i i Quiver.Path.nil)
      = (indecProjRepToSimpleRep k i).app ((Paths.of Q).obj i)
        (f.app ((Paths.of Q).obj i) (indecProjRepBasis k i i Quiver.Path.nil)) := rfl
  rw [← happ, hf, indecProjRepToSimpleRep_app_nil]

/-- **The cover is minimal**: with no nontrivial path `i → i`, every projective representation
mapping onto `Sᵢ` retracts onto `Pᵢ`, so `Pᵢ` is a direct summand of it. Projectivity lifts the
map to `Pᵢ` along the cover, and
`TauCeti.isSplitEpi_of_epi_comp_indecProjRepToSimpleRep` splits the lift. -/
theorem exists_isSplitEpi_of_epi_to_simpleRep {i : Q}
    (h : ∀ p : Quiver.Path i i, p = Quiver.Path.nil)
    {X : QuiverRep k Q} [Projective X] (f : X ⟶ simpleRep k Q i) (hf : Epi f) :
    ∃ g : X ⟶ indecProjRep k Q i, IsSplitEpi g := by
  refine ⟨Projective.factorThru f (indecProjRepToSimpleRep k i), ?_⟩
  refine isSplitEpi_of_epi_comp_indecProjRepToSimpleRep k h _ ?_
  rw [Projective.factorThru_comp]
  exact hf

end Cover

end TauCeti
