/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import TauCeti.CategoryTheory.IrreducibleMorphism

/-!
# Right and left almost split morphisms

A morphism `f : X ⟶ Y` is **right almost split** when it is not a split epimorphism and *every*
morphism `Z ⟶ Y` that is not a split epimorphism factors through it. Dually `f` is **left almost
split** when it is not a split monomorphism and every morphism `X ⟶ Z` that is not a split
monomorphism factors through it. So a right almost split morphism into `Y` is a single map that
absorbs all the "inessential" maps into `Y` at once, and a left almost split morphism out of `X`
absorbs all the inessential maps out of `X`.

These are the two lifting properties an **almost-split (Auslander-Reiten) sequence**
`0 → τM → E → M → 0` carries: `E ⟶ M` is right almost split and `τM ⟶ E` is left almost split.
This file builds them as conditions on a single morphism of an arbitrary category, so that the
sequence-level notion can be assembled from them — it is, as
`CategoryTheory.ShortComplex.IsAlmostSplit` in `TauCeti/CategoryTheory/AlmostSplit/Sequence.lean` —
and proves the two facts that make the indecomposability clauses in the definition of an
almost-split sequence redundant: **the target of a right almost split morphism is indecomposable**,
and dually **the source of a left almost split morphism is indecomposable**. Neither end of an
almost-split sequence has to be *assumed* indecomposable — the lifting properties already force
it.

The connection to `TauCeti.IsIrreducibleMorphism` is the sharpened factorization
`TauCeti.IsRightAlmostSplit.exists_isSplitMono_of_isIrreducibleMorphism`: an irreducible morphism
into `Y` not only factors through a right almost split `f : X ⟶ Y`, it factors through it by a
**split monomorphism**, exhibiting its source as a retract of `X`. This is what makes the middle
term of an almost-split sequence the receptacle of the irreducible morphisms into `M`, and hence
what ties the sequence to the arrows of the Auslander-Reiten quiver.

## Main results

* `TauCeti.IsRightAlmostSplit` and `TauCeti.IsLeftAlmostSplit`: the definitions, with
  `TauCeti.isRightAlmostSplit_iff` and `TauCeti.isLeftAlmostSplit_iff` as the introduction rules
  and the projections `not_isSplitEpi` / `not_isSplitMono` and `factors`.
* `TauCeti.isRightAlmostSplit_op_iff` and `TauCeti.isLeftAlmostSplit_op_iff`: **the two notions are
  exchanged by passage to the opposite category**, so every result about one transports to the
  other.
* `TauCeti.IsRightAlmostSplit.indecomposable`: **the target of a right almost split morphism is
  indecomposable**, and `TauCeti.IsLeftAlmostSplit.indecomposable`: the source of a left almost
  split morphism is indecomposable.
* `TauCeti.IsRightAlmostSplit.exists_isSplitMono_of_isIrreducibleMorphism` and
  `TauCeti.IsLeftAlmostSplit.exists_isSplitEpi_of_isIrreducibleMorphism`: **an irreducible
  morphism factors through an almost split morphism by a split mono, resp. a split epi.**
* `TauCeti.IsRightAlmostSplit.epi_of_epi` and `TauCeti.IsLeftAlmostSplit.mono_of_mono`: a right
  almost split morphism is an epimorphism as soon as *some* non-split-epi into its target is one.
* `TauCeti.IsRightAlmostSplit.not_projective` and `TauCeti.IsLeftAlmostSplit.not_injective`: **the
  target of an epimorphic right almost split morphism is not projective**, and dually the source of
  a monomorphic left almost split morphism is not injective.
* `TauCeti.IsRightAlmostSplit.not_isSplitMono`, `.not_mono` and `.ne_zero` and their left-hand
  duals: **an epimorphic right almost split morphism is neither a split monomorphism nor — in a
  balanced category — a monomorphism, and it is nonzero.**
* Invariance under isomorphisms of the source and the target,
  `TauCeti.isRightAlmostSplit_comp_iso_iff`, `TauCeti.isRightAlmostSplit_iso_comp_iff` and their
  left-hand analogues, so the notions descend to a skeleton.

## Implementation notes

The definitions are conjunctions rather than structures, matching the shape of
`TauCeti.IsIrreducibleMorphism`; their bodies are not exposed outside this module, so
`TauCeti.isRightAlmostSplit_iff` and `TauCeti.isLeftAlmostSplit_iff` are the introduction rules.

Both predicates are stated for `f : X ⟶ Y` in the same category, the right-hand notion being a
condition at the target `Y` and the left-hand one a condition at the source `X`. The lifting
quantifiers range over *all* objects of the ambient category. For the Auslander-Reiten theory of a
finite-dimensional algebra that is the intended reading: the ambient category there is the
finite-dimensional one, as it already is for `TauCeti.IsIrreducibleMorphism`. The distinction is
not cosmetic — quantifying an almost-split sequence's lifting properties over a category of
representations with no finiteness restriction states a strictly stronger condition, and the
existence theorem for such sequences is false in that form (Paquette, *A non-existence theorem for
almost split sequences*, arXiv:1104.1195, exhibits infinite-dimensional indecomposable
representations of the Kronecker quiver that end no almost-split sequence). Instantiating `C` at
the finite-dimensional subcategory is what recovers the intended notion.

A right almost split morphism may well be zero: over a field, the map `0 ⟶ k` is right almost
split, every non-split-epi into the simple projective `k` being zero. So there is no unconditional
analogue here of `TauCeti.IsIrreducibleMorphism.ne_zero`, and this is not an oversight — it is the
boundary case of a projective target, where the almost split morphism is the inclusion of the
radical. `TauCeti.IsRightAlmostSplit.ne_zero` therefore assumes `[Epi f]`, which is exactly what
that boundary case fails.

Indecomposability of the target is proved directly from the definition rather than through
endomorphism rings, so it needs no additivity, no finiteness and no field: given `Y ≅ A ⊞ B` with
both summands nonzero, neither inclusion `A ⟶ Y` nor `B ⟶ Y` is a split epimorphism (a section of
one of them retracts `A ⊞ B` onto that summand along its inclusion, and the two complementary
structure maps then compose to `0`, collapsing the other summand), so both factor through `f`, and
`CategoryTheory.Limits.biprod.desc` assembles the two factorizations into a section of `f`.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995), V.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.1.
* C. Paquette, *A non-existence theorem for almost split sequences*, arXiv:1104.1195 (2011).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### The definitions -/

/-- **A right almost split morphism**: one that is not a split epimorphism, and through which
every morphism to its target that is not a split epimorphism factors.

The negative clause is what makes the notion nonvacuous: without it every split epimorphism would
qualify, the identity among them. With it, a right almost split morphism is in particular not an
isomorphism (`TauCeti.IsRightAlmostSplit.not_isIso`) and its target is indecomposable
(`TauCeti.IsRightAlmostSplit.indecomposable`). -/
def IsRightAlmostSplit {X Y : C} (f : X ⟶ Y) : Prop :=
  ¬ IsSplitEpi f ∧ ∀ (Z : C) (g : Z ⟶ Y), ¬ IsSplitEpi g → ∃ h : Z ⟶ X, h ≫ f = g

/-- **A left almost split morphism**: one that is not a split monomorphism, and through which
every morphism out of its source that is not a split monomorphism factors. This is the condition
of `TauCeti.IsRightAlmostSplit` read in the opposite category
(`TauCeti.isRightAlmostSplit_op_iff`). -/
def IsLeftAlmostSplit {X Y : C} (f : X ⟶ Y) : Prop :=
  ¬ IsSplitMono f ∧ ∀ (Z : C) (g : X ⟶ Z), ¬ IsSplitMono g → ∃ h : Y ⟶ Z, f ≫ h = g

variable {X Y : C} {f : X ⟶ Y}

/-- **The two clauses of being right almost split**, spelled out. This is both the introduction
rule — the body of `TauCeti.IsRightAlmostSplit` is not exposed outside this module — and the
elimination rule; the components are also available as
`TauCeti.IsRightAlmostSplit.not_isSplitEpi` and `TauCeti.IsRightAlmostSplit.factors`. -/
theorem isRightAlmostSplit_iff :
    IsRightAlmostSplit f ↔
      ¬ IsSplitEpi f ∧ ∀ (Z : C) (g : Z ⟶ Y), ¬ IsSplitEpi g → ∃ h : Z ⟶ X, h ≫ f = g :=
  Iff.rfl

/-- **The two clauses of being left almost split**, spelled out; the introduction and elimination
rule for `TauCeti.IsLeftAlmostSplit`. -/
theorem isLeftAlmostSplit_iff :
    IsLeftAlmostSplit f ↔
      ¬ IsSplitMono f ∧ ∀ (Z : C) (g : X ⟶ Z), ¬ IsSplitMono g → ∃ h : Y ⟶ Z, f ≫ h = g :=
  Iff.rfl

/-- A right almost split morphism is not a split epimorphism. -/
theorem IsRightAlmostSplit.not_isSplitEpi (hf : IsRightAlmostSplit f) : ¬ IsSplitEpi f := hf.1

/-- **The factorization property**: every morphism to the target of a right almost split morphism
that is not itself a split epimorphism factors through it. -/
theorem IsRightAlmostSplit.factors (hf : IsRightAlmostSplit f) (Z : C) (g : Z ⟶ Y)
    (hg : ¬ IsSplitEpi g) : ∃ h : Z ⟶ X, h ≫ f = g := hf.2 Z g hg

/-- A left almost split morphism is not a split monomorphism. -/
theorem IsLeftAlmostSplit.not_isSplitMono (hf : IsLeftAlmostSplit f) : ¬ IsSplitMono f := hf.1

/-- **The factorization property**: every morphism out of the source of a left almost split
morphism that is not itself a split monomorphism factors through it. -/
theorem IsLeftAlmostSplit.factors (hf : IsLeftAlmostSplit f) (Z : C) (g : X ⟶ Z)
    (hg : ¬ IsSplitMono g) : ∃ h : Y ⟶ Z, f ≫ h = g := hf.2 Z g hg

/-- **A right almost split morphism is not an isomorphism**, an isomorphism being a split epi. -/
theorem IsRightAlmostSplit.not_isIso (hf : IsRightAlmostSplit f) : ¬ IsIso f :=
  fun _ => hf.not_isSplitEpi inferInstance

/-- **A left almost split morphism is not an isomorphism**, an isomorphism being a split mono. -/
theorem IsLeftAlmostSplit.not_isIso (hf : IsLeftAlmostSplit f) : ¬ IsIso f :=
  fun _ => hf.not_isSplitMono inferInstance

/-- An identity is not right almost split. -/
@[simp]
theorem not_isRightAlmostSplit_id (X : C) : ¬ IsRightAlmostSplit (𝟙 X) :=
  fun hf => hf.not_isIso inferInstance

/-- An identity is not left almost split. -/
@[simp]
theorem not_isLeftAlmostSplit_id (X : C) : ¬ IsLeftAlmostSplit (𝟙 X) :=
  fun hf => hf.not_isIso inferInstance

/-! ### Duality -/

-- Mathlib supplies the two instances `[IsSplitMono g] → IsSplitEpi g.op` and
-- `[IsSplitEpi g] → IsSplitMono g.op`; their converses, needed to move the negative clauses of the
-- two predicates across the duality, are not stated there.
private theorem isSplitMono_of_isSplitEpi_op {Z W : C} (g : Z ⟶ W) [IsSplitEpi g.op] :
    IsSplitMono g :=
  IsSplitMono.mk' ⟨(section_ g.op).unop, Quiver.Hom.op_inj (IsSplitEpi.id g.op)⟩

private theorem isSplitEpi_of_isSplitMono_op {Z W : C} (g : Z ⟶ W) [IsSplitMono g.op] :
    IsSplitEpi g :=
  IsSplitEpi.mk' ⟨(retraction g.op).unop, Quiver.Hom.op_inj (IsSplitMono.id g.op)⟩

/-- **The opposite of a left almost split morphism is right almost split**, and conversely: the
two notions are exchanged by passage to the opposite category. -/
@[simp]
theorem isRightAlmostSplit_op_iff : IsRightAlmostSplit f.op ↔ IsLeftAlmostSplit f := by
  constructor
  · refine fun hf => ⟨fun hs => hf.not_isSplitEpi inferInstance, fun Z g hg => ?_⟩
    have hg' : ¬ IsSplitEpi g.op := fun hs => hg (isSplitMono_of_isSplitEpi_op g)
    obtain ⟨h, hh⟩ := hf.factors (Opposite.op Z) g.op hg'
    exact ⟨h.unop, Quiver.Hom.op_inj (by simpa using hh)⟩
  · refine fun hf => ⟨fun hs => hf.not_isSplitMono (isSplitMono_of_isSplitEpi_op f),
      fun Z g hg => ?_⟩
    have hg' : ¬ IsSplitMono g.unop := fun hs => hg (inferInstanceAs (IsSplitEpi g.unop.op))
    obtain ⟨h, hh⟩ := hf.factors Z.unop g.unop hg'
    exact ⟨h.op, Quiver.Hom.unop_inj (by simpa using hh)⟩

/-- **The opposite of a right almost split morphism is left almost split**, and conversely. -/
@[simp]
theorem isLeftAlmostSplit_op_iff : IsLeftAlmostSplit f.op ↔ IsRightAlmostSplit f := by
  constructor
  · refine fun hf => ⟨fun hs => hf.not_isSplitMono inferInstance, fun Z g hg => ?_⟩
    have hg' : ¬ IsSplitMono g.op := fun hs => hg (isSplitEpi_of_isSplitMono_op g)
    obtain ⟨h, hh⟩ := hf.factors (Opposite.op Z) g.op hg'
    exact ⟨h.unop, Quiver.Hom.op_inj (by simpa using hh)⟩
  · refine fun hf => ⟨fun hs => hf.not_isSplitEpi (isSplitEpi_of_isSplitMono_op f),
      fun Z g hg => ?_⟩
    have hg' : ¬ IsSplitEpi g.unop := fun hs => hg (inferInstanceAs (IsSplitMono g.unop.op))
    obtain ⟨h, hh⟩ := hf.factors Z.unop g.unop hg'
    exact ⟨h.op, Quiver.Hom.unop_inj (by simpa using hh)⟩

/-! ### Invariance under isomorphisms of the source and the target -/

/-- **Postcomposing a right almost split morphism with an isomorphism keeps it right almost
split.** -/
theorem IsRightAlmostSplit.comp_iso (hf : IsRightAlmostSplit f) {Y' : C} (e : Y ≅ Y') :
    IsRightAlmostSplit (f ≫ e.hom) := by
  refine ⟨fun _ => hf.not_isSplitEpi (isSplitEpi_of_isSplitEpi_comp_iso f e), fun Z g hg => ?_⟩
  have hg' : ¬ IsSplitEpi (g ≫ e.symm.hom) :=
    fun _ => hg (isSplitEpi_of_isSplitEpi_comp_iso g e.symm)
  obtain ⟨h, hh⟩ := hf.factors Z (g ≫ e.symm.hom) hg'
  exact ⟨h, by simp [reassoc_of% hh]⟩

/-- **Precomposing a right almost split morphism with an isomorphism keeps it right almost
split.** -/
theorem IsRightAlmostSplit.iso_comp (hf : IsRightAlmostSplit f) {X' : C} (e : X' ≅ X) :
    IsRightAlmostSplit (e.hom ≫ f) := by
  refine ⟨fun _ => hf.not_isSplitEpi (isSplitEpi_of_isSplitEpi_comp e.hom f), fun Z g hg => ?_⟩
  obtain ⟨h, hh⟩ := hf.factors Z g hg
  exact ⟨h ≫ e.inv, by simp [hh]⟩

/-- **Precomposing a left almost split morphism with an isomorphism keeps it left almost
split.** -/
theorem IsLeftAlmostSplit.iso_comp (hf : IsLeftAlmostSplit f) {X' : C} (e : X' ≅ X) :
    IsLeftAlmostSplit (e.hom ≫ f) := by
  refine ⟨fun _ => hf.not_isSplitMono (isSplitMono_of_isSplitMono_iso_comp e f), fun Z g hg => ?_⟩
  have hg' : ¬ IsSplitMono (e.symm.hom ≫ g) :=
    fun _ => hg (isSplitMono_of_isSplitMono_iso_comp e.symm g)
  obtain ⟨h, hh⟩ := hf.factors Z (e.symm.hom ≫ g) hg'
  exact ⟨h, by simp [hh]⟩

/-- **Postcomposing a left almost split morphism with an isomorphism keeps it left almost
split.** -/
theorem IsLeftAlmostSplit.comp_iso (hf : IsLeftAlmostSplit f) {Y' : C} (e : Y ≅ Y') :
    IsLeftAlmostSplit (f ≫ e.hom) := by
  refine ⟨fun _ => hf.not_isSplitMono (isSplitMono_of_isSplitMono_comp f e.hom), fun Z g hg => ?_⟩
  obtain ⟨h, hh⟩ := hf.factors Z g hg
  exact ⟨e.inv ≫ h, by simp [hh]⟩

/-- Being right almost split is invariant under an isomorphism of the target. -/
@[simp]
theorem isRightAlmostSplit_comp_iso_iff {Y' : C} (e : Y ≅ Y') :
    IsRightAlmostSplit (f ≫ e.hom) ↔ IsRightAlmostSplit f := by
  refine ⟨fun hf => ?_, fun hf => hf.comp_iso e⟩
  have h : (f ≫ e.hom) ≫ e.symm.hom = f := by simp
  exact h ▸ hf.comp_iso e.symm

/-- Being right almost split is invariant under an isomorphism of the source. -/
@[simp]
theorem isRightAlmostSplit_iso_comp_iff {X' : C} (e : X' ≅ X) :
    IsRightAlmostSplit (e.hom ≫ f) ↔ IsRightAlmostSplit f := by
  refine ⟨fun hf => ?_, fun hf => hf.iso_comp e⟩
  have h : e.symm.hom ≫ e.hom ≫ f = f := by simp
  exact h ▸ hf.iso_comp e.symm

/-- Being left almost split is invariant under an isomorphism of the source. -/
@[simp]
theorem isLeftAlmostSplit_iso_comp_iff {X' : C} (e : X' ≅ X) :
    IsLeftAlmostSplit (e.hom ≫ f) ↔ IsLeftAlmostSplit f := by
  refine ⟨fun hf => ?_, fun hf => hf.iso_comp e⟩
  have h : e.symm.hom ≫ e.hom ≫ f = f := by simp
  exact h ▸ hf.iso_comp e.symm

/-- Being left almost split is invariant under an isomorphism of the target. -/
@[simp]
theorem isLeftAlmostSplit_comp_iso_iff {Y' : C} (e : Y ≅ Y') :
    IsLeftAlmostSplit (f ≫ e.hom) ↔ IsLeftAlmostSplit f := by
  refine ⟨fun hf => ?_, fun hf => hf.comp_iso e⟩
  have h : (f ≫ e.hom) ≫ e.symm.hom = f := by simp
  exact h ▸ hf.comp_iso e.symm

/-! ### Interaction with epimorphisms, monomorphisms, and irreducible morphisms -/

/-- **A right almost split morphism is an epimorphism as soon as some non-split epimorphism into
its target is one.** For a module category this is how the almost split morphism onto a
non-projective module is seen to be surjective: a projective cover of it is an epimorphism and,
the module being non-projective, not a split one. -/
theorem IsRightAlmostSplit.epi_of_epi (hf : IsRightAlmostSplit f) {Z : C} (g : Z ⟶ Y) [Epi g]
    (hg : ¬ IsSplitEpi g) : Epi f := by
  obtain ⟨h, hh⟩ := hf.factors Z g hg
  have : Epi (h ≫ f) := hh ▸ ‹Epi g›
  exact _root_.CategoryTheory.epi_of_epi h f

/-- **A left almost split morphism is a monomorphism as soon as some non-split monomorphism out of
its source is one.** -/
theorem IsLeftAlmostSplit.mono_of_mono (hf : IsLeftAlmostSplit f) {Z : C} (g : X ⟶ Z) [Mono g]
    (hg : ¬ IsSplitMono g) : Mono f := by
  obtain ⟨h, hh⟩ := hf.factors Z g hg
  have : Mono (f ≫ h) := hh ▸ ‹Mono g›
  exact _root_.CategoryTheory.mono_of_mono f h

/-- **An epimorphic right almost split morphism is not a split monomorphism**: a splitting on that
side would make it an isomorphism. -/
theorem IsRightAlmostSplit.not_isSplitMono (hf : IsRightAlmostSplit f) [Epi f] :
    ¬ IsSplitMono f := fun _ => hf.not_isIso (isIso_of_epi_of_isSplitMono f)

/-- **A monomorphic left almost split morphism is not a split epimorphism**, dually to
`TauCeti.IsRightAlmostSplit.not_isSplitMono`. -/
theorem IsLeftAlmostSplit.not_isSplitEpi (hf : IsLeftAlmostSplit f) [Mono f] :
    ¬ IsSplitEpi f := fun _ => hf.not_isIso (isIso_of_mono_of_isSplitEpi f)

/-- In a balanced category an epimorphic right almost split morphism is not a monomorphism: it
would otherwise be an isomorphism. -/
theorem IsRightAlmostSplit.not_mono [Balanced C] (hf : IsRightAlmostSplit f) [Epi f] :
    ¬ Mono f := fun _ => hf.not_isIso (isIso_of_mono_of_epi f)

/-- In a balanced category a monomorphic left almost split morphism is not an epimorphism, dually
to `TauCeti.IsRightAlmostSplit.not_mono`. -/
theorem IsLeftAlmostSplit.not_epi [Balanced C] (hf : IsLeftAlmostSplit f) [Mono f] :
    ¬ Epi f := fun _ => hf.not_isIso (isIso_of_mono_of_epi f)

/-- **An epimorphic right almost split morphism is nonzero.** A zero epimorphism forces its target
to be a zero object, and the zero morphism into a zero object is a split epimorphism. -/
theorem IsRightAlmostSplit.ne_zero [HasZeroMorphisms C] (hf : IsRightAlmostSplit f) [Epi f] :
    f ≠ 0 := fun h => by
  have hid : 𝟙 Y = 0 := (cancel_epi f).mp (by simp [h])
  exact hf.not_isSplitEpi (IsSplitEpi.mk' ⟨0, by simp [hid]⟩)

/-- **A monomorphic left almost split morphism is nonzero**, dually to
`TauCeti.IsRightAlmostSplit.ne_zero`. -/
theorem IsLeftAlmostSplit.ne_zero [HasZeroMorphisms C] (hf : IsLeftAlmostSplit f) [Mono f] :
    f ≠ 0 := fun h => by
  have hid : 𝟙 X = 0 := (cancel_mono f).mp (by simp [h])
  exact hf.not_isSplitMono (IsSplitMono.mk' ⟨0, by simp [hid]⟩)

/-- **An irreducible morphism into the target of a right almost split morphism factors through it
by a split monomorphism**, so its source is a retract of the source of the almost split morphism.

This is why the middle term of an almost-split sequence receives all the irreducible morphisms
into its right-hand end. -/
theorem IsRightAlmostSplit.exists_isSplitMono_of_isIrreducibleMorphism (hf : IsRightAlmostSplit f)
    {Z : C} {g : Z ⟶ Y} (hg : IsIrreducibleMorphism g) :
    ∃ h : Z ⟶ X, IsSplitMono h ∧ h ≫ f = g := by
  obtain ⟨h, hh⟩ := hf.factors Z g hg.not_isSplitEpi
  exact ⟨h, hg.isSplitMono_of_not_isSplitEpi hh hf.not_isSplitEpi, hh⟩

/-- **An irreducible morphism out of the source of a left almost split morphism factors through it
by a split epimorphism**, so its target is a retract of the target of the almost split
morphism. -/
theorem IsLeftAlmostSplit.exists_isSplitEpi_of_isIrreducibleMorphism (hf : IsLeftAlmostSplit f)
    {Z : C} {g : X ⟶ Z} (hg : IsIrreducibleMorphism g) :
    ∃ h : Y ⟶ Z, IsSplitEpi h ∧ f ≫ h = g := by
  obtain ⟨h, hh⟩ := hf.factors Z g hg.not_isSplitMono
  exact ⟨h, hg.isSplitEpi_of_not_isSplitMono hh hf.not_isSplitMono, hh⟩

/-! ### Projectivity and injectivity of the almost split end -/

/-- **The target of an epimorphic right almost split morphism is not projective.** Were it
projective, its identity would factor through the epimorphism `f`, which is exactly a section of
`f`, and `f` is not a split epimorphism. -/
theorem IsRightAlmostSplit.not_projective (hf : IsRightAlmostSplit f) [Epi f] : ¬ Projective Y :=
  fun _ => hf.not_isSplitEpi
    (IsSplitEpi.mk' ⟨Projective.factorThru (𝟙 Y) f, Projective.factorThru_comp _ _⟩)

/-- **The source of a monomorphic left almost split morphism is not injective**, dually to
`TauCeti.IsRightAlmostSplit.not_projective`: its identity would factor through the monomorphism
`f`, retracting it. -/
theorem IsLeftAlmostSplit.not_injective (hf : IsLeftAlmostSplit f) [Mono f] : ¬ Injective X :=
  fun _ => hf.not_isSplitMono
    (IsSplitMono.mk' ⟨Injective.factorThru (𝟙 X) f, Injective.comp_factorThru _ _⟩)

/-! ### Indecomposability of the almost split end -/

section Indecomposable

variable [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- **The target of a right almost split morphism is indecomposable.** So the indecomposability of
the right-hand end of an almost-split sequence is a consequence of its lifting property rather
than a hypothesis on it. -/
theorem IsRightAlmostSplit.indecomposable (hf : IsRightAlmostSplit f) : Indecomposable Y := by
  refine ⟨fun hY => hf.not_isSplitEpi (IsSplitEpi.mk' ⟨0, hY.eq_of_src _ _⟩), fun A B e => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  -- A section of an inclusion `A ⟶ Y` retracts `A ⊞ B` onto `A` along `biprod.inl`, and
  -- `biprod.inl ≫ biprod.snd = 0` then collapses `B`; symmetrically for the other inclusion.
  have hiA : ¬ IsSplitEpi (biprod.inl ≫ e.inv : A ⟶ Y) := by
    intro h
    obtain ⟨s, hs⟩ := h.exists_splitEpi.some
    have h₁ : s ≫ biprod.inl = e.hom := by
      rw [← cancel_mono e.inv, e.hom_inv_id, Category.assoc]; exact hs
    refine hB ?_
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 B = biprod.inr ≫ (e.inv ≫ s ≫ biprod.inl) ≫ biprod.snd := by
          rw [h₁, e.inv_hom_id, Category.id_comp, biprod.inr_snd]
      _ = 0 := by simp
  have hiB : ¬ IsSplitEpi (biprod.inr ≫ e.inv : B ⟶ Y) := by
    intro h
    obtain ⟨s, hs⟩ := h.exists_splitEpi.some
    have h₁ : s ≫ biprod.inr = e.hom := by
      rw [← cancel_mono e.inv, e.hom_inv_id, Category.assoc]; exact hs
    refine hA ?_
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 A = biprod.inl ≫ (e.inv ≫ s ≫ biprod.inr) ≫ biprod.fst := by
          rw [h₁, e.inv_hom_id, Category.id_comp, biprod.inl_fst]
      _ = 0 := by simp
  obtain ⟨u, hu⟩ := hf.factors A _ hiA
  obtain ⟨v, hv⟩ := hf.factors B _ hiB
  refine hf.not_isSplitEpi (IsSplitEpi.mk' ⟨e.hom ≫ biprod.desc u v, ?_⟩)
  have key : biprod.desc u v ≫ f = e.inv := by
    apply biprod.hom_ext' <;> simp [hu, hv]
  rw [Category.assoc, key, e.hom_inv_id]

/-- **The source of a left almost split morphism is indecomposable**, dually to
`TauCeti.IsRightAlmostSplit.indecomposable`. -/
theorem IsLeftAlmostSplit.indecomposable (hf : IsLeftAlmostSplit f) : Indecomposable X := by
  refine ⟨fun hX => hf.not_isSplitMono (IsSplitMono.mk' ⟨0, hX.eq_of_src _ _⟩), fun A B e => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  -- Dually, a retraction of a projection `X ⟶ A` sections `A ⊞ B` off `A` along `biprod.fst`,
  -- and `biprod.inr ≫ biprod.fst = 0` then collapses `B`.
  have hpA : ¬ IsSplitMono (e.hom ≫ biprod.fst : X ⟶ A) := by
    intro h
    obtain ⟨r, hr⟩ := h.exists_splitMono.some
    have h₁ : biprod.fst ≫ r = e.inv := by
      rw [← cancel_epi e.hom, e.hom_inv_id, ← Category.assoc]; exact hr
    refine hB ?_
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 B = biprod.inr ≫ ((biprod.fst ≫ r) ≫ e.hom) ≫ biprod.snd := by
          rw [h₁, e.inv_hom_id, Category.id_comp, biprod.inr_snd]
      _ = 0 := by simp
  have hpB : ¬ IsSplitMono (e.hom ≫ biprod.snd : X ⟶ B) := by
    intro h
    obtain ⟨r, hr⟩ := h.exists_splitMono.some
    have h₁ : biprod.snd ≫ r = e.inv := by
      rw [← cancel_epi e.hom, e.hom_inv_id, ← Category.assoc]; exact hr
    refine hA ?_
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 A = biprod.inl ≫ ((biprod.snd ≫ r) ≫ e.hom) ≫ biprod.fst := by
          rw [h₁, e.inv_hom_id, Category.id_comp, biprod.inl_fst]
      _ = 0 := by simp
  obtain ⟨u, hu⟩ := hf.factors A _ hpA
  obtain ⟨v, hv⟩ := hf.factors B _ hpB
  refine hf.not_isSplitMono (IsSplitMono.mk' ⟨biprod.lift u v ≫ e.inv, ?_⟩)
  have key : f ≫ biprod.lift u v = e.hom := by
    apply biprod.hom_ext <;> simp [hu, hv]
  rw [← Category.assoc, key, e.hom_inv_id]

end Indecomposable

end TauCeti
