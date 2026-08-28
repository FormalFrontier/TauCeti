/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Simple
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
sequence-level notion can be assembled from them, and proves the two facts that make the
definition of an almost-split sequence non-redundant: **the target of a right almost split
morphism is indecomposable**, and dually **the source of a left almost split morphism is
indecomposable**. Neither end of an almost-split sequence has to be *assumed* indecomposable — the
lifting properties already force it — and a short complex whose `g` is right almost split admits
no splitting, so non-splitness is likewise a consequence rather than a hypothesis.

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
* `TauCeti.IsRightAlmostSplit.indecomposable`: **the target of a right almost split morphism is
  indecomposable**, and `TauCeti.IsLeftAlmostSplit.indecomposable`: the source of a left almost
  split morphism is indecomposable.
* `TauCeti.isEmpty_splitting_of_isRightAlmostSplit` and
  `TauCeti.isEmpty_splitting_of_isLeftAlmostSplit`: a short complex one of whose maps is almost
  split on the corresponding side has no splitting.
* `TauCeti.IsRightAlmostSplit.exists_isSplitMono_of_isIrreducibleMorphism` and
  `TauCeti.IsLeftAlmostSplit.exists_isSplitEpi_of_isIrreducibleMorphism`: **an irreducible
  morphism factors through an almost split morphism by a split mono, resp. a split epi.**
* `TauCeti.IsRightAlmostSplit.epi_of_epi` and `TauCeti.IsLeftAlmostSplit.mono_of_mono`: a right
  almost split morphism is an epimorphism as soon as *some* non-split-epi into its target is one.
* Invariance under isomorphisms of the source and the target,
  `TauCeti.isRightAlmostSplit_comp_iso_iff`, `TauCeti.isRightAlmostSplit_iso_comp_iff` and their
  left-hand analogues, so the notions descend to a skeleton.

Mathlib's `CategoryTheory.Biprod.isIso_inl_iff_isZero` says that an invertible `biprod.inl`
forces the other summand to vanish, and remarks that the three variations on it "are likely not
separately useful". The indecomposability arguments below consume all four structure maps, so the
three remaining cases are recorded here as transports of the Mathlib lemma —
`TauCeti.isZero_of_isIso_biprod_inr` along `CategoryTheory.Limits.biprod.braiding`, and
`TauCeti.isZero_of_isIso_biprod_fst`, `TauCeti.isZero_of_isIso_biprod_snd` by inverting
`biprod.inl ≫ biprod.fst = 𝟙` and `biprod.inr ≫ biprod.snd = 𝟙`.

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
existence theorem for such sequences is false in that form (Paquette, *A note on almost split
sequences*, arXiv:1104.1195, exhibits infinite-dimensional indecomposable representations of the
Kronecker quiver that end no almost-split sequence). Instantiating `C` at the finite-dimensional
subcategory is what recovers the intended notion.

A right almost split morphism may well be zero: over a field, the map `0 ⟶ k` is right almost
split, every non-split-epi into the simple projective `k` being zero. So there is no analogue here
of `TauCeti.IsIrreducibleMorphism.ne_zero`, and this is not an oversight — it is the boundary case
of a projective target, where the almost split morphism is the inclusion of the radical.

Indecomposability of the target is proved directly from the definition rather than through
endomorphism rings, so it needs no finiteness and no field: given `Y ≅ A ⊞ B` with both summands
nonzero, neither inclusion `A ⟶ Y` nor `B ⟶ Y` is a split epimorphism (a split mono that is a
split epi is invertible, and an invertible `biprod.inl` kills `B`), so both factor through `f`, and
`CategoryTheory.Limits.biprod.total` assembles the two factorizations into a section of `f`.

## References

This builds the right and left almost split conditions named in Layer 6 (Auslander-Reiten theory)
of `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md` as the two lifting
clauses of an almost-split sequence, together with the indecomposability of its ends and its
non-splitness, which that layer lists as separate requirements on the sequence.

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995), V.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Invertible structure maps of a binary biproduct -/

section Biproduct

variable [Preadditive C] [HasBinaryBiproducts C] (A B : C)

/-- **If the second inclusion of a binary biproduct is invertible, the first summand is zero**:
`CategoryTheory.Biprod.isIso_inl_iff_isZero` transported along the braiding, which carries
`biprod.inr : B ⟶ A ⊞ B` to `biprod.inl : B ⟶ B ⊞ A`. -/
theorem isZero_of_isIso_biprod_inr [IsIso (biprod.inr : B ⟶ A ⊞ B)] : IsZero A := by
  have h : (biprod.inr : B ⟶ A ⊞ B) ≫ (biprod.braiding A B).hom = biprod.inl := by
    apply biprod.hom_ext <;> simp [biprod.braiding]
  have : IsIso (biprod.inl : B ⟶ B ⊞ A) := by rw [← h]; infer_instance
  exact (Biprod.isIso_inl_iff_isZero B A).mp this

/-- **If the first projection of a binary biproduct is invertible, the second summand is zero**:
`biprod.inl ≫ biprod.fst = 𝟙` makes `biprod.inl` the inverse of `biprod.fst`, so
`CategoryTheory.Biprod.isIso_inl_iff_isZero` applies. -/
theorem isZero_of_isIso_biprod_fst [IsIso (biprod.fst : A ⊞ B ⟶ A)] : IsZero B := by
  have h : inv (biprod.fst : A ⊞ B ⟶ A) = biprod.inl :=
    IsIso.inv_eq_of_inv_hom_id biprod.inl_fst
  have : IsIso (biprod.inl : A ⟶ A ⊞ B) := by rw [← h]; infer_instance
  exact (Biprod.isIso_inl_iff_isZero A B).mp this

/-- **If the second projection of a binary biproduct is invertible, the first summand is zero**:
`biprod.inr ≫ biprod.snd = 𝟙` makes `biprod.inr` the inverse of `biprod.snd`, so
`TauCeti.isZero_of_isIso_biprod_inr` applies. -/
theorem isZero_of_isIso_biprod_snd [IsIso (biprod.snd : A ⊞ B ⟶ B)] : IsZero A := by
  have h : inv (biprod.snd : A ⊞ B ⟶ B) = biprod.inr :=
    IsIso.inv_eq_of_inv_hom_id biprod.inr_snd
  have : IsIso (biprod.inr : B ⟶ A ⊞ B) := by rw [← h]; infer_instance
  exact isZero_of_isIso_biprod_inr A B

end Biproduct

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
of `TauCeti.IsRightAlmostSplit` read in the opposite category. -/
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

/-! ### Invariance under isomorphisms of the source and the target -/

/-- **Postcomposing a right almost split morphism with an isomorphism keeps it right almost
split.** -/
theorem IsRightAlmostSplit.comp_iso (hf : IsRightAlmostSplit f) {Y' : C} (e : Y ≅ Y') :
    IsRightAlmostSplit (f ≫ e.hom) := by
  refine ⟨fun _ => hf.not_isSplitEpi (isSplitEpi_of_isSplitEpi_comp_iso f e), fun Z g hg => ?_⟩
  have hg' : ¬ IsSplitEpi (g ≫ e.symm.hom) :=
    fun _ => hg (isSplitEpi_of_isSplitEpi_comp_iso g e.symm)
  obtain ⟨h, hh⟩ := hf.factors Z (g ≫ e.symm.hom) hg'
  exact ⟨h, by rw [← Category.assoc, hh]; simp⟩

/-- **Precomposing a right almost split morphism with an isomorphism keeps it right almost
split.** -/
theorem IsRightAlmostSplit.iso_comp (hf : IsRightAlmostSplit f) {X' : C} (e : X' ≅ X) :
    IsRightAlmostSplit (e.hom ≫ f) := by
  refine ⟨fun _ => hf.not_isSplitEpi (isSplitEpi_of_isSplitEpi_comp e.hom f), fun Z g hg => ?_⟩
  obtain ⟨h, hh⟩ := hf.factors Z g hg
  exact ⟨h ≫ e.inv, by rw [Category.assoc, ← Category.assoc e.inv, e.inv_hom_id,
    Category.id_comp, hh]⟩

/-- **Precomposing a left almost split morphism with an isomorphism keeps it left almost
split.** -/
theorem IsLeftAlmostSplit.iso_comp (hf : IsLeftAlmostSplit f) {X' : C} (e : X' ≅ X) :
    IsLeftAlmostSplit (e.hom ≫ f) := by
  refine ⟨fun _ => hf.not_isSplitMono (isSplitMono_of_isSplitMono_iso_comp e f), fun Z g hg => ?_⟩
  have hg' : ¬ IsSplitMono (e.symm.hom ≫ g) :=
    fun _ => hg (isSplitMono_of_isSplitMono_iso_comp e.symm g)
  obtain ⟨h, hh⟩ := hf.factors Z (e.symm.hom ≫ g) hg'
  exact ⟨h, by rw [Category.assoc, hh]; simp⟩

/-- **Postcomposing a left almost split morphism with an isomorphism keeps it left almost
split.** -/
theorem IsLeftAlmostSplit.comp_iso (hf : IsLeftAlmostSplit f) {Y' : C} (e : Y ≅ Y') :
    IsLeftAlmostSplit (f ≫ e.hom) := by
  refine ⟨fun _ => hf.not_isSplitMono (isSplitMono_of_isSplitMono_comp f e.hom), fun Z g hg => ?_⟩
  obtain ⟨h, hh⟩ := hf.factors Z g hg
  exact ⟨e.inv ≫ h, by rw [Category.assoc, ← Category.assoc e.hom, e.hom_inv_id,
    Category.id_comp, hh]⟩

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

/-- **An irreducible morphism into the target of a right almost split morphism factors through it
by a split monomorphism**, so its source is a retract of the source of the almost split morphism.
Indeed the factorization exists because an irreducible morphism is not a split epimorphism, and
then irreducibility applied to that very factorization forces the first factor to split, the
second factor being the almost split morphism, which is not a split epimorphism either.

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

/-! ### Indecomposability of the almost split end -/

section Indecomposable

variable [Preadditive C] [HasBinaryBiproducts C]

/-- **The target of a right almost split morphism is indecomposable.**

It is nonzero, since a morphism to a zero object always splits. And if `Y ≅ A ⊞ B` with both
summands nonzero then neither inclusion `A ⟶ Y` nor `B ⟶ Y` is a split epimorphism — each is a
split monomorphism, so a splitting epimorphism would make it invertible, and an invertible
`biprod.inl` forces `B` to vanish. Both inclusions therefore factor through `f`, and
`CategoryTheory.Limits.biprod.total` glues the two factorizations into a section of `f`,
contradicting that `f` does not split. -/
theorem IsRightAlmostSplit.indecomposable (hf : IsRightAlmostSplit f) : Indecomposable Y := by
  refine ⟨fun hY => hf.not_isSplitEpi (IsSplitEpi.mk' ⟨0, hY.eq_of_src _ _⟩), fun A B e => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  have hiA : ¬ IsSplitEpi (biprod.inl ≫ e.inv : A ⟶ Y) := by
    intro _
    have : IsSplitMono (biprod.inl ≫ e.inv : A ⟶ Y) :=
      IsSplitMono.mk' ⟨e.hom ≫ biprod.fst, by simp⟩
    have : IsIso (biprod.inl ≫ e.inv : A ⟶ Y) := isIso_of_mono_of_isSplitEpi _
    have hinl : IsIso (biprod.inl : A ⟶ A ⊞ B) := by
      have hh : (biprod.inl ≫ e.inv) ≫ e.hom = (biprod.inl : A ⟶ A ⊞ B) := by simp
      rw [← hh]
      infer_instance
    exact hB ((Biprod.isIso_inl_iff_isZero A B).mp hinl)
  have hiB : ¬ IsSplitEpi (biprod.inr ≫ e.inv : B ⟶ Y) := by
    intro _
    have : IsSplitMono (biprod.inr ≫ e.inv : B ⟶ Y) :=
      IsSplitMono.mk' ⟨e.hom ≫ biprod.snd, by simp⟩
    have : IsIso (biprod.inr ≫ e.inv : B ⟶ Y) := isIso_of_mono_of_isSplitEpi _
    have hinr : IsIso (biprod.inr : B ⟶ A ⊞ B) := by
      have hh : (biprod.inr ≫ e.inv) ≫ e.hom = (biprod.inr : B ⟶ A ⊞ B) := by simp
      rw [← hh]
      infer_instance
    exact hA (isZero_of_isIso_biprod_inr A B)
  obtain ⟨u, hu⟩ := hf.factors A _ hiA
  obtain ⟨v, hv⟩ := hf.factors B _ hiB
  refine hf.not_isSplitEpi (IsSplitEpi.mk' ⟨e.hom ≫ (biprod.fst ≫ u + biprod.snd ≫ v), ?_⟩)
  have key : (biprod.fst ≫ u + biprod.snd ≫ v) ≫ f
      = (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ e.inv := by
    simp only [Preadditive.add_comp, Category.assoc, hu, hv]
  rw [Category.assoc, key, biprod.total, Category.id_comp, e.hom_inv_id]

/-- **The source of a left almost split morphism is indecomposable**, dually to
`TauCeti.IsRightAlmostSplit.indecomposable`: the two projections of a nontrivial decomposition of
the source are not split monomorphisms, so both factor through `f`, and the two factorizations
glue into a retraction of `f`. -/
theorem IsLeftAlmostSplit.indecomposable (hf : IsLeftAlmostSplit f) : Indecomposable X := by
  refine ⟨fun hX => hf.not_isSplitMono (IsSplitMono.mk' ⟨0, hX.eq_of_src _ _⟩), fun A B e => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  have hpA : ¬ IsSplitMono (e.hom ≫ biprod.fst : X ⟶ A) := by
    intro _
    have : IsSplitEpi (e.hom ≫ biprod.fst : X ⟶ A) :=
      IsSplitEpi.mk' ⟨biprod.inl ≫ e.inv, by simp⟩
    have : IsIso (e.hom ≫ biprod.fst : X ⟶ A) := isIso_of_mono_of_isSplitEpi _
    have hfst : IsIso (biprod.fst : A ⊞ B ⟶ A) := by
      have hh : e.inv ≫ (e.hom ≫ biprod.fst) = (biprod.fst : A ⊞ B ⟶ A) := by simp
      rw [← hh]
      infer_instance
    exact hB (isZero_of_isIso_biprod_fst A B)
  have hpB : ¬ IsSplitMono (e.hom ≫ biprod.snd : X ⟶ B) := by
    intro _
    have : IsSplitEpi (e.hom ≫ biprod.snd : X ⟶ B) :=
      IsSplitEpi.mk' ⟨biprod.inr ≫ e.inv, by simp⟩
    have : IsIso (e.hom ≫ biprod.snd : X ⟶ B) := isIso_of_mono_of_isSplitEpi _
    have hsnd : IsIso (biprod.snd : A ⊞ B ⟶ B) := by
      have hh : e.inv ≫ (e.hom ≫ biprod.snd) = (biprod.snd : A ⊞ B ⟶ B) := by simp
      rw [← hh]
      infer_instance
    exact hA (isZero_of_isIso_biprod_snd A B)
  obtain ⟨u, hu⟩ := hf.factors A _ hpA
  obtain ⟨v, hv⟩ := hf.factors B _ hpB
  refine hf.not_isSplitMono (IsSplitMono.mk' ⟨(u ≫ biprod.inl + v ≫ biprod.inr) ≫ e.inv, ?_⟩)
  have key : f ≫ (u ≫ biprod.inl + v ≫ biprod.inr)
      = e.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) := by
    simp only [Preadditive.comp_add, ← Category.assoc, hu, hv]
  rw [← Category.assoc, key, biprod.total, Category.comp_id, e.hom_inv_id]

end Indecomposable

/-! ### Almost split maps in a short complex -/

section ShortComplex

variable [Preadditive C] {S : ShortComplex C}

/-- **A short complex whose second map is right almost split does not split.** The `not_split`
clause in the definition of an almost-split sequence is therefore redundant: it is implied by the
right almost split clause alone. -/
theorem isEmpty_splitting_of_isRightAlmostSplit (hg : IsRightAlmostSplit S.g) :
    IsEmpty S.Splitting :=
  ⟨fun s => hg.not_isSplitEpi s.isSplitEpi_g⟩

/-- **A short complex whose first map is left almost split does not split.** -/
theorem isEmpty_splitting_of_isLeftAlmostSplit (hf : IsLeftAlmostSplit S.f) :
    IsEmpty S.Splitting :=
  ⟨fun s => hf.not_isSplitMono s.isSplitMono_f⟩

end ShortComplex

end TauCeti
