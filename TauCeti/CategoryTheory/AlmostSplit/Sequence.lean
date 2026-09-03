/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.CategoryTheory.AlmostSplit.Basic

/-!
# Almost-split (Auslander-Reiten) sequences

An **almost-split sequence**, or **Auslander-Reiten sequence**, is a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` whose first map is left almost split and whose second map is right almost
split.  It is the basic object of Auslander-Reiten theory: `B ⟶ C` absorbs every map into `C` that
is not a split epimorphism, and `A ⟶ B` absorbs every map out of `A` that is not a split
monomorphism, so the sequence records all the "inessential" maps at both of its ends at once.

`TauCeti/CategoryTheory/AlmostSplit/Basic.lean` builds the two lifting conditions on a single
morphism; this file assembles them on a `CategoryTheory.ShortComplex` and develops the consequences
of the assembly, which is where the two conditions start to interact with exactness.

The definition carries only three fields, and this is deliberate: the textbook definition also
demands that the sequence does not split, that both ends are indecomposable, and that the right-hand
end is not projective, and **every one of those is a theorem here**, not a hypothesis.
Non-splitness and indecomposability already follow from the lifting properties alone
(`TauCeti.isEmpty_splitting_of_isRightAlmostSplit`, `TauCeti.IsRightAlmostSplit.indecomposable`);
non-projectivity of the right-hand end and non-injectivity of the left-hand end need exactness too,
and are `TauCeti.IsAlmostSplit.not_projective_X₃` and `TauCeti.IsAlmostSplit.not_injective_X₁`
below.  Assuming redundant clauses would only make the predicate harder to establish.

Exactness also removes the degenerate case the morphism-level notions leave open.  A right almost
split morphism may be zero — over a field, `0 ⟶ k` is right almost split — but the second map of an
almost-split sequence is an epimorphism onto a nonzero object and so is never zero
(`TauCeti.IsAlmostSplit.ne_zero_g`), and dually for the first map.

## Main definitions

* `TauCeti.IsAlmostSplit`: a short complex is almost split when it is short exact, its first map is
  left almost split and its second map is right almost split.

## Main results

* `TauCeti.IsAlmostSplit.indecomposable_X₁` and `TauCeti.IsAlmostSplit.indecomposable_X₃`: **both
  ends of an almost-split sequence are indecomposable**, and all three of its objects are nonzero.
* `TauCeti.IsAlmostSplit.isEmpty_splitting`: **an almost-split sequence does not split.**
* `TauCeti.IsAlmostSplit.not_projective_X₃` and `TauCeti.IsAlmostSplit.not_injective_X₁`: **its
  right-hand end is not projective and its left-hand end is not injective.**  A projective
  right-hand end would section the sequence, an injective left-hand end would retract it.
* `TauCeti.IsAlmostSplit.not_mono_g` and `TauCeti.IsAlmostSplit.not_epi_f`: in a balanced category
  the two maps are strictly an epimorphism and a monomorphism.
* `TauCeti.isAlmostSplit_op_iff`: **being almost split is self-dual**, the two lifting conditions
  being exchanged by passage to the opposite category, so every statement about the left-hand end
  dualizes to one about the right-hand end.
* `TauCeti.isAlmostSplit_iff_of_iso`: the notion is invariant under an isomorphism of short
  complexes, so it descends to isomorphism classes of sequences.
* `TauCeti.IsAlmostSplit.exists_isSplitMono_comp_g_eq`: **every irreducible morphism into the
  right-hand end factors through the middle term by a split monomorphism**, which is what makes the
  middle term of an almost-split sequence the receptacle of the irreducible morphisms into its
  right-hand end, and ties the sequence to the arrows of the Auslander-Reiten quiver.

## Implementation notes

The lifting quantifiers of `TauCeti.IsLeftAlmostSplit` and `TauCeti.IsRightAlmostSplit` range over
all objects of the ambient category, and the ambient category intended for Auslander-Reiten theory
is the finite-dimensional one; see the implementation notes of
`TauCeti/CategoryTheory/AlmostSplit/Basic.lean`, where the failure of the unrestricted form is
recorded.  Nothing in this file constrains `C` beyond what each statement needs, so instantiating it
at the finite-dimensional subcategory of representations of a finite-dimensional algebra recovers
the intended notion.

The results needing a `CategoryTheory.ShortComplex.Splitting` sit in their own preadditive section
rather than in the ambient `CategoryTheory.Limits.HasZeroMorphisms` one: `Splitting` is stated for
the zero morphisms coming from the additive structure, which is not syntactically the ambient
instance, so sharing one variable block would leave the two `ShortComplex C`s unequal.

## References

This is the almost-split sequence of Layer 6 (Auslander-Reiten theory, sublayer 6E) of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, together with the properties
that layer records as clauses of the definition and which are proved here to be consequences of it.

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995), V.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

section ZeroMorphisms

variable [HasZeroMorphisms C] {S S₁ S₂ : ShortComplex C}

/-- **An almost-split (Auslander-Reiten) sequence**: a short exact sequence whose first map is left
almost split and whose second map is right almost split.

The textbook additional demands — that the sequence does not split, that its two ends are
indecomposable, and that its right-hand end is not projective — are consequences of these three
clauses (`TauCeti.IsAlmostSplit.isEmpty_splitting`, `TauCeti.IsAlmostSplit.indecomposable_X₁`,
`TauCeti.IsAlmostSplit.indecomposable_X₃`, `TauCeti.IsAlmostSplit.not_projective_X₃`) and are
therefore not fields. -/
structure IsAlmostSplit (S : ShortComplex C) : Prop where
  /-- An almost-split sequence is a short exact sequence. -/
  shortExact : S.ShortExact
  /-- Its first map is left almost split: every morphism out of the left-hand end that is not a
  split monomorphism factors through the middle term. -/
  isLeftAlmostSplit_f : IsLeftAlmostSplit S.f
  /-- Its second map is right almost split: every morphism into the right-hand end that is not a
  split epimorphism factors through the middle term. -/
  isRightAlmostSplit_g : IsRightAlmostSplit S.g

namespace IsAlmostSplit

/-! ### The exactness data -/

/-- The first map of an almost-split sequence is a monomorphism. -/
theorem mono_f (hS : IsAlmostSplit S) : Mono S.f := hS.shortExact.mono_f

/-- The second map of an almost-split sequence is an epimorphism. -/
theorem epi_g (hS : IsAlmostSplit S) : Epi S.g := hS.shortExact.epi_g

/-- An almost-split sequence is exact at its middle term. -/
theorem exact (hS : IsAlmostSplit S) : S.Exact := hS.shortExact.exact

/-! ### The maps of an almost-split sequence -/

/-- The first map of an almost-split sequence is not a split monomorphism, the negative clause of
the left almost split condition. -/
theorem not_isSplitMono_f (hS : IsAlmostSplit S) : ¬ IsSplitMono S.f :=
  hS.isLeftAlmostSplit_f.not_isSplitMono

/-- The second map of an almost-split sequence is not a split epimorphism, the negative clause of
the right almost split condition. -/
theorem not_isSplitEpi_g (hS : IsAlmostSplit S) : ¬ IsSplitEpi S.g :=
  hS.isRightAlmostSplit_g.not_isSplitEpi

/-- The first map of an almost-split sequence is not an isomorphism. -/
theorem not_isIso_f (hS : IsAlmostSplit S) : ¬ IsIso S.f := hS.isLeftAlmostSplit_f.not_isIso

/-- The second map of an almost-split sequence is not an isomorphism. -/
theorem not_isIso_g (hS : IsAlmostSplit S) : ¬ IsIso S.g := hS.isRightAlmostSplit_g.not_isIso

/-- The second map of an almost-split sequence is not a split monomorphism: it is an epimorphism,
so a splitting on that side would make it an isomorphism. -/
theorem not_isSplitMono_g (hS : IsAlmostSplit S) : ¬ IsSplitMono S.g := fun _ => by
  have := hS.epi_g
  exact hS.not_isIso_g (isIso_of_epi_of_isSplitMono S.g)

/-- The first map of an almost-split sequence is not a split epimorphism, dually to
`TauCeti.IsAlmostSplit.not_isSplitMono_g`. -/
theorem not_isSplitEpi_f (hS : IsAlmostSplit S) : ¬ IsSplitEpi S.f := fun _ => by
  have := hS.mono_f
  exact hS.not_isIso_f (isIso_of_mono_of_isSplitEpi S.f)

/-- **The first map of an almost-split sequence is nonzero.**  A zero monomorphism forces its
source to be a zero object, and the zero morphism out of a zero object is a split monomorphism. -/
theorem ne_zero_f (hS : IsAlmostSplit S) : S.f ≠ 0 := fun h => by
  have := hS.mono_f
  have hid : 𝟙 S.X₁ = 0 := (cancel_mono S.f).mp (by simp [h])
  exact hS.not_isSplitMono_f (IsSplitMono.mk' ⟨0, by simp [hid]⟩)

/-- **The second map of an almost-split sequence is nonzero**, dually to
`TauCeti.IsAlmostSplit.ne_zero_f`. -/
theorem ne_zero_g (hS : IsAlmostSplit S) : S.g ≠ 0 := fun h => by
  have := hS.epi_g
  have hid : 𝟙 S.X₃ = 0 := (cancel_epi S.g).mp (by simp [h])
  exact hS.not_isSplitEpi_g (IsSplitEpi.mk' ⟨0, by simp [hid]⟩)

/-! ### The objects of an almost-split sequence -/

/-- **The left-hand end of an almost-split sequence is nonzero**: it is the source of the nonzero
first map. -/
theorem not_isZero_X₁ (hS : IsAlmostSplit S) : ¬ IsZero S.X₁ := fun h =>
  hS.ne_zero_f (h.eq_of_src _ _)

/-- **The middle term of an almost-split sequence is nonzero**: it receives the nonzero first
map. -/
theorem not_isZero_X₂ (hS : IsAlmostSplit S) : ¬ IsZero S.X₂ := fun h =>
  hS.ne_zero_f (h.eq_of_tgt _ _)

/-- **The right-hand end of an almost-split sequence is nonzero**: it is the target of the nonzero
second map. -/
theorem not_isZero_X₃ (hS : IsAlmostSplit S) : ¬ IsZero S.X₃ := fun h =>
  hS.ne_zero_g (h.eq_of_tgt _ _)

section Biproducts

variable [HasBinaryBiproducts C]

/-- **The left-hand end of an almost-split sequence is indecomposable**, by the left almost split
clause alone. -/
theorem indecomposable_X₁ (hS : IsAlmostSplit S) : Indecomposable S.X₁ :=
  hS.isLeftAlmostSplit_f.indecomposable

/-- **The right-hand end of an almost-split sequence is indecomposable**, by the right almost split
clause alone. -/
theorem indecomposable_X₃ (hS : IsAlmostSplit S) : Indecomposable S.X₃ :=
  hS.isRightAlmostSplit_g.indecomposable

end Biproducts

section Balanced

variable [Balanced C]

/-- In a balanced category the second map of an almost-split sequence is a strict epimorphism: it
is not also a monomorphism, since it would then be an isomorphism. -/
theorem not_mono_g (hS : IsAlmostSplit S) : ¬ Mono S.g := fun _ => by
  have := hS.epi_g
  exact hS.not_isIso_g (isIso_of_mono_of_epi S.g)

/-- In a balanced category the first map of an almost-split sequence is a strict monomorphism,
dually to `TauCeti.IsAlmostSplit.not_mono_g`. -/
theorem not_epi_f (hS : IsAlmostSplit S) : ¬ Epi S.f := fun _ => by
  have := hS.mono_f
  exact hS.not_isIso_f (isIso_of_mono_of_epi S.f)

end Balanced

/-! ### Irreducible morphisms and an almost-split sequence -/

/-- **An irreducible morphism into the right-hand end of an almost-split sequence factors through
its middle term by a split monomorphism.**  So the middle term is the receptacle of the irreducible
morphisms into the right-hand end: each of their sources is a retract of it. -/
theorem exists_isSplitMono_comp_g_eq (hS : IsAlmostSplit S) {Z : C} {u : Z ⟶ S.X₃}
    (hu : IsIrreducibleMorphism u) : ∃ v : Z ⟶ S.X₂, IsSplitMono v ∧ v ≫ S.g = u :=
  hS.isRightAlmostSplit_g.exists_isSplitMono_of_isIrreducibleMorphism hu

/-- **An irreducible morphism out of the left-hand end of an almost-split sequence factors through
its middle term by a split epimorphism**, dually to
`TauCeti.IsAlmostSplit.exists_isSplitMono_comp_g_eq`. -/
theorem exists_isSplitEpi_f_comp_eq (hS : IsAlmostSplit S) {Z : C} {u : S.X₁ ⟶ Z}
    (hu : IsIrreducibleMorphism u) : ∃ v : S.X₂ ⟶ Z, IsSplitEpi v ∧ S.f ≫ v = u :=
  hS.isLeftAlmostSplit_f.exists_isSplitEpi_of_isIrreducibleMorphism hu

/-! ### Duality -/

/-- **The opposite of an almost-split sequence is almost split**: the two lifting clauses are
exchanged by `TauCeti.isLeftAlmostSplit_op_iff` and `TauCeti.isRightAlmostSplit_op_iff`, and the
opposite of a short exact sequence is short exact. -/
theorem op (hS : IsAlmostSplit S) : IsAlmostSplit S.op where
  shortExact := hS.shortExact.op
  isLeftAlmostSplit_f := isLeftAlmostSplit_op_iff.mpr hS.isRightAlmostSplit_g
  isRightAlmostSplit_g := isRightAlmostSplit_op_iff.mpr hS.isLeftAlmostSplit_f

/-- **The sequence underlying an almost-split sequence of the opposite category is almost
split.** -/
theorem unop {S : ShortComplex Cᵒᵖ} (hS : IsAlmostSplit S) : IsAlmostSplit S.unop where
  shortExact := hS.shortExact.unop
  isLeftAlmostSplit_f := isRightAlmostSplit_op_iff.mp hS.isRightAlmostSplit_g
  isRightAlmostSplit_g := isLeftAlmostSplit_op_iff.mp hS.isLeftAlmostSplit_f

end IsAlmostSplit

/-- **Being almost split is a self-dual condition.** -/
@[simp]
theorem isAlmostSplit_op_iff : IsAlmostSplit S.op ↔ IsAlmostSplit S :=
  ⟨IsAlmostSplit.unop, IsAlmostSplit.op⟩

/-- **Being almost split is a self-dual condition**, read from the opposite category. -/
@[simp]
theorem isAlmostSplit_unop_iff {S : ShortComplex Cᵒᵖ} : IsAlmostSplit S.unop ↔ IsAlmostSplit S :=
  ⟨IsAlmostSplit.op, IsAlmostSplit.unop⟩

/-! ### Invariance under isomorphisms of short complexes -/

/-- **Being almost split is invariant under an isomorphism of short complexes**, so it descends to
isomorphism classes of sequences. -/
theorem IsAlmostSplit.of_iso (e : S₁ ≅ S₂) (hS : IsAlmostSplit S₁) : IsAlmostSplit S₂ where
  shortExact := ShortComplex.shortExact_of_iso e hS.shortExact
  isLeftAlmostSplit_f := by
    have key : (asIso e.hom.τ₁).symm.hom ≫ S₁.f ≫ (asIso e.hom.τ₂).hom = S₂.f := by
      simp [← e.hom.comm₁₂]
    exact key ▸ (hS.isLeftAlmostSplit_f.comp_iso (asIso e.hom.τ₂)).iso_comp (asIso e.hom.τ₁).symm
  isRightAlmostSplit_g := by
    have key : (asIso e.hom.τ₂).symm.hom ≫ S₁.g ≫ (asIso e.hom.τ₃).hom = S₂.g := by
      simp [← e.hom.comm₂₃]
    exact key ▸ (hS.isRightAlmostSplit_g.comp_iso (asIso e.hom.τ₃)).iso_comp (asIso e.hom.τ₂).symm

/-- Being almost split is invariant under an isomorphism of short complexes. -/
theorem isAlmostSplit_iff_of_iso (e : S₁ ≅ S₂) : IsAlmostSplit S₁ ↔ IsAlmostSplit S₂ :=
  ⟨IsAlmostSplit.of_iso e, IsAlmostSplit.of_iso e.symm⟩

end ZeroMorphisms

/-! ### Non-splitness, projectivity and injectivity -/

section Preadditive

variable [Preadditive C] {S : ShortComplex C}

namespace IsAlmostSplit

/-- **An almost-split sequence does not split.** -/
theorem isEmpty_splitting (hS : IsAlmostSplit S) : IsEmpty S.Splitting :=
  isEmpty_splitting_of_isRightAlmostSplit hS.isRightAlmostSplit_g

variable [Balanced C]

/-- **The right-hand end of an almost-split sequence is not projective.**  A projective right-hand
end would let the identity factor through the epimorphism `S.g`, splitting the sequence. -/
theorem not_projective_X₃ (hS : IsAlmostSplit S) : ¬ Projective S.X₃ := fun _ =>
  hS.isEmpty_splitting.false hS.shortExact.splittingOfProjective

/-- **The left-hand end of an almost-split sequence is not injective.**  An injective left-hand end
would let the identity factor through the monomorphism `S.f`, splitting the sequence. -/
theorem not_injective_X₁ (hS : IsAlmostSplit S) : ¬ Injective S.X₁ := fun _ =>
  hS.isEmpty_splitting.false hS.shortExact.splittingOfInjective

end IsAlmostSplit

end Preadditive

end TauCeti
