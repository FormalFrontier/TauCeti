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
end is not projective, and **every one of those is a theorem**, not a hypothesis.  Non-splitness and
indecomposability already follow from the lifting properties alone, so they are available from the
two lifting fields through `TauCeti.isEmpty_splitting_of_isRightAlmostSplit` and
`TauCeti.IsRightAlmostSplit.indecomposable`; non-projectivity of the right-hand end and
non-injectivity of the left-hand end need exactness too, and are
`CategoryTheory.ShortComplex.IsAlmostSplit.not_projective_X₃` and
`CategoryTheory.ShortComplex.IsAlmostSplit.not_injective_X₁` below.  Assuming redundant clauses
would only make the predicate harder to establish.

Exactness also removes the degenerate case the morphism-level notions leave open.  A right almost
split morphism may be zero — over a field, `0 ⟶ k` is right almost split — but the second map of an
almost-split sequence is an epimorphism onto a nonzero object and so is never zero
(`CategoryTheory.ShortComplex.IsAlmostSplit.ne_zero_g`), and dually for the first map.

## Main definitions

* `CategoryTheory.ShortComplex.IsAlmostSplit`: a short complex is almost split when it is short
  exact, its first map is left almost split and its second map is right almost split.

## Main results

* `CategoryTheory.ShortComplex.IsAlmostSplit.not_isZero_X₁`, `.not_isZero_X₂` and `.not_isZero_X₃`:
  **all three objects of an almost-split sequence are nonzero**, because neither of its maps is.
* `CategoryTheory.ShortComplex.IsAlmostSplit.not_projective_X₃` and `.not_injective_X₁`: **its
  right-hand end is not projective and its left-hand end is not injective.**  A projective
  right-hand end would section the sequence, an injective left-hand end would retract it.
* `CategoryTheory.ShortComplex.isAlmostSplit_op_iff`: **being almost split is self-dual**, the two
  lifting conditions being exchanged by passage to the opposite category, so every statement about
  the left-hand end dualizes to one about the right-hand end.
* `CategoryTheory.ShortComplex.isAlmostSplit_iff_of_iso`: the notion is invariant under an
  isomorphism of short complexes, so it descends to isomorphism classes of sequences.
* `TauCeti.isEmpty_splitting_of_isRightAlmostSplit` and
  `TauCeti.isEmpty_splitting_of_isLeftAlmostSplit`: **a short complex one of whose maps is almost
  split on the corresponding side has no splitting**, so an almost-split sequence does not split.

## Implementation notes

The lifting quantifiers of `TauCeti.IsLeftAlmostSplit` and `TauCeti.IsRightAlmostSplit` range over
all objects of the ambient category, and the ambient category intended for Auslander-Reiten theory
is the finite-dimensional one; see the implementation notes of
`TauCeti/CategoryTheory/AlmostSplit/Basic.lean`, where the failure of the unrestricted form is
recorded.  Nothing in this file constrains `C` beyond what each statement needs, so instantiating it
at the finite-dimensional subcategory of representations of a finite-dimensional algebra recovers
the intended notion.

The declarations about an almost-split sequence sit in the `CategoryTheory.ShortComplex` namespace,
so that `hS.op` and `S.IsAlmostSplit` read as dot notation on Mathlib's
`CategoryTheory.ShortComplex`; the two morphism-level lifting conditions they are assembled from
stay in `TauCeti`, and so do the two non-splitting results, which are statements about a short
complex carrying one almost split map rather than about an almost-split sequence.

Those two results sit in their own preadditive section rather than in the ambient
`CategoryTheory.Limits.HasZeroMorphisms` one: `CategoryTheory.ShortComplex.Splitting` is stated for
the zero morphisms coming from the additive structure, which is not syntactically the ambient
instance, so sharing one variable block would leave the two `ShortComplex C`s unequal.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995), V.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.1.
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti

universe v u

namespace TauCeti

section Splitting

variable {C : Type u} [Category.{v} C] [Preadditive C] {S : ShortComplex C}

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

end Splitting

end TauCeti

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {S S₁ S₂ : ShortComplex C}

/-- **An almost-split (Auslander-Reiten) sequence**: a short exact sequence whose first map is left
almost split and whose second map is right almost split.

The textbook additional demands — that the sequence does not split, that its two ends are
indecomposable, and that its right-hand end is not projective — are consequences of these three
clauses (`TauCeti.isEmpty_splitting_of_isRightAlmostSplit`,
`TauCeti.IsLeftAlmostSplit.indecomposable`, `TauCeti.IsRightAlmostSplit.indecomposable`,
`CategoryTheory.ShortComplex.IsAlmostSplit.not_projective_X₃`) and are therefore not fields. -/
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

/-! ### The maps of an almost-split sequence -/

/-- **The first map of an almost-split sequence is nonzero**: short exactness makes it a
monomorphism, and a zero monomorphism has a zero source, whose identity would split it. -/
theorem ne_zero_f (hS : IsAlmostSplit S) : S.f ≠ 0 := by
  have := hS.shortExact.mono_f
  exact hS.isLeftAlmostSplit_f.ne_zero

/-- **The second map of an almost-split sequence is nonzero**, dually to
`CategoryTheory.ShortComplex.IsAlmostSplit.ne_zero_f`. -/
theorem ne_zero_g (hS : IsAlmostSplit S) : S.g ≠ 0 := by
  have := hS.shortExact.epi_g
  exact hS.isRightAlmostSplit_g.ne_zero

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

/-! ### Projectivity and injectivity of the ends -/

/-- **The right-hand end of an almost-split sequence is not projective.**  This is where exactness
enters: it supplies the epimorphism `S.g` that
`TauCeti.IsRightAlmostSplit.not_projective` asks for, and a projective right-hand end would then
section the sequence. -/
theorem not_projective_X₃ (hS : IsAlmostSplit S) : ¬ Projective S.X₃ := by
  have := hS.shortExact.epi_g
  exact hS.isRightAlmostSplit_g.not_projective

/-- **The left-hand end of an almost-split sequence is not injective**, dually to
`CategoryTheory.ShortComplex.IsAlmostSplit.not_projective_X₃`: exactness supplies the monomorphism
`S.f`, and an injective left-hand end would retract the sequence. -/
theorem not_injective_X₁ (hS : IsAlmostSplit S) : ¬ Injective S.X₁ := by
  have := hS.shortExact.mono_f
  exact hS.isLeftAlmostSplit_f.not_injective

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
theorem isAlmostSplit_of_iso (e : S₁ ≅ S₂) (hS : IsAlmostSplit S₁) : IsAlmostSplit S₂ where
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
  ⟨isAlmostSplit_of_iso e, isAlmostSplit_of_iso e.symm⟩

end CategoryTheory.ShortComplex
