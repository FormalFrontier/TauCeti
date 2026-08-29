/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.AssociatedGraded

/-!
# Homogeneous pieces of the PBW map

The degree-`n` homogeneous part of a symmetric algebra is the span of products of exactly `n`
canonical generators. For a Lie algebra `L` over a commutative ring `R`, the canonical map

`SymmetricAlgebra R L →ₐ[R] gr U(L)`

sends this submodule into the `n`-th PBW graded piece. This file packages the resulting
degreewise linear map and proves that it is surjective.

The proof uses the spanning half of PBW. A word of length exactly `n` maps to the corresponding
product of degree-one classes. A shorter word represents zero in the `n`-th successive quotient.
Consequently every class in that quotient has a homogeneous symmetric representative of degree
`n`.

Injectivity of these component maps is the remaining linear-independence half of the
Poincaré--Birkhoff--Witt theorem. Thus the componentwise surjections isolate the next obstruction
degree by degree, while retaining the global associated-graded map.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.symmetricHomogeneousSubmodule`: the span of products of
  exactly `n` symmetric-algebra generators, for a module over a commutative semiring.
* `TauCeti.UniversalEnvelopingAlgebra.pbwHomogeneousComponentMap`: the degreewise PBW map.
* `TauCeti.UniversalEnvelopingAlgebra.pbwAssociatedGradedMap_apply_homogeneous`: a homogeneous
  element maps to the corresponding direct-sum component.
* `TauCeti.UniversalEnvelopingAlgebra.pbwHomogeneousComponentMap_surjective`: every PBW graded
  piece has a homogeneous symmetric representative of the same degree.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.

This is the degreewise comparison step of the PBW sub-project in Layer 3 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.
-/

public section

open scoped DirectSum

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.Algebra
open TauCeti.Algebra.wordFiltration

universe u v

section Symmetric

variable (R : Type u) (L : Type v) [CommSemiring R] [AddCommMonoid L] [Module R L]

/-- The degree-`n` homogeneous part of `SymmetricAlgebra R L`: the span of products of exactly
`n` canonical generators. -/
noncomputable def symmetricHomogeneousSubmodule (n : ℕ) :
    Submodule R (SymmetricAlgebra R L) :=
  Submodule.span R {p | ∃ l : List L, l.length = n ∧
    (l.map (SymmetricAlgebra.ι R L)).prod = p}

/-- The degree-`n` homogeneous submodule is the span of the products of `n` generators. -/
theorem symmetricHomogeneousSubmodule_def (n : ℕ) :
    symmetricHomogeneousSubmodule R L n =
      Submodule.span R {p | ∃ l : List L, l.length = n ∧
        (l.map (SymmetricAlgebra.ι R L)).prod = p} := (rfl)

/-- A product of `n` symmetric-algebra generators belongs to the degree-`n` homogeneous
submodule. -/
theorem prod_map_ι_mem_symmetricHomogeneousSubmodule (l : List L) :
    (l.map (SymmetricAlgebra.ι R L)).prod ∈
      symmetricHomogeneousSubmodule R L l.length :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

end Symmetric

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The canonical map sends a product of symmetric-algebra generators to the class of the
corresponding word of Lie generators, in the degree given by the length of the word. -/
theorem pbwAssociatedGradedMap_prod_map_ι (l : List L) :
    pbwAssociatedGradedMap R L (l.map (SymmetricAlgebra.ι R L)).prod =
      DirectSum.of (PBWGradedPiece R L) l.length
        (Submodule.Quotient.mk
          (⟨(l.map (_root_.UniversalEnvelopingAlgebra.ι R)).prod,
            prod_map_mem_wordFiltration
              (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap le_rfl⟩ :
            wordFiltration
              (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap l.length)) := by
  rw [map_list_prod]
  have hlist : List.map (pbwAssociatedGradedMap R L)
        (l.map (SymmetricAlgebra.ι R L)) =
      l.map (pbwGradedGenerator R L) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    exact pbwAssociatedGradedMap_ι R L x
  rw [hlist, prod_map_pbwGradedGenerator]

private theorem pbwMap_isHomogeneous (n : ℕ)
    (p : symmetricHomogeneousSubmodule R L n) :
    ∃ x : PBWGradedPiece R L n,
      pbwAssociatedGradedMap R L p = DirectSum.of (PBWGradedPiece R L) n x := by
  have hp : (p : SymmetricAlgebra R L) ∈
      Submodule.span R {q | ∃ l : List L, l.length = n ∧
        (l.map (SymmetricAlgebra.ι R L)).prod = q} := by
    rw [← symmetricHomogeneousSubmodule_def]
    exact p.property
  refine Submodule.span_induction (p := fun a _ ↦
    ∃ x : PBWGradedPiece R L n,
      pbwAssociatedGradedMap R L a = DirectSum.of (PBWGradedPiece R L) n x)
      ?_ ?_ ?_ ?_ hp
  · rintro a ⟨l, hl, rfl⟩
    subst n
    exact ⟨_, pbwAssociatedGradedMap_prod_map_ι R L l⟩
  · exact ⟨0, by simp⟩
  · rintro a b _ _ ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x + y, ?_⟩
    rw [map_add, hx, hy, map_add]
  · rintro r a _ ⟨x, hx⟩
    refine ⟨r • x, ?_⟩
    rw [map_smul, hx]
    exact (DirectSum.of_smul R (M := PBWGradedPiece R L) n r x).symm

/-- The degree-`n` component of the canonical PBW map. Its source is the homogeneous symmetric
submodule, and its target is the `n`-th PBW graded quotient. -/
noncomputable def pbwHomogeneousComponentMap (n : ℕ) :
    symmetricHomogeneousSubmodule R L n →ₗ[R] PBWGradedPiece R L n :=
  (DirectSum.component R ℕ (PBWGradedPiece R L) n).comp <|
    (pbwAssociatedGradedMap R L).toLinearMap.comp
      (symmetricHomogeneousSubmodule R L n).subtype

/-- The degree-`n` component map is the `n`-th direct-sum component of the canonical PBW map.

This is not a `simp` lemma: together with `pbwAssociatedGradedMap_apply_homogeneous`, which
rewrites in the opposite direction, it would cycle. -/
theorem pbwHomogeneousComponentMap_apply (n : ℕ)
    (p : symmetricHomogeneousSubmodule R L n) :
    pbwHomogeneousComponentMap R L n p =
      DirectSum.component R ℕ (PBWGradedPiece R L) n
        (pbwAssociatedGradedMap R L p) := (rfl)

/-- A homogeneous symmetric element maps to the direct-sum inclusion of its degreewise PBW
component. -/
@[simp]
theorem pbwAssociatedGradedMap_apply_homogeneous (n : ℕ)
    (p : symmetricHomogeneousSubmodule R L n) :
    pbwAssociatedGradedMap R L p =
      DirectSum.of (PBWGradedPiece R L) n (pbwHomogeneousComponentMap R L n p) := by
  obtain ⟨x, hx⟩ := pbwMap_isHomogeneous R L n p
  rw [pbwHomogeneousComponentMap_apply, hx]
  apply congrArg (DirectSum.of (PBWGradedPiece R L) n)
  exact (DirectSum.of_eq_same (β := PBWGradedPiece R L) n x).symm

/-- The degree-`n` component map sends a product of `n` symmetric-algebra generators to the class
of the corresponding word of Lie generators. -/
theorem pbwHomogeneousComponentMap_prod_map_ι (l : List L) :
    pbwHomogeneousComponentMap R L l.length
        ⟨(l.map (SymmetricAlgebra.ι R L)).prod,
          prod_map_ι_mem_symmetricHomogeneousSubmodule R L l⟩ =
      Submodule.Quotient.mk
        (⟨(l.map (_root_.UniversalEnvelopingAlgebra.ι R)).prod,
          prod_map_mem_wordFiltration
            (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap le_rfl⟩ :
          wordFiltration
            (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap l.length) := by
  rw [pbwHomogeneousComponentMap_apply, pbwAssociatedGradedMap_prod_map_ι]
  exact DirectSum.of_eq_same (β := PBWGradedPiece R L) l.length _

/-- Every PBW graded piece has a homogeneous symmetric representative of the same degree. This
is the degreewise form of surjectivity of the canonical map `Sym(L) → gr U(L)`. -/
theorem pbwHomogeneousComponentMap_surjective (n : ℕ) :
    Function.Surjective (pbwHomogeneousComponentMap R L n) := by
  intro x
  have hx : x ∈ (pbwHomogeneousComponentMap R L n).range := by
    induction x using pbwGradedPiece_induction_on with
    | word l hl =>
        rcases hl.eq_or_lt with hl | hl
        · subst n
          exact ⟨_, pbwHomogeneousComponentMap_prod_map_ι R L l⟩
        · rw [mk_prod_map_ι_eq_zero_of_length_lt R L hl]
          exact (pbwHomogeneousComponentMap R L n).range.zero_mem
    | zero => exact (pbwHomogeneousComponentMap R L n).range.zero_mem
    | add x y hx hy => exact (pbwHomogeneousComponentMap R L n).range.add_mem hx hy
    | smul r x hx => exact (pbwHomogeneousComponentMap R L n).range.smul_mem r hx
  exact hx

end TauCeti.UniversalEnvelopingAlgebra
