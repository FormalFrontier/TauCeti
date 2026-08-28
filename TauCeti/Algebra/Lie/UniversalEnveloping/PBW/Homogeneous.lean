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
  exactly `n` symmetric-algebra generators.
* `TauCeti.UniversalEnvelopingAlgebra.pbwHomogeneousComponentMap`: the degreewise PBW map.
* `TauCeti.UniversalEnvelopingAlgebra.pbwAssociatedGradedMap_eq_of_componentMap`: a homogeneous
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

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The degree-`n` homogeneous part of `SymmetricAlgebra R L`: the span of products of exactly
`n` canonical generators. -/
noncomputable def symmetricHomogeneousSubmodule (n : ℕ) :
    Submodule R (SymmetricAlgebra R L) :=
  Submodule.span R {p | ∃ l : List L, l.length = n ∧
    (l.map (SymmetricAlgebra.ι R L)).prod = p}

/-- A product of `n` symmetric-algebra generators belongs to the degree-`n` homogeneous
submodule. -/
theorem prod_map_ι_mem_symmetricHomogeneousSubmodule (l : List L) :
    (l.map (SymmetricAlgebra.ι R L)).prod ∈
      symmetricHomogeneousSubmodule R L l.length := by
  apply Submodule.subset_span
  exact ⟨l, rfl, rfl⟩

private theorem pbwAssociatedGradedMap_word (l : List L) :
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
  rw [hlist]
  clear hlist
  induction l using List.reverseRecOn with
  | nil =>
      simpa only [List.map_nil, List.prod_nil, List.length_nil,
        associatedGraded_of_gradedOne] using
        congrArg (DirectSum.of (PBWGradedPiece R L) 0)
          (mk_one_eq_gradedOne
            (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap).symm
  | append_singleton l x ih =>
      rw [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton, ih,
        pbwGradedGenerator_apply, associatedGraded_of_mul_of, gradedMul_apply_mk]
      let h : l.length + 1 = (l ++ [x]).length := by simp
      apply DirectSum.of_eq_of_gradedMonoid_eq
      apply Sigma.ext h
      simp only [GradedMonoid.mk]
      apply heq_of_cast_eq (congrArg (PBWGradedPiece R L) h)
      rw [gradedPiece_cast_mk]
      all_goals try exact h
      apply (Submodule.Quotient.eq _).mpr
      rw [mem_previousRestricted_iff, Submodule.coe_sub, wordFiltration_coe_cast _ h]
      simp

private theorem pbwMap_isHomogeneous (n : ℕ)
    (p : symmetricHomogeneousSubmodule R L n) :
    ∃ x : PBWGradedPiece R L n,
      pbwAssociatedGradedMap R L p = DirectSum.of (PBWGradedPiece R L) n x := by
  let s := symmetricHomogeneousSubmodule R L n
  have hp : (p : SymmetricAlgebra R L) ∈ s := p.property
  refine Submodule.span_induction (p := fun a _ ↦
    ∃ x : PBWGradedPiece R L n,
      pbwAssociatedGradedMap R L a = DirectSum.of (PBWGradedPiece R L) n x)
      ?_ ?_ ?_ ?_ hp
  · rintro a ⟨l, hl, rfl⟩
    subst n
    exact ⟨_, pbwAssociatedGradedMap_word R L l⟩
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

/-- A homogeneous symmetric element maps to the direct-sum inclusion of its degreewise PBW
component. -/
theorem pbwAssociatedGradedMap_eq_of_componentMap (n : ℕ)
    (p : symmetricHomogeneousSubmodule R L n) :
    pbwAssociatedGradedMap R L p =
      DirectSum.of (PBWGradedPiece R L) n (pbwHomogeneousComponentMap R L n p) := by
  obtain ⟨x, hx⟩ := pbwMap_isHomogeneous R L n p
  change pbwAssociatedGradedMap R L p = DirectSum.of (PBWGradedPiece R L) n
    (DirectSum.component R ℕ (PBWGradedPiece R L) n (pbwAssociatedGradedMap R L p))
  rw [hx]
  apply congrArg (DirectSum.of (PBWGradedPiece R L) n)
  exact (DirectSum.of_eq_same (β := PBWGradedPiece R L) n x).symm

private theorem pbwHomogeneous_mem_componentMap_range (k : ℕ)
    (x : wordFiltration
      (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap k) :
    Submodule.Quotient.mk x ∈ (pbwHomogeneousComponentMap R L k).range := by
  let f : L →ₗ[R] U :=
    (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap
  let s : Submodule R U := Submodule.span R {a | ∃ l : List L, l.length ≤ k ∧
    (l.map fun z ↦ f z).prod = a}
  have hid : Submodule.span R (Set.range (id : L → L)) = ⊤ := by
    rw [Set.range_id, Submodule.span_univ]
  have hs : s = wordFiltration f k := by
    simpa only [id_eq] using span_prod_map_eq_wordFiltration f id hid k
  let e : s ≃ₗ[R] wordFiltration f k := LinearEquiv.ofEq _ _ hs
  let q : s →ₗ[R] PBWGradedPiece R L k :=
    (Submodule.mkQ (previousRestricted f k)).comp e.toLinearMap
  have hq_eq (a : U) (ha : a ∈ s) :
      q ⟨a, ha⟩ = Submodule.Quotient.mk
        (⟨a, hs ▸ ha⟩ : wordFiltration f k) := by
    simp only [q, LinearMap.comp_apply, Submodule.mkQ_apply]
    apply congrArg Submodule.Quotient.mk
    exact Subtype.ext (LinearEquiv.coe_ofEq_apply hs _)
  have hq (a : U) (ha : a ∈ s) :
      q ⟨a, ha⟩ ∈ (pbwHomogeneousComponentMap R L k).range := by
    refine Submodule.span_induction (p := fun a ha ↦
      q ⟨a, ha⟩ ∈ (pbwHomogeneousComponentMap R L k).range) ?_ ?_ ?_ ?_ ha
    · rintro a ⟨l, hl, rfl⟩
      rcases hl.eq_or_lt with hl | hl
      · subst k
        refine ⟨⟨(l.map (SymmetricAlgebra.ι R L)).prod,
          prod_map_ι_mem_symmetricHomogeneousSubmodule R L l⟩, ?_⟩
        rw [hq_eq]
        change DirectSum.component R ℕ (PBWGradedPiece R L) l.length
            (pbwAssociatedGradedMap R L (l.map (SymmetricAlgebra.ι R L)).prod) = _
        rw [pbwAssociatedGradedMap_word]
        change (DirectSum.of (PBWGradedPiece R L) l.length
          (Submodule.Quotient.mk _)) l.length = _
        exact DirectSum.of_eq_same (β := PBWGradedPiece R L) l.length _
      · have hprevious : (l.map (_root_.UniversalEnvelopingAlgebra.ι R)).prod ∈
            pbwFiltrationPrevious R L k := by
          cases k with
          | zero => omega
          | succ k =>
              rw [pbwFiltrationPrevious_succ]
              exact prod_map_ι_mem_pbwFiltration R L (Nat.lt_succ_iff.mp hl)
        have hzero : (Submodule.Quotient.mk
            (⟨(l.map fun z ↦ f z).prod,
              prod_map_mem_wordFiltration f (Nat.le_of_lt hl)⟩ :
              wordFiltration f k) : GradedPiece f k) = 0 := by
          rw [Submodule.Quotient.mk_eq_zero, mem_previousRestricted_iff]
          rw [← pbwFiltrationPrevious_def R L]
          change (l.map (_root_.UniversalEnvelopingAlgebra.ι R)).prod ∈
            pbwFiltrationPrevious R L k
          exact hprevious
        have hword : (l.map fun z ↦ f z).prod ∈ s := by
          apply Submodule.subset_span
          exact ⟨l, Nat.le_of_lt hl, rfl⟩
        have hqzero : q ⟨(l.map fun z ↦ f z).prod, hword⟩ = 0 := by
          rw [hq_eq]
          simpa only [f] using hzero
        rw [hqzero]
        exact (pbwHomogeneousComponentMap R L k).range.zero_mem
    · have hzero : (⟨0, s.zero_mem⟩ : s) = 0 := Subtype.ext rfl
      rw [hzero, map_zero]
      exact (pbwHomogeneousComponentMap R L k).range.zero_mem
    · intro a b ha hb hqa hqb
      have hadd : (⟨a + b, s.add_mem ha hb⟩ : s) = ⟨a, ha⟩ + ⟨b, hb⟩ := Subtype.ext rfl
      rw [hadd, map_add]
      exact (pbwHomogeneousComponentMap R L k).range.add_mem hqa hqb
    · intro r a ha hqa
      have hsmul : (⟨r • a, s.smul_mem r ha⟩ : s) = r • ⟨a, ha⟩ := Subtype.ext rfl
      rw [hsmul, map_smul]
      exact (pbwHomogeneousComponentMap R L k).range.smul_mem r hqa
  have hx : (x : U) ∈ s := by
    rw [hs]
    exact x.property
  have hr := hq (x : U) hx
  rw [hq_eq] at hr
  simpa only [f] using hr

/-- Every PBW graded piece has a homogeneous symmetric representative of the same degree. This
is the degreewise form of surjectivity of the canonical map `Sym(L) → gr U(L)`. -/
theorem pbwHomogeneousComponentMap_surjective (n : ℕ) :
    Function.Surjective (pbwHomogeneousComponentMap R L n) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact pbwHomogeneous_mem_componentMap_range R L n x

end TauCeti.UniversalEnvelopingAlgebra
