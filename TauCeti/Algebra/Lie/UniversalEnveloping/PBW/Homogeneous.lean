/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.AssociatedGraded
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous

/-!
# Homogeneous pieces of the PBW map

The degree-`n` piece of a symmetric algebra is defined to be the `n`-th power of the range of its
canonical generator map; no direct-sum decomposition into those pieces is proven. For a Lie algebra
`L` over a commutative ring `R`, the canonical map

`SymmetricAlgebra R L →ₐ[R] gr U(L)`

sends this submodule into the `n`-th PBW graded piece. This file packages the resulting degreewise
linear map, proves that it is surjective, and deduces surjectivity of the ambient map.

The proof uses the spanning half of PBW. A word of length exactly `n` maps to the corresponding
product of degree-one classes. A shorter word represents zero in the `n`-th successive quotient.
Consequently every class in that quotient has a homogeneous symmetric representative of degree
`n`.

Under the standard hypotheses ensuring PBW over a commutative ring, such as projectivity of `L` as
an `R`-module, injectivity of these component maps together with an internal direct-sum
decomposition of `SymmetricAlgebra R L` into its homogeneous submodules would give the remaining
linear-independence half of the Poincaré--Birkhoff--Witt theorem. Thus the componentwise
surjections isolate one part of the next obstruction degree by degree, while retaining the global
associated-graded map.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.pbwHomogeneousComponentMap`: the degreewise PBW map.
* `TauCeti.UniversalEnvelopingAlgebra.pbwAssociatedGradedMap_apply_homogeneous`: a homogeneous
  element maps to the corresponding direct-sum component.
* `TauCeti.UniversalEnvelopingAlgebra.pbwHomogeneousComponentMap_surjective`: every PBW graded
  piece has a homogeneous symmetric representative of the same degree.
* `TauCeti.UniversalEnvelopingAlgebra.pbwAssociatedGradedMap_surjective`: the canonical map is
  onto.

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
open TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The canonical map sends the degree-`n` homogeneous submodule into the degree-`n` summand of
the associated graded. The target is a submodule, so only the spanning words need checking. -/
private theorem homogeneousSubmodule_le_comap_range_lof (n : ℕ) :
    homogeneousSubmodule R L n ≤
      (LinearMap.range (DirectSum.lof R ℕ (PBWGradedPiece R L) n)).comap
        (pbwAssociatedGradedMap R L).toLinearMap := by
  rw [homogeneousSubmodule_eq_span, Submodule.span_le]
  rintro _ ⟨l, rfl, rfl⟩
  exact ⟨_, (pbwAssociatedGradedMap_prod_map_ι R L l).symm⟩

/-- The degree-`n` component of the canonical PBW map. Its source is the homogeneous symmetric
submodule, and its target is the `n`-th PBW graded quotient. -/
noncomputable def pbwHomogeneousComponentMap (n : ℕ) :
    homogeneousSubmodule R L n →ₗ[R] PBWGradedPiece R L n :=
  (DirectSum.component R ℕ (PBWGradedPiece R L) n).comp <|
    (pbwAssociatedGradedMap R L).toLinearMap.comp
      (homogeneousSubmodule R L n).subtype

/-- The degree-`n` component map is the `n`-th direct-sum component of the canonical PBW map.

This is not a `simp` lemma: together with `pbwAssociatedGradedMap_apply_homogeneous`, which
rewrites in the opposite direction, it would cycle. -/
theorem pbwHomogeneousComponentMap_apply (n : ℕ) (p : homogeneousSubmodule R L n) :
    pbwHomogeneousComponentMap R L n p =
      DirectSum.component R ℕ (PBWGradedPiece R L) n
        (pbwAssociatedGradedMap R L p) := (rfl)

/-- A homogeneous symmetric element maps to the direct-sum inclusion of its degreewise PBW
component. -/
@[simp]
theorem pbwAssociatedGradedMap_apply_homogeneous (n : ℕ) (p : homogeneousSubmodule R L n) :
    pbwAssociatedGradedMap R L p =
      DirectSum.of (PBWGradedPiece R L) n (pbwHomogeneousComponentMap R L n p) := by
  obtain ⟨x, hx⟩ := homogeneousSubmodule_le_comap_range_lof R L n p.property
  rw [DirectSum.lof_eq_of, AlgHom.toLinearMap_apply] at hx
  rw [pbwHomogeneousComponentMap_apply, ← hx]
  apply congrArg (DirectSum.of (PBWGradedPiece R L) n)
  exact (DirectSum.of_eq_same (β := PBWGradedPiece R L) n x).symm

/-- The degree-`n` component map sends a product of `n` symmetric-algebra generators to the class
of the corresponding word of Lie generators. -/
@[simp]
theorem pbwHomogeneousComponentMap_prod_map_ι (l : List L) :
    pbwHomogeneousComponentMap R L l.length
        ⟨(l.map (SymmetricAlgebra.ι R L)).prod,
          prod_map_ι_mem_homogeneousSubmodule R L l⟩ =
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
    induction x using gradedPiece_induction_on with
    | word l hl =>
        subst n
        exact ⟨_, pbwHomogeneousComponentMap_prod_map_ι R L l⟩
    | zero => exact (pbwHomogeneousComponentMap R L n).range.zero_mem
    | add x y hx hy => exact (pbwHomogeneousComponentMap R L n).range.add_mem hx hy
    | smul r x hx => exact (pbwHomogeneousComponentMap R L n).range.smul_mem r hx
  exact hx

/-- The canonical map from the symmetric algebra onto the PBW associated graded is surjective. It
is enough to hit each homogeneous generator of the direct sum, which is the degreewise statement. -/
theorem pbwAssociatedGradedMap_surjective :
    Function.Surjective (pbwAssociatedGradedMap R L) := by
  intro x
  have hx : x ∈ (pbwAssociatedGradedMap R L).range := by
    induction x using DirectSum.induction_on with
    | zero => exact (pbwAssociatedGradedMap R L).range.zero_mem
    | of n y =>
        obtain ⟨p, rfl⟩ := pbwHomogeneousComponentMap_surjective R L n y
        exact ⟨(p : SymmetricAlgebra R L),
          pbwAssociatedGradedMap_apply_homogeneous R L n p⟩
    | add x y hx hy => exact (pbwAssociatedGradedMap R L).range.add_mem hx hy
  exact hx

end TauCeti.UniversalEnvelopingAlgebra
