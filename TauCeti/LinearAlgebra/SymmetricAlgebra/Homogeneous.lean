/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import TauCeti.Algebra.WordFiltration.Basic

/-!
# Homogeneous submodules of a symmetric algebra

For a module `M` over a commutative semiring `R`, this file defines the degree-`n` piece of
`SymmetricAlgebra R M` to be the `n`-th power of the range of the canonical generator map,
identifies it with the span of the products of exactly `n` generators, and records that degrees add
under multiplication. The pieces span the whole symmetric algebra, but no internal direct-sum
decomposition is proven here.

## Main definitions and results

* `TauCeti.SymmetricAlgebra.homogeneousSubmodule`: the degree-`n` homogeneous submodule.
* `TauCeti.SymmetricAlgebra.homogeneousSubmodule_eq_span`: it is spanned by the products of
  exactly `n` generators.
* `TauCeti.SymmetricAlgebra.iSup_homogeneousSubmodule_eq_top`: the homogeneous pieces span the
  whole symmetric algebra.
* `TauCeti.SymmetricAlgebra.instGradedMonoid`: the homogeneous submodules form a graded monoid.

This is the homogeneous-piece prerequisite for the degreewise PBW comparison map in
Layer 3, “PBW, a substantial sub-project”, of the
[highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md).
-/

public section

namespace TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The degree-`n` homogeneous part of `SymmetricAlgebra R M`: the `n`-th power of the range of
the canonical generator map. -/
abbrev homogeneousSubmodule (n : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (SymmetricAlgebra.ι R M) ^ n

/-- A product of `n` symmetric-algebra generators is homogeneous of degree `n`. -/
theorem prod_map_ι_mem_homogeneousSubmodule (l : List M) :
    (l.map (SymmetricAlgebra.ι R M)).prod ∈ homogeneousSubmodule R M l.length :=
  TauCeti.Algebra.prod_map_mem_range_pow _ l

/-- Products of exactly `n` elements from a spanning family span the degree-`n` homogeneous
submodule. -/
theorem homogeneousSubmodule_eq_span_of_span {ι : Type*} (e : ι → M)
    (he : Submodule.span R (Set.range e) = ⊤) (n : ℕ) :
    homogeneousSubmodule R M n =
      Submodule.span R {p | ∃ l : List ι, l.length = n ∧
        (l.map fun i ↦ SymmetricAlgebra.ι R M (e i)).prod = p} :=
  (TauCeti.Algebra.span_prod_map_eq_range_pow_of_span _ e he n).symm

/-- The degree-`n` homogeneous submodule is spanned by the products of exactly `n` generators. -/
theorem homogeneousSubmodule_eq_span (n : ℕ) :
    homogeneousSubmodule R M n =
      Submodule.span R {p | ∃ l : List M, l.length = n ∧
        (l.map (SymmetricAlgebra.ι R M)).prod = p} := by
  have hid : Submodule.span R (Set.range (id : M → M)) = ⊤ := by
    rw [Set.range_id, Submodule.span_univ]
  simpa only [id_eq] using homogeneousSubmodule_eq_span_of_span R M id hid n

/-- The homogeneous submodules span the whole symmetric algebra. This is the spanning half of an
internal grading; directness is not asserted here. -/
theorem iSup_homogeneousSubmodule_eq_top :
    (⨆ n, homogeneousSubmodule R M n) = ⊤ := by
  have hadjoin :
      _root_.Algebra.adjoin R (Set.range (SymmetricAlgebra.ι R M)) = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    induction x using _root_.SymmetricAlgebra.induction with
    | algebraMap r => exact (_root_.Algebra.adjoin R _).algebraMap_mem r
    | ι x => exact _root_.Algebra.subset_adjoin (Set.mem_range_self x)
    | mul a b ha hb => exact (_root_.Algebra.adjoin R _).mul_mem ha hb
    | add a b ha hb => exact (_root_.Algebra.adjoin R _).add_mem ha hb
  calc
    (⨆ n, homogeneousSubmodule R M n) =
        ⨆ k, TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι R M) k := by
      apply le_antisymm
      · exact iSup_le fun n ↦ le_iSup_of_le n
          (TauCeti.Algebra.range_pow_le_wordFiltration (SymmetricAlgebra.ι R M) n)
      · refine iSup_le fun k ↦ ?_
        rw [TauCeti.Algebra.wordFiltration_eq_iSup_pow]
        exact iSup_le fun i ↦ le_iSup (homogeneousSubmodule R M) i
    _ = (_root_.Algebra.adjoin R
        (Set.range (SymmetricAlgebra.ι R M))).toSubmodule :=
      TauCeti.Algebra.iSup_wordFiltration_eq_adjoin (SymmetricAlgebra.ι R M)
    _ = ⊤ := by rw [hadjoin]; rfl

/-- The homogeneous submodules form a graded monoid: the unit is homogeneous of degree zero, and
multiplication adds degrees. -/
instance instGradedMonoid : SetLike.GradedMonoid (homogeneousSubmodule R M) :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (SymmetricAlgebra.ι R M))

end TauCeti.SymmetricAlgebra
