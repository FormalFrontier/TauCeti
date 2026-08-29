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

For a module `M` over a commutative semiring `R`, the degree-`n` homogeneous part of
`SymmetricAlgebra R M` is the `n`-th power of the range of the canonical generator map. This file
defines it, identifies it with the span of the products of exactly `n` generators, and records that
degrees add under multiplication.

## Main definitions and results

* `TauCeti.SymmetricAlgebra.homogeneousSubmodule`: the degree-`n` homogeneous submodule.
* `TauCeti.SymmetricAlgebra.homogeneousSubmodule_eq_span`: it is spanned by the products of
  exactly `n` generators.
* `TauCeti.SymmetricAlgebra.instGradedMonoid`: the homogeneous submodules form a graded monoid.

This is the homogeneous-decomposition prerequisite for the degreewise PBW comparison map in
Layer 3, “PBW, a substantial sub-project”, of the
[highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md).
-/

public section

namespace TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The degree-`n` homogeneous part of `SymmetricAlgebra R M`: the `n`-th power of the range of
the canonical generator map. -/
noncomputable def homogeneousSubmodule (n : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (SymmetricAlgebra.ι R M) ^ n

/-- The degree-`n` homogeneous submodule is the `n`-th power of the generator range. -/
theorem homogeneousSubmodule_def (n : ℕ) :
    homogeneousSubmodule R M n = LinearMap.range (SymmetricAlgebra.ι R M) ^ n :=
  (rfl)

/-- A product of `n` symmetric-algebra generators is homogeneous of degree `n`. -/
theorem prod_map_ι_mem_homogeneousSubmodule (l : List M) :
    (l.map (SymmetricAlgebra.ι R M)).prod ∈ homogeneousSubmodule R M l.length :=
  TauCeti.Algebra.prod_map_mem_range_pow _ l

/-- The degree-`n` homogeneous submodule is spanned by the products of exactly `n` generators. -/
theorem homogeneousSubmodule_eq_span (n : ℕ) :
    homogeneousSubmodule R M n =
      Submodule.span R {p | ∃ l : List M, l.length = n ∧
        (l.map (SymmetricAlgebra.ι R M)).prod = p} :=
  (TauCeti.Algebra.span_prod_map_eq_range_pow _ n).symm

/-- The homogeneous submodules form a graded monoid: the unit is homogeneous of degree zero, and
multiplication adds degrees. -/
instance instGradedMonoid : SetLike.GradedMonoid (homogeneousSubmodule R M) :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (SymmetricAlgebra.ι R M))

end TauCeti.SymmetricAlgebra
