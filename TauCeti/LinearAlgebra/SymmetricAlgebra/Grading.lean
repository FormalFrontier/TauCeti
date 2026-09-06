/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous

/-!
# The grading of a symmetric algebra

Let `M` be a free module over a commutative ring. The powers of the image of `M` in its symmetric
algebra are not merely a spanning family: they form an internal direct sum. Thus every element of
the symmetric algebra has a unique finite decomposition into homogeneous terms.

The proof transports the standard total-degree decomposition of a multivariate polynomial ring
across the algebra equivalence associated to a basis of `M`. Besides the intrinsic result for a
free module, the comparison with multivariate homogeneous polynomials is exposed for a specified
basis.

## Main results

* `map_homogeneousSubmodule_equivMvPolynomial`: a basis-induced equivalence carries the degree
  `n` part of a symmetric algebra to the degree `n` part of a multivariate polynomial ring.
* `isInternal_homogeneousSubmodule_of_basis`: a specified basis makes the homogeneous pieces an
  internal direct sum.
* `isInternal_homogeneousSubmodule`: the intrinsic formulation for a free module.
* `homogeneousDecomposition`: the resulting direct-sum decomposition.
-/

public section

namespace TauCeti.SymmetricAlgebra

open Module

universe u v w

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- The algebra equivalence induced by a basis preserves homogeneous degree. -/
theorem map_homogeneousSubmodule_equivMvPolynomial {ι : Type w} (b : Basis ι R M) (n : ℕ) :
    (homogeneousSubmodule R M n).map
        (SymmetricAlgebra.equivMvPolynomial b).toLinearMap =
      MvPolynomial.homogeneousSubmodule ι R n := by
  rw [← MvPolynomial.homogeneousSubmodule_one_pow]
  change (LinearMap.range (SymmetricAlgebra.ι R M) ^ n).map
      (SymmetricAlgebra.equivMvPolynomial b).toAlgHom.toLinearMap = _
  rw [Submodule.map_pow (LinearMap.range (SymmetricAlgebra.ι R M))
    (SymmetricAlgebra.equivMvPolynomial b).toAlgHom n]
  congr 1
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X]
  apply le_antisymm
  · rintro p ⟨x, ⟨m, rfl⟩, rfl⟩
    have hm : m ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        simpa using Submodule.subset_span (R := R) (Set.mem_range_self i)
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul r x _ hx => simpa using Submodule.smul_mem _ r hx
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨SymmetricAlgebra.ι R M (b i), ⟨b i, rfl⟩, by simp⟩

/-- Membership in a homogeneous piece can be tested after applying the polynomial equivalence
induced by a basis. -/
theorem _root_.SymmetricAlgebra.equivMvPolynomial_mem_homogeneousSubmodule_iff {ι : Type w}
    (b : Basis ι R M) (n : ℕ) (p : SymmetricAlgebra R M) :
    SymmetricAlgebra.equivMvPolynomial b p ∈ MvPolynomial.homogeneousSubmodule ι R n ↔
      p ∈ homogeneousSubmodule R M n := by
  rw [← map_homogeneousSubmodule_equivMvPolynomial R M b n]
  constructor
  · rintro ⟨q, hq, hqp⟩
    exact (SymmetricAlgebra.equivMvPolynomial b).injective hqp ▸ hq
  · exact fun hp ↦ ⟨p, hp, rfl⟩

/-- A basis makes the homogeneous pieces of its symmetric algebra independent. -/
theorem iSupIndep_homogeneousSubmodule_of_basis {ι : Type w} (b : Basis ι R M) :
    iSupIndep (homogeneousSubmodule R M) := by
  let e := Submodule.orderIsoMapComap (SymmetricAlgebra.equivMvPolynomial b).toLinearEquiv
  rw [← iSupIndep_map_orderIso_iff e]
  change iSupIndep fun n ↦ (homogeneousSubmodule R M n).map
    (SymmetricAlgebra.equivMvPolynomial b).toLinearMap
  simpa only [map_homogeneousSubmodule_equivMvPolynomial R M b] using
    (MvPolynomial.decomposition :
      DirectSum.Decomposition
        (MvPolynomial.homogeneousSubmodule ι R)).isInternal.submodule_iSupIndep

/-- The homogeneous pieces of the symmetric algebra of a free module are independent. -/
theorem iSupIndep_homogeneousSubmodule [Module.Free R M] :
    iSupIndep (homogeneousSubmodule R M) := by
  let ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  exact iSupIndep_homogeneousSubmodule_of_basis R M b

/-- A basis makes the homogeneous pieces an internal direct sum decomposition of its symmetric
algebra. -/
theorem isInternal_homogeneousSubmodule_of_basis {ι : Type w} (b : Basis ι R M) :
    DirectSum.IsInternal (homogeneousSubmodule R M) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_homogeneousSubmodule_of_basis R M b)
    (iSup_homogeneousSubmodule_eq_top R M)

/-- The homogeneous pieces form an internal direct sum decomposition of the symmetric algebra of
a free module. -/
theorem isInternal_homogeneousSubmodule [Module.Free R M] :
    DirectSum.IsInternal (homogeneousSubmodule R M) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_homogeneousSubmodule R M) (iSup_homogeneousSubmodule_eq_top R M)

/-- The canonical decomposition of the symmetric algebra of a free module into its homogeneous
pieces. -/
@[instance_reducible]
noncomputable def homogeneousDecomposition [Module.Free R M] :
    DirectSum.Decomposition (homogeneousSubmodule R M) :=
  (isInternal_homogeneousSubmodule R M).chooseDecomposition

end TauCeti.SymmetricAlgebra
