/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.LinearAlgebra.TotallyReal.Basic

/-!
# The dimension of a totally real subspace

A totally real subspace `L` for a linear endomorphism `J` is disjoint from its `J`-image, and a
maximal totally real subspace is complementary to it (`TauCeti.LinearAlgebra.TotallyReal.Basic`).
When `J` is injective on `L`, `L` and `J(L)` have the same dimension, so these two conditions
become dimension statements: a totally real subspace has at most half the dimension of the
ambient space, and a maximal totally real subspace has *exactly* half
(`TauCeti.IsTotallyReal.isMaximalTotallyReal_iff_two_mul_finrank_eq`).

This is the linear-algebra half of the statement that the totally real tori `T_α`, `T_β` in the
symmetric product `Sym^g(Σ)` of a Heegaard surface are `g`-dimensional in the `2g`-dimensional
`Sym^g(Σ)` (Ozsváth--Szabó, [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), Section 2);
the corresponding half-dimensionality of Lagrangian subspaces is the same count. Nothing here
needs a symplectic form or an almost complex structure: only injectivity of `J` on `L` is used,
which is automatic when `J² = -1`.

## Main declarations

* `TauCeti.IsTotallyReal.two_mul_finrank_le`: a totally real subspace satisfies
  `2 * finrank R L ≤ finrank R E`.
* `TauCeti.IsMaximalTotallyReal.two_mul_finrank_eq`: a maximal totally real subspace satisfies
  `2 * finrank R L = finrank R E`, hence `TauCeti.IsMaximalTotallyReal.finrank_eq_half` and
  `TauCeti.IsMaximalTotallyReal.even_finrank`.
* `TauCeti.IsTotallyReal.isMaximalTotallyReal_iff_two_mul_finrank_eq`: a totally real subspace is
  maximal totally real exactly when it has half the ambient dimension.
-/

public section

namespace TauCeti

open Module

variable {R E : Type*}

section DivisionRing

variable [DivisionRing R] [AddCommGroup E] [Module R E] [FiniteDimensional R E]
variable {J : E →ₗ[R] E} {L : Submodule R E}

namespace IsTotallyReal

/-- A totally real subspace has at most half the dimension of the ambient space. -/
theorem two_mul_finrank_le (hL : IsTotallyReal J L)
    (hJ : Function.Injective (J.domRestrict L)) :
    2 * finrank R L ≤ finrank R E := by
  have h := Submodule.finrank_add_finrank_le_of_disjoint hL.disjoint
  rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hJ] at h
  omega

/-- A totally real subspace of exactly half the ambient dimension is maximal totally real: the
dimension count forces the sum `L ⊔ J(L)` to be everything. -/
theorem isMaximalTotallyReal (hL : IsTotallyReal J L)
    (hJ : Function.Injective (J.domRestrict L))
    (hdim : 2 * finrank R L = finrank R E) : IsMaximalTotallyReal J L := by
  rw [isMaximalTotallyReal_iff]
  refine (Submodule.isCompl_iff_disjoint L (L.map J) ?_).2 hL.disjoint
  rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hJ]
  omega

end IsTotallyReal

namespace IsMaximalTotallyReal

/-- A maximal totally real subspace has exactly half the dimension of the ambient space. -/
theorem two_mul_finrank_eq (hL : IsMaximalTotallyReal J L)
    (hJ : Function.Injective (J.domRestrict L)) :
    2 * finrank R L = finrank R E := by
  have h : finrank R L + finrank R (L.map J) = finrank R E :=
    Submodule.finrank_add_eq_of_isCompl hL.isCompl
  rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hJ] at h
  omega

/-- The ambient space of a maximal totally real subspace is even-dimensional. -/
theorem even_finrank (hL : IsMaximalTotallyReal J L)
    (hJ : Function.Injective (J.domRestrict L)) :
    Even (finrank R E) := by
  rw [← hL.two_mul_finrank_eq hJ]
  exact even_two_mul _

/-- A maximal totally real subspace is half-dimensional. -/
theorem finrank_eq_half (hL : IsMaximalTotallyReal J L)
    (hJ : Function.Injective (J.domRestrict L)) :
    finrank R L = finrank R E / 2 := by
  have h := hL.two_mul_finrank_eq hJ
  omega

end IsMaximalTotallyReal

/-- A totally real subspace is maximal totally real exactly when it is half-dimensional. -/
theorem IsTotallyReal.isMaximalTotallyReal_iff_two_mul_finrank_eq (hL : IsTotallyReal J L)
    (hJ : Function.Injective (J.domRestrict L)) :
    IsMaximalTotallyReal J L ↔ 2 * finrank R L = finrank R E :=
  ⟨fun h => h.two_mul_finrank_eq hJ, fun h => hL.isMaximalTotallyReal hJ h⟩

end DivisionRing

end TauCeti
