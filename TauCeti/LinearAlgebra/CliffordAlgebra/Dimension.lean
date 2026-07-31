/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension

/-!
# Freeness and dimension of a Clifford algebra

The Clifford relation `ι Q m * ι Q m = Q m` does not preserve the number of generators in a
product, so a Clifford algebra is not graded by degree; what it does do is leave the *size* of the
algebra alone. In characteristic not two this is Mathlib's `CliffordAlgebra.equivExterior`, a
linear (not algebra) isomorphism `CliffordAlgebra Q ≃ₗ[R] ExteriorAlgebra R M` valid for every
quadratic form. Deforming the form therefore deforms the multiplication and nothing else, and the
underlying module of `CliffordAlgebra Q` is as free, and as large, as the exterior algebra of `M`.

This file records that. Over a commutative ring in which `2` is invertible, `CliffordAlgebra Q` is a
free `R`-module whenever `M` is, with an explicit basis
`TauCeti.CliffordAlgebra.basis Q b : Basis (Finset I) R (CliffordAlgebra Q)` attached to a basis `b`
of `M` indexed by a linearly ordered `I`, and it is finite of rank `2 ^ finrank R M` whenever `M` is
finite free. The `2 ^ n` is `∑ₖ (n choose k)` (`finrank_eq_sum_choose`), the count that a
degree-graded argument would produce one exterior power at a time; here it is the count of subsets
of a basis index set instead, because the basis is transported from Mathlib's basis
`Module.Basis.ExteriorAlgebra` of the exterior algebra, indexed by finite subsets.

A second section splits that count in half along Mathlib's `ℤ/2`-grading `evenOdd Q`. Over a field,
and as soon as some vector `v` has `Q v ≠ 0`, right multiplication by `ι Q v` is a linear
automorphism of the Clifford algebra carrying `evenOdd Q i` onto `evenOdd Q (i + 1)`, because a
vector is odd and because `ι Q v * ι Q v = Q v` supplies the inverse. The two halves therefore have
the same dimension, `2 ^ (n - 1)` each, and so in particular does the even subalgebra
`CliffordAlgebra.even Q`.

These counts are what make the structure theory of Clifford algebras run: over an algebraically
closed field a nondegenerate `Q` on a `2l`-dimensional space has
`finrank (CliffordAlgebra Q) = 2 ^ (2 * l) = (2 ^ l) ^ 2`, matching `Module.End` of the
`2 ^ l`-dimensional spin module, so a surjection between the two is forced to be an isomorphism,
while `finrank (even Q) = 2 ^ (2 * l - 1) = 2 * (2 ^ (l - 1)) ^ 2` matches the product of two
matrix algebras one size down, acting on the two half-spin summands.

## Implementation notes

`basis` transports Mathlib's `Module.Basis.ExteriorAlgebra` along `equivExterior`, so its elements
are not by definition the products `ι Q (b i₁) * ⋯ * ι Q (b iₖ)` of generators: `equivExterior` is
built from `CliffordAlgebra.changeForm`, which corrects a product of generators by lower-order
terms. Nothing below needs the products, only their number. Identifying
the two families is the Clifford analogue of a Poincaré-Birkhoff-Witt theorem, and is the content
of the associated-graded isomorphism `gr (CliffordAlgebra Q) ≅ ExteriorAlgebra R M` against the
degree filtration of `TauCeti/LinearAlgebra/CliffordAlgebra/Filtration.lean`; it is left to that
separate milestone.

## Main definitions

* `TauCeti.CliffordAlgebra.basis`: the basis of `CliffordAlgebra Q` indexed by the finite subsets of
  the index set of a basis of `M`, in characteristic not two.
* `TauCeti.CliffordAlgebra.mulRightιEquiv`: right multiplication by a vector of nonzero norm, as a
  linear automorphism of the Clifford algebra, and
  `TauCeti.CliffordAlgebra.evenOddEquivAddOne`, the isomorphism between consecutive halves of the
  `ℤ/2`-grading that it restricts to.

## Main results

* `TauCeti.CliffordAlgebra.rank_eq_rank_exteriorAlgebra` and
  `TauCeti.CliffordAlgebra.finrank_eq_finrank_exteriorAlgebra`: the rank of `CliffordAlgebra Q`
  is the rank of `ExteriorAlgebra R M`. The right-hand sides do not mention `Q`, so this is the
  statement that the size of a Clifford algebra does not depend on the quadratic form.
* `TauCeti.CliffordAlgebra.instFree` and `TauCeti.CliffordAlgebra.instFinite`: the Clifford algebra
  of a free module is free, and of a finite free module is finite.
* `TauCeti.CliffordAlgebra.finrank_eq_two_pow`: `finrank R (CliffordAlgebra Q) = 2 ^ finrank R M`,
  with `TauCeti.CliffordAlgebra.finrank_eq_sum_choose` the same count as a sum of binomial
  coefficients.
* `TauCeti.CliffordAlgebra.map_evenOdd_mulRightιEquiv`: multiplying by a vector of nonzero norm
  exchanges the two halves of the `ℤ/2`-grading.
* `TauCeti.CliffordAlgebra.finrank_evenOdd` and `TauCeti.CliffordAlgebra.finrank_even`: over a field
  each half of the grading, and in particular the even subalgebra, has dimension
  `2 ^ (finrank K V - 1)`.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 0, "The associated graded is the exterior algebra (a PBW-type theorem)".
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open Module CliffordAlgebra

universe u v w

namespace TauCeti

namespace CliffordAlgebra

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
  (Q : QuadraticForm R M)

/-- The basis of `CliffordAlgebra Q` attached to a basis `b` of `M`, indexed by the finite subsets
of the index set of `b`, obtained by transporting Mathlib's basis of `ExteriorAlgebra R M` along
`CliffordAlgebra.equivExterior`.

Its elements are not products of generators by construction; see the implementation notes. -/
@[expose] noncomputable def basis {I : Type w} [LinearOrder I] (b : Basis I R M) :
    Basis (Finset I) R (CliffordAlgebra Q) :=
  b.ExteriorAlgebra.map (equivExterior Q).symm

theorem basis_apply {I : Type w} [LinearOrder I] (b : Basis I R M) (s : Finset I) :
    basis Q b s = (equivExterior Q).symm (b.ExteriorAlgebra s) :=
  rfl

/-- Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to the underlying
`CliffordAlgebra.changeForm`, so the left-hand side is not in normal form. -/
theorem equivExterior_basis {I : Type w} [LinearOrder I] (b : Basis I R M) (s : Finset I) :
    equivExterior Q (basis Q b s) = b.ExteriorAlgebra s := by
  rw [basis_apply, LinearEquiv.apply_symm_apply]

/-- The Clifford algebra of a free module is a free module, in characteristic not two. -/
instance instFree [Module.Free R M] : Module.Free R (CliffordAlgebra Q) :=
  Module.Free.of_equiv (equivExterior Q).symm

/-- The Clifford algebra of a finite free module is a finite module, in characteristic not two. -/
instance instFinite [Module.Free R M] [Module.Finite R M] :
    Module.Finite R (CliffordAlgebra Q) :=
  Module.Finite.equiv (equivExterior Q).symm

/-- A Clifford algebra has the rank of the exterior algebra of the same module. The right-hand side
does not mention `Q`: deforming the quadratic form deforms the multiplication and leaves the
underlying module alone. -/
theorem rank_eq_rank_exteriorAlgebra :
    Module.rank R (CliffordAlgebra Q) = Module.rank R (ExteriorAlgebra R M) :=
  (equivExterior Q).rank_eq

/-- A Clifford algebra has the finite rank of the exterior algebra of the same module; the
finite-rank form of `rank_eq_rank_exteriorAlgebra`, again independent of `Q`. -/
theorem finrank_eq_finrank_exteriorAlgebra :
    finrank R (CliffordAlgebra Q) = finrank R (ExteriorAlgebra R M) :=
  (equivExterior Q).finrank_eq

/-- The Clifford algebra of a finite free module of rank `n` has rank `2 ^ n`, for every quadratic
form on it. -/
theorem finrank_eq_two_pow [Nontrivial R] [Module.Free R M] [Module.Finite R M] :
    finrank R (CliffordAlgebra Q) = 2 ^ finrank R M := by
  rw [finrank_eq_finrank_exteriorAlgebra, ExteriorAlgebra.finrank_eq_two_pow]

/-- The rank of a Clifford algebra as a sum of binomial coefficients: `2 ^ n = ∑ₖ (n choose k)`,
the count that adding up the exterior powers `⋀[R]^k M`, of ranks `(n choose k)`, produces. -/
theorem finrank_eq_sum_choose [Nontrivial R] [Module.Free R M] [Module.Finite R M] :
    finrank R (CliffordAlgebra Q) =
      ∑ k ∈ Finset.range (finrank R M + 1), (finrank R M).choose k := by
  rw [finrank_eq_two_pow, Nat.sum_range_choose]

/-- A Clifford algebra of a finite free module has positive rank, its rank being a power of two. -/
theorem finrank_pos [Nontrivial R] [Module.Free R M] [Module.Finite R M] :
    0 < finrank R (CliffordAlgebra Q) := by
  rw [finrank_eq_two_pow]
  positivity

end CommRing

section EvenOdd

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V) {v : V}

/-- Right multiplication by a vector of nonzero norm, as a linear automorphism of the Clifford
algebra. The Clifford relation `ι Q v * ι Q v = Q v` makes it invertible, its inverse being the
same multiplication scaled by `(Q v)⁻¹`. -/
@[expose] noncomputable def mulRightιEquiv (hv : Q v ≠ 0) :
    CliffordAlgebra Q ≃ₗ[K] CliffordAlgebra Q :=
  LinearEquiv.ofLinear (LinearMap.mulRight K (ι Q v)) ((Q v)⁻¹ • LinearMap.mulRight K (ι Q v))
    (by
      ext y
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.mulRight_apply,
        LinearMap.id_apply, smul_mul_assoc, mul_assoc, ι_sq_scalar]
      rw [← Algebra.commutes, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hv, one_smul])
    (by
      ext y
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.mulRight_apply,
        LinearMap.id_apply, mul_assoc, ι_sq_scalar]
      rw [← Algebra.commutes, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hv, one_smul])

@[simp]
theorem mulRightιEquiv_apply (hv : Q v ≠ 0) (x : CliffordAlgebra Q) :
    mulRightιEquiv Q hv x = x * ι Q v :=
  rfl

/-- Multiplying by a vector of nonzero norm exchanges the two halves of the `ℤ/2`-grading, since a
vector is odd. This is what makes the even and the odd part of a Clifford algebra equidimensional
as soon as the form is not identically zero. -/
theorem map_evenOdd_mulRightιEquiv (hv : Q v ≠ 0) (i : ZMod 2) :
    (evenOdd Q i).map (mulRightιEquiv Q hv).toLinearMap = evenOdd Q (i + 1) := by
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun x hx => ?_) fun y hy => ?_
  · exact evenOdd_mul_le Q i 1 (Submodule.mul_mem_mul hx (ι_mem_evenOdd_one Q v))
  · refine Submodule.mem_map.2 ⟨(Q v)⁻¹ • (y * ι Q v), ?_, ?_⟩
    · have hmem : (Q v)⁻¹ • (y * ι Q v) ∈ evenOdd Q (i + 1 + 1) :=
        Submodule.smul_mem _ _
          (evenOdd_mul_le Q (i + 1) 1 (Submodule.mul_mem_mul hy (ι_mem_evenOdd_one Q v)))
      rwa [add_assoc, h2, add_zero] at hmem
    · simp only [LinearEquiv.coe_coe, mulRightιEquiv_apply, smul_mul_assoc, mul_assoc,
        ι_sq_scalar]
      rw [← Algebra.commutes, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hv, one_smul]

/-- The two halves of the `ℤ/2`-grading of a Clifford algebra are isomorphic as modules, provided
some vector has nonzero norm: multiplication by that vector carries one onto the other. -/
@[expose] noncomputable def evenOddEquivAddOne (hv : Q v ≠ 0) (i : ZMod 2) :
    evenOdd Q i ≃ₗ[K] evenOdd Q (i + 1) :=
  (Submodule.equivMapOfInjective _ (mulRightιEquiv Q hv).injective _).trans
    (LinearEquiv.ofEq _ _ (map_evenOdd_mulRightιEquiv Q hv i))

@[simp]
theorem coe_evenOddEquivAddOne (hv : Q v ≠ 0) (i : ZMod 2) (x : evenOdd Q i) :
    (evenOddEquivAddOne Q hv i x : CliffordAlgebra Q) = x * ι Q v :=
  rfl

/-- Each half of the `ℤ/2`-grading of a Clifford algebra on a finite-dimensional space carrying a
vector of nonzero norm has half the dimension of the whole: `2 ^ (n - 1)` for `n = finrank K V`.

The vector of nonzero norm is what the proof multiplies by; it is not the sharpest hypothesis,
since for the zero form the two halves of the exterior algebra are equidimensional as well
whenever `V ≠ 0`. What it does rule out is `V = 0`, where the Clifford algebra is `K` and entirely
even, so no such statement can hold. -/
theorem finrank_evenOdd [Invertible (2 : K)] [Module.Finite K V] (hv : Q v ≠ 0) (i : ZMod 2) :
    finrank K (evenOdd Q i) = 2 ^ (finrank K V - 1) := by
  have hV : Nontrivial V := ⟨v, 0, fun h => hv (h ▸ (QuadraticMap.map_zero Q))⟩
  have hpos : 0 < finrank K V := Module.finrank_pos
  have hsum : finrank K (evenOdd Q 0) + finrank K (evenOdd Q 1) = 2 ^ finrank K V := by
    rw [Submodule.finrank_add_eq_of_isCompl (evenOdd_isCompl Q), finrank_eq_two_pow]
  have hswap : finrank K (evenOdd Q 0) = finrank K (evenOdd Q 1) :=
    (evenOddEquivAddOne Q hv 0).finrank_eq
  have hi : finrank K (evenOdd Q i) = finrank K (evenOdd Q 0) := by
    fin_cases i
    · rfl
    · exact hswap.symm
  have h2 : 2 * 2 ^ (finrank K V - 1) = 2 ^ finrank K V := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  omega

/-- The even Clifford algebra of a finite-dimensional space carrying a vector of nonzero norm has
dimension `2 ^ (n - 1)`, one power of two below the whole algebra. This is the dimension count
behind the identification of the even subalgebra with a product of two matrix algebras one size
down. -/
theorem finrank_even [Invertible (2 : K)] [Module.Finite K V] (hv : Q v ≠ 0) :
    finrank K (_root_.CliffordAlgebra.even Q) = 2 ^ (finrank K V - 1) :=
  (LinearEquiv.ofEq _ _ (_root_.CliffordAlgebra.even_toSubmodule Q)).finrank_eq.trans
    (finrank_evenOdd Q hv 0)

end EvenOdd

end CliffordAlgebra

end TauCeti
