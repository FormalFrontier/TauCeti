/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Monomial

/-!
# The monomial and Schur bases of the symmetric homogeneous polynomials

Let `σ` be a finite alphabet and `R` a commutative ring.  This file proves that the Schur
polynomials `s_μ` of `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean` form an
`R`-basis of the symmetric polynomials in `σ` that are homogeneous of degree `n`, indexed by the
partitions of `n` with at most `Fintype.card σ` parts.  Taken over `ℤ`, this is the
finite-alphabet, fixed-degree form of "the Schur functions are a `ℤ`-basis of the symmetric
functions"; the stable symmetric-function ring, in which the unqualified statement lives, is not
built here.

## The index set

Both `TauCeti.msymm_eq_zero_of_card_lt` and `TauCeti.schurPoly_eq_zero_iff` say that a partition
with more parts than the alphabet has letters contributes nothing, so neither family is linearly
independent when indexed by *all* partitions of `n`.  The bases below are therefore indexed by the
subtype `{ν : n.Partition // ν.parts.card ≤ Fintype.card σ}`, which is exactly the range in which
`TauCeti.partWeight` records a partition faithfully.

## The route

Everything runs through a single linear map, `TauCeti.partWeightCoeff`, reading a symmetric
homogeneous polynomial at the *sorted* monomials `TauCeti.partWeight σ ν`.  It is bijective: a
symmetric polynomial has the same coefficient at a monomial and at its sorted rearrangement
(`TauCeti.coeff_eq_coeff_partWeight`), so a symmetric homogeneous polynomial is determined by those
coefficients; and the monomial symmetric polynomials, whose coefficients at sorted monomials are
the Kronecker delta (`TauCeti.coeff_msymm_partWeight`), realize every prescription.  Reading that
bijection as a coordinate system is the monomial basis `TauCeti.msymmBasis`.

The Schur basis is the monomial basis transported along the Kostka matrix.  In the monomial basis
the coordinates of `s_μ` are the Kostka numbers `K_{μν}`
(`TauCeti.msymmBasis_repr_schurPoly`), which vanish unless `μ` dominates `ν`
(`TauCeti.kostkaNumber_eq_zero_of_not_dominates`) and equal `1` on the diagonal
(`TauCeti.kostkaNumber_self`).  Since dominance refines the lexicographic linear order on
partitions (`TauCeti.lex_le_of_dominates`), the Kostka matrix is triangular with `1`s on the
diagonal for that linear order, so its determinant is `1` and it is a change of basis.  This is
where the ring hypothesis enters: over `ℕ` the transition matrix is not invertible.

## Main definitions

The module being based, `TauCeti.symmetricHomogeneousSubmodule σ R n`, carries no Schur content and
is defined in `TauCeti/RingTheory/MvPolynomial/Symmetric/Homogeneous.lean`.

* `TauCeti.partWeightCoeff`: the coordinates of a symmetric homogeneous polynomial at the sorted
  monomials.
* `TauCeti.msymmBasis`: **the monomial basis**.
* `TauCeti.schurPolyBasis`: **the Schur basis**.

## Main results

* `TauCeti.coeff_eq_coeff_partWeight`: a symmetric polynomial has the same coefficient at a
  monomial of degree `n` and at the sorted monomial of the partition of its exponents.
* `TauCeti.partWeightCoeff_bijective`: **a symmetric homogeneous polynomial is exactly a
  prescription of coefficients at the sorted monomials**.
* `TauCeti.coe_msymmBasis` and `TauCeti.msymmBasis_repr_apply`: the monomial basis consists of the
  monomial symmetric polynomials, and coordinates in it are coefficients at sorted monomials.
* `TauCeti.msymmBasis_repr_schurPoly`: **the Kostka numbers are the change-of-basis matrix**, the
  coordinates of `s_μ` in the monomial basis.
* `TauCeti.schurPolyBasis` and `TauCeti.coe_schurPolyBasis`: **the Schur polynomials of the
  partitions of `n` with at most `Fintype.card σ` parts are a basis of the symmetric homogeneous
  polynomials of degree `n`.**

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Sections 2 and 6: the monomial symmetric functions are a basis, the Kostka matrix is
  unitriangular for the dominance order, and hence the Schur functions are a basis.
* R. P. Stanley, *Enumerative Combinatorics*, Volume 2, §7.10.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 7, "The Schur functions are a `ℤ`-basis of the symmetric functions; `msymm`-to-`schurPoly`
  change of basis is the Kostka matrix `Kλμ`".
-/

public section

namespace TauCeti

open Finset MvPolynomial

section CommSemiring

variable {σ : Type*} {R : Type*} [CommSemiring R] {n : ℕ}

/-! ### The symmetric homogeneous polynomials -/

variable [Fintype σ]

/-- **A Schur polynomial is symmetric and homogeneous** of degree the natural number its partition
partitions. -/
theorem schurPoly_mem_symmetricHomogeneousSubmodule (μ : n.Partition) :
    schurPoly σ R μ ∈ symmetricHomogeneousSubmodule σ R n :=
  mem_symmetricHomogeneousSubmodule.mpr ⟨schurPoly_isSymmetric μ, isHomogeneous_schurPoly μ⟩

/-- **A monomial symmetric polynomial is symmetric and homogeneous** of degree the natural number
its partition partitions. -/
theorem msymm_mem_symmetricHomogeneousSubmodule [DecidableEq σ] (ν : n.Partition) :
    msymm σ R ν ∈ symmetricHomogeneousSubmodule σ R n :=
  mem_symmetricHomogeneousSubmodule.mpr ⟨msymm_isSymmetric σ R ν, isHomogeneous_msymm R ν⟩

/-! ### Coordinates at the sorted monomials -/

/-- **A symmetric polynomial does not see the order of the exponents of a monomial**: its
coefficient at a monomial of total degree `n` is its coefficient at the sorted monomial of the
partition of those exponents.  This is what makes the coordinates below complete. -/
theorem coeff_eq_coeff_partWeight [DecidableEq σ] {p : MvPolynomial σ R} (hp : p.IsSymmetric)
    {d : σ →₀ ℕ} (hd : d.degree = n) :
    coeff d p = coeff (partWeight σ (weightPartition d hd)) p := by
  obtain ⟨e, he⟩ := exists_perm_mapDomain_eq_partWeight d hd
  conv_rhs => rw [← he, ← hp e]
  exact (coeff_rename_mapDomain _ e.injective _ _).symm

variable (σ R n) in
/-- **The coordinates of a symmetric homogeneous polynomial**: its coefficients at the sorted
monomials `TauCeti.partWeight σ ν`, one for each partition `ν` of `n` short enough for the alphabet
to record.  `TauCeti.partWeightCoeff_bijective` says these coordinates determine the polynomial and
may be prescribed arbitrarily, and `TauCeti.msymmBasis` is the resulting basis. -/
noncomputable def partWeightCoeff :
    symmetricHomogeneousSubmodule σ R n →ₗ[R]
      ({ν : n.Partition // ν.parts.card ≤ Fintype.card σ} →₀ R) :=
  (Finsupp.linearEquivFunOnFinite R R _).symm.toLinearMap ∘ₗ
    LinearMap.pi fun ν => (lcoeff (R := R) (partWeight σ ν.1)).comp
      (symmetricHomogeneousSubmodule σ R n).subtype

/-- The coordinates of `TauCeti.partWeightCoeff` are the coefficients at the sorted monomials.
The body of `TauCeti.partWeightCoeff` is not exposed, so this is what a consumer rewrites with. -/
@[simp]
theorem partWeightCoeff_apply (p : symmetricHomogeneousSubmodule σ R n)
    (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    partWeightCoeff σ R n p ν = coeff (partWeight σ ν.1) (p : MvPolynomial σ R) := by
  simp [partWeightCoeff]

/-- **A symmetric homogeneous polynomial is determined by its coefficients at the sorted
monomials**: away from them symmetry moves each coefficient to a sorted one, and away from degree
`n` homogeneity kills it. -/
theorem partWeightCoeff_injective : Function.Injective (partWeightCoeff σ R n) := by
  classical
  intro p q hpq
  refine Subtype.ext (MvPolynomial.ext _ _ fun d => ?_)
  by_cases hd : d.degree = n
  · have h := DFunLike.congr_fun hpq ⟨weightPartition d hd, card_parts_weightPartition_le d hd⟩
    rw [partWeightCoeff_apply, partWeightCoeff_apply] at h
    rw [coeff_eq_coeff_partWeight (mem_symmetricHomogeneousSubmodule.mp p.2).1 hd,
      coeff_eq_coeff_partWeight (mem_symmetricHomogeneousSubmodule.mp q.2).1 hd, h]
  · rw [(mem_symmetricHomogeneousSubmodule.mp p.2).2.coeff_eq_zero hd,
      (mem_symmetricHomogeneousSubmodule.mp q.2).2.coeff_eq_zero hd]

/-- **The coefficients at the sorted monomials may be prescribed arbitrarily**: the combination of
the monomial symmetric polynomials with the prescribed coefficients realizes them, each `m_ν` being
the indicator of its own sorted monomial. -/
theorem partWeightCoeff_surjective : Function.Surjective (partWeightCoeff σ R n) := by
  classical
  intro f
  refine ⟨⟨∑ ν, f ν • msymm σ R ν.1, Submodule.sum_mem _ fun ν _ =>
    Submodule.smul_mem _ _ (msymm_mem_symmetricHomogeneousSubmodule ν.1)⟩, Finsupp.ext fun ξ => ?_⟩
  rw [partWeightCoeff_apply, coeff_sum]
  refine (Finset.sum_eq_single ξ (fun ν _ hne => ?_) fun hξ => absurd (mem_univ ξ) hξ).trans ?_
  · rw [coeff_smul, coeff_msymm_partWeight R ν.1 ξ.1 ξ.2,
      ite_eq_right fun h => hne (Subtype.ext h.symm), smul_zero]
  · rw [coeff_smul, coeff_msymm_partWeight R ξ.1 ξ.1 ξ.2, ite_eq_left rfl, smul_eq_mul, mul_one]

/-- **A symmetric homogeneous polynomial is exactly a prescription of coefficients at the sorted
monomials.** -/
theorem partWeightCoeff_bijective : Function.Bijective (partWeightCoeff σ R n) :=
  ⟨partWeightCoeff_injective, partWeightCoeff_surjective⟩

/-! ### The monomial basis -/

variable (σ R n) in
/-- **The monomial basis**: the coordinates of `TauCeti.partWeightCoeff` read as a basis of the
symmetric polynomials of degree `n`, indexed by the partitions of `n` with at most `Fintype.card σ`
parts.  Its basis vectors are the monomial symmetric polynomials `m_ν`
(`TauCeti.coe_msymmBasis`), which is what the name records. -/
noncomputable def msymmBasis :
    Module.Basis {ν : n.Partition // ν.parts.card ≤ Fintype.card σ} R
      (symmetricHomogeneousSubmodule σ R n) :=
  .ofRepr (LinearEquiv.ofBijective _ (partWeightCoeff_bijective (σ := σ) (R := R) (n := n)))

/-- **The coordinates in the monomial basis are the coefficients at the sorted monomials**: this is
the normal form of a monomial-basis coordinate, and the elimination rule matching
`TauCeti.coe_msymmBasis`. -/
@[simp]
theorem msymmBasis_repr_apply (p : symmetricHomogeneousSubmodule σ R n)
    (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    (msymmBasis σ R n).repr p ν = coeff (partWeight σ ν.1) (p : MvPolynomial σ R) := by
  -- The coordinate map of `TauCeti.msymmBasis` is the map it was built from.
  have h : (msymmBasis σ R n).repr p = partWeightCoeff σ R n p :=
    LinearEquiv.ofBijective_apply (f := partWeightCoeff σ R n)
      (hf := partWeightCoeff_bijective) p
  rw [h, partWeightCoeff_apply]

/-- **The vectors of the monomial basis are the monomial symmetric polynomials**:
`TauCeti.msymmBasis` is defined through its coordinates, and this reads its basis vectors back as
the polynomials `m_ν` the name records. -/
@[simp]
theorem coe_msymmBasis [DecidableEq σ] (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    ((msymmBasis σ R n ν : symmetricHomogeneousSubmodule σ R n) : MvPolynomial σ R)
      = msymm σ R ν.1 := by
  have h : (msymmBasis σ R n).repr (msymmBasis σ R n ν)
      = (msymmBasis σ R n).repr
        ⟨msymm σ R ν.1, msymm_mem_symmetricHomogeneousSubmodule ν.1⟩ := by
    refine (Module.Basis.repr_self _ ν).trans (Finsupp.ext fun ξ => ?_).symm
    rw [msymmBasis_repr_apply, coeff_msymm_partWeight R ν.1 ξ.1 ξ.2, Finsupp.single_apply]
    exact if_congr (Subtype.ext_iff.symm.trans eq_comm) rfl rfl
  exact congrArg Subtype.val ((msymmBasis σ R n).repr.injective h)

/-- **The Kostka numbers are the coordinates of a Schur polynomial in the monomial basis**, which
is the monomial expansion `TauCeti.schurPoly_eq_sum_kostkaNumber_smul_msymm` read as a change of
basis.  It is not a `simp` lemma: `TauCeti.msymmBasis_repr_apply` already puts a coordinate of the
monomial basis into its normal form as a coefficient. -/
theorem msymmBasis_repr_schurPoly (μ : n.Partition)
    (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    (msymmBasis σ R n).repr ⟨schurPoly σ R μ, schurPoly_mem_symmetricHomogeneousSubmodule μ⟩ ν
      = (kostkaNumber μ ν.1 : R) := by
  rw [msymmBasis_repr_apply]
  exact coeff_schurPoly_partWeight μ ν.1 (by rw [colLen_zero_diagramOf]; exact ν.2)

end CommSemiring

/-! ### The Schur basis -/

section CommRing

variable {σ : Type*} [Fintype σ] {R : Type*} [CommRing R] {n : ℕ}

variable (σ R n) in
/-- The Schur polynomials of the partitions the alphabet records, as elements of the module they
are about to be shown to be a basis of. -/
private noncomputable def schurPolyElem
    (μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    symmetricHomogeneousSubmodule σ R n :=
  ⟨schurPoly σ R μ.1, schurPoly_mem_symmetricHomogeneousSubmodule μ.1⟩

open scoped PartitionLex in
/-- **The Kostka matrix is triangular with `1`s on the diagonal**, hence a change of basis:
`K_{μν}` vanishes unless `μ` dominates `ν`, dominance refines the lexicographic linear order, and
`K_{μμ}` is `1`. -/
private theorem isUnit_det_schurPolyElem :
    IsUnit ((msymmBasis σ R n).det (schurPolyElem σ R n)) := by
  have hentry : ∀ ν μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ},
      (msymmBasis σ R n).toMatrix (schurPolyElem σ R n) ν μ = (kostkaNumber μ.1 ν.1 : R) := by
    intro ν μ
    rw [Module.Basis.toMatrix_apply]
    exact msymmBasis_repr_schurPoly μ.1 ν
  have htri : ((msymmBasis σ R n).toMatrix (schurPolyElem σ R n)).IsUpperTriangular := by
    intro ν μ hμν
    have hlt : (μ : n.Partition) < (ν : n.Partition) := Subtype.coe_lt_coe.mpr hμν
    rw [hentry ν μ, kostkaNumber_eq_zero_of_not_dominates fun hdom =>
      absurd (lex_le_of_dominates hdom) (not_le.mpr hlt), Nat.cast_zero]
  have hdiag : ∏ ν, (msymmBasis σ R n).toMatrix (schurPolyElem σ R n) ν ν = 1 :=
    Finset.prod_eq_one fun ν _ => by rw [hentry ν ν, kostkaNumber_self, Nat.cast_one]
  rw [Module.Basis.det_apply, Matrix.det_of_isUpperTriangular htri, hdiag]
  exact isUnit_one

variable (σ R n) in
/-- **The Schur basis**: the Schur polynomials `s_μ`, for the partitions `μ` of `n` with at most
`Fintype.card σ` parts, are a basis of the symmetric polynomials in `σ` of degree `n`.  Taken over
`ℤ`, this is the finite-alphabet, fixed-degree form of "the Schur functions are a `ℤ`-basis of the
symmetric functions".  The basis vectors are read off by `TauCeti.coe_schurPolyBasis`.

A commutative *ring* is needed: the transition matrix from the monomial basis is the Kostka matrix,
which is unitriangular and so invertible over any commutative ring, but its inverse has negative
entries, and over a semiring such as `ℕ` the Schur polynomials do not span. -/
noncomputable def schurPolyBasis :
    Module.Basis {ν : n.Partition // ν.parts.card ≤ Fintype.card σ} R
      (symmetricHomogeneousSubmodule σ R n) :=
  .mk ((Module.Basis.is_basis_iff_det _).mpr isUnit_det_schurPolyElem).1
    ((Module.Basis.is_basis_iff_det _).mpr isUnit_det_schurPolyElem).2.ge

/-- **The vectors of the Schur basis are the Schur polynomials**: `TauCeti.schurPolyBasis` is
produced from the invertibility of the Kostka matrix rather than from a formula, and this reads its
basis vectors back as the polynomials `s_μ`.  It is what makes the basis usable: a statement about
`TauCeti.schurPolyBasis` becomes a statement about `TauCeti.schurPoly`. -/
@[simp]
theorem coe_schurPolyBasis (μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    ((schurPolyBasis σ R n μ : symmetricHomogeneousSubmodule σ R n) : MvPolynomial σ R)
      = schurPoly σ R μ.1 := by
  have h : schurPolyBasis σ R n μ = schurPolyElem σ R n μ := Module.Basis.mk_apply _ _ μ
  rw [h]
  rfl

end CommRing

end TauCeti
