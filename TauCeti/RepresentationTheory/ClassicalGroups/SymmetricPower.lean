/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.LinearAlgebra.SymmetricPower.Basis
public import TauCeti.RepresentationTheory.ClassicalGroups.Diagonal
public import TauCeti.RepresentationTheory.SymmetricPower

/-!
# Symmetric powers of the standard representation

This file specializes symmetric powers of representations to the standard representation of the
general linear group. The resulting action applies a matrix to every factor of a pure symmetric
tensor.

A diagonal matrix acts diagonally on the basis of `Sym[k]^d (Fin n → k)` given by the unordered
`d`-tuples of standard basis vectors, with eigenvalue the product of the corresponding diagonal
entries. Summing those eigenvalues, the character of the `d`th symmetric power at a diagonal
matrix is the `d`th complete homogeneous symmetric polynomial in its diagonal entries, dual to the
elementary symmetric polynomial the exterior power gives.

## Main definitions

* `TauCeti.symFinTwoEquiv` counts the unordered `d`-tuples of indices in two variables.
* `TauCeti.symPowerRep` is the symmetric-power representation of `GL n k`.
* `TauCeti.symPowerFDRep` is its bundled finite-dimensional form.

## Main results

* `TauCeti.eval_hsymm` evaluates the complete homogeneous symmetric polynomial as a sum over the
  unordered `d`-tuples of indices.
* `TauCeti.eval_hsymm_fin_two` reads that off in two variables: `h_d(x, y) = ∑_{i ≤ d} xⁱ y^{d-i}`.
* `TauCeti.char_symPowerRep_diagonal` identifies the character on diagonal matrices with a
  complete homogeneous symmetric polynomial.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “Symmetric and exterior power representations”.
* The standard-representation specialization is adapted from the formal template in
  `TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower`.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

/-- **The complete homogeneous symmetric polynomial evaluated**: `h_d(f)` is the sum, over the
unordered `d`-tuples of indices, of the product of the values `f` takes on the tuple. -/
theorem eval_hsymm {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R] (f : σ → R)
    (d : ℕ) : MvPolynomial.eval f (MvPolynomial.hsymm σ R d)
      = ∑ s : Sym σ d, ((s : Multiset σ).map f).prod := by
  rw [MvPolynomial.hsymm, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_multiset_prod, Multiset.map_map]
  simp [Function.comp_def]

/-- **A multiset of size `d` over `Fin 2` is determined by how many of its entries are `0`**, and
that count can be anything from `0` to `d`: the two counts sum to `d`, so the pair of them runs
over the antidiagonal of `d`.  This is the rank-two instance of the count
`#(Sym α d) = (#α + d - 1).choose d`, in the form the symmetric-polynomial computation below
consumes. -/
noncomputable def symFinTwoEquiv (d : ℕ) : Sym (Fin 2) d ≃ Fin (d + 1) :=
  (Sym.equivNatSumOfFintype (Fin 2) d).trans <|
    ((finTwoArrowEquiv ℕ).subtypeEquiv fun _ => by
      simp [Fin.sum_univ_two, Finset.mem_antidiagonal]).trans
        (Finset.Nat.antidiagonalEquivFin d)

/-- `TauCeti.symFinTwoEquiv` is the number of entries equal to `0`. -/
@[simp]
theorem coe_symFinTwoEquiv_apply (d : ℕ) (s : Sym (Fin 2) d) :
    (symFinTwoEquiv d s : ℕ) = Multiset.count 0 (s : Multiset (Fin 2)) := (rfl)

/-- The inverse of `TauCeti.symFinTwoEquiv` spelled out: `i` many `0`s and `d - i` many `1`s. -/
@[simp]
theorem coe_symFinTwoEquiv_symm_apply (d : ℕ) (i : Fin (d + 1)) :
    (((symFinTwoEquiv d).symm i : Sym (Fin 2) d) : Multiset (Fin 2))
      = Multiset.replicate (i : ℕ) 0 + Multiset.replicate (d - (i : ℕ)) 1 := by
  simp [symFinTwoEquiv, Fin.sum_univ_two, Multiset.nsmul_singleton]

/-- **The complete homogeneous symmetric polynomial in two variables**: `h_d(x, y)` is the sum of
all `d + 1` monomials `xⁱ y^{d-i}` of degree `d`. -/
theorem eval_hsymm_fin_two {R : Type*} [CommSemiring R] (f : Fin 2 → R) (d : ℕ) :
    MvPolynomial.eval f (MvPolynomial.hsymm (Fin 2) R d)
      = ∑ i ∈ Finset.range (d + 1), f 0 ^ i * f 1 ^ (d - i) := by
  rw [eval_hsymm, ← Fin.sum_univ_eq_sum_range _ (d + 1),
    ← Equiv.sum_comp (symFinTwoEquiv d).symm]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [coe_symFinTwoEquiv_symm_apply]
  simp

variable (k : Type) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The `d`th symmetric power of the standard representation of `GL n k`. -/
noncomputable abbrev symPowerRep :
    Representation k (GL (Fin n) k) (Sym[k]^d (Fin n → k)) :=
  (stdRep k n).symmetricPower d

/-- The symmetric power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev symPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (symPowerRep k n d)

end CommRing

section Field

variable [Field k]

/-- The character of the `d`th symmetric power on a diagonal matrix is the `d`th complete
homogeneous symmetric polynomial in its diagonal entries. -/
@[simp]
theorem char_symPowerRep_diagonal (t : Fin n → kˣ) : (symPowerRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.hsymm (Fin n) k d) := by
  rw [Representation.character, Representation.symmetricPower_apply,
    SymmetricPower.trace_map_of_apply_basis (Pi.basisFun k (Fin n))
      (stdRep k n (diagGL t)) (fun i => (t i : k)) d (stdRep_diagGL_apply_basisFun t)]
  -- both sides sum, over the unordered `d`-tuples of indices, the product of the entries listed
  rw [eval_hsymm]

/-- The character of the bundled `d`th symmetric power on a diagonal matrix is the `d`th complete
homogeneous symmetric polynomial in its diagonal entries. -/
@[simp]
theorem char_symPowerFDRep_diagonal (t : Fin n → kˣ) : (symPowerFDRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.hsymm (Fin n) k d) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_symPowerRep_diagonal k n d t

end Field

end TauCeti
