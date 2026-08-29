/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Subring
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Zeros

/-!
# Almost every place admits a prescribed integral basis

Let `F' / F` be a finite separable extension and fix an `F`-basis `b` of `F'`. This file proves
that `b` is an integral basis over the valuation ring of all but finitely many places of an
algebraic function field `F / k`. This is Stichtenoth, *Algebraic Function Fields and Codes*,
2nd ed., Theorem 3.3.6.

There are two finiteness steps. First, any fixed element of `F'` is integral over `𝒪_P` for all
but finitely many `P`: outside the poles of the finitely many coefficients of its minimal
polynomial over `F`, that polynomial is defined over `𝒪_P`. Second, apply this simultaneously to
the vectors of `b` and its trace-dual basis. If both bases are integral at `P`, the trace formula
for the coordinates in `b` shows that every integral element has integral coordinates;
integrality of the vectors of `b` proves the converse.

This theorem is the finiteness input for the different divisor: a single basis can be used to
compute the complementary module away from finitely many places.

## Main results

* `TauCeti.Place.finite_setOf_not_isIntegral`: an element integral over `F` is integral over the
  valuation rings of all but finitely many places.
* `TauCeti.Place.finite_setOf_not_isIntegralBasis`: every basis is an integral basis at all but
  finitely many places (Stichtenoth, Theorem 3.3.6).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.3.6.
-/

public section

open Module Polynomial

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F'] [Algebra k F] [Algebra F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-! ### Elements integral at almost every place -/

/-- **A fixed element integral over `F` is integral at all but finitely many places.**

Indeed, outside the poles of the coefficients of its minimal polynomial over `F`, that monic
polynomial has coefficients in `𝒪_P` and witnesses integrality over `𝒪_P`. -/
theorem finite_setOf_not_isIntegral (hF : IsFunctionField k F) (x : F') (hx : IsIntegral F x) :
    {P : Place k F | ¬ IsIntegral P.integers x}.Finite := by
  let p : F[X] := minpoly F x
  let S : Set (Place k F) :=
    ⋃ n ∈ p.support, {P : Place k F | P.ord (p.coeff n) < 0}
  have hS : S.Finite := p.support.finite_toSet.biUnion fun n _ ↦
    finite_setOf_ord_neg hF (p.coeff n)
  refine hS.subset fun P hP ↦ ?_
  by_contra hPS
  apply hP
  have hcoeff : (↑p.coeffs : Set F) ⊆ P.integers := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp ha
    exact P.mem_integers_iff_ord_nonneg.mpr
      (not_lt.mp fun hneg ↦ hPS (by
        simp only [S, Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨n, hn, hneg⟩))
  refine ⟨p.toSubring P.integers.toSubring hcoeff,
    (Polynomial.monic_toSubring p P.integers.toSubring hcoeff).mpr
      (minpoly.monic hx), ?_⟩
  have hmap : (p.toSubring P.integers.toSubring hcoeff).map
      (algebraMap P.integers F) = p :=
    Polynomial.map_toSubring p P.integers.toSubring hcoeff
  rw [IsScalarTower.algebraMap_eq P.integers F F', ← Polynomial.eval₂_map, hmap,
    ← Polynomial.aeval_def]
  exact minpoly.aeval F x

/-! ### Bases integral at almost every place -/

/-- **Every basis of a finite separable extension is an integral basis at all but finitely many
places** (Stichtenoth, Theorem 3.3.6). -/
theorem finite_setOf_not_isIntegralBasis (hF : IsFunctionField k F) {ι : Type*}
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (b : Basis ι F F') :
    {P : Place k F | ¬ P.IsIntegralBasis F' b}.Finite := by
  classical
  let _ := FiniteDimensional.fintypeBasisIndex b
  have hb : (⋃ i, {P : Place k F | ¬ IsIntegral P.integers (b i)}).Finite :=
    Set.finite_iUnion fun i ↦
      finite_setOf_not_isIntegral hF (b i) (Algebra.IsIntegral.isIntegral (b i))
  have hbdual : (⋃ i, {P : Place k F | ¬ IsIntegral P.integers (b.traceDual i)}).Finite :=
    Set.finite_iUnion fun i ↦ finite_setOf_not_isIntegral hF (b.traceDual i)
      (Algebra.IsIntegral.isIntegral (b.traceDual i))
  refine (hb.union hbdual).subset fun P hP ↦ ?_
  by_contra hPmem
  apply hP
  apply IsIntegralBasis.of_isIntegral_of_isIntegral_traceDual F' P b
  · intro i
    by_contra hi
    exact hPmem (Or.inl (Set.mem_iUnion_of_mem i hi))
  · intro i
    by_contra hi
    exact hPmem (Or.inr (Set.mem_iUnion_of_mem i hi))

end Place

end TauCeti

end
