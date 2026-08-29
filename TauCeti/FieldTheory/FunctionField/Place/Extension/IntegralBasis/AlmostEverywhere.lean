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

* `TauCeti.Place.finite_setOf_not_isIntegral`: an element of an algebraic extension is integral over
  the valuation rings of all but finitely many places.
* `TauCeti.Place.IsIntegralBasis.of_isIntegral_traceDual`: a basis and its trace dual being
  integral at a place is sufficient for the basis to be an integral basis there.
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

/-- **A fixed element of an algebraic extension is integral at all but finitely many places.**

Indeed, outside the poles of the coefficients of its minimal polynomial over `F`, that monic
polynomial has coefficients in `𝒪_P` and witnesses integrality over `𝒪_P`. -/
theorem finite_setOf_not_isIntegral (hF : IsFunctionField k F) [Algebra.IsAlgebraic F F']
    (x : F') : {P : Place k F | ¬ IsIntegral P.integers x}.Finite := by
  let p : F[X] := minpoly F x
  have hx : IsIntegral F x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
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
      (algebraMap P.integers F) = p := by
    ext n
    rw [Polynomial.coeff_map, ValuationSubring.algebraMap_apply,
      Polynomial.coeff_toSubring]
  rw [IsScalarTower.algebraMap_eq P.integers F F', ← Polynomial.eval₂_map, hmap]
  exact minpoly.aeval F x

/-! ### Bases integral at almost every place -/

/-- If an `F`-basis of `F'` and its trace-dual basis are integral over `𝒪_P`, then the basis is
an integral basis at `P`.

Integrality of the original basis gives containment of its span in the integral closure.
The coordinates in the original basis are traces against its trace-dual basis. Products and
traces of integral elements are integral, and the valuation ring is integrally closed. -/
theorem IsIntegralBasis.of_isIntegral_traceDual {ι : Type*} [Finite ι] [DecidableEq ι]
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (P : Place k F) (b : Basis ι F F')
    (hb : ∀ i, IsIntegral P.integers (b i))
    (hbdual : ∀ i, IsIntegral P.integers (b.traceDual i)) :
    P.IsIntegralBasis F' b := by
  let _ := Fintype.ofFinite ι
  rw [isIntegralBasis_iff_isIntegral_iff_repr_mem]
  intro x
  constructor
  · intro hx i
    have htrace : IsIntegral P.integers (Algebra.trace F F' (x * b.traceDual i)) :=
      Algebra.isIntegral_trace (hx.mul (hbdual i))
    have hmem : Algebra.trace F F' (x * b.traceDual i) ∈ P.integers := by
      obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp htrace
      rw [← hc]
      exact c.2
    have hrepr : b.repr x i = Algebra.trace F F' (x * b.traceDual i) := by
      calc
        b.repr x i = (b.traceDual.traceDual).repr x i := by rw [b.traceDual_traceDual]
        _ = Algebra.trace F F' (x * b.traceDual i) := by
          rw [Basis.traceDual_repr_apply, Algebra.traceForm_apply]
    rw [hrepr]
    exact hmem
  · intro hx
    rw [← b.sum_repr x]
    apply IsIntegral.sum
    intro i _
    have hc : IsIntegral P.integers (b.repr x i) :=
      IsIntegrallyClosed.isIntegral_iff.mpr ⟨⟨b.repr x i, hx i⟩, rfl⟩
    have hc' : IsIntegral P.integers (algebraMap F F' (b.repr x i)) :=
      IsIntegral.algebraMap hc
    simpa only [Algebra.smul_def] using hc'.mul (hb i)

/-- **Every basis of a finite separable extension is an integral basis at all but finitely many
places** (Stichtenoth, Theorem 3.3.6). -/
theorem finite_setOf_not_isIntegralBasis (hF : IsFunctionField k F) {ι : Type*} [Finite ι]
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (b : Basis ι F F') :
    {P : Place k F | ¬ P.IsIntegralBasis F' b}.Finite := by
  classical
  have hb : (⋃ i, {P : Place k F | ¬ IsIntegral P.integers (b i)}).Finite :=
    Set.finite_iUnion fun i ↦ finite_setOf_not_isIntegral hF (b i)
  have hbdual : (⋃ i, {P : Place k F | ¬ IsIntegral P.integers (b.traceDual i)}).Finite :=
    Set.finite_iUnion fun i ↦ finite_setOf_not_isIntegral hF (b.traceDual i)
  refine (hb.union hbdual).subset fun P hP ↦ ?_
  by_contra hPmem
  apply hP
  apply IsIntegralBasis.of_isIntegral_traceDual P b
  · intro i
    by_contra hi
    exact hPmem (Or.inl (Set.mem_iUnion_of_mem i hi))
  · intro i
    by_contra hi
    exact hPmem (Or.inr (Set.mem_iUnion_of_mem i hi))

end Place

end TauCeti

end
