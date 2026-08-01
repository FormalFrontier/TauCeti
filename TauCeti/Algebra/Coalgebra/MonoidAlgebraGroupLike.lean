/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Group-like elements of monoid algebras

Over a commutative ring with connected prime spectrum, the group-like elements of a
monoid algebra are exactly its standard basis elements. The proof compares coefficients
in the group-like comultiplication identity. Connectedness makes every idempotent
coefficient zero or one, and the counit condition excludes the zero element.

## Main declarations

* `TauCeti.MonoidAlgebra.isGroupLikeElem_single_one`: standard basis elements are
  group-like.
* `TauCeti.MonoidAlgebra.isGroupLikeElem_iff_eq_single`: classification of group-like
  elements in a monoid algebra over a connected base.
-/

public section

namespace TauCeti

universe u v

namespace MonoidAlgebra

variable (R : Type u)

private theorem eq_zero_or_eq_one_of_isIdempotentElem
    [CommRing R] [ConnectedSpace (PrimeSpectrum R)] (e : R) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have hopen : IsClopen
      (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases _root_.isClopen_iff.mp hopen with hempty | huniv
  · left
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .zero
    apply SetLike.ext'
    simpa only [PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot] using hempty
  · right
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .one
    apply SetLike.ext'
    simpa only [PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top] using huniv

/-- A standard basis element of a monoid algebra with coefficient one is group-like. -/
theorem isGroupLikeElem_single_one [CommSemiring R] {H : Type v} [Monoid H] (h : H) :
    IsGroupLikeElem R (_root_.MonoidAlgebra.single h (1 : R)) := by
  constructor
  · simp
  · rw [_root_.MonoidAlgebra.comul_single, CommSemiring.comul_apply]
    simp

private theorem tensorEquiv_comul_apply [CommSemiring R]
    {H : Type v} [Monoid H] [DecidableEq H]
    (x : _root_.MonoidAlgebra R H) (g h : H) :
    (_root_.MonoidAlgebra.tensorEquiv R (Coalgebra.comul x)).coeff (g, h) =
      if g = h then x.coeff g else 0 := by
  induction x using _root_.MonoidAlgebra.induction_on with
  | of k =>
      by_cases hgh : g = h <;>
        simp_all [_root_.MonoidAlgebra.comul_single, Finsupp.single_apply]
  | add x y hx hy =>
      by_cases hgh : g = h <;> simp_all
  | smul r x hx =>
      by_cases hgh : g = h <;> simp_all

/-- Over a commutative ring with connected prime spectrum, the group-like elements
of a monoid algebra are exactly its standard basis elements, with a unique basis
index. -/
theorem isGroupLikeElem_iff_eq_single [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {H : Type v} [Monoid H]
    (x : _root_.MonoidAlgebra R H) :
    IsGroupLikeElem R x ↔
      ∃! h : H, x = _root_.MonoidAlgebra.single h 1 := by
  classical
  letI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  constructor
  · intro hx
    have hcoeff (g h : H) :
        (if g = h then x.coeff g else 0) = x.coeff g * x.coeff h := by
      have hcomul := congrArg
        (fun y : TensorProduct R (_root_.MonoidAlgebra R H) (_root_.MonoidAlgebra R H) =>
          (_root_.MonoidAlgebra.tensorEquiv R y).coeff (g, h)) hx.comul_eq_tmul_self
      rw [tensorEquiv_comul_apply] at hcomul
      simpa using hcomul
    have hcoeff_zero_or_one (g : H) : x.coeff g = 0 ∨ x.coeff g = 1 := by
      apply eq_zero_or_eq_one_of_isIdempotentElem R
      exact isIdempotentElem_iff.mpr (by simpa using (hcoeff g g).symm)
    have hx_coeff_ne : x.coeff ≠ 0 := by
      intro hzero
      apply hx.ne_zero
      apply _root_.MonoidAlgebra.coeff_injective
      simpa using hzero
    obtain ⟨h, hh⟩ := Finsupp.support_nonempty_iff.mpr hx_coeff_ne
    have hh_one : x.coeff h = 1 :=
      (hcoeff_zero_or_one h).resolve_left (Finsupp.mem_support_iff.mp hh)
    have hx_single : x = _root_.MonoidAlgebra.single h 1 := by
      apply _root_.MonoidAlgebra.ext
      ext k
      by_cases hk : k = h
      · subst k
        simp [hh_one]
      · have hk_zero : x.coeff k = 0 := by
          have horth := hcoeff k h
          rw [if_neg hk, hh_one, mul_one] at horth
          exact horth.symm
        simp [hk, hk_zero]
    refine ⟨h, hx_single, ?_⟩
    intro h' hx_single'
    exact _root_.MonoidAlgebra.single_left_injective
      (R := R) (M := H) one_ne_zero (hx_single'.symm.trans hx_single)
  · rintro ⟨h, rfl, -⟩
    exact isGroupLikeElem_single_one R h

end MonoidAlgebra

end TauCeti
