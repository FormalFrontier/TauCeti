/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.RingTheory.Huber.PowerBounded
public import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# Nakayama for a matrix with topologically nilpotent entries

Over a complete nonarchimedean ring, `1 - B` is invertible as soon as every entry of `B` is
topologically nilpotent, and consequently a family satisfying `yᵢ = ∑ⱼ Bᵢⱼ • yⱼ` vanishes.

The vanishing argument is split from its topological input. Once `1 - B` is a unit the conclusion
is pure algebra, and `TauCeti.eq_zero_of_isUnit_one_sub_of_forall_eq_sum_smul` states it that way
in `TauCeti.LinearAlgebra.Matrix.Module`, where it needs no ring theory at all: the module `P`
carries **no topology**, and `A` need not be commutative, which is what lets it be applied where
`P` is an abstract subquotient. This file supplies only the topological input.

## Main results

* `TauCeti.Huber.isTopologicallyNilpotent_one_sub_det_one_sub`: `1 - det (1 - B)` is topologically
  nilpotent.
* `TauCeti.Huber.isUnit_one_sub_of_isTopologicallyNilpotent_entries`: hence `1 - B` is a unit.
* `TauCeti.Huber.eq_zero_of_isTopologicallyNilpotent_entries_of_forall_eq_sum_smul`: the
  topological criterion combined with the algebraic core, which is imported from
  `TauCeti.LinearAlgebra.Matrix.Module`.

## References

* [S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*][bosch_guntzer_remmert],
  §3.7.2/1, where this is the algebraic engine behind closedness of finitely generated submodules.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB` @ `37bbdaeb9`, Apache-2.0) has all three of the
topological statements in `projects/AdicSpaces/Adic spaces/Bounded.lean` —
`IsTopologicallyNilpotent.one_sub_det_one_sub_matrix` (:666),
`IsTopologicallyNilpotent.isUnit_one_sub_matrix` (:704) and
`eq_zero_of_forall_eq_sum_topNilp_smul` (:740) — and takes **the same route**: lift to the
power-bounded subring, reduce modulo the topologically nilpotent ideal, apply `RingHom.map_det`,
then `Matrix.isUnit_iff_isUnit_det`. This module was written against this repository's own API and
compared afterwards; since the routes coincide it should be read as a re-derivation of that
argument rather than an independent one. Nothing was copied: the names differ throughout, the
hypotheses here are the plain nonarchimedean bundle rather than AINTLIB's section variables, the
vanishing step goes through Mathlib's `Matrix.Module` action, and the algebraic core is split out,
which AINTLIB does not do.
-/

public section

open scoped Matrix.Module

namespace TauCeti.Huber

/-! ### The determinant modulo topologically nilpotent entries -/

section Topological

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The entries of `B`, viewed in `A°`. Topologically nilpotent elements are power-bounded, so
this is well defined, and it is what puts `B` inside the ideal `A°°` where the determinant
computation happens. -/
private def toPowerBoundedMatrix (B : Matrix n n A)
    (hB : ∀ i j, IsTopologicallyNilpotent (B i j)) : Matrix n n (powerBoundedSubring A) :=
  Matrix.of fun i j ↦ ⟨B i j, mem_powerBoundedSubring.mpr
    (IsPowerBounded.of_isTopologicallyNilpotent (hB i j))⟩

/-- **The determinant of `1 - B` is `1` up to a topologically nilpotent error.** Every entry of
`B` lies in the ideal `A°°` of `A°`, so `1 - B` reduces to the identity modulo that ideal and its
determinant reduces to `1`. -/
theorem isTopologicallyNilpotent_one_sub_det_one_sub {B : Matrix n n A}
    (hB : ∀ i j, IsTopologicallyNilpotent (B i j)) :
    IsTopologicallyNilpotent (1 - (1 - B).det) := by
  set I := topologicallyNilpotentIdeal A with hI
  set B' := toPowerBoundedMatrix B hB with hB'
  have hmap : (Ideal.Quotient.mk I).mapMatrix (1 - B') = 1 := by
    ext i j
    have hzero : Ideal.Quotient.mk I (B' i j) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr (mem_topologicallyNilpotentIdeal.mpr (hB i j))
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, hzero,
      Matrix.one_apply, apply_ite (Ideal.Quotient.mk I)]
  have hmod : Ideal.Quotient.mk I (1 - B').det = 1 := by
    rw [RingHom.map_det, hmap, Matrix.det_one]
  have hmem : (1 : powerBoundedSubring A) - (1 - B').det ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hmod, map_one, sub_self]
  have hcoemap : (powerBoundedSubring A).subtype.mapMatrix (1 - B') = 1 - B := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
      hB', toPowerBoundedMatrix, apply_ite ((↑) : powerBoundedSubring A → A)]
  have hcoe : ((1 - B').det : A) = (1 - B).det := by
    simpa only [← RingHom.map_det, Subring.coe_subtype] using
      congrArg Matrix.det hcoemap
  simpa [hcoe] using (mem_topologicallyNilpotentIdeal.mp hmem)

end Topological

/-! ### Invertibility, and Nakayama -/

section Complete

variable {A : Type*} [CommRing A] [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsUniformAddGroup A] [NonarchimedeanRing A] {n : Type*} [Fintype n] [DecidableEq n]

/-- **`1 - B` is invertible when every entry of `B` is topologically nilpotent.** The determinant
is `1` minus a topologically nilpotent element, hence a unit by the geometric series, and a square
matrix over a commutative ring is a unit exactly when its determinant is. -/
theorem isUnit_one_sub_of_isTopologicallyNilpotent_entries {B : Matrix n n A}
    (hB : ∀ i j, IsTopologicallyNilpotent (B i j)) : IsUnit (1 - B) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simpa using (isTopologicallyNilpotent_one_sub_det_one_sub hB).isUnit_one_sub

omit [DecidableEq n] in
/-- **Nakayama for topologically nilpotent entries.** If every entry of `B` is topologically
nilpotent and `yᵢ = ∑ⱼ Bᵢⱼ • yⱼ` for every `i`, then the whole family vanishes. This is
`TauCeti.eq_zero_of_isUnit_one_sub_of_forall_eq_sum_smul` with its hypothesis discharged; a
consumer wanting a single coordinate applies `congrFun`. -/
theorem eq_zero_of_isTopologicallyNilpotent_entries_of_forall_eq_sum_smul {P : Type*}
    [AddCommGroup P] [Module A P] {B : Matrix n n A} (hB : ∀ i j, IsTopologicallyNilpotent (B i j))
    {y : n → P} (hy : ∀ i, y i = ∑ j, B i j • y j) : y = 0 := by
  classical
  exact eq_zero_of_isUnit_one_sub_of_forall_eq_sum_smul
    (isUnit_one_sub_of_isTopologicallyNilpotent_entries hB) hy

end Complete

end TauCeti.Huber
