/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Tactic.NoncommRing
public import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration

/-!
# Half-normalized Clifford bivectors

The Layer 3 bivector realization of the orthogonal Lie algebra is normalized by its action on
vectors. This module records the generic Clifford-algebra calculation that fixes that normalization
before choosing a standard basis: the half commutator of two generators acts on a third generator
by the polarization of the quadratic form.

The formula is valid over every commutative ring in which `2` is invertible. The factor `⅟2` is
forced: the commutator of the unnormalized expression acts by twice the desired infinitesimal
rotation. This gives the local algebraic input for the roadmap's standard-form
`soEquivBivector_wedge_mulVec` theorem without constructing the transported Lie bracket, the
Lie-algebra equivalence, or a group action.

## Main definitions

* `TauCeti.CliffordAlgebra.cliffordBivector`: the half-normalized commutator of two Clifford
  generators.

## Main results

* `TauCeti.CliffordAlgebra.cliffordBivector_lie_ι`: its commutator action on a generator is the
  infinitesimal rotation determined by `QuadraticMap.polar`.
* `TauCeti.CliffordAlgebra.cliffordBivector_mem_evenOdd_zero` and
  `TauCeti.CliffordAlgebra.cliffordBivector_mem_filtration_two`: it is even and has filtration
  degree at most two.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 3, "the Lie algebra `𝔰𝔬(V) ≅ ⋀²V` inside the Clifford algebra".
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti

namespace CliffordAlgebra

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- The half-normalized Clifford commutator of two generators. Its action on a third generator is
the infinitesimal rotation in `cliffordBivector_lie_ι`; that action, rather than this expression,
fixes the normalization. -/
noncomputable def cliffordBivector (a b : M) : CliffordAlgebra Q :=
  (⅟ (2 : R)) • (ι Q a * ι Q b - ι Q b * ι Q a)

/-- Interchanging the two vectors negates their Clifford bivector. -/
theorem cliffordBivector_swap (a b : M) :
    cliffordBivector Q b a = -cliffordBivector Q a b := by
  rw [cliffordBivector, cliffordBivector, ← smul_neg]
  congr 1
  noncomm_ring

/-- The Clifford bivector of a repeated vector is zero. -/
@[simp]
theorem cliffordBivector_self (a : M) : cliffordBivector Q a a = 0 := by
  rw [cliffordBivector, sub_self, smul_zero]

/-- Clifford bivectors are even. -/
theorem cliffordBivector_mem_evenOdd_zero (a b : M) :
    cliffordBivector Q a b ∈ evenOdd Q 0 := by
  rw [cliffordBivector]
  exact Submodule.smul_mem _ _ <|
    Submodule.sub_mem _ (ι_mul_ι_mem_evenOdd_zero Q a b) (ι_mul_ι_mem_evenOdd_zero Q b a)

/-- Clifford bivectors have filtration degree at most two. -/
theorem cliffordBivector_mem_filtration_two (a b : M) :
    cliffordBivector Q a b ∈ filtration Q 2 := by
  rw [cliffordBivector]
  exact Submodule.smul_mem _ _ <|
    Submodule.sub_mem _ (ι_mul_ι_mem_filtration_two Q a b) (ι_mul_ι_mem_filtration_two Q b a)

/-- The action-normalization identity for the half-normalized Clifford bivector. -/
theorem cliffordBivector_lie_ι (a b x : M) :
    ⁅cliffordBivector Q a b, ι Q x⁆ =
      ι Q (QuadraticMap.polar Q b x • a - QuadraticMap.polar Q a x • b) := by
  rw [cliffordBivector, Ring.lie_def]
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [map_sub, map_smul, map_smul]
  have hbx := ι_mul_ι_add_swap (Q := Q) b x
  have hax := ι_mul_ι_add_swap (Q := Q) a x
  have hA (r : R) : ι Q a * algebraMap R (CliffordAlgebra Q) r = r • ι Q a := by
    calc
      ι Q a * algebraMap R (CliffordAlgebra Q) r = algebraMap R (CliffordAlgebra Q) r * ι Q a :=
        (Algebra.commutes r (ι Q a)).symm
      _ = r • ι Q a := (Algebra.smul_def r (ι Q a)).symm
  have hB (r : R) : ι Q b * algebraMap R (CliffordAlgebra Q) r = r • ι Q b := by
    calc
      ι Q b * algebraMap R (CliffordAlgebra Q) r = algebraMap R (CliffordAlgebra Q) r * ι Q b :=
        (Algebra.commutes r (ι Q b)).symm
      _ = r • ι Q b := (Algebra.smul_def r (ι Q b)).symm
  have h :
      (ι Q a * ι Q b - ι Q b * ι Q a) * ι Q x -
          ι Q x * (ι Q a * ι Q b - ι Q b * ι Q a) =
        (2 : R) • (QuadraticMap.polar Q b x • ι Q a -
          QuadraticMap.polar Q a x • ι Q b) := by
    calc
      (ι Q a * ι Q b - ι Q b * ι Q a) * ι Q x -
          ι Q x * (ι Q a * ι Q b - ι Q b * ι Q a) =
        ι Q a * (ι Q b * ι Q x + ι Q x * ι Q b) -
          ι Q b * (ι Q a * ι Q x + ι Q x * ι Q a) -
          (ι Q a * ι Q x + ι Q x * ι Q a) * ι Q b +
          (ι Q b * ι Q x + ι Q x * ι Q b) * ι Q a := by
            noncomm_ring
      _ = ι Q a * algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q b x) -
          ι Q b * algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q a x) -
          algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q a x) * ι Q b +
          algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q b x) * ι Q a := by
            rw [hbx, hax]
      _ = (2 : R) • (QuadraticMap.polar Q b x • ι Q a -
          QuadraticMap.polar Q a x • ι Q b) := by
            rw [hA, hB, ← Algebra.smul_def, ← Algebra.smul_def]
            rw [two_smul R]
            abel
  rw [h]
  exact invOf_smul_smul (2 : R) _

end CommRing

end CliffordAlgebra

end TauCeti
