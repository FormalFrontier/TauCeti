/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `GL`, `Matrix.GeneralLinearGroup.det` and `Matrix.GeneralLinearGroup.scalar` occur in the
-- statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `Basis` occurs in the statements below.
public import Mathlib.LinearAlgebra.Basis.Defs
-- `Algebra.leftMulMatrix` is the body of `TauCeti.unitsLeftMulMatrix`, so it must be imported
-- publicly.
public import Mathlib.LinearAlgebra.Matrix.ToLin
-- `Algebra.norm` and `Algebra.trace` occur in the statements below.
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs

/-!
# The unit group of an algebra inside a general linear group

Let `S` be an algebra over a commutative semiring `R`, free with basis `b : Module.Basis ι R S`.
Multiplication by `x : S` is an `R`-linear endomorphism of `S`, and its matrix in the basis `b` is
Mathlib's `Algebra.leftMulMatrix b x`. When `x` is a **unit** that matrix is invertible, so the
regular representation restricts to a group homomorphism

`TauCeti.unitsLeftMulMatrix b : Sˣ →* GL ι R`.

It is injective, it sends a unit of the base ring to the corresponding scalar matrix, and it
converts the two standard invariants of an element of `S` into the two standard invariants of a
matrix: its determinant is the algebra norm and its trace is the algebra trace. Only these last
two ask for a ring, the level `Algebra.norm` and `Algebra.trace` are stated at; the embedding
itself lives over a semiring.

The motivating instance is a degree-`2` field extension `E/F`, where this embeds `Eˣ` in
`GL (Fin 2) F` as the **non-split torus**; see
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/NonSplitTorus.lean`. Compare `TauCeti.diagGL`,
which embeds the *split* torus.

## Main definitions

* `TauCeti.unitsLeftMulMatrix`: the units of `S` acting on `S` by left multiplication, read in a
  basis as elements of `GL ι R`.

## Main results

* `TauCeti.unitsLeftMulMatrix_injective`: the embedding is injective.
* `TauCeti.val_det_unitsLeftMulMatrix`: its determinant is `Algebra.norm R`.
* `TauCeti.trace_unitsLeftMulMatrix`: its trace is `Algebra.trace R S`.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9.
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
-/

public section

open Matrix

namespace TauCeti

variable {R S ι : Type*} [Fintype ι] [DecidableEq ι]

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S] (b : Module.Basis ι R S)

/-- The units of `S`, embedded in `GL ι R` by left multiplication read in the basis `b`. -/
noncomputable def unitsLeftMulMatrix : Sˣ →* GL ι R :=
  Units.map (Algebra.leftMulMatrix b).toRingHom.toMonoidHom

/-- The matrix underlying `unitsLeftMulMatrix b x` is `Algebra.leftMulMatrix b x`. -/
@[simp, grind =]
theorem coe_unitsLeftMulMatrix (x : Sˣ) :
    (unitsLeftMulMatrix b x : Matrix ι ι R) = Algebra.leftMulMatrix b (x : S) := by
  rfl

-- Not a `simp` lemma: `simp` rewrites the coercion on the left-hand side through
-- `coe_unitsLeftMulMatrix` first, so this lemma would never fire.
/-- The entries of `unitsLeftMulMatrix b x` are the coordinates of `x * b j` in the basis `b`. -/
theorem unitsLeftMulMatrix_apply (x : Sˣ) (i j : ι) :
    (unitsLeftMulMatrix b x : Matrix ι ι R) i j = b.repr ((x : S) * b j) i :=
  Algebra.leftMulMatrix_eq_repr_mul b (x : S) i j

/-- Left multiplication by a unit determines the unit. -/
theorem unitsLeftMulMatrix_injective : Function.Injective (unitsLeftMulMatrix b) := fun _ _ h =>
  Units.ext (Algebra.leftMulMatrix_injective b (congrArg Units.val h))

/-- A unit of the base ring is sent to the corresponding scalar matrix. -/
@[simp, grind =]
theorem unitsLeftMulMatrix_map_algebraMap (r : Rˣ) :
    unitsLeftMulMatrix b (Units.map (algebraMap R S : R →* S) r) =
      Matrix.GeneralLinearGroup.scalar ι r := by
  refine Units.ext ?_
  have hr : ((Units.map (algebraMap R S : R →* S) r : Sˣ) : S) = algebraMap R S (r : R) := rfl
  rw [coe_unitsLeftMulMatrix, Matrix.GeneralLinearGroup.coe_scalar, hr,
    (Algebra.leftMulMatrix b).commutes (r : R)]
  ext i j
  rw [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  simp

end Semiring

section CommRing

variable [CommRing R]

-- Not a `simp` lemma, for the same reason `Algebra.norm_eq_matrix_det` is not: the left-hand side
-- mentions a choice of basis, which `simp` normalizes away through `coe_unitsLeftMulMatrix`.
/-- The determinant of the matrix of left multiplication by `x` is the algebra norm of `x`. -/
theorem val_det_unitsLeftMulMatrix [Ring S] [Algebra R S] (b : Module.Basis ι R S) (x : Sˣ) :
    (Matrix.GeneralLinearGroup.det (unitsLeftMulMatrix b x) : R) = Algebra.norm R (x : S) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_unitsLeftMulMatrix, Algebra.norm_eq_matrix_det b]

-- Not a `simp` lemma, for the same reason `Algebra.trace_eq_matrix_trace` is not.
/-- The trace of the matrix of left multiplication by `x` is the algebra trace of `x`. -/
theorem trace_unitsLeftMulMatrix [CommRing S] [Algebra R S] (b : Module.Basis ι R S) (x : Sˣ) :
    Matrix.trace (unitsLeftMulMatrix b x : Matrix ι ι R) = Algebra.trace R S (x : S) := by
  rw [coe_unitsLeftMulMatrix, Algebra.trace_eq_matrix_trace b]

end CommRing

end TauCeti
