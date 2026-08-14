/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Lie.SkewAdjoint
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The trace form of `gl n R` and the anticommutation relations it induces

The general linear Lie algebra `gl n R` is `Matrix n n R` with the commutator bracket. Over a
field of characteristic zero, and for nonempty finite `n`, it is reductive rather than semisimple
(in characteristic `p` it need not even be that: for `n` of cardinality `2` in characteristic `2`,
`sl n` is a solvable ideal strictly larger than the centre). Whatever the characteristic, and again
for nonempty `n` over a nontrivial ring, its Killing form is degenerate: the identity matrix is
central and nonzero, so it lies in the radical of every invariant form built from the adjoint
representation. The form that replaces it is the trace form of the *standard* representation,
`⟨X, Y⟩ = trace (X * Y)`.

That motivation is what singles the form out; none of the hypotheses behind it are needed to build
it. The trace form is symmetric and nondegenerate over an arbitrary commutative semiring and an
arbitrary finite index type, and invariant for the commutator bracket as soon as `R` is a
commutative ring.

This file builds that form, both as a bilinear form (`TauCeti.traceBilinForm`) and as the quadratic
form `X ↦ trace (X * X)` (`TauCeti.traceQuadraticForm`), whose Clifford algebra is the one carrying
the canonical anticommutation relations below, and records the three facts a Clifford construction
consumes: the polar form is `2 • ⟨·, ·⟩`, the form is nondegenerate once `2` is invertible, and the
adjoint action lands in the skew-adjoint endomorphisms of the polar form.

The factors of two are then pinned once and for all on the matrix units. Writing `d_ij` for
`ι (Eᵢⱼ)`, the Clifford relation `ι v * ι v = Q v` polarizes to the canonical anticommutation
relations
`d_ij d_kl + d_kl d_ij = 2 δ_jk δ_li`, `d_ij d_ij = δ_ij`.
These are relations in the Clifford algebra of the trace form; over `ℂ` they are the defining
relations of the CAR algebra on `n × n` matrices, but no identification of that Clifford algebra
with a CAR algebra is made here.

## Main definitions

* `TauCeti.traceBilinForm R n`: the bilinear form `(X, Y) ↦ trace (X * Y)` on `Matrix n n R`.
* `TauCeti.traceQuadraticForm R n`: the quadratic form `X ↦ trace (X * X)`, the form whose
  Clifford algebra carries the anticommutation relations below.
* `TauCeti.traceAdjointSO R n`: the adjoint homomorphism of `gl n R` read into the skew-adjoint
  endomorphisms of the polar form of `TauCeti.traceQuadraticForm R n`.

## Main results

* `TauCeti.traceBilinForm_lieInvariant`: the trace form is invariant, by cyclicity of the trace.
* `TauCeti.traceBilinForm_nondegenerate`: it is nondegenerate over any commutative semiring, a
  matrix being determined by the traces of its products.
* `TauCeti.polarBilin_traceQuadraticForm`: the polar form of the trace quadratic form is
  `2 * trace (X * Y)`, the normalization the roadmap pins;
  `TauCeti.polarBilin_traceQuadraticForm_eq_two_smul` is the same statement as an equality of
  bilinear forms, `2 • traceBilinForm`.
* `TauCeti.traceQuadraticForm_nondegenerate`: the quadratic form is nondegenerate when `2` is
  invertible.
* `TauCeti.traceQuadraticForm_ι_mul_ι_add_swap`: the anticommutation relation
  `ι X ι Y + ι Y ι X = 2 trace (X * Y)` for arbitrary generators, of which
  `TauCeti.traceQuadraticForm_ι_single_mul_ι_single_add_swap`, the canonical anticommutation
  relations `d_ij d_kl + d_kl d_ij = 2 δ_jk δ_li` on the matrix units, is the specialization; and
  `TauCeti.traceQuadraticForm_ι_single_mul_self`: the squares `d_ij d_ij = δ_ij`.

## Implementation notes

The roadmap pins these declarations over `ℂ` for `Matrix (Fin N) (Fin N) ℂ`. Nothing in the
statements or proofs asks for that: the form, its symmetry and its nondegeneracy are stated over an
arbitrary commutative semiring and an arbitrary finite index type, exactly as for the Killing form
in `TauCeti/Algebra/Lie/SkewAdjoint.lean`. Additive inverses are assumed only where the
construction being made needs them: the commutator bracket, `QuadraticMap.polarBilin` and
`CliffordAlgebra` are all available only over a `CommRing`, so the invariance, polar-form, adjoint
and anticommutation declarations carry `[CommRing R]`. Only the transfer of nondegeneracy from the
bilinear form to the quadratic form asks for an invertible `2`, carried as an `Invertible`
hypothesis on the single result that needs it.

Mathlib's `Algebra.traceForm R S` is the trace form of the *regular* representation of an algebra,
which on `Matrix n n R` is `Fintype.card n` times the form built here, so it is not a
reparametrization of it; and `LieModule.traceForm`, which does specialize to this form on the
standard representation, is unavailable without the non-instance
`LieRingModule.ofAssociativeModule`. The form is therefore assembled directly from
`Matrix.traceLinearMap` and `LinearMap.mul`.

The two steps that the trace form shares with the Killing form — the polar form of the quadratic
form of a symmetric `B` is `2 • B`, and nondegeneracy passes from `B` to that quadratic form once
`2` is invertible — are general facts about a bilinear form, stated once in
`TauCeti/LinearAlgebra/QuadraticForm/Radical.lean`
(`LinearMap.BilinMap.polarBilin_toQuadraticMap_of_flip` and
`LinearMap.BilinForm.Nondegenerate.toQuadraticMap`); the declarations here and their Killing
counterparts in `TauCeti/Algebra/Lie/SkewAdjoint.lean` are applications of them.

Mathlib does not register `LieRing.ofAssociativeRing` as a global instance, so, as in
`Mathlib/Algebra/Lie/Matrix.lean`, it is a local instance here.

## References

This is the opening of the `gl_N` worked instance ("the CAR algebra") of Layer 9 of
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`: *"its form is the trace form
`Q X = tr (X²)` (nondegenerate where the Killing form is not) ... the generators `d_ab = ι (E_ab)`
satisfy the CAR relations `d_ab d_cd + d_cd d_ab = 2 δ_bc δ_ad` (pinned as the polar-form
equation)"*, together with the trace-form instance of the layer's adjoint homomorphism
`ad : 𝔤 →ₗ⁅K⁆ 𝔰𝔬(𝔤, B)`.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} {n : Type*} [Fintype n]

section BilinForm

section
variable [CommSemiring R]

variable (R n) in
/-- **The trace form of `gl n R`**, `(X, Y) ↦ trace (X * Y)`: the trace form of the standard
representation, which is nondegenerate where the Killing form of `gl n R` is not. -/
def traceBilinForm : LinearMap.BilinForm R (Matrix n n R) :=
  LinearMap.compr₂ (LinearMap.mul R (Matrix n n R)) (Matrix.traceLinearMap n R R)

@[simp]
theorem traceBilinForm_apply (X Y : Matrix n n R) :
    traceBilinForm R n X Y = (X * Y).trace := (rfl)

variable (R n) in
/-- The trace form is its own flip, by cyclicity of the trace. -/
@[simp]
theorem traceBilinForm_flip : LinearMap.flip (traceBilinForm R n) = traceBilinForm R n := by
  ext X Y
  simp [Matrix.trace_mul_comm Y X]

variable (R n) in
/-- The trace form is symmetric, the predicate form of `TauCeti.traceBilinForm_flip`. -/
theorem traceBilinForm_isSymm : LinearMap.BilinForm.IsSymm (traceBilinForm R n) :=
  LinearMap.BilinForm.isSymm_iff_flip.mpr (traceBilinForm_flip R n)

variable (R n) in
/-- **The trace form is nondegenerate**, over any commutative semiring and any finite index type: a
matrix is determined by the traces of its products. -/
theorem traceBilinForm_nondegenerate : (traceBilinForm R n).Nondegenerate :=
  ⟨fun _ hX => Matrix.ext_iff_trace_mul_right.mpr fun Y => by simpa using hX Y,
    fun _ hY => Matrix.ext_iff_trace_mul_left.mpr fun X => by simpa using hY X⟩

variable [DecidableEq n]

/-- The trace form pairs the matrix units perfectly: `⟨Eᵢⱼ a, E_kl b⟩ = δ_jk δ_li a b`. This is the
`δ` bookkeeping that the anticommutation relations inherit. -/
@[simp high]
theorem traceBilinForm_single_single (i j k l : n) (a b : R) :
    traceBilinForm R n (Matrix.single i j a) (Matrix.single k l b)
      = if j = k ∧ l = i then a * b else 0 := by
  rw [traceBilinForm_apply, Matrix.trace_single_mul, Matrix.single_apply, smul_ite, smul_eq_mul,
    smul_zero]
  refine if_congr (and_congr_left fun _ => eq_comm) rfl rfl

end

variable [CommRing R] [DecidableEq n]

variable (R n) in
/-- **The trace form is invariant**: `trace (⁅X, Y⁆ * Z) = -trace (Y * ⁅X, Z⁆)`, which is cyclicity
of the trace after expanding both brackets. Invariance is what makes the adjoint action skew-adjoint
for the form, hence what produces `TauCeti.traceAdjointSO`. -/
theorem traceBilinForm_lieInvariant :
    LinearMap.BilinForm.lieInvariant (Matrix n n R) (traceBilinForm R n) := by
  intro X Y Z
  simp only [traceBilinForm_apply, LieRing.of_associative_ring_bracket, sub_mul, mul_sub,
    Matrix.trace_sub, neg_sub, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm X (Y * Z), Matrix.mul_assoc]

end BilinForm

section QuadraticForm

section
variable [CommSemiring R]

variable (R n) in
/-- **The trace quadratic form of `gl n R`**, `X ↦ trace (X * X)`. Its Clifford algebra is the one
whose generators satisfy the canonical anticommutation relations
`TauCeti.traceQuadraticForm_ι_single_mul_ι_single_add_swap`. -/
def traceQuadraticForm : QuadraticForm R (Matrix n n R) :=
  LinearMap.BilinMap.toQuadraticMap (traceBilinForm R n)

/-- The trace quadratic form evaluates at `X` to `trace (X * X)`. This is the equation the roadmap
pins `TauCeti.traceQuadraticForm` by. -/
@[simp]
theorem traceQuadraticForm_apply (X : Matrix n n R) :
    traceQuadraticForm R n X = (X * X).trace :=
  LinearMap.BilinMap.toQuadraticMap_apply _ X

end

variable [CommRing R]

variable (R n) in
/-- **The polar form of the trace quadratic form is `2 • ⟨·, ·⟩`**, the trace form being symmetric.
Every factor of two in the anticommutation relations comes from this one equation. -/
@[simp]
theorem polarBilin_traceQuadraticForm_eq_two_smul :
    QuadraticMap.polarBilin (traceQuadraticForm R n) = (2 : R) • traceBilinForm R n := by
  rw [traceQuadraticForm]
  exact LinearMap.BilinMap.polarBilin_toQuadraticMap_of_flip (traceBilinForm_flip R n)

/-- **The polar form of the trace quadratic form, read pointwise**: `2 * trace (X * Y)`. This is the
normalization the roadmap pins, and the equation from which the anticommutation relations follow;
`TauCeti.polarBilin_traceQuadraticForm_eq_two_smul` is the same statement for the forms
themselves. -/
theorem polarBilin_traceQuadraticForm (X Y : Matrix n n R) :
    QuadraticMap.polarBilin (traceQuadraticForm R n) X Y = 2 * (X * Y).trace := by
  rw [polarBilin_traceQuadraticForm_eq_two_smul]
  simp

variable (R n) in
/-- **The trace quadratic form is nondegenerate** over a ring in which `2` is invertible. What
`TauCeti.traceBilinForm_nondegenerate` controls is the trace form `B` itself; `2` must be invertible
both to transfer nondegeneracy from `B` to the polar form `2 • B` and to pass from the polar form
back to the quadratic form, a quadratic form being a finer invariant than its polar form. -/
theorem traceQuadraticForm_nondegenerate [Invertible (2 : R)] :
    (traceQuadraticForm R n).Nondegenerate := by
  rw [traceQuadraticForm]
  exact LinearMap.BilinForm.Nondegenerate.toQuadraticMap (traceBilinForm_nondegenerate R n)
    (traceBilinForm_flip R n)

variable [DecidableEq n]

variable (R n) in
/-- **The adjoint homomorphism of `gl n R` for the trace form**: `ad : gl n R →ₗ⁅R⁆ 𝔰𝔬(gl n R, Q)`,
the trace-form instance of `TauCeti.LieAlgebra.adjointSO`. Composing it with the quadratic
realization inside the Clifford algebra of `TauCeti.traceQuadraticForm R n` would give the adjoint
quadratic lift; that composite is not built here. -/
def traceAdjointSO :
    Matrix n n R →ₗ⁅R⁆
      skewAdjointLieSubalgebra (QuadraticMap.polarBilin (traceQuadraticForm R n)) :=
  LieAlgebra.adjointSO (traceBilinForm R n) (traceBilinForm_lieInvariant R n)

/-- The trace-form adjoint homomorphism is `ad` with its codomain restricted. -/
@[simp]
theorem coe_traceAdjointSO (X : Matrix n n R) :
    (traceAdjointSO R n X : Module.End R (Matrix n n R)) = _root_.LieAlgebra.ad R _ X :=
  LieAlgebra.coe_adjointSO (traceBilinForm R n) (traceBilinForm_lieInvariant R n) X

variable (R n) in
/-- The kernel of the trace-form adjoint homomorphism is the centre of `gl n R`, which for nonempty
`n` over a nontrivial ring is nonzero: the map is not injective, and the adjoint representation of
`gl n R` is therefore unfaithful — the reason the form here is the trace form of the standard
representation and not the Killing form. Over a field of characteristic zero that failure is the
reductive-not-semisimple behaviour of `gl n R`. -/
@[simp]
theorem ker_traceAdjointSO :
    (traceAdjointSO R n).ker = _root_.LieAlgebra.center R (Matrix n n R) :=
  LieAlgebra.ker_adjointSO (traceBilinForm R n) (traceBilinForm_lieInvariant R n)

end QuadraticForm

section CAR

open CliffordAlgebra

variable [CommRing R] [DecidableEq n]

omit [DecidableEq n] in
/-- **The anticommutation relation in the Clifford algebra of the trace form**: any two generators
anticommute up to `2 trace (X * Y)`, the polar-form normalization. -/
theorem traceQuadraticForm_ι_mul_ι_add_swap (X Y : Matrix n n R) :
    ι (traceQuadraticForm R n) X * ι (traceQuadraticForm R n) Y
      + ι (traceQuadraticForm R n) Y * ι (traceQuadraticForm R n) X
      = algebraMap R _ (2 * (X * Y).trace) := by
  rw [ι_mul_ι_add_swap, ← QuadraticMap.polarBilin_apply_apply, polarBilin_traceQuadraticForm]

/-- **The canonical anticommutation relations** on the matrix units: writing `d_ij` for
`ι (Eᵢⱼ)` in the Clifford algebra of the trace quadratic form,
`d_ij d_kl + d_kl d_ij = 2 δ_jk δ_li`,
the matrix units being paired by the trace form exactly when `j = k` and `l = i`. -/
theorem traceQuadraticForm_ι_single_mul_ι_single_add_swap (i j k l : n) (a b : R) :
    ι (traceQuadraticForm R n) (Matrix.single i j a)
        * ι (traceQuadraticForm R n) (Matrix.single k l b)
      + ι (traceQuadraticForm R n) (Matrix.single k l b)
        * ι (traceQuadraticForm R n) (Matrix.single i j a)
      = algebraMap R _ (if j = k ∧ l = i then 2 * (a * b) else 0) := by
  rw [traceQuadraticForm_ι_mul_ι_add_swap, ← traceBilinForm_apply, traceBilinForm_single_single]
  split <;> simp

/-- **The squares of the matrix-unit generators**: `d_ij d_ij = δ_ij`, so the off-diagonal units
square to zero in the Clifford algebra and the diagonal ones square to a scalar. -/
@[simp high]
theorem traceQuadraticForm_ι_single_mul_self (i j : n) (a : R) :
    ι (traceQuadraticForm R n) (Matrix.single i j a)
        * ι (traceQuadraticForm R n) (Matrix.single i j a)
      = algebraMap R _ (if i = j then a * a else 0) := by
  rw [ι_sq_scalar, traceQuadraticForm_apply, ← traceBilinForm_apply,
    traceBilinForm_single_single]
  simp [eq_comm, and_self]

/-- Two matrix-unit generators anticommute whenever they are not paired by the trace form: the
`δ_jk δ_li` of `TauCeti.traceQuadraticForm_ι_single_mul_ι_single_add_swap` vanishes. -/
theorem traceQuadraticForm_ι_single_mul_ι_single_comm_of_not_paired (i j k l : n) (a b : R)
    (h : ¬(j = k ∧ l = i)) :
    ι (traceQuadraticForm R n) (Matrix.single i j a)
        * ι (traceQuadraticForm R n) (Matrix.single k l b)
      = -(ι (traceQuadraticForm R n) (Matrix.single k l b)
        * ι (traceQuadraticForm R n) (Matrix.single i j a)) := by
  rw [eq_neg_iff_add_eq_zero, traceQuadraticForm_ι_single_mul_ι_single_add_swap]
  simp [h]

end CAR

end TauCeti
