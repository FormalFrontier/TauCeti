/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.FieldTheory.Galois.Basic
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.Matrix.CharpolyFinTwo

/-!
# Trace and norm in a separable quadratic extension

For a separable quadratic extension `L/K` the trace and norm are the two elementary symmetric
functions of the pair `{x, σx}`, where `σ` is the nontrivial automorphism: `tr x = x + σx` and
`N x = x · σx` (`algebraMap_trace_eq_add`, `algebraMap_norm_eq_mul`). Everything else here is a
consequence. The headline is the discriminant characterisation of the generators:

* `discrim_eq_zero_iff_mem_range_algebraMap`: the discriminant `t² - 4n` of `X² - tX + n`, the
  characteristic polynomial of multiplication by `θ`, vanishes exactly when `θ ∈ K`. (That
  polynomial is the *minimal* polynomial of `θ` precisely when `θ ∉ K`, which is what the
  statement says.) Forwards the discriminant equals `(θ - σθ)²`, so it vanishes only where `σ`
  fixes `θ`; `discrim_ne_zero` is the contrapositive, kept separately because it is the
  direction consumers use;
* `exists_discrim_ne_zero` turns that into a choice principle: some `θ` has nonzero
  discriminant, hence generates. This is what a construction over `L/K` picks its generator by.

Three results need neither separability nor a field structure on `L`, and are stated over a
quadratic `K`-algebra that is only a commutative ring — so they also cover the split algebra
`K × K` and the non-reduced `K[X]/(X²)`. They see `L` only as a free `K`-module of rank two:

* `trace_algebraMap_add_algebraMap_mul` and `norm_algebraMap_add_algebraMap_mul` evaluate the
  trace and norm of `b + aθ` — the first by `K`-linearity of the trace, the second from the
  `2 × 2` identity `det (b • 1 + a • M) = b² + ab · tr M + a² · det M`. This is how a statement
  about one generator transfers to another;
* `discrim_eq_zero_of_mem_range_algebraMap`, the easy half of the characterisation: a rational
  `θ = c` has `t = 2c` and `n = c²`, so `t² - 4n = 0`.

Separability is genuinely needed for the other half, and hence for `discrim_ne_zero` and
`exists_discrim_ne_zero`: over a purely inseparable quadratic extension the trace form vanishes,
so `t = 0` and `t² - 4n = 0` for *every* `θ`. In characteristic two `discrim_ne_zero` says
`t ≠ 0`, reflecting that a separable quadratic extension is then Artin–Schreier rather than
Kummer.

These are consumed by the extension quadratic twist in
`TauCeti/AlgebraicGeometry/EllipticCurve/QuadraticTwist.lean`, which advances
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 5 (twists): `exists_discrim_ne_zero` is what the
twist chooses its generator by, and `discrim_ne_zero` is exactly what makes the twist by a
generator elliptic.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/RingTheory/Norm/Quadratic.lean` at the roadmap's pin `bc2fe8ff7396`, FLT PR #1088,
Apache 2.0). That file's own header reads `Authors: Kevin Buzzard, Claude`; following this
repository's convention for adapted material, the upstream authorship is credited here rather
than in the copyright header. Ported with the source's `@[expose]` dropped, and with the two
square-root lemmas left to the PR that consumes them.
-/

public section

section CommRing

variable (K L : Type*) [Field K] [CommRing L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L]

namespace Algebra.IsQuadraticExtension

/-- The trace of `b + aθ` in a quadratic algebra is `a·tr(θ) + 2b`. Neither separability nor
invertibility in `L` is needed: this is `K`-linearity of the trace together with
`tr(b) = [L : K]·b = 2b`. -/
@[simp]
theorem trace_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.trace K L (algebraMap K L b + algebraMap K L a * θ)
      = a * Algebra.trace K L θ + 2 * b := by
  rw [map_add, Algebra.trace_algebraMap, ← Algebra.smul_def, map_smul,
    Algebra.IsQuadraticExtension.finrank_eq_two]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The norm of `b + aθ` in a quadratic algebra is `b² + ab·tr(θ) + a²·N(θ)`. Neither
separability nor invertibility in `L` is needed: in any `K`-basis of `L`, multiplication by
`b + aθ` has matrix `a • M - (-b) • 1` where `M` is the matrix of multiplication by `θ`, and
`TauCeti.Matrix.det_smul_sub_smul_one_fin_two` evaluates that pencil determinant as
`det M · a² + tr M · ab + b²`. -/
@[simp]
theorem norm_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.norm K (algebraMap K L b + algebraMap K L a * θ)
      = b ^ 2 + a * b * Algebra.trace K L θ + a ^ 2 * Algebra.norm K θ := by
  classical
  let bs : Module.Basis (Fin 2) K L :=
    Module.finBasisOfFinrankEq K L (finrank_eq_two K L)
  have key : Algebra.leftMulMatrix bs (algebraMap K L b + algebraMap K L a * θ)
      = a • Algebra.leftMulMatrix bs θ - (-b) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [neg_smul, sub_neg_eq_add, add_comm, map_add, map_mul, AlgHom.commutes, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, Algebra.smul_def]
    simp [Algebra.smul_def]
  rw [Algebra.norm_eq_matrix_det bs, Algebra.trace_eq_matrix_trace bs,
    Algebra.norm_eq_matrix_det bs, key, TauCeti.Matrix.det_smul_sub_smul_one_fin_two]
  ring

/-- The discriminant vanishes on the base field: for `θ = c ∈ K` the trace is `2c` and the norm
is `c²`, so `t² - 4n = 0`. Neither separability nor invertibility in `L` is needed — only that
`L` is free of rank two, so this also covers the split algebra `K × K`, where `θ = (c, c)` is the
statement's content. Over a separable quadratic *extension* it is the converse half of
`discrim_eq_zero_iff_mem_range_algebraMap`, and it is what lets a construction that chose `θ` by
*nonzero discriminant* recover that `θ` generates the extension. It is the `a = 0`, `b = c` case
of the two evaluations above, so it is derived from them rather than recomputed. -/
theorem discrim_eq_zero_of_mem_range_algebraMap {θ : L} (hθ : θ ∈ Set.range (algebraMap K L)) :
    Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ = 0 := by
  obtain ⟨c, rfl⟩ := hθ
  have ht := trace_algebraMap_add_algebraMap_mul K L 0 c (0 : L)
  have hn := norm_algebraMap_add_algebraMap_mul K L 0 c (0 : L)
  simp only [map_zero, zero_mul, add_zero, mul_zero, zero_add] at ht hn
  rw [ht, hn]
  ring

end Algebra.IsQuadraticExtension

end CommRing

section Field

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

namespace Algebra.IsQuadraticExtension

/-- In a separable quadratic extension, the trace of `x` is `x + σx`, where `σ` is the
nontrivial automorphism. -/
theorem algebraMap_trace_eq_add {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (x : L) :
    algebraMap K L (Algebra.trace K L x) = x + σ x := by
  classical
  rw [trace_eq_sum_automorphisms, univ_eq_pair K L hσ, Finset.sum_pair (Ne.symm hσ)]
  simp

/-- In a separable quadratic extension, the norm of `x` is `x * σx`, where `σ` is the
nontrivial automorphism. -/
theorem algebraMap_norm_eq_mul {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (x : L) :
    algebraMap K L (Algebra.norm K x) = x * σ x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, univ_eq_pair K L hσ, Finset.prod_pair (Ne.symm hσ)]
  simp

/-- **Nonzero discriminant characterises the generators** of a separable quadratic extension: for
`t`, `n` the trace and norm of `θ`, so that `θ² = tθ - n`, the discriminant `t² - 4n` of the
characteristic polynomial `X² - tX + n` of multiplication by `θ` vanishes exactly when `θ` lies
in `K`. (Equivalently, that polynomial is the minimal polynomial of `θ` exactly when `θ` does
not lie in `K`.) Forwards, over the nontrivial automorphism `σ` the discriminant equals
`(θ - σθ)²`, so it vanishes only if `σ` fixes `θ`; backwards is
`discrim_eq_zero_of_mem_range_algebraMap`, which needs neither separability nor a field. This is
the form a construction wants: it chooses `θ` by nonzero discriminant and needs to know that `θ`
generates. -/
@[simp]
theorem discrim_eq_zero_iff_mem_range_algebraMap {θ : L} :
    Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ = 0 ↔ θ ∈ Set.range (algebraMap K L) := by
  refine ⟨fun h0 => ?_, discrim_eq_zero_of_mem_range_algebraMap K L⟩
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  have h1 : (θ - σ θ) ^ 2 = 0 := by
    have h2 := congrArg (algebraMap K L) h0
    simp only [map_sub, map_pow, map_mul, map_zero, map_ofNat,
      algebraMap_trace_eq_add K L hσ, algebraMap_norm_eq_mul K L hσ] at h2
    linear_combination h2
  exact mem_range_algebraMap_of_apply_eq K L hσ
    (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1)).symm

/-- A generator of a separable quadratic extension — an element outside `K` — has nonzero
discriminant. The contrapositive half of `discrim_eq_zero_iff_mem_range_algebraMap`, kept as a
named lemma because that is the direction every consumer uses. -/
theorem discrim_ne_zero {θ : L} (hθ : θ ∉ Set.range (algebraMap K L)) :
    Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ ≠ 0 :=
  fun h0 => hθ ((discrim_eq_zero_iff_mem_range_algebraMap K L).mp h0)


/-- A separable quadratic extension has an element of nonzero discriminant `t² - 4n`. Such an
element is automatically a generator, by `discrim_eq_zero_of_mem_range_algebraMap`. Stating it as an
existence result is what lets a construction over `L/K` choose one. -/
theorem exists_discrim_ne_zero :
    ∃ θ : L, Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ ≠ 0 :=
  ⟨_, discrim_ne_zero K L (exists_notMem_range_algebraMap K L).choose_spec⟩

end Algebra.IsQuadraticExtension

end Field

end
