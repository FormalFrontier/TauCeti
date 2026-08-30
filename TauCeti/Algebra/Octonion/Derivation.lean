/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import TauCeti.Algebra.Lie.Derivation
public import TauCeti.Algebra.Octonion.Basic

/-!
# Derivations of the split octonions

`G₂` is the derivation algebra of the split octonions, and its fundamental representation is
supposed to be the `7`-dimensional space of imaginary octonions. Neither statement can even be made
until one knows that a derivation of `𝕆` lands in the imaginary octonions and respects the norm
form; that is what this file proves.

Let `D` be a derivation of `TauCeti.Octonion R`. Applying `D` to the rank-two equation
`x² = tr x · x - N x · 1` and to the polarization
`x * conj y + y * conj x = ⟨x, y⟩ · 1` of the norm gives one
identity in `𝕆`,

`tr (D x) · x = ⟨x, D x⟩ · 1`,

and everything follows from it. Evaluated at the diagonal idempotent `e = ⟨1, 0, 0, 0⟩` — an
element whose existence is exactly the splitness of `𝕆` — its two diagonal entries read
`tr (D e) = ⟨e, D e⟩` and `0 = ⟨e, D e⟩`. Polarizing it and feeding `e` into the second slot forces
`tr (D x) = 0` for **every** `x`, and with the trace gone the identity itself collapses to
`⟨x, D x⟩ = 0`: a derivation is skew for the norm form.

So `D` maps all of `𝕆` into the imaginary octonions, commutes with conjugation, and lies in the
orthogonal Lie algebra of the norm: `Der 𝕆 ≤ 𝔰𝔬(N)`
(`TauCeti.Octonion.derivationLieAlgebra_le_skewAdjointLieSubalgebra`). In particular the imaginary
octonions are a Lie submodule (`TauCeti.Octonion.imaginaryLieSubmodule`) — this is the candidate
`7`-dimensional fundamental representation — and, when scalar multiplication by `2` on `𝕆` is
regular, `Der 𝕆` acts faithfully on it, since `𝕆 = R · 1 ⊕ Im 𝕆` and a derivation kills `1`.

## Main definitions

* `TauCeti.Octonion.imaginaryLieSubmodule`: the imaginary octonions as a Lie submodule of `𝕆` over
  `Der 𝕆`, so that `Im 𝕆` is a representation of `Der 𝕆`.
* `TauCeti.Octonion.diagonalDerivation`: the derivations coming from the diagonal torus of the
  `SL₃` acting on the vector entries of a Zorn vector matrix.

## Main results

* `TauCeti.Octonion.trace_derivation_apply_eq_zero`: a derivation of `𝕆` has values of trace `0`, so
  (`TauCeti.Octonion.derivation_apply_mem_imaginary`) its image lies in the imaginary octonions.
* `TauCeti.Octonion.derivation_apply_conj`: a derivation commutes with conjugation.
* `TauCeti.Octonion.polar_derivation_apply_self_eq_zero` and
  `TauCeti.Octonion.polar_derivation_apply_left_eq_neg`: a derivation is **skew** for the symmetric
  bilinear form of the norm, `⟨D x, y⟩ = -⟨x, D y⟩`.
* `TauCeti.Octonion.derivationLieAlgebra_le_skewAdjointLieSubalgebra`: `Der 𝕆 ≤ 𝔰𝔬(N)`, the
  previous item as an inclusion of Lie subalgebras of `Module.End R 𝕆`.
* `TauCeti.Octonion.isFaithful_imaginaryLieSubmodule`: when scalar multiplication by `2` on `𝕆` is
  regular, `Der 𝕆` acts faithfully on `Im 𝕆`; `TauCeti.Octonion.instIsFaithfulImaginaryLieSubmodule`
  is the instance form of that, under `[NoZeroSMulDivisors R (Octonion R)]` and `[NeZero (2 : R)]`.
* `TauCeti.Octonion.diagonalDerivation` and
  `TauCeti.Octonion.instNontrivialDerivationLieAlgebra`: the diagonal endomorphisms are derivations,
  so `Der 𝕆` is not the zero Lie algebra and none of the above is vacuous.

## Implementation notes

Everything is stated over a commutative ring; the base is a field nowhere. The faithfulness result
is stated for the exact hypothesis its proof uses, `IsSMulRegular (Octonion R) (2 : R)`, which is
not a class; the instance form of it therefore asks for the two classes
`[NoZeroSMulDivisors R (Octonion R)]` and `[NeZero (2 : R)]`, which imply it but are strictly
stronger. Some such hypothesis is necessary (over `𝔽₂` conjugation is the identity, so `Im 𝕆`
contains `1` and the argument that `Im 𝕆` complements `R · 1` breaks down).

The two coordinate extractions the argument needs — reading the `a` and `b` entries of an equation
between multiples of `⟨1, 0, 0, 0⟩` and of `1` — are isolated in a private lemma, so no public
statement here is about entries of a vector matrix.

Derivations are taken in the bundled form `D : TauCeti.derivationLieAlgebra R (Octonion R)` of
`TauCeti/Algebra/Lie/Derivation.lean`, and are applied through the coercion
`(D : Module.End R (Octonion R))`, which is the simp-normal form of their action there.

## References

This is the first half of the `G₂ = Der(𝕆)` target of Layer 8 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md` ("Build
`derivationLieAlgebra (Octonion K)` ... and that `Im 𝕆` is its `7`-dimensional irreducible"). The
count `finrank (Der 𝕆) = 14`, the type-`G₂` Killing-simplicity, and the identification with
`LieAlgebra.g₂` are not proved here.

* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*, §2.
* R. D. Schafer, *An Introduction to Nonassociative Algebras*, Ch. III, where the skewness of a
  derivation of a composition algebra for its norm form is Lemma 3.4.
-/

public section

namespace TauCeti

namespace Octonion

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} [CommRing R] (D : derivationLieAlgebra R (Octonion R))

/-! ### The key identity -/

/-- Conjugation as a reflection in the trace: `conj x = tr x · 1 - x`, the form of
`TauCeti.Octonion.add_conj` a derivation is applied to. -/
private theorem conj_eq_trace_smul_one_sub (x : Octonion R) :
    conj x = trace x • (1 : Octonion R) - x := by
  rw [← add_conj]
  abel

/-- **A derivation negates conjugated inputs.** It kills `1` and conjugation is the reflection
`x ↦ tr x · 1 - x`, so `D (conj x) = -D x`. Once the values of `D` are known to have vanishing
trace this
upgrades to `TauCeti.Octonion.derivation_apply_conj`, the statement that `D` commutes with
conjugation; that is the form to use, and this one is what proves it. -/
theorem derivation_apply_conj_eq_neg (x : Octonion R) :
    (D : Module.End R (Octonion R)) (conj x) = -(D : Module.End R (Octonion R)) x := by
  rw [conj_eq_trace_smul_one_sub, map_sub, map_smul,
    derivationLieAlgebra.apply_one_eq_zero, smul_zero, zero_sub]

/-- **The identity everything below comes from**: `tr (D x) · x = ⟨x, D x⟩ · 1`.

Applying `D` to the rank-two equation `x² = tr x · x - N x · 1` gives
`D x · x + x · D x = tr x · D x`,
and the polarization `x * conj y + y * conj x = ⟨x, y⟩ · 1` of the norm at `y = D x`, with both
conjugates
rewritten as reflections in the trace, gives
`tr (D x) · x + tr x · D x - (x · D x + D x · x) = ⟨x, D x⟩ · 1`. Substituting the first into the
second is the statement. -/
private theorem trace_derivation_smul_eq_polar_smul_one (x : Octonion R) :
    trace ((D : Module.End R (Octonion R)) x) • x
      = QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) x) •
        (1 : Octonion R) := by
  set d := (D : Module.End R (Octonion R)) x with hd
  have h₁ : d * x + x * d = trace x • d := by
    have h := derivationLieAlgebra.leibniz D x x
    rw [mul_self, map_sub, map_smul, map_smul, derivationLieAlgebra.apply_one_eq_zero, smul_zero,
      sub_zero, ← hd] at h
    exact h.symm
  have h₂ := mul_conj_add_mul_conj x d
  rw [conj_eq_trace_smul_one_sub d, conj_eq_trace_smul_one_sub x, mul_sub, mul_sub,
    mul_smul_comm, mul_one, mul_smul_comm, mul_one] at h₂
  have h₃ : trace d • x + (trace x • d - (d * x + x * d))
      = QuadraticMap.polar (normQuadraticForm R) x d • (1 : Octonion R) := by
    rw [← h₂]; abel
  rwa [h₁, sub_self, add_zero] at h₃

/-- The polarization of `TauCeti.Octonion.trace_derivation_smul_eq_polar_smul_one`: the identity is
quadratic in `x`, and this is its associated bilinear form. -/
private theorem trace_derivation_smul_add_smul (x y : Octonion R) :
    trace ((D : Module.End R (Octonion R)) x) • y + trace ((D : Module.End R (Octonion R)) y) • x
      = (QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) y) +
          QuadraticMap.polar (normQuadraticForm R) y ((D : Module.End R (Octonion R)) x)) •
        (1 : Octonion R) := by
  have hx := trace_derivation_smul_eq_polar_smul_one D x
  have hy := trace_derivation_smul_eq_polar_smul_one D y
  have h := trace_derivation_smul_eq_polar_smul_one D (x + y)
  have hL : trace ((D : Module.End R (Octonion R)) (x + y)) • (x + y)
      = trace ((D : Module.End R (Octonion R)) x) • x +
          trace ((D : Module.End R (Octonion R)) y) • y +
          (trace ((D : Module.End R (Octonion R)) x) • y +
            trace ((D : Module.End R (Octonion R)) y) • x) := by
    rw [map_add, map_add]
    module
  have hR : QuadraticMap.polar (normQuadraticForm R) (x + y)
        ((D : Module.End R (Octonion R)) (x + y))
      = QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) x) +
          QuadraticMap.polar (normQuadraticForm R) y ((D : Module.End R (Octonion R)) y) +
          (QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) y) +
            QuadraticMap.polar (normQuadraticForm R) y ((D : Module.End R (Octonion R)) x)) := by
    rw [map_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_add_right]
    ring
  rw [hL, hR, hx, hy] at h
  have h' : trace ((D : Module.End R (Octonion R)) x) • y +
        trace ((D : Module.End R (Octonion R)) y) • x
      = (QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) x) +
          QuadraticMap.polar (normQuadraticForm R) y ((D : Module.End R (Octonion R)) y) +
          (QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) y) +
            QuadraticMap.polar (normQuadraticForm R) y ((D : Module.End R (Octonion R)) x))) •
          (1 : Octonion R)
        - QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) x) •
          (1 : Octonion R)
        - QuadraticMap.polar (normQuadraticForm R) y ((D : Module.End R (Octonion R)) y) •
          (1 : Octonion R) := by
    rw [← h]; abel
  rw [h']
  module

/-- The two coordinate extractions the argument needs. The diagonal idempotent `⟨1, 0, 0, 0⟩` and
the unit `1 = ⟨1, 1, 0, 0⟩` differ in their second diagonal entry, so an equation between multiples
of them forces both multipliers to vanish. -/
private theorem eq_zero_and_eq_zero_of_smul_diagIdempotent {r c : R}
    (h : r • (⟨1, 0, 0, 0⟩ : Octonion R) = c • (1 : Octonion R)) : r = 0 ∧ c = 0 := by
  have ha := congrArg Octonion.a h
  have hb := congrArg Octonion.b h
  simp only [smul_a, smul_b, one_a, one_b, smul_eq_mul, mul_one, mul_zero] at ha hb
  exact ⟨ha.trans hb.symm, hb.symm⟩

/-! ### Derivations are imaginary-valued and skew -/

/-- **A derivation of `𝕆` has values of trace `0`.**

Evaluating the key identity `tr (D x) · x = ⟨x, D x⟩ · 1` at the diagonal idempotent `e` gives
`tr (D e) = 0`, because the two sides have different second diagonal entries; polarizing the
identity and putting `e` in the second slot then gives `tr (D x) · e = ⟨x, D e⟩ + ⟨e, D x⟩ · 1` for
arbitrary `x`, and the same entry comparison finishes. Not a `simp` lemma, because
`TauCeti.Octonion.trace_apply` already takes its left-hand side apart. -/
theorem trace_derivation_apply_eq_zero (x : Octonion R) :
    trace ((D : Module.End R (Octonion R)) x) = 0 := by
  obtain ⟨he, -⟩ := eq_zero_and_eq_zero_of_smul_diagIdempotent
    (trace_derivation_smul_eq_polar_smul_one D ⟨1, 0, 0, 0⟩)
  have h := trace_derivation_smul_add_smul D x ⟨1, 0, 0, 0⟩
  rw [he, zero_smul, add_zero] at h
  exact (eq_zero_and_eq_zero_of_smul_diagIdempotent h).1

/-- **A derivation of `𝕆` takes imaginary values**, that is
`TauCeti.Octonion.trace_derivation_apply_eq_zero` read through the definition of the imaginary
octonions as the kernel of the trace. In particular the imaginary octonions are stable under `D`;
that is `TauCeti.Octonion.imaginaryLieSubmodule`. Not a `simp` lemma, because
`TauCeti.Octonion.mem_imaginary` and `TauCeti.Octonion.trace_apply` already take its left-hand side
apart, for the same reason as `TauCeti.Octonion.trace_derivation_apply_eq_zero`. -/
theorem derivation_apply_mem_imaginary (x : Octonion R) :
    (D : Module.End R (Octonion R)) x ∈ imaginary R :=
  mem_imaginary.mpr (trace_derivation_apply_eq_zero D x)

/-- **A derivation commutes with conjugation.** Conjugation negates the imaginary octonions and the
values of `D` are imaginary, so the sign in
`TauCeti.Octonion.derivation_apply_conj_eq_neg` is the one conjugation itself supplies. -/
@[simp]
theorem derivation_apply_conj (x : Octonion R) :
    (D : Module.End R (Octonion R)) (conj x) = conj ((D : Module.End R (Octonion R)) x) := by
  rw [derivation_apply_conj_eq_neg,
    mem_imaginary_iff_conj_eq_neg.mp (derivation_apply_mem_imaginary D x)]

/-- **A derivation is skew for the norm form**, in the quadratic form of that statement:
`⟨x, D x⟩ = 0`. This is the key identity once its left-hand side is known to vanish, and it is the
infinitesimal norm-preservation statement `d/dt|₀ N (x + t • D x) = 0`. -/
@[simp]
theorem polar_derivation_apply_self_eq_zero (x : Octonion R) :
    QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) x) = 0 := by
  have h := trace_derivation_smul_eq_polar_smul_one D x
  rw [trace_derivation_apply_eq_zero, zero_smul] at h
  have ha := congrArg Octonion.a h.symm
  simpa using ha

/-- **A derivation is skew for the norm form**: `⟨D x, y⟩ = -⟨x, D y⟩`, the bilinear form of
`TauCeti.Octonion.polar_derivation_apply_self_eq_zero`. Packaged as an inclusion of Lie subalgebras
this is `TauCeti.Octonion.derivationLieAlgebra_le_skewAdjointLieSubalgebra`. -/
theorem polar_derivation_apply_left_eq_neg (x y : Octonion R) :
    QuadraticMap.polar (normQuadraticForm R) ((D : Module.End R (Octonion R)) x) y
      = -QuadraticMap.polar (normQuadraticForm R) x ((D : Module.End R (Octonion R)) y) := by
  have h := polar_derivation_apply_self_eq_zero D (x + y)
  rw [map_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    QuadraticMap.polar_add_right, polar_derivation_apply_self_eq_zero,
    polar_derivation_apply_self_eq_zero, zero_add, add_zero] at h
  rw [QuadraticMap.polar_comm]
  exact eq_neg_of_add_eq_zero_right h

/-- **`Der 𝕆 ≤ 𝔰𝔬(N)`**: every derivation of the split octonions is skew-adjoint for the symmetric
bilinear form of the norm, so the derivation algebra is a Lie subalgebra of the orthogonal Lie
algebra of that form. This is the inclusion `Der 𝕆 ↪ 𝔰𝔬(N)` that the dimension count of `Der 𝕆`
runs through; once `Der 𝕆` is identified with `G₂` — which is not done here — it becomes the
familiar `G₂ ↪ 𝔰𝔬₈`. -/
theorem derivationLieAlgebra_le_skewAdjointLieSubalgebra (R : Type*) [CommRing R] :
    derivationLieAlgebra R (Octonion R)
      ≤ skewAdjointLieSubalgebra (QuadraticMap.polarBilin (normQuadraticForm R)) := by
  intro D hD
  -- Membership in the bundled Lie subalgebra is membership in the skew-adjoint submodule it is
  -- built from; crossing that wrapper is what lets the membership lemma below rewrite.
  change D ∈ (QuadraticMap.polarBilin (normQuadraticForm R)).skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro x y
  simpa using polar_derivation_apply_left_eq_neg ⟨D, hD⟩ x y

/-! ### The imaginary octonions as a representation of `Der 𝕆` -/

/-- **The imaginary octonions as a Lie submodule of `𝕆` over `Der 𝕆`.** A derivation takes
imaginary values on all of `𝕆`, so in particular it preserves the imaginary octonions. This is the
carrier of the candidate `7`-dimensional fundamental representation of `G₂`; its dimension is
`TauCeti.Octonion.finrank_imaginary`, reached through
`TauCeti.Octonion.toSubmodule_imaginaryLieSubmodule`. -/
def imaginaryLieSubmodule (R : Type*) [CommRing R] :
    LieSubmodule R (derivationLieAlgebra R (Octonion R)) (Octonion R) where
  __ := imaginary R
  lie_mem {D _} _ := derivation_apply_mem_imaginary D _

@[simp]
theorem toSubmodule_imaginaryLieSubmodule (R : Type*) [CommRing R] :
    (imaginaryLieSubmodule R).toSubmodule = imaginary R :=
  (rfl)

@[simp]
theorem mem_imaginaryLieSubmodule {x : Octonion R} :
    x ∈ imaginaryLieSubmodule R ↔ trace x = 0 :=
  mem_imaginary

/-- **`Der 𝕆` acts faithfully on the imaginary octonions**, so no information is lost by restricting
the derivation algebra to its candidate fundamental representation.

A derivation kills `1`, and `x - conj x` is imaginary with `D (x - conj x) = 2 · D x`, so a
derivation vanishing on the imaginary octonions vanishes outright as soon as scalar multiplication
by `2` on `𝕆` is regular. That regularity is the exact hypothesis the proof uses; the instance
`TauCeti.Octonion.instIsFaithfulImaginaryLieSubmodule` supplies it from typeclasses. -/
theorem isFaithful_imaginaryLieSubmodule (h2 : IsSMulRegular (Octonion R) (2 : R)) :
    LieModule.IsFaithful R (derivationLieAlgebra R (Octonion R))
      (imaginaryLieSubmodule R) := by
  rw [LieModule.isFaithful_iff']
  intro D hD
  refine derivationLieAlgebra.ext fun x => ?_
  have hx : x - conj x ∈ imaginaryLieSubmodule R := by simp
  have h := congrArg (Subtype.val) (hD ⟨x - conj x, hx⟩)
  rw [LieSubmodule.coe_bracket] at h
  simp only [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply, map_sub,
    derivation_apply_conj_eq_neg, sub_neg_eq_add, ZeroMemClass.coe_zero] at h
  have h₂ : (2 : R) • (D : Module.End R (Octonion R)) x = 0 := by
    rw [two_smul]
    exact h
  simp [h2.right_eq_zero_of_smul h₂]

/-- **`Der 𝕆` acts faithfully on the imaginary octonions** over a base for which `2` is a nonzero
scalar acting without zero divisors, the typeclass form of
`TauCeti.Octonion.isFaithful_imaginaryLieSubmodule`. -/
instance instIsFaithfulImaginaryLieSubmodule [NoZeroSMulDivisors R (Octonion R)]
    [NeZero (2 : R)] :
    LieModule.IsFaithful R (derivationLieAlgebra R (Octonion R))
      (imaginaryLieSubmodule R) :=
  isFaithful_imaginaryLieSubmodule <| IsSMulRegular.of_right_eq_zero_of_smul fun _ h =>
    (eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left (NeZero.ne (2 : R))

/-! ### An explicit family of derivations

Everything above is a statement about an arbitrary derivation, so it is worth knowing that there
are some. `SL₃` acts on the Zorn vector matrices by `⟨a, b, v, w⟩ ↦ ⟨a, b, A v, (Aᵀ)⁻¹ w⟩`, and
differentiating that action at the identity along a traceless *diagonal* matrix `diag (r, s, -r-s)`
gives the derivations below. -/

/-- The endomorphism underlying `TauCeti.Octonion.diagonalDerivation`. -/
private def diagonalDerivationEnd (r s : R) : Module.End R (Octonion R) where
  toFun x := ⟨0, 0, fun i => ![r, s, -r - s] i * x.v i, fun i => -(![r, s, -r - s] i) * x.w i⟩
  map_add' x y := by
    refine Octonion.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_) <;> simp <;> ring
  map_smul' c x := by
    refine Octonion.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_) <;> simp <;> ring

@[simp] private theorem diagonalDerivationEnd_apply_a (r s : R) (x : Octonion R) :
    (diagonalDerivationEnd r s x).a = 0 := (rfl)

@[simp] private theorem diagonalDerivationEnd_apply_b (r s : R) (x : Octonion R) :
    (diagonalDerivationEnd r s x).b = 0 := (rfl)

@[simp] private theorem diagonalDerivationEnd_apply_v (r s : R) (x : Octonion R) (i : Fin 3) :
    (diagonalDerivationEnd r s x).v i = ![r, s, -r - s] i * x.v i := (rfl)

@[simp] private theorem diagonalDerivationEnd_apply_w (r s : R) (x : Octonion R) (i : Fin 3) :
    (diagonalDerivationEnd r s x).w i = -(![r, s, -r - s] i) * x.w i := (rfl)

section Coordinates

open Matrix

attribute [local simp] vec3_dotProduct cross_apply Matrix.vecHead Matrix.vecTail

/-- **The diagonal endomorphisms are derivations.** On the scalar entries the two dot products
`v ⬝ᵥ w'` pick up opposite scalings and cancel; on the vector entries the Leibniz rule is the
infinitesimal Cauchy--Binet relation `(c ⊙ u) ⨯₃ w + u ⨯₃ (c ⊙ w) = -c ⊙ (u ⨯₃ w)`, valid exactly
because `r + s + (-r - s) = 0`. -/
private theorem diagonalDerivationEnd_mem (r s : R) :
    diagonalDerivationEnd r s ∈ derivationLieAlgebra R (Octonion R) := by
  rw [mem_derivationLieAlgebra]
  intro x y
  refine Octonion.ext ?_ ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp; ring
  · simp; ring
  · fin_cases i <;> simp <;> ring
  · fin_cases i <;> simp <;> ring

end Coordinates

/-- **The diagonal derivations of `𝕆`**, the tangent directions at the identity of the diagonal
torus of the `SL₃` acting on the vector entries. They are what shows the results above are not
vacuous: `TauCeti.Octonion.instNontrivialDerivationLieAlgebra`. -/
def diagonalDerivation (r s : R) : derivationLieAlgebra R (Octonion R) :=
  ⟨diagonalDerivationEnd r s, diagonalDerivationEnd_mem r s⟩

@[simp] theorem diagonalDerivation_apply_a (r s : R) (x : Octonion R) :
    ((diagonalDerivation r s : Module.End R (Octonion R)) x).a = 0 := (rfl)

@[simp] theorem diagonalDerivation_apply_b (r s : R) (x : Octonion R) :
    ((diagonalDerivation r s : Module.End R (Octonion R)) x).b = 0 := (rfl)

@[simp] theorem diagonalDerivation_apply_v (r s : R) (x : Octonion R) (i : Fin 3) :
    ((diagonalDerivation r s : Module.End R (Octonion R)) x).v i =
      ![r, s, -r - s] i * x.v i := (rfl)

@[simp] theorem diagonalDerivation_apply_w (r s : R) (x : Octonion R) (i : Fin 3) :
    ((diagonalDerivation r s : Module.End R (Octonion R)) x).w i =
      -(![r, s, -r - s] i) * x.w i := (rfl)

/-- **`𝕆` has nonzero derivations**, so the derivation algebra whose skewness the rest of this file
establishes is not the zero Lie algebra. The witness is the diagonal derivation
`diag (1, 0, -1)`, which sends `⟨0, 0, e₀, 0⟩` to itself. -/
instance instNontrivialDerivationLieAlgebra [Nontrivial R] :
    Nontrivial (derivationLieAlgebra R (Octonion R)) := by
  refine ⟨diagonalDerivation 1 0, 0, fun h => ?_⟩
  -- the derivation sends `⟨0, 0, e₀, 0⟩` to itself, so `h` reads `(1 : R) = 0`
  have h₁ := congrArg (fun D : derivationLieAlgebra R (Octonion R) =>
    ((D : Module.End R (Octonion R)) ⟨0, 0, ![1, 0, 0], 0⟩).v 0) h
  simp at h₁

end Octonion

end TauCeti
