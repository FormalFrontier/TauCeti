/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import TauCeti.RingTheory.Polynomial.IsIntegral

import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Field

/-!
# Changes of variables between integral models

A change of variables `D : VariableChange K` carrying one integral Weierstrass model to another
need not be integral itself: its scaling factor `D.u` is a unit of `K`, and `D.r`, `D.s`, `D.t` are
elements of `K`. This file shows that when `R` is integrally closed in `K`, as soon as `D.u` comes
from a unit of `R` the rest follows — `D` is the base change of a `VariableChange R`.

## Main results

* `WeierstrassCurve.VariableChange.exists_baseChange_eq_of_smul_eq`: for `R` integrally closed in
  `K` (`IsIntegrallyClosedIn R K`), if `D • W₁ = W₂` with `W₁` and `W₂` integral over `R` and `D.u`
  the image of a unit of `R`, then `D = C₀.baseChange K` for some `C₀ : VariableChange R`.

The integral-closedness hypothesis is what the proof actually consumes. A discrete valuation ring
with its fraction field is the intended application and satisfies it through
`isIntegrallyClosed_iff_isIntegrallyClosedIn`, but no valuation is used anywhere below.

## How it is proved

Each of `r`, `s`, `t` is exhibited as a root of an explicit **monic** polynomial over `R`, built
from the change-of-variables formulas for the invariants, and `R` is integrally closed:

* `r` from the `b₆`- and `b₈`-relations, as a root of a quartic. The two are combined as
  `b₈-relation − r · b₆-relation`: that cancels the `r³ · b₂` terms and turns `3r⁴ − 4r⁴` into
  `−r⁴`, leaving `b₈ + 2r · b₆ + r² · b₄ − r⁴`. The `r⁴` term does not cancel and must not — it is
  the quartic's leading term;
* `s` from the `a₂`-relation, as a root of a quadratic, once `r` is known to lie in `R`;
* `t` from the `a₆`-relation, likewise a quadratic, once `r` is known.

The three arguments are separate private lemmas rather than one proof: each is a distinct
integrality certificate with its own polynomial, and taken together they are past the repository's
hard cap on proof length. `s` and `t` take the integral representative of `r` as a hypothesis,
which is why they are stated after it rather than beside it.

## Why this is not in `EllipticCurve/VariableChange.lean`

That file is where this repository keeps its `VariableChange` API, and the statement below is about
`VariableChange.baseChange`, so it would sit there naturally — except that the proof needs
`WeierstrassCurve.IsIntegral` and `integralModel`, i.e. Mathlib's `EllipticCurve.Reduction` with its
valuation machinery. `VariableChange.lean` currently imports only
`Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange`, and three modules import it; putting the
descent there would push the reduction cone onto all of them. The topic here is integral models, so
the file is named for them.

## Provenance

⚠ *mathlib-track*. Statements about Mathlib's own `IsIntegral` for Weierstrass models and
`VariableChange.baseChange`, with no Tau Ceti definitions involved.

Ported from FLT, https://github.com/ImperialCollegeLondon/FLT
@ `bc2fe8ff7396469a16c2a6d51d6117f5825d93a0` (Apache-2.0), file
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`, declaration
`WeierstrassCurve.exists_variableChange_baseChange_eq_of_smul_eq`, by Kevin Buzzard. The source
commit is FLT PR #1088, "Quadratic twist to split multiplicative reduction". The mathematics is
unchanged: the same three polynomials, the same `linear_combination` certificates. The single
66-line proof is split into the three integrality arguments plus their assembly, so that no
declaration exceeds the length cap. Two hypotheses are weakened relative to the source, which
states the descent for a discrete valuation ring: the integrality certificates need only
`Algebra R K`, and the assembly needs only `IsIntegrallyClosedIn R K`.
-/

public section

namespace WeierstrassCurve

namespace VariableChange

variable (R : Type*) [CommRing R] {K : Type*} [Field K] [Algebra R K]

/-! ### The three integrality certificates

These need nothing of `R` beyond its algebra structure on `K`: each exhibits a monic polynomial
over `R` killing the coordinate. Integral closedness enters only in the assembly below, which is
where the roots are pulled back into `R`. -/

/-- **`r` is integral**: it is a root of the monic quartic obtained from the `b₆`- and
`b₈`-relations as `b₈-relation − r · b₆-relation`. -/
private theorem isIntegral_r_of_smul_eq {W₁ W₂ : WeierstrassCurve K} [IsIntegral R W₁]
    [IsIntegral R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) (u₀ : Rˣ)
    (hau : algebraMap R K ↑u₀ = ↑D.u) : _root_.IsIntegral R D.r := by
  have hb₆ : (↑D.u : K) ^ 6 * W₂.b₆
      = W₁.b₆ + 2 * D.r * W₁.b₄ + D.r ^ 2 * W₁.b₂ + 4 * D.r ^ 3 := by
    rw [← hD, variableChange_b₆]
    simp only [Units.val_inv_eq_inv_val]
    field
  have hb₈ : (↑D.u : K) ^ 8 * W₂.b₈
      = W₁.b₈ + 3 * D.r * W₁.b₆ + 3 * D.r ^ 2 * W₁.b₄ + D.r ^ 3 * W₁.b₂ + 3 * D.r ^ 4 := by
    rw [← hD, variableChange_b₈]
    simp only [Units.val_inv_eq_inv_val]
    field
  refine ⟨.X ^ 4 + (.C (-(W₁.integralModel R).b₄) * .X ^ 2
      + .C (-(2 * (W₁.integralModel R).b₆) - (↑u₀ : R) ^ 6 * (W₂.integralModel R).b₆) * .X
      + .C ((↑u₀ : R) ^ 8 * (W₂.integralModel R).b₈ - (W₁.integralModel R).b₈)),
    Polynomial.monic_X_pow_add (by compute_degree!), ?_⟩
  rw [← Polynomial.aeval_def]
  simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, Polynomial.aeval_X,
    Polynomial.aeval_C]
  rw [integralModel_b₄_eq R W₁, integralModel_b₆_eq R W₁, integralModel_b₈_eq R W₁,
    integralModel_b₆_eq R W₂, integralModel_b₈_eq R W₂, hau]
  linear_combination hb₈ - D.r * hb₆

/-- **`s` is integral**, given an integral representative `rR` of `r`: it is a root of the monic
quadratic coming from the `a₂`-relation. -/
private theorem isIntegral_s_of_smul_eq {W₁ W₂ : WeierstrassCurve K} [IsIntegral R W₁]
    [IsIntegral R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) (u₀ : Rˣ)
    (hau : algebraMap R K ↑u₀ = ↑D.u) (rR : R) (hrR : algebraMap R K rR = D.r) :
    _root_.IsIntegral R D.s := by
  have ha₂ : (↑D.u : K) ^ 2 * W₂.a₂ = W₁.a₂ - D.s * W₁.a₁ + 3 * D.r - D.s ^ 2 := by
    rw [← hD, variableChange_a₂]
    simp only [Units.val_inv_eq_inv_val]
    field
  refine IsIntegral.of_sq_add_mul_add_eq_zero (b := algebraMap R K (W₁.integralModel R).a₁)
    (c := algebraMap R K ((↑u₀ : R) ^ 2 * (W₂.integralModel R).a₂
      - (W₁.integralModel R).a₂ - 3 * rR)) isIntegral_algebraMap isIntegral_algebraMap ?_
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [integralModel_a₁_eq R W₁, integralModel_a₂_eq R W₁, integralModel_a₂_eq R W₂, hau, hrR]
  linear_combination ha₂

/-- **`t` is integral**, given an integral representative `rR` of `r`: it is a root of the monic
quadratic coming from the `a₆`-relation. -/
private theorem isIntegral_t_of_smul_eq {W₁ W₂ : WeierstrassCurve K} [IsIntegral R W₁]
    [IsIntegral R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) (u₀ : Rˣ)
    (hau : algebraMap R K ↑u₀ = ↑D.u) (rR : R) (hrR : algebraMap R K rR = D.r) :
    _root_.IsIntegral R D.t := by
  have ha₆ : (↑D.u : K) ^ 6 * W₂.a₆ = W₁.a₆ + D.r * W₁.a₄ + D.r ^ 2 * W₁.a₂ + D.r ^ 3
      - D.t * W₁.a₃ - D.t ^ 2 - D.r * D.t * W₁.a₁ := by
    rw [← hD, variableChange_a₆]
    simp only [Units.val_inv_eq_inv_val]
    field
  -- The constant term is `u₀⁶ · a₆(W₂)` MINUS the bracketed `r`-polynomial in `W₁`'s invariants;
  -- written as a subtraction so the sign of the `a₆(W₂)` term cannot be misread across the wrap.
  refine IsIntegral.of_sq_add_mul_add_eq_zero
    (b := algebraMap R K ((W₁.integralModel R).a₃ + rR * (W₁.integralModel R).a₁))
    (c := algebraMap R K ((↑u₀ : R) ^ 6 * (W₂.integralModel R).a₆
      - ((W₁.integralModel R).a₆ + rR * (W₁.integralModel R).a₄
        + rR ^ 2 * (W₁.integralModel R).a₂ + rR ^ 3)))
    isIntegral_algebraMap isIntegral_algebraMap ?_
  simp only [map_add, map_sub, map_mul, map_pow]
  rw [integralModel_a₁_eq R W₁, integralModel_a₂_eq R W₁, integralModel_a₃_eq R W₁,
    integralModel_a₄_eq R W₁, integralModel_a₆_eq R W₁, integralModel_a₆_eq R W₂, hau, hrR]
  linear_combination ha₆

/-! ### Assembly

Pulling the three roots back into `R` is exactly `IsIntegrallyClosedIn R K`, and that is the only
hypothesis this section adds. A discrete valuation ring together with its fraction field is the
intended way to obtain it — see `isIntegrallyClosed_iff_isIntegrallyClosedIn` — but nothing here
requires a valuation, and `K` need not be a fraction field. -/

section Descent

variable [IsIntegrallyClosedIn R K]

/-- **A change of variables between two integral models whose scaling factor is a unit of `R` is
the base change of a change of variables over `R`.** `R` is assumed integrally closed in `K`; `W₁`
and `W₂` integral over `R`; and `D.u` the image of `u₀ : Rˣ`. The witness has that same `u₀` as its
scaling factor. -/
theorem exists_baseChange_eq_of_smul_eq {W₁ W₂ : WeierstrassCurve K}
    [IsIntegral R W₁] [IsIntegral R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) (u₀ : Rˣ)
    (hau : algebraMap R K ↑u₀ = ↑D.u) : ∃ C₀ : VariableChange R, C₀.baseChange K = D := by
  obtain ⟨rR, hrR⟩ :=
    IsIntegrallyClosedIn.isIntegral_iff.mp (isIntegral_r_of_smul_eq R D hD u₀ hau)
  obtain ⟨sR, hsR⟩ :=
    IsIntegrallyClosedIn.isIntegral_iff.mp (isIntegral_s_of_smul_eq R D hD u₀ hau rR hrR)
  obtain ⟨tR, htR⟩ :=
    IsIntegrallyClosedIn.isIntegral_iff.mp (isIntegral_t_of_smul_eq R D hD u₀ hau rR hrR)
  exact ⟨⟨u₀, rR, sR, tR⟩, VariableChange.ext (Units.ext hau) hrR hsR htR⟩

end Descent

end VariableChange

end WeierstrassCurve

end
