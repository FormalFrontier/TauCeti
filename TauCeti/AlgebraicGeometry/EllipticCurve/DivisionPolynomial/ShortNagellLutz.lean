/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Discriminant
-- Proof-only, and not reachable transitively: `Torsion/Discriminant.lean` imports this
-- module non-publicly, so `evalEval_ψ₂_of_isCharNeTwoNF` is not re-exported through it.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms
public import TauCeti.AlgebraicGeometry.EllipticCurve.ShortWeierstrass

/-!
# The Nagell–Lutz theorem for a short Weierstrass model

For `A B : ℤ`, a nonzero rational point of finite order on `y² = x³ + Ax + B` has **integral**
coordinates, and its `y`-coordinate satisfies `y = 0` or `y² ∣ Δ`. That is the classical
statement, and unlike the long-model theorem it has no order-two exception.

The exception disappears for a computable reason rather than by assumption. On a short model
`a₁ = a₃ = 0`, so `ψ₂ = 2y`; a point of order two makes `ψ₂` vanish, hence `y = 0`, and then the
curve equation exhibits `x` as a rational root of the **monic** `X³ + AX + B`, so `x` is an
integer too. The long model's honest bound `4x, 8y ∈ ℤ` therefore sharpens to full integrality
exactly here.

The same collapse turns the discriminant companion into its classical form: it gives
`ψ₂ = 0 ∨ ψ₂² ∣ 4Δ`, and substituting `ψ₂ = 2y₀` yields `2y₀ = 0 ∨ 4y₀² ∣ 4Δ`, from which the `4`
cancels on both sides.

**No `Δ ≠ 0` hypothesis.** The source carries one on all three of its headline theorems and uses
it in none of them; what the argument needs is that the *point* is nonsingular, not that the curve
is elliptic. See the Provenance note.

## Main results

* `WeierstrassCurve.lutz_nagell`: the theorem at the roadmap's explicit short model
  `y² = x³ + Ax + B` — integral coordinates together with `y₀ = 0 ∨ y₀² ∣ Δ`.
* `WeierstrassCurve.isInteger_of_torsion`: the integrality half, with no order-two exception, for
  any integral model in characteristic-≠-2 normal form.
* `WeierstrassCurve.y_eq_zero_or_sq_dvd_Δ_of_torsion`: the discriminant half, likewise.

The three results above `lutz_nagell` are stated at `[W.IsCharNeTwoNF]`, i.e. `a₁ = a₃ = 0`, not
at `shortCurve`: no step uses `a₂ = 0`, and the cubic `X³ + a₂X² + a₄X + a₆` is monic either way.
`lutz_nagell` is their specialisation, and costs nothing to obtain — Mathlib's
`isCharNeTwoNF_of_isShortNF` supplies the instance.

## Roadmap

New mathematics: `TauCetiRoadmap/EllipticCurves/README.md:821` — "**The torsion subgroup and
Nagell–Lutz**". Lines `:828`–`:830` name this target: for an integral **short** model
`y² = x³ + Ax + B`, "the classical full form — `x, y ∈ ℤ` and `y = 0` or `y² ∣ Δ`
(`lutz_nagell`; AEC VIII.7)".

## Provenance

Ported from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), from two files whose authorship differs and is
credited separately.

**`LutzNagellTheorem/Main.lean` — `Authors: Chris Birkbeck`.** All three headline theorems come
from it: `lutz_nagell_integrality` (`:40`), `lutz_nagell_discriminant` (`:53`) and `lutz_nagell`
(`:71`). That file carries its own author header, so it is credited to Chris Birkbeck rather than
to the project's usual pair, and the header of this file names them accordingly.

**`LutzNagellTheorem/GeneralMain.lean` — no author header.** Its
`lutz_nagell_integrality_short` (`:155`) is where the order-two collapse is carried out; with no
header to go on it is credited to the project, as the sibling ports in this chain are.

**The `Δ ≠ 0` hypothesis is dropped.** All three source theorems take
`hΔ : (shortCurveZ A B).Δ ≠ 0`; none uses it. It occurs in the three signatures and twice in the
bodies, both times in `lutz_nagell` forwarding it to the two theorems whose proofs never mention
it — a pass-through of a hypothesis nothing consumes, which this repository's `unusedArguments`
linter would reject in any case.

One further adaptation: `ψ₂ = 2y` is stated over an arbitrary commutative ring, since the point
lives over `ℚ` while the conclusion is over `ℤ` and both need it. The monic-root step follows the
source and goes through `isInteger_of_is_root_of_monic` — Mathlib's, which is what the source's
own lemma of that name restates.
-/

public section

open Polynomial

namespace WeierstrassCurve

open TauCeti.WeierstrassCurve

variable {W : WeierstrassCurve ℤ} [W.IsCharNeTwoNF]

/-- **Nagell–Lutz, discriminant half.** For a torsion point with integral coordinates on an
integral model in characteristic-≠-2 normal form, either `y₀ = 0` or `y₀²` divides the
discriminant.

The general companion gives `ψ₂ = 0 ∨ ψ₂² ∣ 4Δ`; here `ψ₂ = 2y₀`, so the first disjunct is
`2y₀ = 0` and the second is `4y₀² ∣ 4Δ`, and the `4` cancels on both sides. -/
theorem y_eq_zero_or_sq_dvd_Δ_of_torsion {x y : ℚ}
    (hns : (W.baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    {x₀ y₀ : ℤ} (hx : algebraMap ℤ ℚ x₀ = x) (hy : algebraMap ℤ ℚ y₀ = y) :
    y₀ = 0 ∨ y₀ ^ 2 ∣ W.Δ := by
  rcases evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ_rat hns htor hx hy with hκ | hdvd
  · rw [evalEval_ψ₂_of_isCharNeTwoNF] at hκ
    exact Or.inl (by omega)
  · refine Or.inr ?_
    rw [evalEval_ψ₂_of_isCharNeTwoNF] at hdvd
    ring_nf at hdvd
    exact (mul_dvd_mul_iff_right (by norm_num : (4 : ℤ) ≠ 0)).mp hdvd

/-- **Nagell–Lutz, integrality half.** On an integral model in characteristic-≠-2 normal form a
nonzero torsion point has integral coordinates — with *no* order-two exception.

The long-model theorem leaves order two aside with only `4x, 8y ∈ ℤ`. Here that case collapses:
`ψ₂ = 2y`, so order two forces `y = 0`, and the curve equation then exhibits `x` as a rational root
of the monic `X³ + a₂X² + a₄X + a₆`. The `a₂` term costs nothing — the cubic is monic either
way. -/
theorem isInteger_of_torsion {x y : ℚ}
    (hns : (W.baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns)) :
    IsLocalization.IsInteger ℤ x ∧ IsLocalization.IsInteger ℤ y := by
  rcases isInteger_or_order_two_of_torsion_rat hns htor with h | ⟨h2, -, -⟩
  · exact h
  · have hy : y = 0 := y_eq_zero_of_order_two two_ne_zero hns (h2 ▸ addOrderOf_nsmul_eq_zero _)
    refine ⟨?_, hy ▸ ⟨0, by simp⟩⟩
    have hmonic : (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : ℤ[X]).Monic := by
      simpa [add_assoc] using monic_X_pow_add (n := 3) (by compute_degree!)
    have heq := hns.left
    rw [Affine.equation_iff] at heq
    simp only [a₃_of_isCharNeTwoNF, WeierstrassCurve.baseChange, map_a₂, map_a₄, map_a₆,
      eq_intCast, zero_mul] at heq
    rw [hy] at heq
    refine isInteger_of_is_root_of_monic hmonic ?_
    -- `aeval_C` must fire before the casts are normalised: `eq_intCast` would otherwise rewrite
    -- `C W.a₂` to an `ℤ[X]` cast, which `aeval_C` no longer matches.
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
    simp only [eq_intCast]
    linarith

variable (A B : ℤ)

/-- **The Nagell–Lutz theorem.** Let `A B : ℤ` and let `(x, y)` be a nonzero rational point of
finite order on `y² = x³ + Ax + B`. Then `x` and `y` are integers, and either `y = 0` or
`y² ∣ Δ`.

This is the classical statement, and the form `TauCetiRoadmap/EllipticCurves/README.md:830` names
`lutz_nagell`. It is the specialisation of the two theorems above at a short model: Mathlib's
`isCharNeTwoNF_of_isShortNF` supplies the instance, so there is nothing to discharge. No hypothesis
`Δ ≠ 0` is needed — see the module docstring. -/
theorem lutz_nagell {x y : ℚ}
    (hns : ((shortCurve A B).baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns)) :
    ∃ x₀ y₀ : ℤ, (x₀ : ℚ) = x ∧ (y₀ : ℚ) = y ∧
      (y₀ = 0 ∨ y₀ ^ 2 ∣ (shortCurve A B).Δ) := by
  obtain ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩ := isInteger_of_torsion hns htor
  exact ⟨x₀, y₀, by simpa using hx₀, by simpa using hy₀,
    y_eq_zero_or_sq_dvd_Δ_of_torsion hns htor hx₀ hy₀⟩

end WeierstrassCurve
