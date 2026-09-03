/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.RiemannRoch.DegreeZero
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc

/-!
# Uniqueness of the Riemann–Roch data

The Riemann–Roch theorem asserts that there are a natural number `g₀` and a divisor `W` of an
algebraic function field `F / k` with

`ℓ(D) = deg D + 1 - g₀ + ℓ(W - D)` for every divisor `D`.

This file proves that such a pair is essentially unique, **before** any such pair is constructed:
`g₀` is forced to be the genus `g(F/k)` of Riemann's theorem, `W` is forced to have
`ℓ(W) = g` and `deg W = 2g - 2`, and any two such `W` are linearly equivalent, so they span a
single divisor class.  Once a Weil differential produces one such `W` — the canonical divisor —
these statements say that the genus and the canonical class of the Riemann–Roch theorem are the
genus and the canonical class, and not merely some pair that happens to satisfy the identity.
This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed. (GTM 254),
Proposition 1.6.1.

The proofs use only Riemann's theorem and the degree-zero calculus already available: `g₀ = g`
comes from evaluating the identity at divisors of large degree, where Riemann's theorem is an
equality and `ℓ(W - D)` vanishes because `W - D` is a negative divisor; `ℓ(W) = g₀` and
`deg W = 2g₀ - 2` come from evaluating it at `D = 0` and at `D = W`; and the linear equivalence
of two Riemann–Roch divisors comes from `ℓ(W' - W) = 1` together with `deg (W' - W) = 0`, which
is exactly the criterion for a degree-zero divisor to be principal.

The predicate is not vacuous: the rational function field satisfies the Riemann–Roch identity
with `g₀ = 0` and `W = -2 · P_∞`, proved here from the closed formula
`ℓ(D) = (deg D + 1)⁺` for divisors of `k(x)`.  Applying `TauCeti.Divisor.IsRiemannRochDivisor`'s
consequences to that witness recovers `g(k(x)) = 0`, `ℓ(-2 · P_∞) = 0` and
`deg (-2 · P_∞) = -2 = 2g - 2`.

## Main definitions

* `TauCeti.Divisor.IsRiemannRochDivisor`: `W` satisfies the Riemann–Roch identity with the
  natural number `g₀` in the role of the genus.  The name is provisional in the sense that the
  results below show the only such divisors are the canonical ones, with `g₀ = g`.

## Main results

* `TauCeti.Divisor.IsRiemannRochDivisor.genus_eq`: `g₀` is the genus (Stichtenoth,
  Proposition 1.6.1).
* `TauCeti.Divisor.IsRiemannRochDivisor.dim_eq` and
  `TauCeti.Divisor.IsRiemannRochDivisor.degree_eq`: `ℓ(W) = g₀` and `deg W = 2g₀ - 2`.
* `TauCeti.Divisor.IsRiemannRochDivisor.indexOfSpecialty_eq`: the identity read as duality,
  `i(D) = ℓ(W - D)`.
* `TauCeti.Divisor.IsRiemannRochDivisor.linearlyEquivalent`: **any two Riemann–Roch divisors are
  linearly equivalent**, so the class they determine — the canonical class — is well defined
  ahead of its construction; `TauCeti.Divisor.IsRiemannRochDivisor.of_linearlyEquivalent` is the
  converse transport, so the property depends only on the divisor class.
* `TauCeti.Divisor.isRiemannRochDivisor_neg_two_zsmul_ofPoint_infty`: `-2 · P_∞` is a
  Riemann–Roch divisor of the rational function field, with `g₀ = 0`.

## Provenance

The mathematics is Stichtenoth's and the Lean development is independent.  The roadmap's
coordination section records that `vaca22/riemann-roch-function-fields` (Guanghao Li,
Apache-2.0) carries a complete function-field Riemann–Roch by the same Stichtenoth route, and
that this roadmap specifies the mathematics rather than that code; no code is copied or adapted
from it here.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.6.1.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **A Riemann–Roch divisor for the value `g₀`**: a divisor `W` for which the Riemann–Roch
identity `ℓ(D) = deg D + 1 - g₀ + ℓ(W - D)` holds at every divisor `D`, with the natural number
`g₀` in the role of the genus (Stichtenoth, Theorem 1.5.15 in the form of Proposition 1.6.1).

The results in this file show that `g₀` is then the genus of `F / k` and that any two such `W`
are linearly equivalent; the Riemann–Roch theorem itself is the assertion that one exists, and
exhibits the divisor of a nonzero Weil differential as such a `W`. -/
def Divisor.IsRiemannRochDivisor (W : Divisor k F) (g₀ : ℕ) : Prop :=
  ∀ D : Divisor k F, (Divisor.dim D : ℤ) = Divisor.degree D + 1 - g₀ + Divisor.dim (W - D)

/-- The defining property of a Riemann–Roch divisor, as an `Iff` for rewriting. -/
theorem Divisor.isRiemannRochDivisor_iff {W : Divisor k F} {g₀ : ℕ} :
    W.IsRiemannRochDivisor g₀ ↔
      ∀ D : Divisor k F,
        (Divisor.dim D : ℤ) = Divisor.degree D + 1 - g₀ + Divisor.dim (W - D) :=
  Iff.rfl

variable {W W' : Divisor k F} {g₀ g₁ : ℕ}

/-- **`ℓ(W) = g₀` for a Riemann–Roch divisor** (Stichtenoth, Corollary 1.5.16): evaluate the
Riemann–Roch identity at `D = 0`, where `ℓ(0) = 1`. -/
theorem Divisor.IsRiemannRochDivisor.dim_eq (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀) :
    Divisor.dim W = g₀ := by
  have h := hW 0
  rw [Divisor.degree_zero, Divisor.dim_zero_of_isIntegrallyClosedIn hF hex, sub_zero] at h
  omega

/-- **`deg W = 2g₀ - 2` for a Riemann–Roch divisor** (Stichtenoth, Corollary 1.5.16): evaluate
the Riemann–Roch identity at `D = W`, where `ℓ(W - W) = ℓ(0) = 1`, and use `ℓ(W) = g₀`. -/
theorem Divisor.IsRiemannRochDivisor.degree_eq (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀) :
    Divisor.degree W = 2 * g₀ - 2 := by
  have h := hW W
  rw [sub_self, Divisor.dim_zero_of_isIntegrallyClosedIn hF hex, hW.dim_eq hF hex] at h
  omega

/-- **The value `g₀` of a Riemann–Roch divisor is the genus** (Stichtenoth,
Proposition 1.6.1).

Riemann's theorem is an equality `ℓ(D) = deg D + 1 - g` in large degree.  The divisors
`D = W + n · P`, for a place `P` and `n ≥ 1`, have arbitrarily large degree and satisfy
`W - D = -n · P < 0`, so `ℓ(W - D) = 0` and the Riemann–Roch identity reads
`ℓ(D) = deg D + 1 - g₀` there; comparing the two forces `g₀ = g`. -/
theorem Divisor.IsRiemannRochDivisor.genus_eq (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀) :
    g₀ = genus k F := by
  obtain ⟨c, hc⟩ := exists_forall_dim_eq_degree_add_one_sub_genus hF hex
  obtain ⟨P⟩ := Place.nonempty hF
  set n : ℕ := (c - Divisor.degree W).toNat + 1 with hn
  set D : Divisor k F := W + (n : ℤ) • WeilDivisor.ofPoint P with hD
  -- `ℓ(W - D) = 0`, because `W - D = -n · P` is a negative divisor.
  have hsub : W - D = (-(n : ℤ)) • WeilDivisor.ofPoint P := by
    rw [hD, neg_zsmul]
    abel
  have hvanish : Divisor.dim (W - D) = 0 := by
    refine hsub ▸ Divisor.dim_eq_zero_of_lt_zero hF
      (WeilDivisor.zsmul_ofPoint_lt_zero P ?_)
    omega
  -- `deg D` is large enough for Riemann's theorem to be an equality at `D`.
  have hPdeg : (1 : ℤ) ≤ P.degree := by
    exact_mod_cast P.one_le_degree_of_isFunctionField hF
  have hnge : c - Divisor.degree W ≤ (n : ℤ) := by
    rw [hn]; push_cast; omega
  have hmul : (n : ℤ) ≤ (n : ℤ) * P.degree :=
    le_mul_of_one_le_right (Int.natCast_nonneg n) hPdeg
  have hdegD : c ≤ Divisor.degree D := by
    rw [hD, Divisor.degree_add, Divisor.degree_zsmul, Divisor.degree_ofPoint]
    linarith
  have hriemann := hc D hdegD
  have hRR := hW D
  rw [hvanish] at hRR
  omega

/-- **The Riemann–Roch identity, read as duality**: for a Riemann–Roch divisor `W`, the index of
specialty of `D` is `ℓ(W - D)` (Stichtenoth, Theorem 1.5.14 in the presence of Theorem 1.5.15). -/
theorem Divisor.IsRiemannRochDivisor.indexOfSpecialty_eq (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀) (D : Divisor k F) :
    Divisor.indexOfSpecialty D = Divisor.dim (W - D) := by
  have h := hW D
  rw [Divisor.indexOfSpecialty_def, ← hW.genus_eq hF hex]
  omega

/-- **Any two Riemann–Roch divisors are linearly equivalent** (Stichtenoth,
Proposition 1.6.1): they determine a single divisor class, the canonical class, and they do so
before any of them has been constructed.

Both identities compute `ℓ(W' - D) - ℓ(W - D)` as a difference of the two values of `g₀`, which
agree by `TauCeti.Divisor.IsRiemannRochDivisor.genus_eq`; taking `D = W` gives `ℓ(W' - W) = 1`,
while `deg (W' - W) = 0` by `TauCeti.Divisor.IsRiemannRochDivisor.degree_eq`, and a degree-zero
divisor with a nonzero Riemann–Roch space is principal. -/
theorem Divisor.IsRiemannRochDivisor.linearlyEquivalent (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀)
    (hW' : W'.IsRiemannRochDivisor g₁) :
    (Place.orderSystem hF).LinearlyEquivalent W W' := by
  have hg : g₀ = g₁ := by rw [hW.genus_eq hF hex, hW'.genus_eq hF hex]
  have hself := hW W
  rw [sub_self, Divisor.dim_zero_of_isIntegrallyClosedIn hF hex] at hself
  have hother := hW' W
  have hdim : 1 ≤ Divisor.dim (W' - W) := by omega
  have hdeg : Divisor.degree (W' - W) = 0 := by
    rw [Divisor.degree_sub, hW'.degree_eq hF hex, hW.degree_eq hF hex, hg]
    omega
  obtain ⟨z, hz⟩ :=
    (Divisor.one_le_dim_iff_exists_principal_eq_of_degree_eq_zero hF hdeg).mp hdim
  exact ((Divisor.linearlyEquivalent_iff hF).mpr ⟨z, hz⟩).symm

/-- **Being a Riemann–Roch divisor depends only on the divisor class**: linearly equivalent
divisors have Riemann–Roch spaces of the same dimension, so the identity transports. -/
theorem Divisor.IsRiemannRochDivisor.of_linearlyEquivalent (hF : IsFunctionField k F)
    (hW : W.IsRiemannRochDivisor g₀)
    (h : (Place.orderSystem hF).LinearlyEquivalent W W') :
    W'.IsRiemannRochDivisor g₀ := by
  obtain ⟨z, hz⟩ := (Divisor.linearlyEquivalent_iff hF).mp h
  intro D
  have hequiv : (Place.orderSystem hF).LinearlyEquivalent (W - D) (W' - D) :=
    (Divisor.linearlyEquivalent_iff hF).mpr ⟨z, by rw [hz]; abel⟩
  rw [← Divisor.dim_eq_of_linearlyEquivalent hF hequiv]
  exact hW D

/-! ### The rational function field -/

/-- **`-2 · P_∞` is a Riemann–Roch divisor of `k(x)`, with `g₀ = 0`**: the closed formula
`ℓ(D) = (deg D + 1)⁺` on the rational function field turns the Riemann–Roch identity into an
identity between truncated integers.

This is the witness that keeps `TauCeti.Divisor.IsRiemannRochDivisor` from being vacuous, and
the acceptance instance for the general statements above: it has `deg (-2 · P_∞) = -2`,
`ℓ(-2 · P_∞) = 0` and, by `TauCeti.Divisor.IsRiemannRochDivisor.genus_eq`, `g(k(x)) = 0`. -/
theorem Divisor.isRiemannRochDivisor_neg_two_zsmul_ofPoint_infty (k : Type*) [Field k] :
    Divisor.IsRiemannRochDivisor
      ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k) : Divisor k (RatFunc k)) 0 := by
  intro D
  have hdegW : Divisor.degree
      ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k) : Divisor k (RatFunc k)) = -2 := by
    rw [Divisor.degree_zsmul, Divisor.degree_ofPoint, Place.degree_infty, Nat.cast_one, mul_one]
  rw [Divisor.dim_ratFunc, Divisor.dim_ratFunc, Divisor.degree_sub, hdegW]
  omega

end TauCeti
