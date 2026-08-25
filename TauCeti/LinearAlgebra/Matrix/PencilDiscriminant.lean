/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuadraticDiscriminant
public import TauCeti.LinearAlgebra.Matrix.QuadraticFormCongruence
public import TauCeti.LinearAlgebra.Matrix.SymplecticMultiplier

/-!
# The discriminant of a matrix pencil realised over every prime

Let `q` and `t` be integers. `TauCeti.Matrix.eq_quadratic_form_of_det_det_one_sub` shows that an
integer realised, modulo every prime `ℓ` other than one exceptional `p`, as the determinant of the
pencil `r • M - s • 1` of a `2 × 2` matrix `M` with `M.det = q` and `(1 - M).det = q + 1 - t` is
forced to equal `q * r ^ 2 - t * (r * s) + s ^ 2`. This file draws the conclusion that follows when
such an integer exists and is **non-negative** at every `(r, s)` avoiding `p`:

`t ^ 2 ≤ 4 * q`.

Equivalently `discrim q (-t) 1 ≤ 0`, the binary quadratic form above having leading coefficient
`q`, middle coefficient `-t` and constant coefficient `1`.

Nothing about elliptic curves appears here, and none is proved: the matrix data is a **hypothesis**
throughout. The intended instance is the `q`-power Frobenius `π` of a curve over a field of
characteristic `p`, where the realising integer is the degree of the isogeny `r π - s` — manifestly
non-negative, and known to be an isogeny only away from both coordinates — and `M` is the matrix of
`π` on the `ℓ`-torsion; the conclusion is then the Hasse bound. Supplying that instance is the work
of the Weil pairing and is not done here.

Two forms of the hypothesis are given. The first asks for the three determinants directly. The
second asks instead for the **symplectic multipliers** `Aᵀ J A = d • J` of the same three matrices,
which is what a pairing scaling by the degree supplies, and reads the determinants off them with
`Matrix.det_eq_of_transpose_mul_J_mul_eq_smul`. Since `Matrix.J` lives on `l ⊕ l` for a singleton
`l` rather than on `Fin 2`, the second form quantifies over matrices there and reindexes.

Neither statement constrains the sign of `q`, and neither concludes anything about the value of the
form. A caller wanting the form itself to be non-negative — which needs `0 < q`, and which is how
the source states its conclusion — composes with `nonneg_of_discrim_le_zero`:

```
nonneg_of_discrim_le_zero hq (by simpa [discrim] using sq_le_four_mul_of_exists_nonneg_pencil_det …)
```

That is a one-line transport which would have to repeat the whole matrix-data interface to be
stated, so, as with the corresponding step in
`TauCeti/LinearAlgebra/Matrix/QuadraticFormCongruence.lean`, it is left to consumers rather than
exported as a corollary.

## Main results

* `TauCeti.Matrix.sq_le_four_mul_of_exists_nonneg_pencil_det`: from per-prime determinant data.
* `TauCeti.Matrix.sq_le_four_mul_of_exists_nonneg_symplectic_multiplier`: from per-prime symplectic
  multipliers.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `dev/hasse-weil @ 513e83879e2f`), file
`HasseWeil/WeilPairing/Assembly.lean`, declarations `qf_nonneg_of_frob_det_residual`,
`qf_nonneg_of_frob_det_residual_both` and `qf_nonneg_of_pairing_scaling`, together with
`frob_det_data_of_scaling` from `HasseWeil/WeilPairing/PairingDet.lean`.

Changes from the source. Its three theorems conclude `0 ≤ q * r ^ 2 - t * r * s + s ^ 2` and so
each assume `0 < q`; the conclusion here is the discriminant bound `t ^ 2 ≤ 4 * q` that their
proofs pass through, which needs no hypothesis on `q` and from which the non-negativity of the form
is the displayed one-liner above. The first two differ only in their locus — the source's
`hres` is indexed by `p ∤ s` alone, the `_both` version by `p ∤ r ∧ p ∤ s` — and the first follows
from the second by weakening a hypothesis, `fun r s _ hs => hres r s hs`, so only the second is
carried; `TauCeti/Algebra/QuadraticDiscriminant.lean` declined the same pair for the same reason.
The source threads a function `deg : ℤ → ℤ → ℤ` with `∀ r s, 0 ≤ deg r s` through all three; the
realising integer is quantified existentially per `(r, s)` here, since nothing needs the choices to
cohere into a function. Primality of `p` is not assumed: the per-prime family only ever excludes
`p`, and the locus only needs `p` to be a non-unit, so `p ≠ 1` suffices. Finally,
`frob_det_data_of_scaling` is not reproduced: it is the conjunction of three applications of
`Matrix.det_eq_of_transpose_mul_J_mul_eq_smul`, and is taken inline.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, V.1.1 and V.1.2 — the Hasse bound, and the
  positivity of the degree form on a rank-two lattice that yields it.
-/

public section

open Matrix

namespace TauCeti.Matrix

variable {p : ℕ} {q t : ℤ}

/-- **The discriminant bound from per-prime pencil determinants.** Suppose that at every `(r, s)`
with `p ∤ r` and `p ∤ s` some non-negative integer is realised, modulo every prime `ℓ ≠ p`, as the
determinant of the pencil `r • M - s • 1` of a `2 × 2` matrix `M` over `ZMod ℓ` with `M.det = q`
and `(1 - M).det = q + 1 - t`. Then `t ^ 2 ≤ 4 * q`.

No hypothesis on `q` is needed, and `p` need only be a non-unit. -/
theorem sq_le_four_mul_of_exists_nonneg_pencil_det (hp : p ≠ 1)
    (h : ∀ r s : ℤ, ¬ (p : ℤ) ∣ r → ¬ (p : ℤ) ∣ s → ∃ D : ℤ, 0 ≤ D ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
        M.det = (q : ZMod ℓ) ∧ (1 - M).det = ((q + 1 - t : ℤ) : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (D : ZMod ℓ)) :
    t ^ 2 ≤ 4 * q := by
  have hu : ¬ IsUnit (p : ℤ) := by rw [Int.isUnit_iff]; omega
  have hd : discrim q (-t) 1 ≤ 0 := by
    refine Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd hu fun r s hr hs => ?_
    obtain ⟨D, hD0, hD⟩ := h r s hr hs
    -- the realising integer *is* the form, so its non-negativity is the form's
    rw [eq_quadratic_form_of_det_det_one_sub (p := p) hD] at hD0
    linarith
  simpa [discrim] using hd

variable {l : Type*} [DecidableEq l] [Fintype l] [Unique l]

/-- **The discriminant bound from per-prime symplectic multipliers.** The hypothesis of
`sq_le_four_mul_of_exists_nonneg_pencil_det` with each determinant replaced by the symplectic
multiplier that forces it: `Aᵀ * J * A = d • J` gives `A.det = d` in rank two, by
`Matrix.det_eq_of_transpose_mul_J_mul_eq_smul`.

This is the shape a pairing supplies. On the `ℓ`-torsion of an elliptic curve the Weil pairing `e`
satisfies `e (A S) (A T) = e S T ^ deg A` for every isogeny `A` separately — no additivity in `A`,
which is what makes it available — and that scaling is exactly `Aᵀ J A = (deg A) • J`. -/
theorem sq_le_four_mul_of_exists_nonneg_symplectic_multiplier (hp : p ≠ 1)
    (h : ∀ r s : ℤ, ¬ (p : ℤ) ∣ r → ¬ (p : ℤ) ∣ s → ∃ D : ℤ, 0 ≤ D ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∃ M : Matrix (l ⊕ l) (l ⊕ l) (ZMod ℓ),
        Mᵀ * J l (ZMod ℓ) * M = (q : ZMod ℓ) • J l (ZMod ℓ) ∧
        (1 - M)ᵀ * J l (ZMod ℓ) * (1 - M) = ((q + 1 - t : ℤ) : ZMod ℓ) • J l (ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1)ᵀ * J l (ZMod ℓ)
            * ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1) = (D : ZMod ℓ) • J l (ZMod ℓ)) :
    t ^ 2 ≤ 4 * q := by
  -- `l ⊕ l` has two elements, so the data may be carried over to `Fin 2`; any equivalence serves.
  have e : Fin 2 ≃ l ⊕ l := (Fintype.equivFinOfCardEq (by simp)).symm
  refine sq_le_four_mul_of_exists_nonneg_pencil_det hp fun r s hr hs => ?_
  obtain ⟨D, hD0, hD⟩ := h r s hr hs
  refine ⟨D, hD0, fun ℓ hℓ hℓne => ?_⟩
  obtain ⟨M, hdet, hone, hpencil⟩ := hD ℓ hℓ hℓne
  -- `Matrix.submatrix` commutes with `1`, `-` and `•`, so all three determinants survive.
  have hone' : (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) - M.submatrix e e = (1 - M).submatrix e e := by
    simp [submatrix_sub, Pi.sub_apply]
  have hpencil' : (r : ZMod ℓ) • M.submatrix e e - (s : ZMod ℓ) • (1 : Matrix (Fin 2) (Fin 2) _)
      = ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).submatrix e e := by
    simp [submatrix_sub, submatrix_smul, Pi.sub_apply, Pi.smul_apply]
  refine ⟨M.submatrix e e, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self]
    exact det_eq_of_transpose_mul_J_mul_eq_smul hdet
  · rw [hone', det_submatrix_equiv_self]
    exact det_eq_of_transpose_mul_J_mul_eq_smul hone
  · rw [hpencil', det_submatrix_equiv_self]
    exact det_eq_of_transpose_mul_J_mul_eq_smul hpencil

end TauCeti.Matrix
