/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Int.CongrAllPrimes
public import TauCeti.LinearAlgebra.Matrix.CharpolyFinTwo
import Mathlib.Tactic.LinearCombination

/-!
# A quadratic form forced by per-prime matrix congruences

Let `q` and `t` be integers, thought of as the size of the base field and the trace of Frobenius.
This file shows that an integer `D` is *forced* to equal the binary quadratic form
`q * r ^ 2 - t * (r * s) + s ^ 2` as soon as, for every prime `ℓ` other than one exceptional `p`,
`D` is realised modulo `ℓ` as the determinant of the pencil `r • M - s • 1` of some `2 × 2` matrix
`M` over `ZMod ℓ` with determinant `q` and trace `t`.

Nothing about elliptic curves appears here, and none is proved: the matrix data is a
**hypothesis** throughout. The intended instance — where `D` is the degree of `r π - s` for the
`q`-power Frobenius `π`, and `M` is its matrix on the `ℓ`-torsion — is what makes the conclusion
the Hasse quadratic form, but supplying that instance is the work of the Weil pairing and is not
done here.

Two forms of the hypothesis are provided, because a Weil pairing supplies determinants rather
than traces: one taking `M.trace = t` directly, and one taking `(1 - M).det = q + 1 - t`, from
which the trace is read off.

## Main results

* `eq_quadratic_form_of_det_trace`: from per-prime data with `det` and `trace`.
* `eq_quadratic_form_of_det_det_one_sub`: the same from `det` data alone.
When the realised integer is non-negative — as a degree is — non-negativity of the form follows
by rewriting, `eq_quadratic_form_of_det_trace h ▸ hD`; that is left to consumers rather than
exported as a corollary.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/WeilPairing/Reduction.lean`, declarations `deg_eq_of_frobMatrix_data`,
`frob_det_congruence` and `deg_eq_of_frob_det_data`.

Three deviations. The source's fourth declaration, `qf_nonneg_of_frobMatrix_data`, is **not**
reproduced: it is a one-line `▸` transport of the equality theorem above it that repeats the whole
matrix-data interface to do so, which is why the Main results section above leaves that step to
consumers. The source's `det_smul_sub_smul_one_fin_two_of` takes `M.det = q` and
`M.trace = t` as hypotheses; TauCeti already has the unconditional
`Matrix.det_smul_sub_smul_one_fin_two` (merged as #2328), so that lemma is used and the
hypotheses are substituted at the call site. And the source's `det_one_sub_fin_two` is not
reproduced: `(1 - M).det = 1 - M.trace + M.det` is a three-line computation, kept private here.
The names say what is concluded rather than naming the elliptic-curve instance, since no curve
occurs in any statement.
-/

public section

open Matrix TauCeti.Matrix

namespace TauCeti.Matrix

variable {p ℓ : ℕ} {q t D r s : ℤ}

/-- **The per-prime congruence.** If `M` has determinant `q`, trace `t`, and the pencil
`r • M - s • 1` has determinant `D`, then `D` agrees with `q * r ^ 2 - t * (r * s) + s ^ 2`
modulo `ℓ`. -/
theorem intCast_eq_quadratic_form_of_det_trace {M : Matrix (Fin 2) (Fin 2) (ZMod ℓ)}
    (hdet : M.det = (q : ZMod ℓ)) (htrace : M.trace = (t : ZMod ℓ))
    (hpencil : ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (D : ZMod ℓ)) :
    (D : ZMod ℓ) = ((q * r ^ 2 - t * (r * s) + s ^ 2 : ℤ) : ZMod ℓ) := by
  rw [← hpencil, det_smul_sub_smul_one_fin_two, hdet, htrace]
  push_cast
  ring

/-- **The per-prime congruence, from determinants alone.** A Weil pairing supplies determinants
rather than traces, so the trace hypothesis is replaced by `(1 - M).det = q + 1 - t`. -/
theorem intCast_eq_quadratic_form_of_det_det_one_sub {M : Matrix (Fin 2) (Fin 2) (ZMod ℓ)}
    (hdet : M.det = (q : ZMod ℓ)) (hdetOneSub : (1 - M).det = ((q + 1 - t : ℤ) : ZMod ℓ))
    (hpencil : ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (D : ZMod ℓ)) :
    (D : ZMod ℓ) = ((q * r ^ 2 - t * (r * s) + s ^ 2 : ℤ) : ZMod ℓ) := by
  refine intCast_eq_quadratic_form_of_det_trace hdet ?_ hpencil
  -- `1 - M` is the pencil at `r = s = -1`, so the trace is read off the two determinants.
  have h : (1 - M).det = M.det * (-1) ^ 2 - M.trace * (-1 * -1) + (-1 : ZMod ℓ) ^ 2 := by
    simpa [neg_add_eq_sub] using det_smul_sub_smul_one_fin_two M (-1) (-1)
  rw [hdetOneSub, hdet] at h
  push_cast at h
  linear_combination h

/-- **The quadratic form is forced.** If for every prime `ℓ ≠ p` the integer `D` is realised
modulo `ℓ` as the pencil determinant of a `2 × 2` matrix with determinant `q` and trace `t`, then
`D = q * r ^ 2 - t * (r * s) + s ^ 2` as integers. -/
theorem eq_quadratic_form_of_det_trace
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      M.det = (q : ZMod ℓ) ∧ M.trace = (t : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (D : ZMod ℓ)) :
    D = q * r ^ 2 - t * (r * s) + s ^ 2 :=
  Int.eq_of_intCast_eq_all_primes_ne (p := p) fun ℓ hℓ hℓne ↦
    let ⟨_, hdet, htrace, hpencil⟩ := h ℓ hℓ hℓne
    intCast_eq_quadratic_form_of_det_trace hdet htrace hpencil

/-- **The quadratic form is forced, from determinants alone.** -/
theorem eq_quadratic_form_of_det_det_one_sub
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      M.det = (q : ZMod ℓ) ∧ (1 - M).det = ((q + 1 - t : ℤ) : ZMod ℓ) ∧
        ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (D : ZMod ℓ)) :
    D = q * r ^ 2 - t * (r * s) + s ^ 2 :=
  Int.eq_of_intCast_eq_all_primes_ne (p := p) fun ℓ hℓ hℓne ↦
    let ⟨_, hdet, hdetOneSub, hpencil⟩ := h ℓ hℓ hℓne
    intCast_eq_quadratic_form_of_det_det_one_sub hdet hdetOneSub hpencil

end TauCeti.Matrix
