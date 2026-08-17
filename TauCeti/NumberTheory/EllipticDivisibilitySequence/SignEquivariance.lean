/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.FinCases

/-!
# The elliptic relator is sign-equivariant in its four indices

For an odd sequence `W : ℤ → R`, Mathlib's `IsEllipticNet.atomRel W a b c d` changes sign under a
transposition of its four arguments. This file proves that for the three adjacent transpositions
and then, by inducting over the generators of `Equiv.Perm (Fin 4)`, for an arbitrary permutation:
`atomRelFin4 W (t ∘ σ) = sign σ • atomRelFin4 W t`.

This is **skew-symmetry, not alternation**, and the distinction is not pedantic here. `R` is an
arbitrary commutative ring, so `2` may be a zero divisor or vanish; the usual implication from
`f = -f` to `f = 0` is unavailable, and nothing below forces the relator to vanish when two indices
coincide. That vanishing is a separate fact, and it is Mathlib's: given `W 0 = 0`, each of the six
`IsEllipticNet.atomRel_same` lemmas has the shape `_ * W 0 * _`, hence is zero. The descent uses
both, from their two sources.

The point is that descent. Deducing the four-index relation from the one-index odd and even
recurrences works by ordering the four indices and shrinking the largest, which is only available
once the relation may be reordered freely — this file — and once repeated indices can be
discharged — Mathlib's `atomRel_same` family with `W 0 = 0`.

## Main definitions

* `IsEllipticNet.atomRelFin4`: `atomRel` with its four indices packaged as a `Fin 4`-tuple, the
  form an arbitrary permutation acts on.

## Main results

* `IsEllipticNet.atomRel_swap₁₂`, `atomRel_swap₂₃`, `atomRel_swap₃₄`: the three adjacent
  transpositions each negate `atomRel`.
* `IsEllipticNet.atomRelFin4_perm`: `atomRelFin4 W (t ∘ σ) = sign σ • atomRelFin4 W t` for every
  `σ : Equiv.Perm (Fin 4)`. Note this is sign-equivariance, not alternation — see the header. The
  sign-cancelled orientation is one `rw [atomRelFin4_perm odd, ← mul_smul, Int.units_mul_self,
  one_smul]` away and is not stated here: it has no consumer until the descent slice, which is
  where it will land, next to the proof that uses it.

## Implementation notes

The three transpositions are the generators `Mathlib`'s `Equiv.Perm.mclosure_swap_castSucc_succ`
gives for `Perm (Fin 4)`, which is what makes the induction in `atomRelFin4_perm` go through with
exactly these three lemmas as its base cases.

Each transposition rests on `IsEllipticNet.neg_atom`, `-atom W a b = atom W b a`, which is where the
oddness of `W` enters; nothing else here needs a hypothesis on `W`.

## Provenance

Ported from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declarations `rel₄_swap₀₁`, `rel₄_swap₁₂`, `rel₄_swap₂₃`, `relFin4` and `relFin4_perm`. The
source's `relFin4_perm'` — the sign-cancelled orientation — was **considered and not ported**: it
has no consumer until the descent slice, and lands there beside `rel₄_of_oddRec_evenRec`, the proof
that uses it. That file's header reads `Authors: David Kurniadi Angdinata`; following this
repository's convention for adapted material the upstream authorship is credited here rather than
in the copyright header. J. Xu is acknowledged for the surrounding LutzNagell development — he
authors `Universal.lean` and co-authors `DivisionPolynomialOmega.lean` at the same revision — as
context for this port, not as an author of the declarations above.

Restated over Mathlib's names for this API: the source's `rel₄` is `IsEllipticNet.atomRel` and its
`addMulSub` is `IsEllipticNet.atom`, and the source's standing `neg : ∀ k, W (-k) = -W k` hypothesis
is Mathlib's `W.Odd`. The transpositions are numbered from one, as Mathlib numbers its
`atomRel_same₁₂ … atomRel_same₃₄` family, rather than from zero as the source does.
-/

public section

open Equiv

namespace IsEllipticNet

variable {R : Type*} [CommRing R] {W : ℤ → R}

/-- Transposing the first two indices negates the relator. -/
theorem atomRel_swap₁₂ (odd : W.Odd) (a b c d : ℤ) :
    atomRel W a b c d = -atomRel W b a c d := by
  simp_rw [atomRel, ← neg_atom odd a b]
  ring

/-- Transposing the middle two indices negates the relator. -/
theorem atomRel_swap₂₃ (odd : W.Odd) (a b c d : ℤ) :
    atomRel W a b c d = -atomRel W a c b d := by
  simp_rw [atomRel, ← neg_atom odd b c]
  ring

/-- Transposing the last two indices negates the relator. -/
theorem atomRel_swap₃₄ (odd : W.Odd) (a b c d : ℤ) :
    atomRel W a b c d = -atomRel W a b d c := by
  simp_rw [atomRel, ← neg_atom odd c d]
  ring

variable (W) in
/-- The relator with its four indices packaged as a tuple, the form a permutation acts on. -/
def atomRelFin4 (t : Fin 4 → ℤ) : R := atomRel W (t 0) (t 1) (t 2) (t 3)

/-- The `@[simp]` unfolding equation for `atomRelFin4`, and the supported way to compute with it:
the tuple packaging carries no content of its own, so unfolding is always progress. The body is
exported unexposed — a plain `public section`, no `@[expose]` — so an importing module cannot
unfold it directly and reaches the formula through this lemma. -/
@[simp]
theorem atomRelFin4_def (t : Fin 4 → ℤ) :
    atomRelFin4 W t = atomRel W (t 0) (t 1) (t 2) (t 3) := (rfl)

/-- **The relator is sign-equivariant**: permuting the four indices multiplies it by the sign of
the permutation. This is skew-symmetry; it does *not* say the relator vanishes at repeated indices,
which over a ring with `2` a zero divisor does not follow, and which Mathlib's `atomRel_same`
family supplies separately from `W 0 = 0`. -/
theorem atomRelFin4_perm (odd : W.Odd) (σ : Perm (Fin 4)) :
    ∀ t : Fin 4 → ℤ, atomRelFin4 W (t ∘ σ) = Perm.sign σ • atomRelFin4 W t := by
  have hmem := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction
    (motive := fun (σ : Perm (Fin 4)) _ ↦
      ∀ t, atomRelFin4 W (t ∘ σ) = Perm.sign σ • atomRelFin4 W t)
    (fun _ hgen t ↦ ?generator)
    (fun t ↦ by simp)
    (fun σ τ _ _ hσ hτ t ↦ by
      rw [Perm.coe_mul, ← Function.comp_assoc, hτ, hσ, map_mul, mul_comm, mul_smul])
    hmem
  case generator =>
    obtain ⟨i, rfl⟩ := hgen
    fin_cases i <;>
      simp only [Perm.sign_swap Fin.castSucc_lt_succ.ne, Units.neg_smul, one_smul, atomRelFin4_def,
        Function.comp_apply, Fin.isValue]
    exacts [atomRel_swap₁₂ odd _ _ _ _, atomRel_swap₂₃ odd _ _ _ _, atomRel_swap₃₄ odd _ _ _ _]

end IsEllipticNet
