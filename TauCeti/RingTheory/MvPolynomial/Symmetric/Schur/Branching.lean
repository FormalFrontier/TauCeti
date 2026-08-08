/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Combinatorics.Young.Interlacing
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic

/-!
# The branching rule for Schur polynomials

Setting the last variable of a Schur polynomial to `1` splits it into the Schur polynomials, in one
variable fewer, of the shapes that **interlace** its own:

`s_μ(x₀, …, x_{n-1}, 1) = ∑_{ν ≺ μ} s_ν(x₀, …, x_{n-1})`.

This is `TauCeti.eval_diagramSchurPoly_of_apply_last_eq_one`, an identity of polynomials over an
arbitrary commutative semiring.  Over `ℂ`, and for a shape `μ` of at most `n + 1` rows — so that
`μ` is the highest weight of a polynomial irreducible of `GLₙ₊₁` and `s_μ` its character — it reads
as the multiplicity-free branching rule for the restriction `GLₙ₊₁ ↓ GLₙ`: that irreducible
restricts to the direct sum, each with multiplicity one, of the irreducibles whose highest weights
interlace `μ`.  That reading is not proved here, and it does not transfer to positive
characteristic: there the identity of characters no longer forces a direct-sum decomposition,
because the representations of `GLₙ₊₁` are not semisimple in general.  The theorems below are the
polynomial identity alone.

Nothing analytic happens here.  `TauCeti.diagramSchurPoly` is by construction the generating
function of the bounded semistandard tableaux of its shape, so the identity is the sum-over-a-
partition form of the bijection `TauCeti.BoundedSSYT.fiberEquiv` of
`TauCeti.Combinatorics.Young.Interlacing`: a tableau in the `n + 1` letters `{0, …, n}` is a
tableau in the `n` letters `{0, …, n - 1}` on an interlacing sub-shape, together with the cells
carrying the top letter `n`.  Those cells contribute the variable that is being set to `1`, which
is exactly why the specialization, rather than the polynomial itself, is what factors.

## Main results

* `TauCeti.BoundedSSYT.weight_restrict`: the weight form of `TauCeti.BoundedSSYT.content_restrict`,
  that erasing the top letter of a tableau does not change how often any of the remaining letters
  occurs.
* `TauCeti.eval_diagramSchurPoly_of_apply_last_eq_one`: the branching rule, for any evaluation
  sending the last variable to `1`, and `TauCeti.eval_snoc_one_diagramSchurPoly`, its form for the
  evaluation built by appending `1` to a family of values.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5, Example 3.
* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/RepresentationTheory/ClassicalGroups/README.md),
  Layer 6, "branching rules".
-/

public section

namespace TauCeti

open MvPolynomial

variable {R : Type*} [CommSemiring R]

namespace BoundedSSYT

variable {n : ℕ} {μ ν : _root_.YoungDiagram}

/-- **Erasing the top letter changes no other multiplicity**, read on weights: the combinatorial
statement is `TauCeti.BoundedSSYT.content_restrict`, and the weight of a bounded tableau is its
content restricted to the alphabet. -/
theorem weight_restrict (T : BoundedSSYT (n + 1) μ) (hν : restrictShape T = ν) (i : Fin n) :
    weight (restrict T ν hν) i = weight T i.castSucc := by
  rw [weight_apply, weight_apply, Fin.val_castSucc, content_restrict T hν i.isLt]

end BoundedSSYT

/-- **The branching rule for Schur polynomials.**  Evaluating `s_μ` in `n + 1` variables at a
family whose last member is `1` gives the sum of the `s_ν` in the first `n` variables, over the
shapes `ν` interlacing `μ` with at most `n` rows, each occurring once.

The identity is one of polynomials over an arbitrary commutative semiring.  Over `ℂ`, and for a
shape `μ` of at most `n + 1` rows, it is the character form of the multiplicity-free branching rule
for the restriction `GLₙ₊₁ ↓ GLₙ`. -/
theorem eval_diagramSchurPoly_of_apply_last_eq_one (n : ℕ) (μ : _root_.YoungDiagram)
    (x : Fin (n + 1) → R) (hx : x (Fin.last n) = 1) :
    eval x (diagramSchurPoly (n + 1) R μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          eval (fun i : Fin n => x i.castSucc) (diagramSchurPoly n R ν) := by
  simp only [eval_diagramSchurPoly]
  rw [← BoundedSSYT.sum_eq_sum_interlacingShapes n μ
    fun ν T => ∏ i : Fin n, x i.castSucc ^ BoundedSSYT.weight T i]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Fin.prod_univ_castSucc, hx, one_pow, mul_one]
  exact Finset.prod_congr rfl fun i _ => by rw [BoundedSSYT.weight_restrict T rfl i]

/-- **The branching rule for Schur polynomials**, evaluated at a family of values with a `1`
appended. -/
theorem eval_snoc_one_diagramSchurPoly (n : ℕ) (μ : _root_.YoungDiagram) (x : Fin n → R) :
    eval (Fin.snoc x 1) (diagramSchurPoly (n + 1) R μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, eval x (diagramSchurPoly n R ν) := by
  rw [eval_diagramSchurPoly_of_apply_last_eq_one n μ _ (by simp)]
  exact Finset.sum_congr rfl fun ν _ => by simp

end TauCeti
