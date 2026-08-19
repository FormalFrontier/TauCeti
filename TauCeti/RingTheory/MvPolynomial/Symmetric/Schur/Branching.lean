/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Interlacing
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic

/-!
# The branching rule for Schur polynomials

A Schur polynomial in `n + 1` variables is a polynomial in its last variable whose terms are
Schur polynomials in the first `n`, one term for each shape that **interlaces** its own:

`s_μ(x₀, …, x_n) = ∑_{ν ≺ μ} x_n ^ (|μ| - |ν|) · s_ν(x₀, …, x_{n-1})`.

This is `TauCeti.diagramSchurPoly_eq_sum_interlacingShapes`, an identity of *polynomials* over an
arbitrary commutative semiring.  The exponent of the last variable is forced: the cells of `μ` not
in `ν` are exactly the cells carrying the top letter, so a shape `ν` contributes in degree
`|μ| - |ν|` and in no other — the coefficient of `x_n ^ k` is thus the sum of the `s_ν` over the
interlacing shapes `ν` of cardinality `|μ| - k`, of which there may be several.  Specializing the
last variable recovers the identities of values that this grading refines:
`TauCeti.eval_snoc_diagramSchurPoly` at an arbitrary value, and at `1` the multiplicity-free form

`s_μ(x₀, …, x_{n-1}, 1) = ∑_{ν ≺ μ} s_ν(x₀, …, x_{n-1})`,

both as an identity of polynomials (`TauCeti.aeval_snoc_one_diagramSchurPoly`) and, at a family of
values, as `TauCeti.eval_diagramSchurPoly_of_apply_last_eq_one`.  At `0` instead every term of
positive degree dies, leaving the single degree-zero term, the one for `ν = μ`, and one reads off
the **stability** of Schur polynomials (`TauCeti.aeval_snoc_zero_diagramSchurPoly`): a shape has
the same Schur polynomial in `n` and in `n + 1` variables, once the extra variable is set to zero
— both being zero when the shape has more than `n` rows, so that no term at all survives.

Over `ℂ`, and for a shape `μ` of at most `n + 1` rows — so that `μ` is the highest weight of a
polynomial irreducible of `GLₙ₊₁` and `s_μ` its character — the specialization at `1` reads as the
multiplicity-free branching rule for the restriction `GLₙ₊₁ ↓ GLₙ`: that irreducible restricts to
the direct sum, each with multiplicity one, of the irreducibles whose highest weights interlace
`μ`.  That reading is not proved here, and it does not transfer to positive characteristic: there
the identity of characters no longer forces a direct-sum decomposition, because the representations
of `GLₙ₊₁` are not semisimple in general.  The graded identity is the sharper statement the
Gelfand-Tsetlin theory iterates, since it records not only which shapes occur but the weight of
each occurrence.

Nothing analytic happens here.  `TauCeti.diagramSchurPoly` is by construction the generating
function of the bounded semistandard tableaux of its shape, so the identity is the sum-over-a-
partition form of the bijection `TauCeti.BoundedSSYT.fiberEquiv` of
`TauCeti.Combinatorics.Young.Interlacing`: a tableau in the `n + 1` letters `{0, …, n}` is a
tableau in the `n` letters `{0, …, n - 1}` on an interlacing sub-shape, together with the cells
carrying the top letter `n`.  Those cells are what the last variable counts.

## Main results

* `TauCeti.BoundedSSYT.weight_restrict`: the weight form of `TauCeti.BoundedSSYT.content_restrict`,
  that erasing the top letter of a tableau does not change how often any of the remaining letters
  occurs, and `TauCeti.BoundedSSYT.card_add_weight_last`: the erased letter accounts for exactly
  the cells the sub-shape drops.
* `TauCeti.BoundedSSYT.weight_eq_mapDomain_add_single`: the resulting splitting of the weight of a
  tableau into the weight of its restriction and the multiplicity of the top letter.
* `TauCeti.diagramSchurPoly_eq_sum_interlacingShapes`: **the branching rule**, as an identity of
  polynomials graded by the last variable.
* `TauCeti.aeval_snoc_diagramSchurPoly`: the substitution of an arbitrary value for the last
  variable, in an arbitrary algebra, from which `TauCeti.eval_snoc_diagramSchurPoly`,
  `TauCeti.aeval_snoc_one_diagramSchurPoly`, `TauCeti.eval_snoc_one_diagramSchurPoly` and
  `TauCeti.eval_diagramSchurPoly_of_apply_last_eq_one` — the specializations at an arbitrary
  value and at `1` — are read off.
* `TauCeti.aeval_snoc_zero_diagramSchurPoly`: **stability**, the specialization at `0`.

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
content restricted to the alphabet.

Not a `simp` lemma: `simp` already reduces the left-hand side by unfolding `weight` and applying
the `simp` lemma `TauCeti.BoundedSSYT.content_restrict` it transports, so tagging it would only
duplicate that route. -/
theorem weight_restrict (T : BoundedSSYT (n + 1) μ) (hν : restrictShape T = ν) (i : Fin n) :
    weight (restrict T ν hν) i = weight T i.castSucc := by
  rw [weight_apply, weight_apply, Fin.val_castSucc, content_restrict T hν i.isLt]

/-- **The top letter fills exactly the cells the sub-shape drops.**  Every cell of `μ` carries a
letter, and the letters below the top one occupy precisely the cells of the sub-shape `ν`, so the
multiplicity of the top letter makes up the difference `|μ| - |ν|`.  Stated as an addition, which
is the form the exponent bookkeeping of the branching rule needs. -/
theorem card_add_weight_last (T : BoundedSSYT (n + 1) μ) :
    (restrictShape T).card + weight T (Fin.last n) = μ.card := by
  have hsum : ∑ i, weight T i = μ.card := sum_weight T
  rw [Fin.sum_univ_castSucc] at hsum
  rw [← hsum, ← sum_weight (restrict T _ rfl)]
  exact congrArg (· + weight T (Fin.last n))
    (Finset.sum_congr rfl fun i _ => weight_restrict T rfl i)

/-- **The weight of a tableau splits along the top letter**: it is the weight of the restriction,
transported into the first `n` letters, together with the multiplicity of the top letter.  This is
the exponent-vector form of the branching bijection, and is what turns the sum over tableaux
defining a Schur polynomial into a sum of monomials in the last variable. -/
theorem weight_eq_mapDomain_add_single (T : BoundedSSYT (n + 1) μ) (hν : restrictShape T = ν) :
    weight T = Finsupp.mapDomain Fin.castSucc (weight (restrict T ν hν))
      + Finsupp.single (Fin.last n) (weight T (Fin.last n)) := by
  ext i
  induction i using Fin.lastCases with
  | last =>
    rw [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.mapDomain_of_notMem_range _ _
        (by rintro ⟨j, hj⟩; exact absurd hj (Fin.castSucc_lt_last j).ne),
      zero_add]
  | cast j =>
    have hne : Fin.castSucc j ≠ Fin.last n := (Fin.castSucc_lt_last j).ne
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply (Fin.castSucc_injective n),
      Finsupp.single_eq_of_ne hne, add_zero, weight_restrict T hν j]

end BoundedSSYT

/-- **The branching rule for Schur polynomials**, as an identity of polynomials over an arbitrary
commutative semiring: `s_μ` in `n + 1` variables is the sum, over the shapes `ν` interlacing `μ`
with at most `n` rows, of `s_ν` in the first `n` variables times the last variable raised to
`|μ| - |ν|`.

Each interlacing shape occurs exactly once, in exactly one degree in the last variable.  Over `ℂ`,
and for a shape `μ` of at most `n + 1` rows, setting the last variable to `1` is the character form
of the multiplicity-free `GLₙ₊₁ ↓ GLₙ` branching rule. -/
theorem diagramSchurPoly_eq_sum_interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram) :
    diagramSchurPoly (n + 1) R μ
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          X (Fin.last n) ^ (μ.card - ν.card) * rename Fin.castSucc (diagramSchurPoly n R ν) := by
  have key : ∀ T : BoundedSSYT (n + 1) μ,
      (monomial (BoundedSSYT.weight T) (1 : R))
        = X (Fin.last n) ^ (μ.card - (BoundedSSYT.restrictShape T).card) *
            rename Fin.castSucc
              (monomial (BoundedSSYT.weight (BoundedSSYT.restrict T _ rfl)) (1 : R)) := by
    intro T
    have hcard := BoundedSSYT.card_add_weight_last T
    have hexp : μ.card - (BoundedSSYT.restrictShape T).card
        = BoundedSSYT.weight T (Fin.last n) := by omega
    have hw : BoundedSSYT.weight T
        = Finsupp.single (Fin.last n) (BoundedSSYT.weight T (Fin.last n))
          + Finsupp.mapDomain Fin.castSucc
              (BoundedSSYT.weight (BoundedSSYT.restrict T _ rfl)) :=
      (BoundedSSYT.weight_eq_mapDomain_add_single T rfl).trans (add_comm _ _)
    rw [rename_monomial, X_pow_eq_monomial, monomial_mul, one_mul, hexp]
    exact congrArg (monomial · (1 : R)) hw
  rw [diagramSchurPoly_eq_sum, Finset.sum_congr rfl fun T _ => key T,
    BoundedSSYT.sum_eq_sum_interlacingShapes n μ fun ν S =>
      X (Fin.last n) ^ (μ.card - ν.card) * rename Fin.castSucc (monomial (BoundedSSYT.weight S) 1)]
  exact Finset.sum_congr rfl fun ν _ => by
    rw [← Finset.mul_sum, ← map_sum, diagramSchurPoly_eq_sum]

/-- **The branching rule, with the last variable substituted.**  Substituting a family of values in
an `R`-algebra for the first `n` variables of `s_μ` and `t` for the last gives the sum of
`t ^ (|μ| - |ν|) · s_ν` over the shapes `ν` interlacing `μ`.  The specializations below are the
cases of an evaluation in `R` itself, and of the variables themselves for the first `n`. -/
theorem aeval_snoc_diagramSchurPoly {A : Type*} [CommSemiring A] [Algebra R A] (n : ℕ)
    (μ : _root_.YoungDiagram) (x : Fin n → A) (t : A) :
    aeval (Fin.snoc x t) (diagramSchurPoly (n + 1) R μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          t ^ (μ.card - ν.card) * aeval x (diagramSchurPoly n R ν) := by
  rw [diagramSchurPoly_eq_sum_interlacingShapes, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_mul, map_pow, aeval_X, Fin.snoc_last, aeval_rename, Fin.snoc_comp_castSucc]

/-- **The branching rule, evaluated at an arbitrary last value.**  Substituting `t` for the last
variable of `s_μ` gives the sum of `t ^ (|μ| - |ν|) · s_ν` over the shapes `ν` interlacing `μ`. -/
theorem eval_snoc_diagramSchurPoly (n : ℕ) (μ : _root_.YoungDiagram) (x : Fin n → R) (t : R) :
    eval (Fin.snoc x t) (diagramSchurPoly (n + 1) R μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          t ^ (μ.card - ν.card) * eval x (diagramSchurPoly n R ν) := by
  simpa only [aeval_eq_eval] using aeval_snoc_diagramSchurPoly (R := R) n μ x t

/-- **The branching rule with the last variable set to `1`, as an identity of polynomials.**  This
is stronger than the identity of values `TauCeti.eval_diagramSchurPoly_of_apply_last_eq_one` below:
over a general commutative semiring an identity holding at every family of values need not hold
between the polynomials themselves. -/
theorem aeval_snoc_one_diagramSchurPoly (n : ℕ) (μ : _root_.YoungDiagram) :
    aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) R) 1) (diagramSchurPoly (n + 1) R μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, diagramSchurPoly n R ν := by
  rw [aeval_snoc_diagramSchurPoly]
  exact Finset.sum_congr rfl fun ν _ => by rw [one_pow, one_mul, aeval_X_left_apply]

/-- **Stability of Schur polynomials.**  A shape has the same Schur polynomial in `n` and in
`n + 1` variables, once the extra variable is set to `0`: only the shape itself survives the
specialization, every other interlacing shape being smaller and so carrying a positive power of
the vanishing variable.  A shape of more than `n` rows interlaces no shape of at most `n` rows
that is as large, so there both sides vanish.

Not a `simp` lemma: substituting polynomials for the variables, `simp` rewrites `aeval` to
`bind₁` by `MvPolynomial.aeval_eq_bind₁`, so this left-hand side is not in `simp`-normal form. -/
theorem aeval_snoc_zero_diagramSchurPoly (n : ℕ) (μ : _root_.YoungDiagram) :
    aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) R) 0) (diagramSchurPoly (n + 1) R μ)
      = diagramSchurPoly n R μ := by
  have hvanish : ∀ ν ∈ YoungDiagram.interlacingShapes n μ, ν ≠ μ →
      (0 : MvPolynomial (Fin n) R) ^ (μ.card - ν.card) * aeval X (diagramSchurPoly n R ν) = 0 := by
    intro ν hν hne
    have hsub : ν.cells ⊆ μ.cells :=
      YoungDiagram.cells_subset_iff.mpr (YoungDiagram.mem_interlacingShapes.mp hν).1.le
    have hlt : ν.card < μ.card :=
      Finset.card_lt_card (lt_of_le_of_ne hsub fun h => hne (YoungDiagram.ext h))
    rw [zero_pow (by omega), zero_mul]
  rw [aeval_snoc_diagramSchurPoly]
  rcases le_or_gt (μ.colLen 0) n with hμ | hμ
  · have hself : μ ∈ YoungDiagram.interlacingShapes n μ :=
      YoungDiagram.mem_interlacingShapes.mpr
        ⟨YoungDiagram.interlacedBy_iff.mpr
          fun i => ⟨μ.rowLen_anti i (i + 1) (Nat.le_succ i), le_rfl⟩, hμ⟩
    rw [Finset.sum_eq_single_of_mem μ hself hvanish, Nat.sub_self, pow_zero, one_mul,
      aeval_X_left_apply]
  · rw [diagramSchurPoly_eq_zero_of_lt_colLen hμ]
    refine Finset.sum_eq_zero fun ν hν => hvanish ν hν ?_
    rintro rfl
    have := (YoungDiagram.mem_interlacingShapes.mp hν).2
    omega

/-- **The branching rule for Schur polynomials**, evaluated at a family of values with a `1`
appended. -/
theorem eval_snoc_one_diagramSchurPoly (n : ℕ) (μ : _root_.YoungDiagram) (x : Fin n → R) :
    eval (Fin.snoc x 1) (diagramSchurPoly (n + 1) R μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, eval x (diagramSchurPoly n R ν) := by
  rw [eval_snoc_diagramSchurPoly]
  exact Finset.sum_congr rfl fun ν _ => by rw [one_pow, one_mul]

/-- **The branching rule for Schur polynomials**, at any evaluation sending the last variable
to `1`: the value of `s_μ` in `n + 1` variables is the sum of the values of the `s_ν` in the first
`n`, over the shapes `ν` interlacing `μ` with at most `n` rows, each occurring once. -/
theorem eval_diagramSchurPoly_of_apply_last_eq_one (n : ℕ) (μ : _root_.YoungDiagram)
    (x : Fin (n + 1) → R) (hx : x (Fin.last n) = 1) :
    eval x (diagramSchurPoly (n + 1) R μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          eval (fun i : Fin n => x i.castSucc) (diagramSchurPoly n R ν) := by
  conv_lhs => rw [← Fin.snoc_init_self x, hx]
  rw [eval_snoc_one_diagramSchurPoly, Fin.init_def]

end TauCeti
