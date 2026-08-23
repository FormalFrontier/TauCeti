/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb
public import TauCeti.GroupTheory.SpecificGroups.Braid
import Mathlib.Tactic.LinearCombination

/-!
# The Jones representation of the braid group

For a unit `a : Rˣ`, set the Temperley-Lieb loop value to
`δ = -(a ^ 2 + a⁻¹ ^ 2)`. The Kauffman-bracket assignment

`σ i ↦ a • 1 + a⁻¹ • e i`

satisfies the braid relations and defines `TauCeti.TemperleyLieb.jones`, a representation of
`TauCeti.BraidGroup n` in the units of `TemperleyLieb R δ n`. At this loop value the
coefficient-swapped element `a⁻¹ • 1 + a • e i` is the inverse of the assigned crossing.
Composing this representation with the Markov trace is the braid route to the Jones polynomial;
the trace is not built here.

## Main definitions

* `TauCeti.TemperleyLieb.jonesDelta`: the loop value `-(a ^ 2 + a⁻¹ ^ 2)`.
* `TauCeti.TemperleyLieb.jonesUnit`: the Kauffman-bracket expansion of one crossing as a unit.
* `TauCeti.TemperleyLieb.jones`: the Jones representation
  `BraidGroup n →* (TemperleyLieb R (jonesDelta a) n)ˣ`.

## Main results

* `TauCeti.TemperleyLieb.jones_sigma`: the representation sends `sigma i` to `jonesUnit a i`.
* `TauCeti.TemperleyLieb.jones_sigma_ne_one_two`: the representation is nontrivial on two
  strands over a nontrivial base ring.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103-111.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3
  (the Kauffman bracket and Jones polynomial).
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.

This is Layer 4 ("knot theory, done properly") of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`), whose knot-polynomial bullet asks for the Jones
polynomial "from the Kauffman bracket on a diagram and from the Temperley-Lieb / Jones
representation of a braid".
-/

public section

namespace TauCeti.TemperleyLieb

variable (R : Type*) [CommRing R] (n : ℕ)
variable {R n}

/-- The loop value `-(a ^ 2 + a⁻¹ ^ 2)` at which the Jones representation is defined. -/
def jonesDelta (a : Rˣ) : R := -((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2)

/-- The defining equation of the Jones loop value. -/
@[simp]
theorem jonesDelta_def (a : Rˣ) :
    jonesDelta a = -((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2) := (rfl)

/-- The Jones loop value is symmetric in `a` and `a⁻¹`, which is what lets the two coefficients
of a crossing be swapped. -/
theorem jonesDelta_eq_neg_inv_sq_add_sq (a : Rˣ) :
    jonesDelta a = -((((a⁻¹ : Rˣ) : R)) ^ 2 + (a : R) ^ 2) := by
  rw [jonesDelta_def]
  ring

/-- The Kauffman-bracket expansion of an elementary braid, as a unit of the Temperley-Lieb
algebra: `a • 1 + a⁻¹ • e i`, with inverse `a⁻¹ • 1 + a • e i`. -/
def jonesUnit (a : Rˣ) (i : Fin (n - 1)) : (TemperleyLieb R (jonesDelta a) n)ˣ where
  val := crossing (jonesDelta a) (a : R) ((a⁻¹ : Rˣ) : R) i
  inv := crossing (jonesDelta a) ((a⁻¹ : Rˣ) : R) (a : R) i
  val_inv := crossing_mul_crossing_swap_eq_one a.mul_inv (jonesDelta_def a) i
  inv_val := crossing_mul_crossing_swap_eq_one a.inv_mul (jonesDelta_eq_neg_inv_sq_add_sq a) i

/-- The value of the Kauffman-bracket unit. -/
@[simp]
theorem jonesUnit_val (a : Rˣ) (i : Fin (n - 1)) :
    ((jonesUnit a i : (TemperleyLieb R (jonesDelta a) n)ˣ) : TemperleyLieb R (jonesDelta a) n)
      = crossing (jonesDelta a) (a : R) ((a⁻¹ : Rˣ) : R) i := (rfl)

/-- The value of the inverse of the Kauffman-bracket unit. -/
@[simp]
theorem jonesUnit_inv_val (a : Rˣ) (i : Fin (n - 1)) :
    (((jonesUnit a i : (TemperleyLieb R (jonesDelta a) n)ˣ)⁻¹ :
        (TemperleyLieb R (jonesDelta a) n)ˣ) : TemperleyLieb R (jonesDelta a) n)
      = crossing (jonesDelta a) ((a⁻¹ : Rˣ) : R) (a : R) i := (rfl)

private theorem jones_braid_coeff (a : Rˣ) :
    ((a⁻¹ : Rˣ) : R) * ((a : R) ^ 2 + (a : R) * ((a⁻¹ : Rˣ) : R) * jonesDelta a
      + ((a⁻¹ : Rˣ) : R) ^ 2) = 0 := by
  rw [jonesDelta_def]
  linear_combination
    (-((a⁻¹ : Rˣ) : R) * ((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2)) * a.mul_inv

variable (n) in
/-- The Jones representation of the braid group in the units of the Temperley-Lieb algebra: the
elementary braid `σ i` goes to the Kauffman-bracket expansion `a • 1 + a⁻¹ • e i` of a crossing.
Composing it with the Markov trace is the braid route to the Jones polynomial. -/
def jones (a : Rˣ) : BraidGroup n →* (TemperleyLieb R (jonesDelta a) n)ˣ :=
  BraidGroup.lift (fun i => jonesUnit a i)
    (fun h => Units.ext <| by
      simp only [Units.val_mul, jonesUnit_val]
      exact crossing_mul_crossing_comm _ _ _ _ h)
    (fun h => Units.ext <| by
      simp only [Units.val_mul, jonesUnit_val]
      exact crossing_braid (jones_braid_coeff a) h)

/-- The Jones representation takes an elementary braid to the Kauffman-bracket unit. -/
@[simp]
theorem jones_sigma (a : Rˣ) (i : Fin (n - 1)) :
    jones n a (BraidGroup.sigma i) = jonesUnit a i :=
  BraidGroup.lift_sigma _ _ _ i

/-- The Jones representation of the two-strand braid group is nontrivial: the elementary braid
does not go to the identity. -/
theorem jones_sigma_ne_one_two [Nontrivial R] (a : Rˣ) (i : Fin (2 - 1)) :
    jones 2 a (BraidGroup.sigma i) ≠ 1 := by
  intro h
  have hval : (a : R) • (1 : TemperleyLieb R (jonesDelta a) 2)
      + ((a⁻¹ : Rˣ) : R) • e (jonesDelta a) i = 1 := by
    rw [← crossing_def, ← jonesUnit_val, ← jones_sigma, h, Units.val_one]
  have hone : (1 : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  have hmat := congrArg (fun x => twoStrandRep (jonesDelta a) x 1 0) hval
  simp [hone] at hmat

end TauCeti.TemperleyLieb
