/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Complements on admissible changes of variables

Material complementing `Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean`: the
negation automorphism `[-1]` of a Weierstrass curve as an admissible change of variables, with
its involution API. This is the nontrivial automorphism in the `Aut (E, O)` milestone of
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 1, proved in
`TauCeti/AlgebraicGeometry/EllipticCurve/Aut.lean` to exhaust `Aut(E)` with the identity when
`j(E) ∉ {0, 1728}`.

Everything here is stated over a commutative ring: `⟨-1, 0, -a₁, -a₃⟩` is an admissible change
of variables for a Weierstrass curve over any commutative ring, and the two identities it
satisfies are polynomial. Only the nontriviality `negVariableChange_ne_one` needs the curve to
be elliptic over a nontrivial ring.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean` at the roadmap's pin
`bc2fe8ff7396` (FLT PR #1088), Apache 2.0, by Kevin Buzzard and Claude), generalised here from
FLT's field-level statements to a commutative ring.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (E : WeierstrassCurve R)

/-- The automorphism `[-1] : (x, y) ↦ (x, -y - a₁x - a₃)` of a Weierstrass curve, as an admissible
change of variables `⟨-1, 0, -a₁, -a₃⟩`. It fixes `E` (`negVariableChange_smul_self`) and is an
involution (`negVariableChange_mul_self`). -/
def negVariableChange : VariableChange R :=
  ⟨-1, 0, -E.a₁, -E.a₃⟩

@[simp] lemma negVariableChange_u : E.negVariableChange.u = -1 := by
  simp only [negVariableChange]

@[simp] lemma negVariableChange_r : E.negVariableChange.r = 0 := by
  simp only [negVariableChange]

@[simp] lemma negVariableChange_s : E.negVariableChange.s = -E.a₁ := by
  simp only [negVariableChange]

@[simp] lemma negVariableChange_t : E.negVariableChange.t = -E.a₃ := by
  simp only [negVariableChange]

/-- The negation automorphism fixes the curve. -/
@[simp] lemma negVariableChange_smul_self : E.negVariableChange • E = E := by
  ext <;>
    simp only [negVariableChange, variableChange_def, inv_neg, inv_one, Units.val_neg,
      Units.val_one] <;>
    ring

/-- The negation automorphism is an involution. -/
@[simp] lemma negVariableChange_mul_self : E.negVariableChange * E.negVariableChange = 1 := by
  simp [VariableChange.mul_def, VariableChange.one_def, negVariableChange,
    Odd.neg_one_pow (by decide : Odd 3)]

/-- The negation automorphism commutes with base change along a ring homomorphism. -/
@[simp] lemma negVariableChange_map {A : Type*} [CommRing A] (φ : R →+* A) :
    (E.map φ).negVariableChange = E.negVariableChange.map φ := by
  ext <;> simp [negVariableChange, VariableChange.map, map_a₁, map_a₃]

/-- The negation automorphism is its own inverse, being an involution. -/
@[simp] lemma negVariableChange_inv : E.negVariableChange⁻¹ = E.negVariableChange :=
  inv_eq_of_mul_eq_one_left E.negVariableChange_mul_self

/-- The negation automorphism is nontrivial for an elliptic curve: where `2 ≠ 0` it has
`u = -1 ≠ 1`, and where `2 = 0` it has `(s, t) = (-a₁, -a₃) ≠ (0, 0)`, since an elliptic curve
over a ring in which `2 = 0` cannot have `a₁ = a₃ = 0`. -/
lemma negVariableChange_ne_one [Nontrivial R] [E.IsElliptic] : E.negVariableChange ≠ 1 := by
  intro h
  rcases eq_or_ne (2 : R) 0 with h2 | h2
  · have hs := congrArg VariableChange.s h
    have ht := congrArg VariableChange.t h
    simp only [negVariableChange, VariableChange.one_def, neg_eq_zero] at hs ht
    grind [a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero]
  · contrapose h2
    have hv : (-1 : R) = 1 := by
      simpa [VariableChange.one_def] using congrArg (fun C : VariableChange R ↦ (C.u : R)) h
    linear_combination -hv

end WeierstrassCurve

end
