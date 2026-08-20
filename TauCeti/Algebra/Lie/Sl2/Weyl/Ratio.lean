/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import TauCeti.Algebra.Lie.Sl2.Basic
public import TauCeti.Algebra.Lie.Sl2.Weyl.Automorphism

public section

/-!
# The scaled Weyl elements and their Weyl ratios

Let `t : IsSl2Triple H E F` be an `sl₂` triple in an associative algebra `A`, with `E` and `F`
nilpotent, and let `A` also be an algebra over a commutative ring `R`. For a unit `c` of `R` the
rescaled elements `c • E` and `c⁻¹ • F` form an `sl₂` triple with the same Cartan element
(`TauCeti.isSl2Triple_smulUnits`), so the Weyl element of
`TauCeti/Algebra/Lie/Sl2/Weyl/Automorphism.lean` is available at every scale:

```text
n (c) = exp (c • E) · exp (-(c⁻¹ • F)) · exp (c • E),
```

Chevalley's `n_α(c) = x_α(c) x_{-α}(-c⁻¹) x_α(c)`. Their ratios

```text
h (c) = n (c) · n (1)⁻¹
```

are the elements denoted `h_α(c) = n_α(c) n_α(1)⁻¹` in Chevalley's construction. This file
constructs both parameterized families and proves their conjugation relations against the triple.
It does not prove that `c ↦ h_α(c)` is multiplicative, so it does not package this family as a
cocharacter.

The scaled Weyl element inverts the Cartan element and interchanges the two nilpotent elements with
a scale, `n (c) E n (c)⁻¹ = -(c⁻²) • F` and `n (c) F n (c)⁻¹ = -(c²) • E`, while its effect on an
element on which `E` and `F` have opposite eigenvalues — a Cartan element, in the intended
application — is the coreflection `y ↦ y - q • H`, *independently of* `c`. That independence is what
makes `h (c)` centralise every element with those opposite eigenvalues, while acting on the two root
vectors with the expected exponents,

```text
h (c) E h (c)⁻¹ = c² • E,     h (c) F h (c)⁻¹ = c⁻² • F,
```

Centralisation of a whole Cartan subalgebra is not proved here — this file has no Cartan
subalgebra and no root space decomposition. It is the consequence of the displayed hypotheses in a
setting supplying them, where every Cartan element `y` has `⁅y, E⁆ = α(y) • E` and
`⁅y, F⁆ = -(α(y) • F)` for the root `α` of the triple.

On the root subgroups themselves the same relations read
`h (c) x_α(u) h (c)⁻¹ = x_α(c² u)` and `n (c) x_α(u) n (c)⁻¹ = x_{-α}(-c⁻² u)`, and conjugation
carries one scaled Weyl element to another, `h (c) n (u) h (c)⁻¹ = n (c² u)`.

Nothing here needs a Cartan subalgebra, a weight-space decomposition or any finiteness: the whole
content is the rescaling of the triple together with the relations already proved for the Weyl
element at scale one. The `ℚ`-algebra hypothesis is inherited from the exponentials, which divide
by factorials.

## Main definitions

* `TauCeti.weylUnitSMul`: the scaled Weyl element `n (c)`.
* `TauCeti.weylRatio`: the family of Weyl ratios `h (c) = n (c) n (1)⁻¹`.

## Main results

* `TauCeti.isSl2Triple_smulUnits`: rescaling an `sl₂` triple by a unit of the base ring.
* `TauCeti.weylUnitSMul_one` and `TauCeti.weylRatio_one`: at scale one the scaled Weyl element is
  the Weyl element and its ratio is trivial.
* `TauCeti.weylRatio_def`: the characteristic equation defining the Weyl ratio.
* `TauCeti.weylUnitSMul_eq_weylRatio_mul`: the normal form `n_α(c) = h_α(c) n_α(1)`.
* `TauCeti.weylUnitSMul_conj_h`, `TauCeti.weylUnitSMul_conj_e`, `TauCeti.weylUnitSMul_conj_f`:
  the scaled Weyl element negates the Cartan element and interchanges the two nilpotent elements
  with the scales `c⁻²` and `c²`.
* `TauCeti.weylUnitSMul_conj_of_lie_eq_smul`: the coreflection formula, independent of the scale.
* `TauCeti.weylRatio_conj_of_lie_eq_smul` and `TauCeti.weylRatio_conj_h`: the Weyl ratio
  centralises every element on which `E` and `F` have opposite eigenvalues.
* `TauCeti.weylRatio_conj_e` and `TauCeti.weylRatio_conj_f`: it scales the two nilpotent elements
  by `c²` and `c⁻²`.
* `TauCeti.weylRatio_conj_exp_smul`, `TauCeti.weylRatio_conj_exp_neg_smul` and
  `TauCeti.weylUnitSMul_conj_exp_smul`: the same relations read on the root subgroup elements.
* `TauCeti.weylRatio_conj_weylUnitSMul`: conjugation by `h (c)` carries `n (u)` to `n (c² u)`.
* `TauCeti.lie_weylRatio_conj`: the Weyl ratio preserves the eigenspaces of the Cartan
  element.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.1.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.

These Weyl-ratio relations are prerequisites for the coroot cocharacter and its relations against
the root subgroups, which are part of the pinning data asked for by Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, consumed by milestone L0 of the `CFSGStatement`
roadmap.
-/

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Conjugation by a unit -/

section Conjugation

variable {A : Type*} [Ring A] [Algebra ℚ A] {H E F : A}

variable (hE : IsNilpotent E) (hF : IsNilpotent F) (ht : IsSl2Triple H E F)

include ht

/-- The Weyl element carries the negated lowering element back to the raising element. -/
private theorem inv_weylUnit_conj_e :
    (((weylUnit hE hF)⁻¹ : Aˣ) : A) * E * ((weylUnit hE hF : Aˣ) : A) = -F := by
  have key : ((weylUnit hE hF : Aˣ) : A) * F * (((weylUnit hE hF)⁻¹ : Aˣ) : A) = -E := by
    rw [coe_weylUnit, coe_inv_weylUnit]
    exact weylUnit_conj_f ht hE hF
  -- Rewrite the displayed products as the inverse `ConjAct` action to cancel conjugations.
  change (ConjAct.toConjAct (weylUnit hE hF))⁻¹ • E = -F
  rw [← neg_eq_iff_eq_neg]
  rw [← smul_neg]
  change (ConjAct.toConjAct (weylUnit hE hF))⁻¹ • (-E) = F
  rw [← key]
  exact inv_smul_smul _ _

/-- The Weyl element carries the negated raising element back to the lowering element. -/
private theorem inv_weylUnit_conj_f :
    (((weylUnit hE hF)⁻¹ : Aˣ) : A) * F * ((weylUnit hE hF : Aˣ) : A) = -E := by
  have key : ((weylUnit hE hF : Aˣ) : A) * E * (((weylUnit hE hF)⁻¹ : Aˣ) : A) = -F := by
    rw [coe_weylUnit, coe_inv_weylUnit]
    exact weylUnit_conj_e ht hE hF
  -- Rewrite the displayed products as the inverse `ConjAct` action to cancel conjugations.
  change (ConjAct.toConjAct (weylUnit hE hF))⁻¹ • F = -E
  rw [← neg_eq_iff_eq_neg]
  rw [← smul_neg]
  change (ConjAct.toConjAct (weylUnit hE hF))⁻¹ • (-F) = E
  rw [← key]
  exact inv_smul_smul _ _

end Conjugation

section Scaled

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {H E F : A}

variable [Algebra ℚ A]

/-! ## The scaled Weyl elements -/

/-- **The Weyl element of an `sl₂` triple at scale `c`**, the unit
`exp (c • E) · exp (-(c⁻¹ • F)) · exp (c • E)`.

For the images of a Chevalley root pair in a representation this is Chevalley's
`n_α(c) = x_α(c) x_{-α}(-c⁻¹) x_α(c)`; at `c = 1` it is `TauCeti.weylUnit`. -/
noncomputable def weylUnitSMul (hE : IsNilpotent E) (hF : IsNilpotent F) (c : Rˣ) : Aˣ :=
  weylUnit (hE.smul (c : R)) (hF.smul ((c⁻¹ : Rˣ) : R))

variable (hE : IsNilpotent E) (hF : IsNilpotent F)

/-- The scaled Weyl element is the threefold product of exponentials it is defined to be. -/
@[simp]
theorem coe_weylUnitSMul (c : Rˣ) :
    ((weylUnitSMul (R := R) hE hF c : Aˣ) : A) =
      IsNilpotent.exp ((c : R) • E) * IsNilpotent.exp (-(((c⁻¹ : Rˣ) : R) • F)) *
        IsNilpotent.exp ((c : R) • E) :=
  coe_weylUnit _ _

/-- The inverse of the scaled Weyl element is obtained by negating every exponent. -/
@[simp]
theorem coe_inv_weylUnitSMul (c : Rˣ) :
    (((weylUnitSMul (R := R) hE hF c)⁻¹ : Aˣ) : A) =
      IsNilpotent.exp (-((c : R) • E)) * IsNilpotent.exp (((c⁻¹ : Rˣ) : R) • F) *
        IsNilpotent.exp (-((c : R) • E)) :=
  coe_inv_weylUnit _ _

/-- At scale one the scaled Weyl element is the Weyl element. -/
@[simp]
theorem weylUnitSMul_one : weylUnitSMul (R := R) hE hF 1 = weylUnit hE hF := by
  ext
  rw [coe_weylUnitSMul, coe_weylUnit]
  simp

/-! ## The coreflection formula -/

/-- **The coreflection formula does not see the scale.** An element `y` on which `E` and `F` have
the opposite eigenvalues `q` and `-q` is carried by conjugation with the scaled Weyl element to
`y - q • H`, whatever the scale `c`.

For a Cartan element `y` of the triple of a root `α` this is the coreflection
`y ↦ y - α(y) • α^∨`, and its independence of `c` is what makes the Weyl ratio
`TauCeti.weylRatio` centralise `y` (`TauCeti.weylRatio_conj_of_lie_eq_smul`), hence, in a setting
where every Cartan element satisfies these hypotheses, the whole Cartan subalgebra. -/
theorem weylUnitSMul_conj_of_lie_eq_smul (ht : IsSl2Triple H E F) {y : A} {q : ℚ}
    (hye : ⁅y, E⁆ = q • E) (hyf : ⁅y, F⁆ = -(q • F)) (c : Rˣ) :
    ((weylUnitSMul (R := R) hE hF c : Aˣ) : A) * y *
        (((weylUnitSMul (R := R) hE hF c)⁻¹ : Aˣ) : A) = y - q • H := by
  have hye' : ⁅y, ((c : R) • E)⁆ = q • ((c : R) • E) := by
    rw [lie_smul, hye, smul_comm]
  have hyf' : ⁅y, (((c⁻¹ : Rˣ) : R) • F)⁆ = -(q • (((c⁻¹ : Rˣ) : R) • F)) := by
    rw [lie_smul, hyf, smul_neg, smul_comm]
  exact weylUnit_conj_of_lie_eq_smul (isSl2Triple_smulUnits ht c) (hE.smul (c : R))
    (hF.smul ((c⁻¹ : Rˣ) : R)) hye' hyf'

/-- The scaled Weyl element negates the Cartan element of the triple. -/
theorem weylUnitSMul_conj_h (ht : IsSl2Triple H E F) (c : Rˣ) :
    ((weylUnitSMul (R := R) hE hF c : Aˣ) : A) * H *
        (((weylUnitSMul (R := R) hE hF c)⁻¹ : Aˣ) : A) = -H := by
  rw [weylUnitSMul_conj_of_lie_eq_smul hE hF ht (ht.lie_h_e_smul ℚ)
    (ht.lie_lie_smul_f ℚ)]
  module

/-- **The scaled Weyl element carries the raising element to the lowering element**, scaled by
`c⁻²`. For a Chevalley root pair this is `n_α(c) x_α(u) n_α(c)⁻¹ = x_{-α}(-c⁻² u)` read on the
Lie-algebra generator. -/
theorem weylUnitSMul_conj_e (ht : IsSl2Triple H E F) (c : Rˣ) :
    ((weylUnitSMul (R := R) hE hF c : Aˣ) : A) * E *
        (((weylUnitSMul (R := R) hE hF c)⁻¹ : Aˣ) : A) =
      -((((c⁻¹ : Rˣ) : R) ^ 2) • F) := by
  have key : ((weylUnitSMul (R := R) hE hF c : Aˣ) : A) * ((c : R) • E) *
      (((weylUnitSMul (R := R) hE hF c)⁻¹ : Aˣ) : A) = -(((c⁻¹ : Rˣ) : R) • F) := by
    rw [coe_weylUnitSMul, coe_inv_weylUnitSMul]
    exact weylUnit_conj_e (isSl2Triple_smulUnits ht c) (hE.smul (c : R))
        (hF.smul ((c⁻¹ : Rˣ) : R))
  rw [mul_smul_comm, smul_mul_assoc] at key
  have h2 := congrArg (fun x : A => ((c⁻¹ : Rˣ) : R) • x) key
  simp only [smul_smul, Units.inv_mul, one_smul, smul_neg] at h2
  rw [h2, sq]

/-- **The scaled Weyl element carries the lowering element to the raising element**, scaled by
`c²`. -/
theorem weylUnitSMul_conj_f (ht : IsSl2Triple H E F) (c : Rˣ) :
    ((weylUnitSMul (R := R) hE hF c : Aˣ) : A) * F *
        (((weylUnitSMul (R := R) hE hF c)⁻¹ : Aˣ) : A) = -((((c : Rˣ) : R) ^ 2) • E) := by
  have key : ((weylUnitSMul (R := R) hE hF c : Aˣ) : A) * (((c⁻¹ : Rˣ) : R) • F) *
      (((weylUnitSMul (R := R) hE hF c)⁻¹ : Aˣ) : A) = -((c : R) • E) := by
    rw [coe_weylUnitSMul, coe_inv_weylUnitSMul]
    exact weylUnit_conj_f (isSl2Triple_smulUnits ht c) (hE.smul (c : R))
        (hF.smul ((c⁻¹ : Rˣ) : R))
  rw [mul_smul_comm, smul_mul_assoc] at key
  have h2 := congrArg (fun x : A => ((c : Rˣ) : R) • x) key
  simp only [smul_smul, Units.mul_inv, one_smul, smul_neg] at h2
  rw [h2, sq]

/-- **Conjugating a root subgroup element by the scaled Weyl element.** The exponential of `u • E`
is carried to the exponential of `-(c⁻² u) • F`; for a Chevalley root pair this is
`n_α(c) x_α(u) n_α(c)⁻¹ = x_{-α}(-c⁻² u)`. -/
theorem weylUnitSMul_conj_exp_smul (ht : IsSl2Triple H E F) (c : Rˣ) (u : R) :
    ((weylUnitSMul (R := R) hE hF c : Aˣ) : A) * IsNilpotent.exp (u • E) *
        (((weylUnitSMul (R := R) hE hF c)⁻¹ : Aˣ) : A) =
      IsNilpotent.exp (-((u * ((c⁻¹ : Rˣ) : R) ^ 2) • F)) := by
  -- Regard the displayed product as Mathlib's conjugation action, which commutes with `exp`.
  change ConjAct.toConjAct (weylUnitSMul (R := R) hE hF c) •
    IsNilpotent.exp (u • E) = _
  rw [← IsNilpotent.exp_smul _ (hE.smul u)]
  simp only [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, mul_smul_comm,
    smul_mul_assoc, weylUnitSMul_conj_e hE hF ht c, smul_neg, smul_smul]

/-! ## Weyl ratios -/

/-- **The Weyl ratio at `c`**, the element `n (c) · n (1)⁻¹` obtained from the scaled Weyl element
and the Weyl element.

For the images of a Chevalley root pair in a representation this is Chevalley's
`h_α(c) = n_α(c) n_α(1)⁻¹`. No multiplicativity statement about this parameterized family is made
here. -/
noncomputable def weylRatio (hE : IsNilpotent E) (hF : IsNilpotent F) (c : Rˣ) : Aˣ :=
  weylUnitSMul hE hF c * (weylUnit hE hF)⁻¹

/-- The Weyl ratio is the scaled Weyl element multiplied by the inverse scale-one element. -/
theorem weylRatio_def (c : Rˣ) :
    weylRatio (R := R) hE hF c = weylUnitSMul hE hF c * (weylUnit hE hF)⁻¹ := by
  rw [weylRatio]

/-- The Weyl ratio at `1` is trivial. -/
@[simp]
theorem weylRatio_one : weylRatio (R := R) hE hF 1 = 1 := by
  rw [weylRatio_def, weylUnitSMul_one, mul_inv_cancel]

/-- The scaled Weyl element factors as its Weyl ratio times the Weyl element: the normal
form `n_α(c) = h_α(c) n_α(1)`. -/
theorem weylUnitSMul_eq_weylRatio_mul (c : Rˣ) :
    weylUnitSMul (R := R) hE hF c = weylRatio hE hF c * weylUnit hE hF := by
  rw [weylRatio_def, inv_mul_cancel_right]

/-- Conjugation by the Weyl ratio is conjugation by the Weyl element followed by
conjugation by the scaled Weyl element. -/
private theorem weylRatio_conj_eq (c : Rˣ) (x : A) :
    ((weylRatio (R := R) hE hF c : Aˣ) : A) * x *
        (((weylRatio (R := R) hE hF c)⁻¹ : Aˣ) : A) =
      ((weylUnitSMul (R := R) hE hF c : Aˣ) : A) *
        ((((weylUnit hE hF)⁻¹ : Aˣ) : A) * x * ((weylUnit hE hF : Aˣ) : A)) *
        (((weylUnitSMul (R := R) hE hF c)⁻¹ : Aˣ) : A) := by
  rw [weylRatio_def, Units.val_mul, mul_inv_rev, inv_inv, Units.val_mul]
  simp only [mul_assoc]

variable (ht : IsSl2Triple H E F)

include ht

/-- **The Weyl ratio centralises every element on which `E` and `F` have opposite eigenvalues.**
In the intended application these are the elements of the Cartan subalgebra. -/
theorem weylRatio_conj_of_lie_eq_smul {y : A} {q : ℚ}
    (hye : ⁅y, E⁆ = q • E) (hyf : ⁅y, F⁆ = -(q • F)) (c : Rˣ) :
    ((weylRatio (R := R) hE hF c : Aˣ) : A) * y *
        (((weylRatio (R := R) hE hF c)⁻¹ : Aˣ) : A) = y := by
  have hy' : (((weylUnit hE hF)⁻¹ : Aˣ) : A) * y * ((weylUnit hE hF : Aˣ) : A) = y - q • H :=
    inv_weylUnit_conj_of_lie_eq_smul ht hE hF hye hyf
  have hye' : ⁅y - q • H, E⁆ = (-q) • E := by
    rw [sub_lie, hye, smul_lie, ht.lie_h_e_nsmul]
    module
  have hyf' : ⁅y - q • H, F⁆ = -((-q) • F) := by
    rw [sub_lie, hyf, smul_lie, ht.lie_h_f_nsmul]
    module
  rw [weylRatio_conj_eq, hy', weylUnitSMul_conj_of_lie_eq_smul hE hF ht hye' hyf']
  module

/-- **The Weyl ratio scales the raising element by `c²`.** -/
theorem weylRatio_conj_e (c : Rˣ) :
    ((weylRatio (R := R) hE hF c : Aˣ) : A) * E *
        (((weylRatio (R := R) hE hF c)⁻¹ : Aˣ) : A) = (((c : Rˣ) : R) ^ 2) • E := by
  rw [weylRatio_conj_eq, inv_weylUnit_conj_e hE hF ht, mul_neg, neg_mul,
    weylUnitSMul_conj_f hE hF ht c, neg_neg]

/-- **The Weyl ratio scales the lowering element by `c⁻²`.** -/
theorem weylRatio_conj_f (c : Rˣ) :
    ((weylRatio (R := R) hE hF c : Aˣ) : A) * F *
        (((weylRatio (R := R) hE hF c)⁻¹ : Aˣ) : A) = (((c⁻¹ : Rˣ) : R) ^ 2) • F := by
  rw [weylRatio_conj_eq, inv_weylUnit_conj_f hE hF ht, mul_neg, neg_mul,
    weylUnitSMul_conj_e hE hF ht c, neg_neg]

/-- **The Weyl ratio centralises the Cartan element of the triple.** -/
theorem weylRatio_conj_h (c : Rˣ) :
    ((weylRatio (R := R) hE hF c : Aˣ) : A) * H *
        (((weylRatio (R := R) hE hF c)⁻¹ : Aˣ) : A) = H := by
  exact weylRatio_conj_of_lie_eq_smul hE hF ht (ht.lie_h_e_smul ℚ)
    (ht.lie_lie_smul_f ℚ) c

/-- **Conjugating a root subgroup element by the Weyl ratio.** For a Chevalley root pair this is
the relation `h_α(c) x_α(u) h_α(c)⁻¹ = x_α(c² u)`. -/
theorem weylRatio_conj_exp_smul (c : Rˣ) (u : R) :
    ((weylRatio (R := R) hE hF c : Aˣ) : A) * IsNilpotent.exp (u • E) *
        (((weylRatio (R := R) hE hF c)⁻¹ : Aˣ) : A) =
      IsNilpotent.exp ((u * ((c : Rˣ) : R) ^ 2) • E) := by
  -- Regard the displayed product as Mathlib's conjugation action, which commutes with `exp`.
  change ConjAct.toConjAct (weylRatio (R := R) hE hF c) • IsNilpotent.exp (u • E) = _
  rw [← IsNilpotent.exp_smul _ (hE.smul u)]
  simp only [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, mul_smul_comm,
    smul_mul_assoc, weylRatio_conj_e hE hF ht c, smul_smul]

/-- Conjugating the opposite root subgroup element by the Weyl ratio. -/
theorem weylRatio_conj_exp_neg_smul (c : Rˣ) (u : R) :
    ((weylRatio (R := R) hE hF c : Aˣ) : A) * IsNilpotent.exp (-(u • F)) *
        (((weylRatio (R := R) hE hF c)⁻¹ : Aˣ) : A) =
      IsNilpotent.exp (-((u * ((c⁻¹ : Rˣ) : R) ^ 2) • F)) := by
  -- Regard the displayed product as Mathlib's conjugation action, which commutes with `exp`.
  change ConjAct.toConjAct (weylRatio (R := R) hE hF c) • IsNilpotent.exp (-(u • F)) = _
  rw [← IsNilpotent.exp_smul _ (hF.smul u).neg]
  simp only [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, mul_neg, neg_mul,
    mul_smul_comm, smul_mul_assoc, weylRatio_conj_f hE hF ht c, smul_smul]

/-- **The Weyl ratio rescales the scaled Weyl elements**: conjugation by `h_α(c)` carries
`n_α(u)` to `n_α(c² u)`. -/
theorem weylRatio_conj_weylUnitSMul (c u : Rˣ) :
    weylRatio (R := R) hE hF c * weylUnitSMul hE hF u * (weylRatio (R := R) hE hF c)⁻¹ =
      weylUnitSMul hE hF (c ^ 2 * u) := by
  have hval : ((c ^ 2 * u : Rˣ) : R) = ((u : Rˣ) : R) * ((c : Rˣ) : R) ^ 2 := by
    push_cast
    ring
  have hinv : (((c ^ 2 * u : Rˣ)⁻¹ : Rˣ) : R) =
      ((u⁻¹ : Rˣ) : R) * ((c⁻¹ : Rˣ) : R) ^ 2 := by
    rw [mul_inv_rev, ← inv_pow]
    push_cast
    ring
  ext
  -- Extensionality turns unit conjugation into Mathlib's `ConjAct` action on the carrier.
  change ConjAct.toConjAct (weylRatio (R := R) hE hF c) •
      ((weylUnitSMul (R := R) hE hF u : Aˣ) : A) =
    ((weylUnitSMul (R := R) hE hF (c ^ 2 * u) : Aˣ) : A)
  rw [coe_weylUnitSMul, coe_weylUnitSMul, hval, hinv, smul_mul', smul_mul']
  simp only [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  rw [weylRatio_conj_exp_smul hE hF ht,
    weylRatio_conj_exp_neg_smul hE hF ht]

/-- **The Weyl ratio preserves the eigenspaces of the Cartan element.** It centralises
`H`, so conjugation by it commutes with the adjoint action of `H`. -/
theorem lie_weylRatio_conj {z : A} {m : R} (hhz : ⁅H, z⁆ = m • z) (c : Rˣ) :
    ⁅H, ((weylRatio (R := R) hE hF c : Aˣ) : A) * z *
        (((weylRatio (R := R) hE hF c)⁻¹ : Aˣ) : A)⁆ =
      m • (((weylRatio (R := R) hE hF c : Aˣ) : A) * z *
        (((weylRatio (R := R) hE hF c)⁻¹ : Aˣ) : A)) := by
  set g : Aˣ := weylRatio (R := R) hE hF c
  let φ := MulSemiringAction.toAlgEquiv R A (ConjAct.toConjAct g)
  have hH : φ H = H := weylRatio_conj_h hE hF ht c
  -- The displayed products are the underlying conjugation algebra equivalence `φ`.
  change ⁅H, φ z⁆ = m • φ z
  calc
    ⁅H, φ z⁆ = ⁅φ H, φ z⁆ := by rw [hH]
    _ = φ ⁅H, z⁆ := (LieHom.map_lie (φ : A →ₗ⁅R⁆ A) H z).symm
    _ = φ (m • z) := by rw [hhz]
    _ = m • φ z := map_smul φ m z

end Scaled

end TauCeti
