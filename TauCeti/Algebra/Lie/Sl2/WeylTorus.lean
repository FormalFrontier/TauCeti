/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.WeylAutomorphism

public section

/-!
# The scaled Weyl elements and their Weyl ratios

Let `t : IsSl2Triple H E F` be an `sl₂` triple in an associative algebra `A`, with `E` and `F`
nilpotent, and let `A` also be an algebra over a commutative ring `R`. For a unit `c` of `R` the
rescaled elements `c • E` and `c⁻¹ • F` form an `sl₂` triple with the same Cartan element
(`TauCeti.isSl2Triple_smulUnits`), so the Weyl element of
`TauCeti/Algebra/Lie/Sl2/WeylAutomorphism.lean` is available at every scale:

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
makes `h (c)` centralise the whole Cartan subalgebra while acting on the two root vectors with the
expected exponents,

```text
h (c) E h (c)⁻¹ = c² • E,     h (c) F h (c)⁻¹ = c⁻² • F,
```

On the root subgroups themselves the same relations read
`h (c) x_α(u) h (c)⁻¹ = x_α(c² u)` and `n (c) x_α(u) n (c)⁻¹ = x_{-α}(-c⁻² u)`, and conjugation
carries one scaled Weyl element to another, `h (c) n (u) h (c)⁻¹ = n (c² u)`.

Nothing here needs a Cartan subalgebra, a weight-space decomposition or any finiteness: the whole
content is the rescaling of the triple together with the relations already proved for the Weyl
element at scale one. The `ℚ`-algebra hypothesis is inherited from the exponentials, which divide
by factorials.

## Main definitions

* `TauCeti.weylUnitSMul`: the scaled Weyl element `n (c)`.
* `TauCeti.corootUnit`: the family of Weyl ratios `h (c) = n (c) n (1)⁻¹`.

## Main results

* `TauCeti.exp_units_conj`: conjugating a nilpotent exponential by a unit exponentiates the
  conjugate.
* `TauCeti.isSl2Triple_smulUnits`: rescaling an `sl₂` triple by a unit of the base ring.
* `TauCeti.weylUnitSMul_one` and `TauCeti.corootUnit_one`: at scale one the scaled Weyl element is
  the Weyl element and its ratio is trivial.
* `TauCeti.weylUnitSMul_eq_corootUnit_mul`: the normal form `n_α(c) = h_α(c) n_α(1)`.
* `TauCeti.weylUnitSMul_conj_h`, `TauCeti.weylUnitSMul_conj_e`, `TauCeti.weylUnitSMul_conj_f`:
  the scaled Weyl element negates the Cartan element and interchanges the two nilpotent elements
  with the scales `c⁻²` and `c²`.
* `TauCeti.weylUnitSMul_conj_of_lie_eq_smul`: the coreflection formula, independent of the scale.
* `TauCeti.corootUnit_conj_of_lie_eq_smul` and `TauCeti.corootUnit_conj_h`: the Weyl ratio
  centralises every element on which `E` and `F` have opposite eigenvalues.
* `TauCeti.corootUnit_conj_e` and `TauCeti.corootUnit_conj_f`: it scales the two nilpotent elements
  by `c²` and `c⁻²`.
* `TauCeti.corootUnit_conj_exp_smul`, `TauCeti.corootUnit_conj_exp_smul_neg` and
  `TauCeti.weylUnitSMul_conj_exp_smul`: the same relations read on the root subgroup elements.
* `TauCeti.corootUnit_conj_weylUnitSMul`: conjugation by `h (c)` carries `n (u)` to `n (c² u)`.
* `TauCeti.lie_corootUnit_conj`: the Weyl ratio preserves the eigenspaces of the Cartan
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

omit [Algebra ℚ A] in
/-- Conjugation by a unit distributes over a product. -/
private theorem units_conj_mul (g : Aˣ) (x y : A) :
    (g : A) * (x * y) * ((g⁻¹ : Aˣ) : A) =
      ((g : A) * x * ((g⁻¹ : Aˣ) : A)) * ((g : A) * y * ((g⁻¹ : Aˣ) : A)) := by
  simp only [mul_assoc]
  congr 1
  congr 1
  rw [← mul_assoc ((g⁻¹ : Aˣ) : A) (g : A) _, Units.inv_mul, one_mul]

omit [Algebra ℚ A] in
/-- Conjugation by the inverse of a unit undoes conjugation by that unit. -/
private theorem units_conj_symm (g : Aˣ) {x y : A}
    (h : (g : A) * x * ((g⁻¹ : Aˣ) : A) = y) :
    ((g⁻¹ : Aˣ) : A) * y * (g : A) = x := by
  subst h
  simp [mul_assoc]

/-- **Conjugating a nilpotent exponential by a unit exponentiates the conjugate.** Conjugation is
a ring endomorphism and the exponential of a nilpotent element is a finite sum of its powers, so
the two operations commute. -/
theorem exp_units_conj (g : Aˣ) {x : A} (hx : IsNilpotent x) :
    (g : A) * IsNilpotent.exp x * ((g⁻¹ : Aˣ) : A) =
      IsNilpotent.exp ((g : A) * x * ((g⁻¹ : Aˣ) : A)) := by
  obtain ⟨k, hk⟩ := hx
  have hk' : ((g : A) * x * ((g⁻¹ : Aˣ) : A)) ^ k = 0 := by
    rw [Units.conj_pow, hk, mul_zero, zero_mul]
  rw [IsNilpotent.exp_eq_sum hk, IsNilpotent.exp_eq_sum hk', Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Units.conj_pow, mul_smul_comm, smul_mul_assoc]

variable (hE : IsNilpotent E) (hF : IsNilpotent F) (ht : IsSl2Triple H E F)

include ht

/-- The Weyl element carries the negated lowering element back to the raising element. -/
private theorem inv_weylUnit_conj_e :
    (((weylUnit hE hF)⁻¹ : Aˣ) : A) * E * ((weylUnit hE hF : Aˣ) : A) = -F := by
  have key : ((weylUnit hE hF : Aˣ) : A) * F * (((weylUnit hE hF)⁻¹ : Aˣ) : A) = -E := by
    rw [coe_weylUnit, coe_inv_weylUnit]
    exact weylUnit_conj_f ht hE hF
  rw [← neg_eq_iff_eq_neg, ← neg_mul, ← mul_neg]
  exact units_conj_symm (weylUnit hE hF) key

/-- The Weyl element carries the negated raising element back to the lowering element. -/
private theorem inv_weylUnit_conj_f :
    (((weylUnit hE hF)⁻¹ : Aˣ) : A) * F * ((weylUnit hE hF : Aˣ) : A) = -E := by
  have key : ((weylUnit hE hF : Aˣ) : A) * E * (((weylUnit hE hF)⁻¹ : Aˣ) : A) = -F := by
    rw [coe_weylUnit, coe_inv_weylUnit]
    exact weylUnit_conj_e ht hE hF
  rw [← neg_eq_iff_eq_neg, ← neg_mul, ← mul_neg]
  exact units_conj_symm (weylUnit hE hF) key

/-- The Weyl element negates the Cartan element in either direction. -/
private theorem inv_weylUnit_conj_h :
    (((weylUnit hE hF)⁻¹ : Aˣ) : A) * H * ((weylUnit hE hF : Aˣ) : A) = -H := by
  have key : ((weylUnit hE hF : Aˣ) : A) * H * (((weylUnit hE hF)⁻¹ : Aˣ) : A) = -H := by
    rw [coe_weylUnit, coe_inv_weylUnit]
    exact weylUnit_conj_h ht hE hF
  rw [← neg_eq_iff_eq_neg, ← neg_mul, ← mul_neg]
  exact units_conj_symm (weylUnit hE hF) key

end Conjugation

/-! ## Rescaling an `sl₂` triple -/

section Scaled

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {H E F : A}

/-- **Rescaling an `sl₂` triple by a unit of the base ring.** Scaling the raising element by `c`
and the lowering element by `c⁻¹` leaves their bracket, hence the Cartan element, unchanged.

For the triple of a root `α` this is the reparametrisation of the pair of root subgroups that the
scaled Weyl element `TauCeti.weylUnitSMul` is built from. -/
theorem isSl2Triple_smulUnits (ht : IsSl2Triple H E F) (c : Rˣ) :
    IsSl2Triple H ((c : R) • E) (((c⁻¹ : Rˣ) : R) • F) where
  h_ne_zero := ht.h_ne_zero
  lie_e_f := by
    rw [smul_lie, lie_smul, ht.lie_e_f, smul_smul, Units.mul_inv, one_smul]
  lie_h_e_nsmul := by rw [lie_smul, ht.lie_h_e_nsmul, smul_comm]
  lie_h_f_nsmul := by rw [lie_smul, ht.lie_h_f_nsmul, smul_neg, smul_comm]

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

/-- The scaled Weyl element negates the Cartan element of the triple. -/
theorem weylUnitSMul_conj_h (ht : IsSl2Triple H E F) (c : Rˣ) :
    ((weylUnitSMul (R := R) hE hF c : Aˣ) : A) * H *
        (((weylUnitSMul (R := R) hE hF c)⁻¹ : Aˣ) : A) = -H := by
  rw [coe_weylUnitSMul, coe_inv_weylUnitSMul]
  exact weylUnit_conj_h (isSl2Triple_smulUnits ht c) (hE.smul (c : R))
      (hF.smul ((c⁻¹ : Rˣ) : R))

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
  rw [exp_units_conj _ (hE.smul u), mul_smul_comm, smul_mul_assoc,
    weylUnitSMul_conj_e hE hF ht c, smul_neg, smul_smul]

/-! ## Weyl ratios -/

/-- **The Weyl ratio at `c`**, the element `n (c) · n (1)⁻¹` obtained from the scaled Weyl element
and the Weyl element.

For the images of a Chevalley root pair in a representation this is Chevalley's
`h_α(c) = n_α(c) n_α(1)⁻¹`. No multiplicativity statement about this parameterized family is made
here. -/
noncomputable def corootUnit (hE : IsNilpotent E) (hF : IsNilpotent F) (c : Rˣ) : Aˣ :=
  weylUnitSMul hE hF c * (weylUnit hE hF)⁻¹

/-- The Weyl ratio at `1` is trivial. -/
@[simp]
theorem corootUnit_one : corootUnit (R := R) hE hF 1 = 1 := by
  rw [corootUnit, weylUnitSMul_one, mul_inv_cancel]

/-- The scaled Weyl element factors as its Weyl ratio times the Weyl element: the normal
form `n_α(c) = h_α(c) n_α(1)`. -/
theorem weylUnitSMul_eq_corootUnit_mul (c : Rˣ) :
    weylUnitSMul (R := R) hE hF c = corootUnit hE hF c * weylUnit hE hF := by
  rw [corootUnit, inv_mul_cancel_right]

/-- Conjugation by the Weyl ratio is conjugation by the Weyl element followed by
conjugation by the scaled Weyl element. -/
private theorem corootUnit_conj_eq (c : Rˣ) (x : A) :
    ((corootUnit (R := R) hE hF c : Aˣ) : A) * x *
        (((corootUnit (R := R) hE hF c)⁻¹ : Aˣ) : A) =
      ((weylUnitSMul (R := R) hE hF c : Aˣ) : A) *
        ((((weylUnit hE hF)⁻¹ : Aˣ) : A) * x * ((weylUnit hE hF : Aˣ) : A)) *
        (((weylUnitSMul (R := R) hE hF c)⁻¹ : Aˣ) : A) := by
  rw [corootUnit, Units.val_mul, mul_inv_rev, inv_inv, Units.val_mul]
  simp only [mul_assoc]

variable (ht : IsSl2Triple H E F)

include ht

/-- **The Weyl ratio scales the raising element by `c²`.** -/
theorem corootUnit_conj_e (c : Rˣ) :
    ((corootUnit (R := R) hE hF c : Aˣ) : A) * E *
        (((corootUnit (R := R) hE hF c)⁻¹ : Aˣ) : A) = (((c : Rˣ) : R) ^ 2) • E := by
  rw [corootUnit_conj_eq, inv_weylUnit_conj_e hE hF ht, mul_neg, neg_mul,
    weylUnitSMul_conj_f hE hF ht c, neg_neg]

/-- **The Weyl ratio scales the lowering element by `c⁻²`.** -/
theorem corootUnit_conj_f (c : Rˣ) :
    ((corootUnit (R := R) hE hF c : Aˣ) : A) * F *
        (((corootUnit (R := R) hE hF c)⁻¹ : Aˣ) : A) = (((c⁻¹ : Rˣ) : R) ^ 2) • F := by
  rw [corootUnit_conj_eq, inv_weylUnit_conj_f hE hF ht, mul_neg, neg_mul,
    weylUnitSMul_conj_e hE hF ht c, neg_neg]

/-- **The Weyl ratio centralises the Cartan element of the triple.** -/
theorem corootUnit_conj_h (c : Rˣ) :
    ((corootUnit (R := R) hE hF c : Aˣ) : A) * H *
        (((corootUnit (R := R) hE hF c)⁻¹ : Aˣ) : A) = H := by
  rw [corootUnit_conj_eq, inv_weylUnit_conj_h hE hF ht, mul_neg, neg_mul,
    weylUnitSMul_conj_h hE hF ht c, neg_neg]

/-- **Conjugating a root subgroup element by the Weyl ratio.** For a Chevalley root pair this is
the relation `h_α(c) x_α(u) h_α(c)⁻¹ = x_α(c² u)`. -/
theorem corootUnit_conj_exp_smul (c : Rˣ) (u : R) :
    ((corootUnit (R := R) hE hF c : Aˣ) : A) * IsNilpotent.exp (u • E) *
        (((corootUnit (R := R) hE hF c)⁻¹ : Aˣ) : A) =
      IsNilpotent.exp ((u * ((c : Rˣ) : R) ^ 2) • E) := by
  rw [exp_units_conj _ (hE.smul u), mul_smul_comm, smul_mul_assoc,
    corootUnit_conj_e hE hF ht c, smul_smul]

/-- Conjugating the opposite root subgroup element by the Weyl ratio. -/
theorem corootUnit_conj_exp_smul_neg (c : Rˣ) (u : R) :
    ((corootUnit (R := R) hE hF c : Aˣ) : A) * IsNilpotent.exp (-(u • F)) *
        (((corootUnit (R := R) hE hF c)⁻¹ : Aˣ) : A) =
      IsNilpotent.exp (-((u * ((c⁻¹ : Rˣ) : R) ^ 2) • F)) := by
  rw [exp_units_conj _ (hF.smul u).neg, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc,
    corootUnit_conj_f hE hF ht c, smul_smul]

/-- **The Weyl ratio rescales the scaled Weyl elements**: conjugation by `h_α(c)` carries
`n_α(u)` to `n_α(c² u)`. -/
theorem corootUnit_conj_weylUnitSMul (c u : Rˣ) :
    corootUnit (R := R) hE hF c * weylUnitSMul hE hF u * (corootUnit (R := R) hE hF c)⁻¹ =
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
  rw [Units.val_mul, Units.val_mul, coe_weylUnitSMul, coe_weylUnitSMul, hval, hinv,
    units_conj_mul, units_conj_mul, corootUnit_conj_exp_smul hE hF ht,
    corootUnit_conj_exp_smul_neg hE hF ht]

/-- **The Weyl ratio preserves the eigenspaces of the Cartan element.** It centralises
`H`, so conjugation by it commutes with the adjoint action of `H`; for a root triple, this says
that the ratio normalises every root space. -/
theorem lie_corootUnit_conj {z : A} {m : ℚ} (hhz : ⁅H, z⁆ = m • z) (c : Rˣ) :
    ⁅H, ((corootUnit (R := R) hE hF c : Aˣ) : A) * z *
        (((corootUnit (R := R) hE hF c)⁻¹ : Aˣ) : A)⁆ =
      m • (((corootUnit (R := R) hE hF c : Aˣ) : A) * z *
        (((corootUnit (R := R) hE hF c)⁻¹ : Aˣ) : A)) := by
  set g : Aˣ := corootUnit (R := R) hE hF c
  have hH : (g : A) * H * ((g⁻¹ : Aˣ) : A) = H := corootUnit_conj_h hE hF ht c
  have hHg : H * (g : A) = (g : A) * H := by
    conv_lhs => rw [← hH]
    simp only [mul_assoc]
    rw [Units.inv_mul, mul_one]
  have hgH : ((g⁻¹ : Aˣ) : A) * H = H * ((g⁻¹ : Aˣ) : A) := by
    conv_lhs => rw [← hH]
    simp only [← mul_assoc]
    rw [Units.inv_mul, one_mul]
  have key : ⁅H, (g : A) * z * ((g⁻¹ : Aˣ) : A)⁆ = (g : A) * ⁅H, z⁆ * ((g⁻¹ : Aˣ) : A) := by
    simp only [LieRing.of_associative_ring_bracket, mul_sub, sub_mul]
    rw [← mul_assoc, ← mul_assoc, hHg]
    simp only [mul_assoc]
    rw [hgH]
  rw [key, hhz, mul_smul_comm, smul_mul_assoc]

/-! ## The coreflection formula -/

/-- **The coreflection formula does not see the scale.** An element `y` on which `E` and `F` have
the opposite eigenvalues `q` and `-q` is carried by conjugation with the scaled Weyl element to
`y - q • H`, whatever the scale `c`.

For a Cartan element `y` of the triple of a root `α` this is the coreflection
`y ↦ y - α(y) • α^∨`, and its independence of `c` is what makes the Weyl ratio
`TauCeti.corootUnit` centralise the Cartan subalgebra. -/
theorem weylUnitSMul_conj_of_lie_eq_smul {y : A} {q : ℚ}
    (hye : ⁅y, E⁆ = q • E) (hyf : ⁅y, F⁆ = -(q • F)) (c : Rˣ) :
    ((weylUnitSMul (R := R) hE hF c : Aˣ) : A) * y *
        (((weylUnitSMul (R := R) hE hF c)⁻¹ : Aˣ) : A) = y - q • H := by
  have hye' : ⁅y, ((c : R) • E)⁆ = q • ((c : R) • E) := by
    rw [lie_smul, hye, smul_comm]
  have hyf' : ⁅y, (((c⁻¹ : Rˣ) : R) • F)⁆ = -(q • (((c⁻¹ : Rˣ) : R) • F)) := by
    rw [lie_smul, hyf, smul_neg, smul_comm]
  exact weylUnit_conj_of_lie_eq_smul (isSl2Triple_smulUnits ht c) (hE.smul (c : R))
    (hF.smul ((c⁻¹ : Rˣ) : R)) hye' hyf'

/-- **The Weyl ratio centralises every element on which `E` and `F` have opposite eigenvalues.**
In the intended application these are the elements of the Cartan subalgebra. -/
theorem corootUnit_conj_of_lie_eq_smul {y : A} {q : ℚ}
    (hye : ⁅y, E⁆ = q • E) (hyf : ⁅y, F⁆ = -(q • F)) (c : Rˣ) :
    ((corootUnit (R := R) hE hF c : Aˣ) : A) * y *
        (((corootUnit (R := R) hE hF c)⁻¹ : Aˣ) : A) = y := by
  have hy' : (((weylUnit hE hF)⁻¹ : Aˣ) : A) * y * ((weylUnit hE hF : Aˣ) : A) = y - q • H :=
    inv_weylUnit_conj_of_lie_eq_smul ht hE hF hye hyf
  have hye' : ⁅y - q • H, E⁆ = (-q) • E := by
    rw [sub_lie, hye, smul_lie, ht.lie_h_e_nsmul]
    module
  have hyf' : ⁅y - q • H, F⁆ = -((-q) • F) := by
    rw [sub_lie, hyf, smul_lie, ht.lie_h_f_nsmul]
    module
  rw [corootUnit_conj_eq, hy', weylUnitSMul_conj_of_lie_eq_smul hE hF ht hye' hyf']
  module

end Scaled

end TauCeti
