/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# Invariant sesquilinear forms on a representation

A sesquilinear form `H : V →ₗ⋆[R] V →ₗ[R] R` on the space of a representation `ρ` is **invariant**
when every `ρ g` preserves it, `H (ρ g x) (ρ g y) = H x y`.  This is the Hermitian companion of the
bilinear `TauCeti.Representation.IsInvariantForm`, and the two together are what produce a real
structure on a complex representation with Frobenius-Schur indicator `1`.

The vocabulary and the construction that produces invariant forms use only the star-semiring
algebra of the scalars, and are stated for a module over an arbitrary commutative star semiring:
the invariant forms are a submodule of all sesquilinear forms, and summing an arbitrary form over
the group makes it invariant, exactly as
`TauCeti/RepresentationTheory/InvariantForm/SumOfConjugates.lean` does for a bilinear form.

Positivity is what asks for more, and the second half of the file is over `ℂ`.  Here the sum does
more work than it does over `ℝ`: there the sum of the coordinate dot products is merely *nonzero*,
while over `ℂ` the sum of the coordinate Hermitian forms is still **positive definite**, because
each summand is, and a sum of nonnegative complex numbers vanishes only when every summand does.
So the construction gives an invariant inner product outright, not just a nonzero invariant form.

Positive semidefiniteness is Mathlib's `LinearMap.IsPosSemidef` for the complex order (activate it
with `open scoped ComplexOrder`), which packages Hermitian symmetry `conj (H x y) = H y x`
(`LinearMap.IsSymm` for the conjugation `starRingEnd ℂ`) together with `0 ≤ H x x`.  Definiteness
is carried separately as `H x x ≠ 0` off the origin, which is the form the Schur-lemma argument
downstream consumes.

The positivity half is stated over `ℂ` rather than over an `RCLike` field.  The order that
`LinearMap.IsPosSemidef` needs is the one `Complex.partialOrder` supplies in the `ComplexOrder`
scope, and `RCLike` supplies a second, lower-priority partial order in the same scope; stating the
positivity results over `RCLike` would fix the wrong one of the two for the `ℂ`-only consumer,
`TauCeti/RepresentationTheory/InvariantForm/RealStructure.lean`.

## Main definitions

* `Representation.IsInvariantSesqForm`: a sesquilinear form invariant for a representation, with
  its unfolding `Representation.isInvariantSesqForm_iff` and the accessor
  `Representation.IsInvariantSesqForm.apply`.
* `Representation.invariantSesqForms`: the invariant sesquilinear forms, as a submodule of all
  sesquilinear forms on `V`.
* `Representation.sumOfConjugatesSesqForm`: the sum of a sesquilinear form over the conjugates of a
  representation of a finite monoid.

## Main results

* `Representation.isInvariantSesqForm_sumOfConjugatesSesqForm`: that sum is invariant.
* `Representation.isPosSemidef_sumOfConjugatesSesqForm`: that sum is positive semidefinite if the
  form is.
* `Representation.exists_isInvariantSesqForm_isPosSemidef_apply_self_ne_zero`: **a
  finite-dimensional complex representation of a finite group carries a positive definite invariant
  Hermitian form.**  This is the unitarian trick for a finite group, with the undivided sum in
  place of the average.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 7: the "compatible Hermitian form" that the realizability target
  `frobeniusSchurIndicatorRep_eq_one_realizable` is built from.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
-/

public section

open scoped ComplexOrder

open TauCeti

namespace Representation

open TauCeti.Representation

/-! ### Invariant sesquilinear forms -/

section Monoid

variable {R G V : Type*} [CommSemiring R] [StarRing R] [Monoid G] [AddCommMonoid V] [Module R V]

/-- A sesquilinear form `H` is **invariant** for a representation `ρ` when every `ρ g` preserves
it: `H (ρ g x) (ρ g y) = H x y`.  This is the Hermitian companion of
`TauCeti.Representation.IsInvariantForm`, stated pointwise because a sesquilinear form is out of
reach of `LinearMap.compl₁₂`, which asks for a form linear in its first argument. -/
def IsInvariantSesqForm (ρ : Representation R G V) (H : V →ₗ⋆[R] V →ₗ[R] R) : Prop :=
  ∀ (g : G) (x y : V), H (ρ g x) (ρ g y) = H x y

variable {ρ : Representation R G V} {H K : V →ₗ⋆[R] V →ₗ[R] R}

/-- A sesquilinear form is invariant for `ρ` exactly when it satisfies the pointwise equation
`H (ρ g x) (ρ g y) = H x y`. -/
theorem isInvariantSesqForm_iff :
    IsInvariantSesqForm ρ H ↔ ∀ (g : G) (x y : V), H (ρ g x) (ρ g y) = H x y := (Iff.rfl)

/-- An invariant sesquilinear form takes the same value on `ρ g x` and `ρ g y` as it does on `x`
and `y`. -/
@[grind =]
theorem IsInvariantSesqForm.apply (hH : IsInvariantSesqForm ρ H) (g : G) (x y : V) :
    H (ρ g x) (ρ g y) = H x y :=
  isInvariantSesqForm_iff.mp hH g x y

/-- The invariant sesquilinear forms of `ρ`, as a submodule of all sesquilinear forms on `V`. -/
def invariantSesqForms (ρ : Representation R G V) : Submodule R (V →ₗ⋆[R] V →ₗ[R] R) where
  carrier := {H | IsInvariantSesqForm ρ H}
  add_mem' hH hK g x y := by
    simp only [LinearMap.add_apply, IsInvariantSesqForm.apply hH g x y,
      IsInvariantSesqForm.apply hK g x y]
  zero_mem' _ _ _ := rfl
  smul_mem' c _ hH g x y := by
    simp only [LinearMap.smul_apply, IsInvariantSesqForm.apply hH g x y]

/-- Membership in `Representation.invariantSesqForms` is invariance. -/
@[simp]
theorem mem_invariantSesqForms : H ∈ invariantSesqForms ρ ↔ IsInvariantSesqForm ρ H := Iff.rfl

/-- The zero form is invariant. -/
@[simp]
theorem isInvariantSesqForm_zero : IsInvariantSesqForm ρ (0 : V →ₗ⋆[R] V →ₗ[R] R) :=
  fun _ _ _ => rfl

/-- A sum of invariant sesquilinear forms is invariant. -/
theorem IsInvariantSesqForm.add (hH : IsInvariantSesqForm ρ H) (hK : IsInvariantSesqForm ρ K) :
    IsInvariantSesqForm ρ (H + K) :=
  (invariantSesqForms ρ).add_mem hH hK

/-- A scalar multiple of an invariant sesquilinear form is invariant. -/
theorem IsInvariantSesqForm.smul (c : R) (hH : IsInvariantSesqForm ρ H) :
    IsInvariantSesqForm ρ (c • H) :=
  (invariantSesqForms ρ).smul_mem c hH

variable [Fintype G]

/-- The **sum of a sesquilinear form over the conjugates** of a representation of a finite monoid,
`∑ g, H (ρ g ·) (ρ g ·)`.  No division by the order of the monoid is performed, exactly as in
`TauCeti.Representation.sumOfConjugatesForm` for a bilinear form; when `G` is a group the plain sum
is already invariant. -/
def sumOfConjugatesSesqForm (ρ : Representation R G V) (H : V →ₗ⋆[R] V →ₗ[R] R) :
    V →ₗ⋆[R] V →ₗ[R] R :=
  ∑ g : G, (H.comp (ρ g)).compl₂ (ρ g)

@[simp]
theorem sumOfConjugatesSesqForm_apply (ρ : Representation R G V) (H : V →ₗ⋆[R] V →ₗ[R] R)
    (x y : V) : sumOfConjugatesSesqForm ρ H x y = ∑ g : G, H (ρ g x) (ρ g y) := by
  simp [sumOfConjugatesSesqForm]

/-- The sum over the conjugates of a Hermitian form is Hermitian. -/
theorem isSymm_sumOfConjugatesSesqForm (hH : H.IsSymm) : (sumOfConjugatesSesqForm ρ H).IsSymm where
  eq x y := by
    simpa only [sumOfConjugatesSesqForm_apply, map_sum] using
      Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => hH.eq (ρ g x) (ρ g y)

end Monoid

/-! ### Invariance of the conjugate sum -/

section Group

variable {R G V : Type*} [CommSemiring R] [StarRing R] [Group G] [Fintype G] [AddCommMonoid V]
  [Module R V]

/-- The sum of a sesquilinear form over the conjugates of a representation of a finite group is
invariant: translating the summation index by `h` moves the sum for `ρ h x` and `ρ h y` back to the
sum for `x` and `y`. -/
@[simp]
theorem isInvariantSesqForm_sumOfConjugatesSesqForm (ρ : Representation R G V)
    (H : V →ₗ⋆[R] V →ₗ[R] R) : IsInvariantSesqForm ρ (sumOfConjugatesSesqForm ρ H) := by
  intro h x y
  simp only [sumOfConjugatesSesqForm_apply]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
  simp [map_mul, Module.End.mul_apply]

end Group

/-! ### Positivity of the conjugate sum -/

section Positivity

variable {G V : Type*} [Monoid G] [Fintype G] [AddCommMonoid V] [Module ℂ V]
  {ρ : Representation ℂ G V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}

/-- The sum over the conjugates of a nonnegative form is nonnegative. -/
theorem isNonneg_sumOfConjugatesSesqForm (hH : H.IsNonneg) :
    (sumOfConjugatesSesqForm ρ H).IsNonneg where
  nonneg x := by
    rw [sumOfConjugatesSesqForm_apply]
    exact Finset.sum_nonneg fun g _ => hH.nonneg (ρ g x)

/-- The sum over the conjugates of a positive semidefinite form is positive semidefinite. -/
theorem isPosSemidef_sumOfConjugatesSesqForm (hH : H.IsPosSemidef) :
    (sumOfConjugatesSesqForm ρ H).IsPosSemidef where
  isSymm := isSymm_sumOfConjugatesSesqForm hH.isSymm
  isNonneg := isNonneg_sumOfConjugatesSesqForm hH.isNonneg

/-- A vector with vanishing self-pairing for the conjugate sum of a nonnegative form already has
vanishing self-pairing for the form itself: the summand at `g = 1` is one of the nonnegative
summands of a vanishing sum. -/
theorem apply_self_eq_zero_of_sumOfConjugatesSesqForm_apply_self_eq_zero (hH : H.IsNonneg) {x : V}
    (hx : sumOfConjugatesSesqForm ρ H x x = 0) : H x x = 0 := by
  rw [sumOfConjugatesSesqForm_apply] at hx
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun g (_ : g ∈ Finset.univ) => hH.nonneg (ρ g x))).mp hx 1 (Finset.mem_univ 1)
  simpa using h1

end Positivity

/-! ### The coordinate Hermitian form and the unitarian trick -/

section Existence

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]

/-- **A finite-dimensional complex representation of a finite group carries a positive definite
invariant Hermitian form.**  Take the coordinate Hermitian form of a basis -- the sesquilinear form
of the identity matrix, `∑ i, conj (b.repr x i) * b.repr y i` -- and sum it over the conjugates.
The sum stays Hermitian and nonnegative, and it stays definite because a vanishing sum of
nonnegative complex numbers has vanishing summands, in particular the one at `g = 1`.

This is the unitarian trick for a finite group, with the undivided sum in place of the average, so
no invertibility of the group order is needed.  Over `ℝ` the same recipe gives only a *nonzero*
invariant form (`TauCeti.Representation.exists_isInvariantForm_isSymm_ne_zero`); it is the
definiteness of the Hermitian form that makes this statement stronger. -/
theorem exists_isInvariantSesqForm_isPosSemidef_apply_self_ne_zero (ρ : Representation ℂ G V)
    [FiniteDimensional ℂ V] :
    ∃ H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ,
      IsInvariantSesqForm ρ H ∧ H.IsPosSemidef ∧ ∀ x : V, x ≠ 0 → H x x ≠ 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set b := Module.finBasis ℂ V with hb
  set H₀ : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ) b b 1 with hH₀
  have hH₀apply : ∀ x y : V, H₀ x y = ∑ i, (starRingEnd ℂ) (b.repr x i) * b.repr y i := by
    intro x y
    simp [hH₀, Matrix.toLinearMapₛₗ₂_apply, Matrix.one_apply, smul_eq_mul, mul_comm,
      Finset.sum_ite_eq]
  have hH₀symm : H₀.IsSymm := by
    refine ⟨fun x y => ?_⟩
    simp only [hH₀apply, map_sum, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hH₀nonneg : H₀.IsNonneg := by
    refine ⟨fun x => ?_⟩
    rw [hH₀apply]
    exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _
  have hH₀def : ∀ x : V, H₀ x x = 0 → x = 0 := by
    intro x hx
    rw [hH₀apply] at hx
    have hzero : ∀ i, b.repr x i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => star_mul_self_nonneg (b.repr x j))).mp hx i
        (Finset.mem_univ i)
      simpa [mul_eq_zero, or_self] using this
    exact b.repr.map_eq_zero_iff.mp (Finsupp.ext hzero)
  refine ⟨sumOfConjugatesSesqForm ρ H₀, isInvariantSesqForm_sumOfConjugatesSesqForm ρ H₀,
    isPosSemidef_sumOfConjugatesSesqForm ⟨hH₀symm, hH₀nonneg⟩, fun x hx hzero => hx ?_⟩
  exact hH₀def x
    (apply_self_eq_zero_of_sumOfConjugatesSesqForm_apply_self_eq_zero hH₀nonneg hzero)

end Existence

end Representation
