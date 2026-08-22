/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NormCoeff

/-!
# Ideal convolution of ideal arithmetic functions

The Dirichlet convolution of two arithmetic functions on the nonzero ideals of the ring of integers
of a number field `K` sums over the factorizations `B * C = A` of a nonzero ideal `A`. This file
constructs that index set, defines the convolution, and proves that it makes
`TauCeti.IdealArithmeticFunction K` a commutative monoid with identity
`TauCeti.IdealArithmeticFunction.delta`, bilinear over the pointwise additive structure.

## Main definitions

* `TauCeti.IdealArithmeticFunction.delta` is the ideal arithmetic function that is `1` at the unit
  ideal and `0` elsewhere.
* `TauCeti.Ideal.divisorsAntidiagonal A` is the finite set of pairs `(B, C)` of nonzero ideals with
  `B * C = A`; it is the ideal analogue of Mathlib's `Nat.divisorsAntidiagonal`.
* `TauCeti.IdealArithmeticFunction.convolution f g` is the ideal Dirichlet convolution.
* `TauCeti.IdealArithmeticFunction.convolutionPow f n` is the `n`-fold convolution power of `f`.
* `TauCeti.normCoeff_convolution` transports ideal convolution to Mathlib's Dirichlet convolution.

## Main results

* `TauCeti.IdealArithmeticFunction.convolution_comm`,
  `TauCeti.IdealArithmeticFunction.convolution_assoc`,
  `TauCeti.IdealArithmeticFunction.delta_convolution` and
  `TauCeti.IdealArithmeticFunction.convolution_delta`: the convolution monoid laws.
* `TauCeti.IdealArithmeticFunction.convolution_add` and
  `TauCeti.IdealArithmeticFunction.add_convolution`: bilinearity over pointwise addition.
* `TauCeti.IdealArithmeticFunction.convolution_one_one_ne_mul`: ideal convolution is not the
  pointwise product.

## Implementation notes

`TauCeti.IdealArithmeticFunction K` is a `Pi` type, so it already carries Mathlib's *pointwise*
`CommRing` structure, in which `f * g` is `fun A => f A * g A` and `1` is the everywhere-one
function. Convolution is therefore deliberately **not** registered as a `Mul` instance and its
identity is the separate function `TauCeti.IdealArithmeticFunction.delta`; this is the roadmap's
convention that pointwise multiplication and ideal convolution stay distinct operations on one
carrier. The monoid laws are stated as ordinary theorems about
`TauCeti.IdealArithmeticFunction.convolution`, and
`TauCeti.IdealArithmeticFunction.convolution_one_one_ne_mul` records that the two products really do
differ. Consequently iterated convolution is the explicit
`TauCeti.IdealArithmeticFunction.convolutionPow` rather than a `Monoid.npow`.

Excluding the zero ideal from the carrier is what makes the index set finite: `⊥ * J = ⊥` for every
`J`, so the zero ideal has infinitely many factorizations while a nonzero ideal has only finitely
many, by Mathlib's `UniqueFactorizationMonoid.fintypeSubtypeDvd` for the unique factorization
monoid `Ideal (𝓞 K)`.

## Roadmap role

This is Layer **2.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, built on the Layer
**0.1** carrier of `TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean`. Its consumers are
the ideal Möbius function and von Mangoldt transform of Layer 2 and the local factors of Layer 3.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField

namespace IdealArithmeticFunction

variable {K : Type*} [Field K]

/-! ### The convolution identity -/

open Classical in
/-- The **delta function** on nonzero ideals: `1` at the unit ideal and `0` elsewhere. It is the
identity for ideal convolution. It is *not* the pointwise unit `(1 : IdealArithmeticFunction K)`,
which is the everywhere-one function. -/
noncomputable def delta : IdealArithmeticFunction K := fun A => if A = 1 then 1 else 0

/-- The delta function takes the value `1` at the unit ideal. -/
@[simp]
theorem delta_one : delta (1 : (Ideal (𝓞 K))⁰) = 1 := by
  simp [delta]

/-- The delta function vanishes away from the unit ideal. -/
@[simp]
theorem delta_of_ne_one {A : (Ideal (𝓞 K))⁰} (hA : A ≠ 1) : delta A = 0 := by
  simp [delta, hA]

end IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

namespace Ideal

/-! ### The antidiagonal of a nonzero ideal -/

/-- A nonzero ideal admits only finitely many factorizations into two nonzero ideals. This is where
the exclusion of `⊥` from the carrier bites: every ideal `J` satisfies `⊥ * J = ⊥`. -/
theorem finite_setOf_mul_eq (A : (Ideal (𝓞 K))⁰) :
    {p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ | p.1 * p.2 = A}.Finite := by
  let hfin : Fintype {I : Ideal (𝓞 K) // I ∣ (A : Ideal (𝓞 K))} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd _ (nonZeroDivisors.coe_ne_zero A)
  have hdvd : {I : Ideal (𝓞 K) | I ∣ (A : Ideal (𝓞 K))}.Finite :=
    Set.Finite.ofFinset
      (Finset.univ.image (Subtype.val : {I : Ideal (𝓞 K) // I ∣ (A : Ideal (𝓞 K))} → _))
      (by simp)
  -- The first factor of a factorization divides `A` and determines the second factor.
  refine Set.Finite.of_finite_image (f := fun p => ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))
    (hdvd.subset ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨(p.2 : Ideal (𝓞 K)), by simpa using congrArg Subtype.val hp.symm⟩
  · rintro p hp q hq hpq
    have h1 : p.1 = q.1 := Subtype.ext hpq
    have h2 : p.2 = q.2 := by
      refine mul_left_cancel (a := p.1) ?_
      rw [hp, ← hq, h1]
    exact Prod.ext h1 h2

/-- The **antidiagonal** of a nonzero ideal `A`: the finite set of pairs `(B, C)` of nonzero ideals
with `B * C = A`. It is the index set of the ideal Dirichlet convolution, and the ideal analogue of
Mathlib's `Nat.divisorsAntidiagonal`. -/
noncomputable def divisorsAntidiagonal (A : (Ideal (𝓞 K))⁰) :
    Finset ((Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰) :=
  (finite_setOf_mul_eq A).toFinset

/-- A pair lies in the antidiagonal of `A` exactly when its two entries multiply to `A`. -/
@[simp]
theorem mem_divisorsAntidiagonal {A : (Ideal (𝓞 K))⁰} {p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰} :
    p ∈ divisorsAntidiagonal A ↔ p.1 * p.2 = A := by
  simp [divisorsAntidiagonal]

/-- The antidiagonal is stable under swapping the two factors. -/
theorem swap_mem_divisorsAntidiagonal {A : (Ideal (𝓞 K))⁰}
    {p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰} (hp : p ∈ divisorsAntidiagonal A) :
    p.swap ∈ divisorsAntidiagonal A := by
  rw [mem_divisorsAntidiagonal] at hp ⊢
  rwa [Prod.fst_swap, Prod.snd_swap, mul_comm]

/-- The first entry of an antidiagonal pair divides `A`. -/
theorem fst_dvd_of_mem_divisorsAntidiagonal {A : (Ideal (𝓞 K))⁰}
    {p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰} (hp : p ∈ divisorsAntidiagonal A) :
    (p.1 : Ideal (𝓞 K)) ∣ (A : Ideal (𝓞 K)) :=
  ⟨(p.2 : Ideal (𝓞 K)), by
    simpa using congrArg Subtype.val (mem_divisorsAntidiagonal.mp hp).symm⟩

/-- The second entry of an antidiagonal pair divides `A`. -/
theorem snd_dvd_of_mem_divisorsAntidiagonal {A : (Ideal (𝓞 K))⁰}
    {p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰} (hp : p ∈ divisorsAntidiagonal A) :
    (p.2 : Ideal (𝓞 K)) ∣ (A : Ideal (𝓞 K)) := by
  have h := fst_dvd_of_mem_divisorsAntidiagonal (swap_mem_divisorsAntidiagonal hp)
  rwa [Prod.fst_swap] at h

/-- The unit ideal factors only as `1 * 1`. -/
@[simp]
theorem divisorsAntidiagonal_one :
    divisorsAntidiagonal (1 : (Ideal (𝓞 K))⁰) = {(1, 1)} := by
  ext p
  simp only [mem_divisorsAntidiagonal, Finset.mem_singleton, Prod.ext_iff]
  constructor
  · intro h
    have h' : (p.1 : Ideal (𝓞 K)) * (p.2 : Ideal (𝓞 K)) = 1 := by
      simpa using congrArg Subtype.val h
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · simpa [Ideal.one_eq_top] using
        Ideal.isUnit_iff.mp (isUnit_of_dvd_one ⟨(p.2 : Ideal (𝓞 K)), h'.symm⟩)
    · simpa [Ideal.one_eq_top] using Ideal.isUnit_iff.mp
        (isUnit_of_dvd_one ⟨(p.1 : Ideal (𝓞 K)), by rw [← h', mul_comm]⟩)
  · rintro ⟨h1, h2⟩
    rw [h1, h2, mul_one]

/-- Every nonzero ideal other than the unit ideal has at least the two factorizations `1 * A` and
`A * 1`. -/
theorem one_lt_card_divisorsAntidiagonal {A : (Ideal (𝓞 K))⁰} (hA : A ≠ 1) :
    1 < (divisorsAntidiagonal A).card := by
  refine Finset.one_lt_card.mpr ⟨(1, A), by simp, (A, 1), by simp, ?_⟩
  simp only [ne_eq, Prod.mk.injEq, not_and]
  exact fun h => absurd h.symm hA

end Ideal

namespace IdealArithmeticFunction

/-! ### Ideal convolution -/

/-- The **ideal Dirichlet convolution** of two ideal arithmetic functions: the value at a nonzero
ideal `A` is the sum of `f B * g C` over the factorizations `B * C = A` into nonzero ideals. -/
noncomputable def convolution (f g : IdealArithmeticFunction K) : IdealArithmeticFunction K :=
  fun A => ∑ p ∈ Ideal.divisorsAntidiagonal A, f p.1 * g p.2

/-- The defining formula for ideal convolution. -/
@[simp]
theorem convolution_apply (f g : IdealArithmeticFunction K) (A : (Ideal (𝓞 K))⁰) :
    convolution f g A = ∑ p ∈ Ideal.divisorsAntidiagonal A, f p.1 * g p.2 :=
  (rfl)

/-- At the unit ideal, convolution is the product of the two values there. -/
theorem convolution_apply_one (f g : IdealArithmeticFunction K) :
    convolution f g 1 = f 1 * g 1 := by
  simp

/-! ### The monoid laws -/

/-- Ideal convolution is commutative. -/
theorem convolution_comm (f g : IdealArithmeticFunction K) :
    convolution f g = convolution g f := by
  funext A
  simp only [convolution_apply]
  refine Finset.sum_equiv (Equiv.prodComm _ _) (fun p => ?_) (fun p _ => ?_)
  · simp [mul_comm]
  · simp [mul_comm]

/-- Ideal convolution is associative. -/
theorem convolution_assoc (f g h : IdealArithmeticFunction K) :
    convolution (convolution f g) h = convolution f (convolution g h) := by
  funext A
  simp only [convolution_apply, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
  -- Both iterated sums range over the triple factorizations of `A`; the reindexing is the one
  -- Mathlib uses for `ArithmeticFunction.mul_smul'`, transported to ideal factorizations.
  refine Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ => ⟨(k, l * j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ => ⟨(i * k, l), (i, k)⟩) ?_ ?_ ?_ ?_ ?_ <;>
    aesop (add simp mul_assoc)

/-- The delta function is a left identity for ideal convolution. -/
@[simp]
theorem delta_convolution (f : IdealArithmeticFunction K) : convolution delta f = f := by
  funext A
  have h1 : ((1 : (Ideal (𝓞 K))⁰), A) ∈ Ideal.divisorsAntidiagonal A := by simp
  have key : ∀ p ∈ Ideal.divisorsAntidiagonal A, p ≠ ((1 : (Ideal (𝓞 K))⁰), A) →
      delta p.1 * f p.2 = 0 := by
    rintro ⟨B, C⟩ hB hne
    have hBC : B * C = A := by simpa using hB
    have hB1 : B ≠ 1 := by
      rintro rfl
      rw [one_mul] at hBC
      exact hne (by rw [hBC])
    simp [hB1]
  rw [convolution_apply, Finset.sum_eq_single_of_mem _ h1 key]
  simp

/-- The delta function is a right identity for ideal convolution. -/
@[simp]
theorem convolution_delta (f : IdealArithmeticFunction K) : convolution f delta = f := by
  rw [convolution_comm, delta_convolution]

/-! ### Bilinearity over the pointwise additive structure -/

/-- Convolving with the zero function gives zero. -/
@[simp]
theorem convolution_zero (f : IdealArithmeticFunction K) : convolution f 0 = 0 := by
  funext A
  simp

/-- Convolving the zero function with anything gives zero. -/
@[simp]
theorem zero_convolution (f : IdealArithmeticFunction K) : convolution 0 f = 0 := by
  rw [convolution_comm, convolution_zero]

/-- Ideal convolution distributes over pointwise addition on the right. -/
theorem convolution_add (f g h : IdealArithmeticFunction K) :
    convolution f (g + h) = convolution f g + convolution f h := by
  funext A
  simp [mul_add, Finset.sum_add_distrib]

/-- Ideal convolution distributes over pointwise addition on the left. -/
theorem add_convolution (f g h : IdealArithmeticFunction K) :
    convolution (f + g) h = convolution f h + convolution g h := by
  rw [convolution_comm, convolution_add, convolution_comm h f, convolution_comm h g]

/-- Ideal convolution is homogeneous in its second argument. -/
theorem convolution_smul (c : ℂ) (f g : IdealArithmeticFunction K) :
    convolution f (c • g) = c • convolution f g := by
  funext A
  simp only [convolution_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- Ideal convolution is homogeneous in its first argument. -/
theorem smul_convolution (c : ℂ) (f g : IdealArithmeticFunction K) :
    convolution (c • f) g = c • convolution f g := by
  rw [convolution_comm, convolution_smul, convolution_comm]

/-- Ideal convolution commutes with pointwise negation on the right. -/
theorem convolution_neg (f g : IdealArithmeticFunction K) :
    convolution f (-g) = -convolution f g := by
  funext A
  simp

/-- Ideal convolution commutes with pointwise negation on the left. -/
theorem neg_convolution (f g : IdealArithmeticFunction K) :
    convolution (-f) g = -convolution f g := by
  rw [convolution_comm, convolution_neg, convolution_comm]

/-- Ideal convolution distributes over pointwise subtraction on the right. -/
theorem convolution_sub (f g h : IdealArithmeticFunction K) :
    convolution f (g - h) = convolution f g - convolution f h := by
  rw [sub_eq_add_neg, convolution_add, convolution_neg, sub_eq_add_neg]

/-- Ideal convolution distributes over pointwise subtraction on the left. -/
theorem sub_convolution (f g h : IdealArithmeticFunction K) :
    convolution (f - g) h = convolution f h - convolution g h := by
  rw [sub_eq_add_neg, add_convolution, neg_convolution, sub_eq_add_neg]

/-! ### Iterated convolution -/

/-- The `n`-fold ideal convolution power of `f`, with `convolutionPow f 0 = delta`. -/
noncomputable def convolutionPow (f : IdealArithmeticFunction K) :
    ℕ → IdealArithmeticFunction K
  | 0 => delta
  | n + 1 => convolution (convolutionPow f n) f

/-- The empty convolution power is the convolution identity. -/
@[simp]
theorem convolutionPow_zero (f : IdealArithmeticFunction K) : convolutionPow f 0 = delta :=
  (rfl)

/-- The recursion defining the convolution powers. -/
@[simp]
theorem convolutionPow_succ (f : IdealArithmeticFunction K) (n : ℕ) :
    convolutionPow f (n + 1) = convolution (convolutionPow f n) f :=
  (rfl)

/-- The first convolution power is the function itself. -/
theorem convolutionPow_one (f : IdealArithmeticFunction K) : convolutionPow f 1 = f := by
  rw [convolutionPow_succ, convolutionPow_zero, delta_convolution]

/-- The recursion defining the convolution powers, with the new factor on the left. -/
theorem convolutionPow_succ' (f : IdealArithmeticFunction K) (n : ℕ) :
    convolutionPow f (n + 1) = convolution f (convolutionPow f n) := by
  rw [convolutionPow_succ, convolution_comm]

/-- Convolution powers add exponents. -/
theorem convolutionPow_add (f : IdealArithmeticFunction K) (m n : ℕ) :
    convolutionPow f (m + n) = convolution (convolutionPow f m) (convolutionPow f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Nat.add_assoc, convolutionPow_succ, ih, convolutionPow_succ, convolution_assoc]

/-! ### Convolution is not the pointwise product -/

/-- Convolving the everywhere-one function with itself counts the factorizations of a nonzero
ideal: this is the ideal divisor-counting function. -/
theorem convolution_one_one_apply (A : (Ideal (𝓞 K))⁰) :
    convolution (1 : IdealArithmeticFunction K) 1 A = (Ideal.divisorsAntidiagonal A).card := by
  simp

/-- The **rejection test** against confusing the two products on `IdealArithmeticFunction K`: ideal
convolution is not the pointwise multiplication carried by the `Pi` ring structure. The
everywhere-one function is a pointwise unit, whereas convolving it with itself counts
factorizations, and the ring of integers of a number field is not a field, so some nonzero ideal has
more than one factorization. -/
theorem convolution_one_one_ne_mul :
    convolution (1 : IdealArithmeticFunction K) 1 ≠ (1 : IdealArithmeticFunction K) * 1 := by
  intro hcontra
  obtain ⟨P, hPbot, hPmax⟩ :=
    Ring.exists_maximal_of_not_isField (NumberField.RingOfIntegers.not_isField K)
  have hPmem : P ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hPbot
  have hAne : (⟨P, hPmem⟩ : (Ideal (𝓞 K))⁰) ≠ 1 := by
    intro h
    exact hPmax.ne_top (by simpa [Ideal.one_eq_top] using congrArg Subtype.val h)
  have hcard : ((Ideal.divisorsAntidiagonal (⟨P, hPmem⟩ : (Ideal (𝓞 K))⁰)).card : ℂ) = 1 := by
    rw [← convolution_one_one_apply, hcontra]
    simp
  exact absurd (by exact_mod_cast hcard) (Ideal.one_lt_card_divisorsAntidiagonal hAne).ne'

end IdealArithmeticFunction

/-! ## Compatibility with Dirichlet convolution -/

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def normFiber (n : ℕ) : Finset ((Ideal (𝓞 K))⁰) :=
  (finite_normFiber K n).toFinset

@[simp]
private theorem mem_normFiber {I : (Ideal (𝓞 K))⁰} {n : ℕ} :
    I ∈ normFiber K n ↔ Ideal.absNorm (I : Ideal (𝓞 K)) = n := by
  simp [normFiber]

private theorem normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n = ∑ I ∈ normFiber K n, f I := by
  rw [normCoeff_apply, finsum_mem_eq_finite_toFinset_sum _ (finite_normFiber K n)]
  simp only [normFiber]

/-- Regrouping sends the identity for ideal convolution to the identity for Mathlib's Dirichlet
convolution. -/
@[simp]
theorem normCoeff_delta : normCoeff K IdealArithmeticFunction.delta = 1 := by
  classical
  ext n
  by_cases hn : n = 1
  · subst n
    rw [normCoeff_apply_one, IdealArithmeticFunction.delta_one]
    simp
  · simp only [normCoeff_eq_sum_normFiber, ArithmeticFunction.one_apply, hn]
    apply Finset.sum_eq_zero
    intro I hI
    apply IdealArithmeticFunction.delta_of_ne_one
    intro hI_one
    subst I
    have hnorm := (mem_normFiber K).mp hI
    exact hn (by simpa using hnorm.symm)

/-- Regrouping by absolute norm transports ideal convolution to Mathlib's Dirichlet convolution
of arithmetic functions. -/
@[simp]
theorem normCoeff_convolution (f g : IdealArithmeticFunction K) :
    normCoeff K (f.convolution g) = normCoeff K f * normCoeff K g := by
  ext n
  rcases n with _ | n
  · simp
  simp only [normCoeff_eq_sum_normFiber, IdealArithmeticFunction.convolution_apply,
    ArithmeticFunction.mul_apply, Finset.sum_mul_sum, Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun ⟨A, p⟩ ↦
      ⟨(Ideal.absNorm (p.1 : Ideal (𝓞 K)), Ideal.absNorm (p.2 : Ideal (𝓞 K))),
        ⟨p.1, p.2⟩⟩)
    (fun ⟨_d, ⟨B, C⟩⟩ ↦ ⟨B * C, (B, C)⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Finset.mem_sigma, mem_normFiber, Ideal.mem_divisorsAntidiagonal,
      Nat.mem_divisorsAntidiagonal] <;>
    aesop

/-- Regrouping transports iterated ideal convolution to powers under Mathlib's Dirichlet
convolution. -/
@[simp]
theorem normCoeff_convolutionPow (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K (f.convolutionPow n) = normCoeff K f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [IdealArithmeticFunction.convolutionPow_succ, normCoeff_convolution, ih,
      pow_succ]

end TauCeti
