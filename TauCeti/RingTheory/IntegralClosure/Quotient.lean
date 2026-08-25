/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Integrality over an algebra, tested on quotients

A failure of `x : R` to be integral over `A` is already a failure modulo a **prime** ideal of `R`.
That is what this file proves, together with the elementary description of integrality in a
quotient that the argument runs on: `x` becomes integral over `A` in `R ⧸ J` exactly when some
monic polynomial over `A` sends `x` into `J`.

The point of reaching a *prime* is that `R ⧸ J` is then a **domain**. So a theorem about integral
elements proved only for domains extends to an arbitrary commutative ring, as long as its
hypothesis survives pulling back along `Ideal.Quotient.mk J`. The valuative criterion
`TauCeti.isIntegral_of_forall_valuation_le_one` — the hard direction of Wedhorn's Proposition
7.18 — is such a theorem, and is what this file was written for.

## Main results

* `TauCeti.isIntegral_quotient_iff` : integrality of `x` over `A` after passing to `R ⧸ J` is the
  statement that some monic polynomial over `A` sends `x` into `J`.
* `TauCeti.isIntegral_of_forall_isPrime` : if `x` becomes integral over `A` in every prime
  quotient of `R`, then it is integral over `A`.
* `TauCeti.isIntegral_of_forall_isPrime_map` : the same for a subring `B ⊆ R`, phrased with the
  image subring `B.map (Ideal.Quotient.mk J)` that a criterion quantifying over subrings of
  `R ⧸ J` needs.

The first of these needs only a ring and a two-sided ideal; commutativity enters with the prime,
so the other two ask for it.

Mathlib's integrality-in-a-quotient lemmas, `RingHom.IsIntegral.quotient` and
`isIntegral_quotientMap_iff`, say that a *ring hom* is integral, with source and target both
quotiented. The criterion here is about a single element, keeps `A` unquotiented, and hands back
the monic witness, which is what the argument below consumes.

## Method

The statement is the positive one — integral in every prime quotient implies integral — and the
argument runs on its contrapositive, which is where the prime comes from.

The values `f(x)` of monic polynomials `f` over `A` form a **submonoid** of `R`: monic
polynomials are closed under multiplication and evaluation is multiplicative, and `f = 1` gives
the unit. Non-integrality of `x` says exactly that `0` is not one of those values — that the zero
ideal is disjoint from the submonoid. `Ideal.exists_le_prime_disjoint` then supplies a **prime**
ideal still disjoint from it, and `isIntegral_quotient_iff` reads that disjointness back as
non-integrality in the quotient.

Packaging the monic values as a submonoid is the whole trick: the multiplicative closure Mathlib's
Zorn argument needs is precisely "a product of monic polynomials is monic", so no bespoke
maximality argument is required here, and no finiteness or noetherian hypothesis on `R` appears.

The subring form is a corollary rather than a separate argument. Only one direction of the
comparison is needed — that integrality over the image subring implies integrality over `B` —
and it holds because `B` surjects onto that image, so a monic polynomial over the image lifts to
a monic polynomial over `B`.
-/

public section

namespace TauCeti

open Polynomial

section Quotient

variable {A R : Type*} [CommRing A] [Ring R] [Algebra A R]

/-! ### Integrality after passing to a quotient -/

/-- Evaluating a polynomial over `A` at `x` and then reducing mod `J` is evaluating it at the
reduction of `x`: the structure map to `R ⧸ J` factors through `R`. -/
private theorem eval₂_quotient (x : R) (J : Ideal R) [J.IsTwoSided] (f : A[X]) :
    eval₂ (algebraMap A (R ⧸ J)) (Ideal.Quotient.mk J x) f
      = Ideal.Quotient.mk J (eval₂ (algebraMap A R) x f) := by
  rw [hom_eval₂, Ideal.Quotient.mk_comp_algebraMap]

/-- **Integrality in a quotient is a monic polynomial landing in the ideal.** The reduction of `x`
is integral over `A` in `R ⧸ J` exactly when some monic polynomial over `A` sends `x` into `J`. -/
theorem isIntegral_quotient_iff (x : R) (J : Ideal R) [J.IsTwoSided] :
    IsIntegral A (Ideal.Quotient.mk J x) ↔
      ∃ f : A[X], f.Monic ∧ eval₂ (algebraMap A R) x f ∈ J := by
  refine exists_congr fun f ↦ and_congr_right fun _ ↦ ?_
  rw [eval₂_quotient, Ideal.Quotient.eq_zero_iff_mem]

end Quotient

section Prime

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

/-! ### Non-integrality is witnessed modulo a prime -/

/-- The values of monic polynomials over `A` at `x`, as a submonoid of `R`. It is a submonoid
because a product of monic polynomials is monic and evaluation is multiplicative, and `1` is
monic.

Packaging them this way is what lets `Ideal.exists_le_prime_disjoint` run the maximality argument
instead of a bespoke one. -/
private def monicValues (A : Type*) [CommRing A] [Algebra A R] (x : R) : Submonoid R where
  carrier := {r | ∃ f : A[X], f.Monic ∧ eval₂ (algebraMap A R) x f = r}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, eval₂_mul _ _⟩
  one_mem' := ⟨1, monic_one, eval₂_one _ _⟩

/-- **Integrality is detected in the prime quotients.** If the reduction of `x` is integral over
`A` in `R ⧸ J` for every prime ideal `J` of `R`, then `x` is integral over `A`.

This is what lets a criterion for integrality that has been proved only for domains be applied to
an arbitrary commutative ring: every `R ⧸ J` here is a domain, so the criterion supplies exactly
the hypotheses this lemma consumes. -/
theorem isIntegral_of_forall_isPrime {x : R}
    (h : ∀ J : Ideal R, J.IsPrime → IsIntegral A (Ideal.Quotient.mk J x)) : IsIntegral A x := by
  by_contra hni
  -- non-integrality says exactly that `0` is not the value of a monic polynomial
  have hdisj : Disjoint ((⊥ : Ideal R) : Set R) (monicValues A x) := by
    rw [Set.disjoint_left]
    rintro r hr ⟨f, hf, hfr⟩
    exact hni ⟨f, hf, hfr.trans (Ideal.mem_bot.1 hr)⟩
  -- Mathlib's maximality argument turns that into a prime still avoiding every monic value
  obtain ⟨J, hJ, -, hJdisj⟩ := (⊥ : Ideal R).exists_le_prime_disjoint (monicValues A x) hdisj
  -- but `x` is integral modulo that prime, so some monic value does lie in `J`
  obtain ⟨f, hf, hfx⟩ := (isIntegral_quotient_iff x J).1 (h J hJ)
  exact Set.disjoint_left.1 hJdisj hfx ⟨f, hf, rfl⟩

end Prime

section Subring

variable {R : Type*} [CommRing R]

/-! ### The subring form -/

/-- The corestriction of `Ideal.Quotient.mk J` to a map onto the image subring `B.map (mk J)`. It
is the surjection along which a monic polynomial over the image is lifted back to one over `B`. -/
private def quotMap (B : Subring R) (J : Ideal R) : B →+* B.map (Ideal.Quotient.mk J) :=
  ((Ideal.Quotient.mk J).comp B.subtype).codRestrict _ fun b ↦ Subring.mem_map.2 ⟨b, b.2, rfl⟩

/-- `quotMap` is surjective: the image subring consists exactly of the reductions of elements of
`B`. -/
private theorem quotMap_surjective (B : Subring R) (J : Ideal R) :
    Function.Surjective (quotMap B J) := by
  rintro ⟨y, hy⟩
  obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 hy
  exact ⟨⟨b, hb⟩, rfl⟩

/-- Corestricting `Ideal.Quotient.mk J` and then including the image subring is the structure map
of `B` into `R ⧸ J`: both send `b` to its class. Naming the identity keeps the definitional step
out of the proof below. -/
private theorem algebraMap_comp_quotMap (B : Subring R) (J : Ideal R) :
    (algebraMap (B.map (Ideal.Quotient.mk J)) (R ⧸ J)).comp (quotMap B J) = algebraMap B (R ⧸ J) :=
  rfl

/-- Integrality over the image subring implies integrality over `B` itself: `B` surjects onto the
image, so a monic polynomial over the image lifts to a monic polynomial over `B`. -/
private theorem isIntegral_of_isIntegral_map (B : Subring R) (x : R) (J : Ideal R)
    (h : IsIntegral (B.map (Ideal.Quotient.mk J)) (Ideal.Quotient.mk J x)) :
    IsIntegral B (Ideal.Quotient.mk J x) := by
  obtain ⟨g, hg, hgx⟩ := h
  obtain ⟨f, hfg, -, hfm⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts _).2 (map_surjective _ (quotMap_surjective B J) g)) hg
  refine ⟨f, hfm, ?_⟩
  rw [← hgx, ← hfg, eval₂_map, algebraMap_comp_quotMap]

/-- **The subring form of `isIntegral_of_forall_isPrime`.** If the reduction of `x` is integral
over the image subring `B.map (Ideal.Quotient.mk J)` for every prime `J` of `R`, then `x` is
integral over the subring `B` itself. The image subring is the shape a criterion that quantifies
over subrings of `R ⧸ J` produces. -/
theorem isIntegral_of_forall_isPrime_map {B : Subring R} {x : R}
    (h : ∀ J : Ideal R, J.IsPrime →
      IsIntegral (B.map (Ideal.Quotient.mk J)) (Ideal.Quotient.mk J x)) : IsIntegral B x :=
  isIntegral_of_forall_isPrime fun J hJ ↦ isIntegral_of_isIntegral_map B x J (h J hJ)

end Subring

end TauCeti
