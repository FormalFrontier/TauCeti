/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Ideal
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion

/-!
# Homomorphisms topologically of finite type

Wedhorn's §6.6. A ring homomorphism `φ : A → B` is *topologically of finite type* when `B` is
presented as an `A`-algebra by an open quotient map out of the completion of a weighted restricted
power-series ring `A⟨X₁, …, Xₖ⟩_T` on finitely many variables, each weight `Tᵢ` finite. It is
*strictly* topologically of finite type when the trivial weight family `Tᵢ = {1}` suffices, so
that the presenting algebra is `TauCeti.Huber.restrictedMvPowerSeriesCompletion`, the object this
library writes `A⟨X₁, …, Xₖ⟩`.

The notion is what three results the adic-spaces roadmap needs are stated in terms of: the second
half of Proposition and Definition 6.36 (a Tate ring is strongly noetherian exactly when every
Tate ring topologically of finite type over it is noetherian), Remark 6.37(1), and Example 6.38,
which Proposition 8.30 cites by name.

## What is and is not assumed

Wedhorn states 6.28 and 6.29 for an `f`-adic `A` and a *complete* `f`-adic `B`. **Those standing
hypotheses are deliberately not imposed here**: the definitions ask only that `A` be a
nonarchimedean topological commutative ring — the least that lets `A⟨X⟩_T` be formed at all — and
that `B` be a topological commutative ring. The predicates are therefore defined on a wider class
than Wedhorn's, and agree with his on the class he considers. A consumer that needs completeness
of `B` should assume it alongside, not read it out of these definitions.

## Notation, and one thing it is easy to get backwards

`A⟨X₁, …, Xₖ⟩_T` names the **uncompleted** weighted ring `TauCeti.Huber.weightedRestrictedSubring`
of Wedhorn's Remark and Definition 5.48, as it does in the roadmap (`AdicSpaces/README.md`, §0.4).
Wedhorn's presenting algebra in 6.28/6.29 is its **completion**, which he writes `Â⟨…⟩`; at the
trivial weight family that completion is `restrictedMvPowerSeriesCompletion`, which this library
writes `A⟨X₁, …, Xₖ⟩` without a subscript. So the domain of `π` below is a completion throughout,
never the subring itself.

## The weighted algebra, and why not the Tate-only one

The presenting algebra is the **weighted** one. That is Wedhorn's own 6.29(i), and it is what the
roadmap asks for (`AdicSpaces/README.md`, §5.2): the Tate-only algebra is too narrow downstream,
since `A_inf` is Huber and not Tate. Definition 6.28, the strict variant, is the Tate-only case;
the implication between them is `IsStrictlyTopologicallyFiniteType.isTopologicallyFiniteType`.

Two conditions on the weight family are in play and they are not the same. Wedhorn's standing
hypothesis on `T` — needed even to *form* `A⟨X⟩_T` — is `TauCeti.Huber.IsWeightFamily`, that
`Tᵢ^m · U` is a neighbourhood of zero for every `m` and every neighbourhood `U` of zero. The
phrasing in 6.29(i), that each `Tᵢ · A` is open, is the `U = ⊤` case, and is recovered from it by
`TauCeti.Huber.IsWeightFamily.isOpen_weightMul_top`; the converse is not available here (see that
lemma's docstring). Finiteness of each `Tᵢ` is a separate requirement of 6.29(i) — it is what makes
the notion one of *finite* type — and is carried explicitly, since `IsWeightFamily` does not imply
it.

## Main definitions

* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType`: Wedhorn Definition 6.28.
* `TauCeti.Huber.IsTopologicallyFiniteType`: Wedhorn Proposition and Definition 6.29(i).

## Main results

* `TauCeti.Huber.isStrictlyTopologicallyFiniteType_algebraMap`: the structure map
  `A → A⟨X₁, …, Xₖ⟩` is strictly topologically of finite type — the presentation by the identity.
* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.isTopologicallyFiniteType`: strictly
  topologically of finite type implies topologically of finite type, by the trivial weight family.
* `TauCeti.Huber.IsTopologicallyFiniteType.continuous`: such a `φ` is continuous, since it factors
  through the presenting algebra's structure map.
* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.comp_isOpenQuotientMap` and
  `TauCeti.Huber.IsTopologicallyFiniteType.comp_isOpenQuotientMap`: both notions are stable under
  composing with a further open quotient map.
* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.quotientMk` and
  `TauCeti.Huber.IsTopologicallyFiniteType.quotientMk`: in particular, stable under passing to a
  quotient by an ideal.
* `TauCeti.Huber.isStrictlyTopologicallyFiniteType_quotientMk_algebraMap`: every quotient of
  `A⟨X₁, …, Xₖ⟩` is strictly topologically of finite type over `A` — the shape of every Laurent
  and rational presentation.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §6.6, Definition 6.28 and
  Proposition and Definition 6.29.
-/

public section

namespace TauCeti.Huber

open UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {B : Type*} [CommRing B] [TopologicalSpace B]

/-- **Wedhorn Proposition and Definition 6.29(i)**: `φ : A → B` is *topologically of finite type*
when `B` is presented, as an `A`-algebra, by an open quotient map out of the completion of a
weighted restricted power-series ring on finitely many variables with each weight `Tᵢ` finite. -/
def IsTopologicallyFiniteType (φ : A →+* B) : Prop :=
  ∃ (k : ℕ) (T : Fin k → Set A) (_ : ∀ i, (T i).Finite) (hT : IsWeightFamily T)
    (π : Completion (weightedRestrictedSubring T hT) →+* B),
    IsOpenQuotientMap π ∧ π.comp (algebraMap A (Completion (weightedRestrictedSubring T hT))) = φ

/-- Unfolding lemma for the sealed definition `TauCeti.Huber.IsTopologicallyFiniteType`. -/
theorem isTopologicallyFiniteType_iff {φ : A →+* B} :
    IsTopologicallyFiniteType φ ↔
      ∃ (k : ℕ) (T : Fin k → Set A) (_ : ∀ i, (T i).Finite) (hT : IsWeightFamily T)
        (π : Completion (weightedRestrictedSubring T hT) →+* B),
        IsOpenQuotientMap π ∧
          π.comp (algebraMap A (Completion (weightedRestrictedSubring T hT))) = φ :=
  (Iff.rfl)

/-- **Wedhorn Definition 6.28**: `φ : A → B` is *strictly* topologically of finite type when the
presenting algebra can be taken to be `A⟨X₁, …, Xₖ⟩`, the trivial weight family. -/
def IsStrictlyTopologicallyFiniteType (φ : A →+* B) : Prop :=
  ∃ (k : ℕ) (π : restrictedMvPowerSeriesCompletion k A →+* B),
    IsOpenQuotientMap π ∧
      π.comp (algebraMap A (restrictedMvPowerSeriesCompletion k A)) = φ

/-- Unfolding lemma for the sealed definition
`TauCeti.Huber.IsStrictlyTopologicallyFiniteType`. -/
theorem isStrictlyTopologicallyFiniteType_iff {φ : A →+* B} :
    IsStrictlyTopologicallyFiniteType φ ↔
      ∃ (k : ℕ) (π : restrictedMvPowerSeriesCompletion k A →+* B),
        IsOpenQuotientMap π ∧
          π.comp (algebraMap A (restrictedMvPowerSeriesCompletion k A)) = φ :=
  (Iff.rfl)

/-- **The presentation by the identity**: the structure map `A → A⟨X₁, …, Xₖ⟩` is strictly
topologically of finite type. This is the witness that the conditions are simultaneously
satisfiable, and the `k = 0` case says the completion map `A → Â` is one too. -/
theorem isStrictlyTopologicallyFiniteType_algebraMap (k : ℕ) :
    IsStrictlyTopologicallyFiniteType (algebraMap A (restrictedMvPowerSeriesCompletion k A)) :=
  ⟨k, RingHom.id _, IsOpenQuotientMap.id, RingHom.id_comp _⟩

/-- The trivial weight family is finite and satisfies the standing hypothesis, so a strict
presentation is a presentation. -/
theorem IsStrictlyTopologicallyFiniteType.isTopologicallyFiniteType {φ : A →+* B}
    (h : IsStrictlyTopologicallyFiniteType φ) : IsTopologicallyFiniteType φ := by
  obtain ⟨k, π, hπ, hcomm⟩ := h
  exact ⟨k, _, fun _ ↦ Set.finite_singleton 1, isWeightFamily_one_weight, π, hπ, hcomm⟩

/-- A homomorphism topologically of finite type is continuous: it factors as an open quotient map
after the presenting algebra's structure map, and both are continuous. -/
theorem IsTopologicallyFiniteType.continuous {φ : A →+* B} (h : IsTopologicallyFiniteType φ) :
    Continuous φ := by
  obtain ⟨k, T, _, hT, π, hπ, hcomm⟩ := h
  rw [← hcomm]
  exact hπ.continuous.comp (continuous_algebraMap_completion_weightedRestrictedSubring k A hT)

/-! ### Stability under a further open quotient

Wedhorn presents an algebra topologically of finite type as an open quotient of a restricted
power-series ring, so composing that presentation with another open quotient map is again a
presentation of the same shape. This is what lets a *quotient* of `A⟨X₁, …, Xₖ⟩` — the form every
rational localisation and Laurent presentation takes — inherit finite type without exhibiting a
fresh presentation by hand.
-/

section OpenQuotient

variable {C : Type*} [CommRing C] [TopologicalSpace C]

/-- **A strict presentation pushes along an open quotient map.** If `φ : A → B` is strictly
topologically of finite type and `ψ : B → C` is an open quotient map, then so is `ψ ∘ φ`: compose
the presenting `A⟨X₁, …, Xₖ⟩ ↠ B` with `ψ`, and use that open quotient maps compose. -/
theorem IsStrictlyTopologicallyFiniteType.comp_isOpenQuotientMap {φ : A →+* B} {ψ : B →+* C}
    (h : IsStrictlyTopologicallyFiniteType φ) (hψ : IsOpenQuotientMap ψ) :
    IsStrictlyTopologicallyFiniteType (ψ.comp φ) := by
  obtain ⟨k, π, hπ, hcomm⟩ := h
  exact ⟨k, ψ.comp π, hψ.comp hπ, by rw [RingHom.comp_assoc, hcomm]⟩

/-- **A presentation pushes along an open quotient map**, the weighted form of
`TauCeti.Huber.IsStrictlyTopologicallyFiniteType.comp_isOpenQuotientMap`. The weight family is
carried across unchanged; only the presenting map moves. -/
theorem IsTopologicallyFiniteType.comp_isOpenQuotientMap {φ : A →+* B} {ψ : B →+* C}
    (h : IsTopologicallyFiniteType φ) (hψ : IsOpenQuotientMap ψ) :
    IsTopologicallyFiniteType (ψ.comp φ) := by
  obtain ⟨k, T, hTfin, hT, π, hπ, hcomm⟩ := h
  exact ⟨k, T, hTfin, hT, ψ.comp π, hψ.comp hπ, by rw [RingHom.comp_assoc, hcomm]⟩

variable [IsTopologicalRing B]

/-- **Strict finite type passes to a quotient by an ideal.** The quotient map of a topological
ring is an open quotient map, so this is the previous lemma at `ψ = Ideal.Quotient.mk I`. -/
theorem IsStrictlyTopologicallyFiniteType.quotientMk {φ : A →+* B}
    (h : IsStrictlyTopologicallyFiniteType φ) (I : Ideal B) :
    IsStrictlyTopologicallyFiniteType ((Ideal.Quotient.mk I).comp φ) :=
  h.comp_isOpenQuotientMap (QuotientRing.isOpenQuotientMap_mk I)

/-- **Finite type passes to a quotient by an ideal.** -/
theorem IsTopologicallyFiniteType.quotientMk {φ : A →+* B} (h : IsTopologicallyFiniteType φ)
    (I : Ideal B) : IsTopologicallyFiniteType ((Ideal.Quotient.mk I).comp φ) :=
  h.comp_isOpenQuotientMap (QuotientRing.isOpenQuotientMap_mk I)

/-- **Every quotient of `A⟨X₁, …, Xₖ⟩` is strictly topologically of finite type over `A`.** This is
the form every Laurent and rational presentation takes — Wedhorn's Examples 6.38 and 6.39 exhibit
their rings this way — so it is the statement those examples reduce to once the presenting ideal
is named. -/
theorem isStrictlyTopologicallyFiniteType_quotientMk_algebraMap (k : ℕ)
    (I : Ideal (restrictedMvPowerSeriesCompletion k A)) :
    IsStrictlyTopologicallyFiniteType
      ((Ideal.Quotient.mk I).comp (algebraMap A (restrictedMvPowerSeriesCompletion k A))) :=
  (isStrictlyTopologicallyFiniteType_algebraMap k).quotientMk I

end OpenQuotient

end TauCeti.Huber
