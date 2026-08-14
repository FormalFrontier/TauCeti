/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty
public import Mathlib.Topology.Algebra.UniformRing

/-!
# The universal property of the completed algebra of `A⟨X⟩_T`

Wedhorn's Proposition 5.50 —
`existsUnique_continuous_ringHom_weightedRestrictedSubring_of_isWeightedVarPowerBounded` — is the
universal property of the restricted-series ring `A⟨X⟩_T` itself. This file carries it across the
separated completion: a ring homomorphism `φ : A →+* B` into a complete Hausdorff nonarchimedean
ring, continuous at zero, together with weight-bounded values `bᵢ`, extends to the completion of
`A⟨X⟩_T` in exactly one continuous way.

Neither half is new mathematics; both compose 5.50 with a standard property of the completion.
Existence is `UniformSpace.Completion.extensionHom` applied to the evaluation homomorphism, which
is available exactly because the target is already assumed complete and Hausdorff — the same
hypotheses 5.50 carries, so the completed statement asks for nothing extra. Uniqueness is
`completion_weightedRestrictedSubring_ringHom_ext_of_continuous`, itself
`UniformSpace.Completion.ext` — two continuous maps out of a completion that agree on the image of
the coercion are equal — applied to 5.50's own uniqueness clause for the restrictions along
`UniformSpace.Completion.coeRingHom`.

At the trivial weight family `Tᵢ = {1}` the domain is the completed restricted power-series
algebra `TauCeti.Huber.restrictedMvPowerSeriesCompletion k A`, which the roadmap writes
`A⟨X₁,…,Xₖ⟩` for an arbitrary Tate ring, so this is that algebra's universal property. It is
stated for a general weight family because nothing in the argument uses triviality.

## Main definitions

* `weightedEvalHomCompletion`: the evaluation homomorphism of 5.50, extended to the completion.

## Main results

* `existsUnique_continuous_ringHom_completion_weightedRestrictedSubring`: the `∃!` that the phrase
  "universal property" names, under `IsWeightBounded`.
* existsUnique_continuous_ringHom_completion_weightedRestrictedSubring_of_isWeightedVarPowerBounded
  — the same under `IsWeightedVarPowerBounded`, the coordinatewise condition Proposition 5.50
  states. This is the one to cite as 5.50.
* `completion_weightedRestrictedSubring_ringHom_ext_of_continuous`: the uniqueness half on its own,
  which asks of the target only a semiring structure and a Hausdorff topology.
* `weightedEvalHomCompletion_coe`: the value of the extension on the image of `A⟨X⟩_T`. The body of
  the definition is not exported, so this is how a consumer computes with it.
* `continuous_weightedEvalHomCompletion`: the extension is continuous.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 5.50.
-/

public section

namespace TauCeti.Huber

open UniformSpace

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {T : Fin k → Set A}

/-! ### Uniqueness

Uniqueness asks far less of the target than existence does, so it is proved first, under its own
hypotheses on `B`. -/

section Uniqueness

variable {B : Type*} [Semiring B] [TopologicalSpace B] [T2Space B]

/-- **A continuous homomorphism out of the completion of `A⟨X⟩_T` is determined by its values on
the generators.** Two of them agreeing on every constant series *and* every variable are equal.

This is `weightedRestrictedSubring_ringHom_ext_of_continuous` carried across the completion: that
lemma identifies the two restrictions along `UniformSpace.Completion.coeRingHom`, and
`UniformSpace.Completion.ext` propagates the agreement to the completion by density of the image
of the coercion. The completeness and `T3Space` hypotheses that the universal property below
carries are what the evaluation homomorphism needs in order to exist; uniqueness needs neither. -/
theorem completion_weightedRestrictedSubring_ringHom_ext_of_continuous (hT : IsWeightFamily T)
    {f g : Completion (weightedRestrictedSubring T hT) →+* B} (hf : Continuous f)
    (hg : Continuous g) (hC : ∀ a, f (weightedC T hT a) = g (weightedC T hT a))
    (hX : ∀ i, f (weightedX T hT i) = g (weightedX T hT i)) : f = g := by
  -- `⇑UniformSpace.Completion.coeRingHom` is the coercion `((↑) : _ → Completion _)`, by the
  -- definition of `coeRingHom`, so composing with it is restriction along the coercion. That
  -- unfolding is the only definitional bridge the proof crosses, and `hcomp` states it once.
  have hcomp : ∀ (h : Completion (weightedRestrictedSubring T hT) →+* B)
      (x : weightedRestrictedSubring T hT), (h.comp Completion.coeRingHom) x = h x :=
    fun _ _ ↦ rfl
  have key : f.comp Completion.coeRingHom = g.comp Completion.coeRingHom :=
    weightedRestrictedSubring_ringHom_ext_of_continuous hT
      (by simpa only [RingHom.coe_comp] using hf.comp Completion.continuous_coeRingHom)
      (by simpa only [RingHom.coe_comp] using hg.comp Completion.continuous_coeRingHom)
      (fun a ↦ (hcomp f _).trans ((hC a).trans (hcomp g _).symm))
      fun i ↦ (hcomp f _).trans ((hX i).trans (hcomp g _).symm)
  exact DFunLike.coe_injective (Completion.ext hf hg fun x ↦
    (hcomp f x).symm.trans ((DFunLike.congr_fun key x).trans (hcomp g x)))

end Uniqueness

/-! ### The extended evaluation homomorphism and the universal property -/

section UniversalProperty

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T3Space B] {φ : A →+* B} {b : Fin k → B}

/-- The evaluation homomorphism of Proposition 5.50, extended to the completion of `A⟨X⟩_T`.
The extension exists because the target is complete and Hausdorff. -/
noncomputable def weightedEvalHomCompletion (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) :
    Completion (weightedRestrictedSubring T hT) →+* B :=
  Completion.extensionHom (weightedEvalHom hT hφ hb) (continuous_weightedEvalHom hT hφ hb)

/-- The extension is the evaluation homomorphism on the image of `A⟨X⟩_T`. The body of
`weightedEvalHomCompletion` is not exported, so this is how a consumer computes with it. -/
@[simp]
theorem weightedEvalHomCompletion_coe (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) (f : weightedRestrictedSubring T hT) :
    weightedEvalHomCompletion hT hφ hb (f : Completion (weightedRestrictedSubring T hT))
      = weightedEvalHom hT hφ hb f :=
  Completion.extensionHom_coe (weightedEvalHom hT hφ hb) (continuous_weightedEvalHom hT hφ hb) f

/-- The extended evaluation homomorphism is continuous: it is a `UniformSpace.Completion`
extension, and those are continuous by construction. -/
theorem continuous_weightedEvalHomCompletion (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) : Continuous (weightedEvalHomCompletion hT hφ hb) :=
  Completion.continuous_extension

/-- **The universal property of the completion of `A⟨X⟩_T`, under `IsWeightBounded`.** Given
`φ : A →+* B` continuous at zero and weight-bounded values `b`, there is exactly one continuous
ring homomorphism from the completion of `A⟨X⟩_T` to `B` restricting to `φ` on the constants and
sending each `Xᵢ` to `bᵢ`.

This mirrors `existsUnique_continuous_ringHom_weightedRestrictedSubring`, the uncompleted
statement under the same uniform hypothesis. Proposition 5.50's own hypothesis is the
coordinatewise one, so the theorem to cite as 5.50 is the `_of_isWeightedVarPowerBounded` form of
this one, below:
`existsUnique_continuous_ringHom_completion_weightedRestrictedSubring_of_isWeightedVarPowerBounded`.

As in the uncompleted statement, uniqueness is among *continuous* homomorphisms, and continuity is
used at both steps of the argument: 5.50 pins `ψ` down on the image of `A⟨X⟩_T` from its values on
the constants and the variables, by density of the polynomials, and the density of that image in
the completion carries the agreement the rest of the way. Whether a discontinuous homomorphism
with the same values can exist is not addressed here. -/
theorem existsUnique_continuous_ringHom_completion_weightedRestrictedSubring
    (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ T b) :
    ∃! ψ : Completion (weightedRestrictedSubring T hT) →+* B, Continuous ψ ∧
      (∀ a, ψ ((weightedC T hT a : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT)) = φ a) ∧
      ∀ i, ψ ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = b i := by
  -- The extension's values on the generators: its value on the image of `A⟨X⟩_T` composed with
  -- the uncompleted evaluation's own computations.
  have hC₀ : ∀ a, weightedEvalHomCompletion hT hφ hb
      ((weightedC T hT a : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = φ a := fun a ↦ by
    rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]
  have hX₀ : ∀ i, weightedEvalHomCompletion hT hφ hb
      ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = b i := fun i ↦ by
    rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]
  exact ⟨weightedEvalHomCompletion hT hφ hb,
    ⟨continuous_weightedEvalHomCompletion hT hφ hb, hC₀, hX₀⟩,
    fun _ ⟨hψ, hC, hX⟩ ↦ completion_weightedRestrictedSubring_ringHom_ext_of_continuous hT hψ
      (continuous_weightedEvalHomCompletion hT hφ hb)
      (fun a ↦ (hC a).trans (hC₀ a).symm) fun i ↦ (hX i).trans (hX₀ i).symm⟩

/-- **Wedhorn 5.50 for the completed algebra**, under the hypothesis Proposition 5.50 itself
carries: each weighted variable `φ(Tᵢ) · bᵢ` power-bounded as a set, one index at a time.

This is the theorem to cite as 5.50 for the completion. It is the statement above composed with
`isWeightBounded_of_isWeightedVarPowerBounded`, exactly as
`existsUnique_continuous_ringHom_weightedRestrictedSubring_of_isWeightedVarPowerBounded` relates
to its own uniform form. -/
theorem
  existsUnique_continuous_ringHom_completion_weightedRestrictedSubring_of_isWeightedVarPowerBounded
    (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0) (hb : IsWeightedVarPowerBounded φ T b) :
    ∃! ψ : Completion (weightedRestrictedSubring T hT) →+* B, Continuous ψ ∧
      (∀ a, ψ ((weightedC T hT a : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT)) = φ a) ∧
      ∀ i, ψ ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = b i :=
  existsUnique_continuous_ringHom_completion_weightedRestrictedSubring hT hφ
    (isWeightBounded_of_isWeightedVarPowerBounded hb)

end UniversalProperty

end TauCeti.Huber

end
