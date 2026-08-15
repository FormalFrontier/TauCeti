/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Mul

/-!
# The evaluation of `A⟨X⟩_T` as a ring homomorphism

The additive and multiplicative laws of Wedhorn's evaluation are proved in
`WeightedEval/Map.lean` and `WeightedEval/Mul.lean` as statements about individual
`T`-restricted series. On `A⟨X⟩_T` itself — where restrictedness is carried by membership rather
than by a hypothesis — they assemble into a ring homomorphism, which is the shape Proposition 5.50
needs.

Its continuity is `TauCeti.Huber.continuous_weightedEvalHom` in `WeightedEval/Continuous.lean`.
The uniqueness that makes 5.50 a *universal* property is
`TauCeti.Huber.weightedRestrictedSubring_ringHom_ext_of_continuous` in
`WeightedRestrictedSeries/Basic.lean`; `WeightedEval/UniversalProperty.lean` puts the two
together, and its `∃!` statement identifies this homomorphism as the only continuous one
with these values on the generators.

## Main definitions

* `TauCeti.Huber.weightedEvalHom`: evaluation as a ring homomorphism `A⟨X⟩_T →+* B`.

## Main results

* `TauCeti.Huber.coe_weightedEvalHom`: it is `TauCeti.Huber.weightedEval` on the underlying
  series, which is how every computation about it is done.
* `TauCeti.Huber.weightedEvalHom_weightedC` and `TauCeti.Huber.weightedEvalHom_weightedX`: it
  sends `weightedC a` to `φ a` and `weightedX i` to `bᵢ`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50.
-/

public section

open Pointwise Topology

namespace TauCeti.Huber

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B]
  [T3Space B] {φ : A →+* B} {T : Fin k → Set A} {b : Fin k → B}

/-- **Wedhorn's evaluation as a ring homomorphism** `A⟨X⟩_T →+* B`, sending a series to the sum of
its terms at `b` along `φ`.

It is a homomorphism on `A⟨X⟩_T` rather than on all of `A[[X]]`: the ring laws below hold for
`T`-restricted series, and membership in `TauCeti.Huber.weightedRestrictedSubring` is what carries
that restrictedness. The hypotheses are those of the summability theorem — `φ` continuous at zero
and the weighted monomials bounded — together with `IsWeightFamily T` for the domain to be a
ring. -/
noncomputable def weightedEvalHom (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) : weightedRestrictedSubring T hT →+* B where
  toFun f := weightedEval φ b (f : MvPowerSeries (Fin k) A)
  map_one' := by
    rw [OneMemClass.coe_one, ← MvPowerSeries.monomial_zero_one, weightedEval_monomial]
    simp
  map_mul' f g := weightedEval_mul hφ hb (mem_weightedRestrictedSubring.mp f.property)
    (mem_weightedRestrictedSubring.mp g.property)
  map_zero' := weightedEval_zero φ b
  map_add' f g := weightedEval_add hφ hb (mem_weightedRestrictedSubring.mp f.property)
    (mem_weightedRestrictedSubring.mp g.property)

/-- The homomorphism is `TauCeti.Huber.weightedEval` on the underlying series. The body is not
exported, so this is how a consumer computes with it. -/
@[simp]
theorem coe_weightedEvalHom (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) (f : weightedRestrictedSubring T hT) :
    weightedEvalHom hT hφ hb f = weightedEval φ b (f : MvPowerSeries (Fin k) A) := (rfl)

/-- The homomorphism sends the constant series `weightedC a` to `φ a`. -/
theorem weightedEvalHom_weightedC (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) (a : A) :
    weightedEvalHom hT hφ hb (weightedC T hT a) = φ a := by
  rw [coe_weightedEvalHom, coe_weightedC, weightedEval_C]

/-- The homomorphism sends the `i`-th variable `weightedX i` to `bᵢ`. -/
theorem weightedEvalHom_weightedX (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) (i : Fin k) :
    weightedEvalHom hT hφ hb (weightedX T hT i) = b i := by
  rw [coe_weightedEvalHom, coe_weightedX, weightedEval_X]

end TauCeti.Huber

end
