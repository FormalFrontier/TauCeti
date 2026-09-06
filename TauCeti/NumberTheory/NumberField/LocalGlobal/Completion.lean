/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension

/-!
# Canonical maps between number-field completions

Let `L/K` be an extension of number fields, and let `w` be a finite place of `L` above a finite
place `v` of `K`. The embedding `K → L` extends uniquely to a continuous map `K_v → L_w`.
This file packages that map as the algebra homomorphism `completionAlgHom`, installs the algebra
and topological scalar structures it induces, and proves its compatibility in towers.

The underlying continuous ring homomorphism is
`IsDedekindDomain.HeightOneSpectrum.adicCompletionExtension`. Packaging it over `K` is what makes
the completion map usable by scalar extension and tensor-product constructions without choosing
an unrelated algebra structure on `L_w` over `K_v`.

## Main definitions

* `TauCeti.NumberField.completionAlgHom`: the canonical `K`-algebra homomorphism `K_v → L_w`.
* `TauCeti.NumberField.completionAlgebra`: the induced algebra structure of `L_w` over `K_v`.

## Main results

* `TauCeti.NumberField.eq_completionAlgHom_of_continuous`: uniqueness among continuous ring
  homomorphisms extending `K → L`.
* `TauCeti.NumberField.completionAlgHom_comp`: compatibility in a tower of number fields.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §6.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.NumberField

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- The canonical map `K_v → L_w` for a finite place `w` of `L` above a finite place `v` of
`K`, as a `K`-algebra homomorphism. -/
def completionAlgHom {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    v.adicCompletion K →ₐ[K] w.adicCompletion L where
  toRingHom := v.adicCompletionExtension K L w
  commutes' x := v.adicCompletionExtension_coe K L w x

/-- The canonical completion map agrees with the given embedding `K → L` on `K`. -/
@[simp]
theorem completionAlgHom_algebraMap {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] (x : K) :
    completionAlgHom v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  exact (completionAlgHom v w).commutes x

/-- The canonical map between completions is continuous. -/
theorem continuous_completionAlgHom {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Continuous (completionAlgHom v w) :=
  v.continuous_adicCompletionExtension K L w

/-- A continuous ring homomorphism `K_v → L_w` extending `K → L` is the canonical completion
map. -/
theorem eq_completionAlgHom_of_continuous {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (f : v.adicCompletion K →+* w.adicCompletion L) (hf : Continuous f)
    (hcomp : ∀ x : K, f (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x)) :
    f = (completionAlgHom v w : v.adicCompletion K →+* w.adicCompletion L) :=
  v.eq_adicCompletionExtension_of_continuous K L w hf hcomp

/-- The algebra structure on `L_w` over `K_v` induced by the canonical completion map. -/
@[reducible]
noncomputable instance completionAlgebra {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (completionAlgHom v w).toRingHom.toAlgebra

/-- The global field, its completion, and the completion of an extension form a scalar tower for
the canonical completion algebra. -/
instance completionIsScalarTower {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ (completionAlgHom_algebraMap v w x).symm

/-- Scalar multiplication by `K_v` on `L_w` is continuous for the canonical completion
algebra. -/
instance completionContinuousSMul {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) :=
  continuousSMul_of_algebraMap _ _ (continuous_completionAlgHom v w)

/-- Canonical completion maps compose in a tower of number fields. -/
theorem completionAlgHom_comp {M L : Type*} [Field M] [NumberField M] [Algebra K M]
    [Field L] [NumberField L] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    (v : HeightOneSpectrum (𝒪 K)) (u : HeightOneSpectrum (𝒪 M))
    (w : HeightOneSpectrum (𝒪 L)) [u.asIdeal.LiesOver v.asIdeal]
    [w.asIdeal.LiesOver u.asIdeal] [w.asIdeal.LiesOver v.asIdeal] :
    (completionAlgHom u w).toRingHom.comp (completionAlgHom v u).toRingHom =
      (completionAlgHom v w).toRingHom := by
  apply eq_completionAlgHom_of_continuous v w
  · exact (continuous_completionAlgHom u w).comp (continuous_completionAlgHom v u)
  · intro x
    simp only [completionAlgHom, RingHom.comp_apply, Function.comp_apply,
      IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
      Algebra.algebraMap_self_apply]
    rw [v.adicCompletionExtension_coe K M u x,
      u.adicCompletionExtension_coe M L w (algebraMap K M x),
      IsScalarTower.algebraMap_apply K M L]

end TauCeti.NumberField
