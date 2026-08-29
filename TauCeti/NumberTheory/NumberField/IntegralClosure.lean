/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
public import Mathlib.NumberTheory.ClassNumber.Finite
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# The integral closure of `𝓞 K` in a finite extension of number fields

For a finite extension `L` of a number field `K`, the integral closure of `𝓞 K` in `L` is the
integral closure of `ℤ` in `L`, hence isomorphic to `𝓞 L`. Two consequences transfer along that
identification and are the finiteness inputs of the Mordell–Weil descent: the class group of the
integral closure is finite, and its unit group is finitely generated.

Both are stated for `integralClosure (𝓞 K) L` rather than for `𝓞 L`, because that is the ring the
descent actually produces — `WeierstrassCurve.Affine.ringOfIntegersFactor` is an integral closure
in a quotient `K[X] ⧸ (p)`, not a ring of integers presented as such.

## Main results

* `isIntegralClosure_int_integralClosure` : the integral closure of `𝓞 K` in `L` is the integral
  closure of `ℤ` in `L`.
* `NumberField.finite_classGroup_integralClosure` : the **class number theorem** for it.
* `NumberField.fg_units_integralClosure` : the finite-generation half of **Dirichlet's unit
  theorem** for it.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/Mathlib/Basic.lean`, Apache-2.0.
  That file collects general-purpose results its author flags as Mathlib candidates; these three
  are adapted from it essentially verbatim.
-/

public section

open NumberField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The integral closure of `𝓞 K` in an extension `L` of `K` is the integral closure of `ℤ`
in `L`. -/
theorem isIntegralClosure_int_integralClosure :
    IsIntegralClosure (integralClosure (𝓞 K) L) ℤ L := by
  refine ⟨Subtype.val_injective, fun {x} ↦ ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩⟩
  · exact ⟨⟨x, IsIntegral.tower_top (A := 𝓞 K) hx⟩, rfl⟩
  · have hyint : IsIntegral (𝓞 K) (algebraMap (integralClosure (𝓞 K) L) L y) := y.2
    have := isIntegral_trans (R := ℤ) _ hyint
    rwa [hy] at this

variable [NumberField K] [FiniteDimensional K L]

/-- The **class number theorem** for the integral closure of `𝓞 K` in a finite extension `L`
of the number field `K`: its class group is finite. -/
theorem NumberField.finite_classGroup_integralClosure :
    Finite (ClassGroup (integralClosure (𝓞 K) L)) := by
  have : NumberField L := .of_module_finite K L
  have := isIntegralClosure_int_integralClosure K L
  have := ClassGroup.fintypeOfAdmissibleOfFinite ℚ L
    (S := integralClosure (𝓞 K) L) AbsoluteValue.absIsAdmissible
  exact Finite.of_fintype _

/-- **Dirichlet's unit theorem** (finite generation) for the integral closure of `𝓞 K` in a
finite extension `L` of the number field `K`: its unit group is finitely generated. -/
theorem NumberField.fg_units_integralClosure :
    Group.FG (integralClosure (𝓞 K) L)ˣ := by
  have : NumberField L := .of_module_finite K L
  have e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] (𝓞 L) :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  have : Group.FG (𝓞 L)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  exact Group.fg_of_surjective
    (f := (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv).toMonoidHom)
    (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv).surjective

end
