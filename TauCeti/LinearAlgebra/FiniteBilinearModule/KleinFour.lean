/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic

/-!
# Finite quadratic modules on the Klein four-group

A `ℚ/ℤ`-valued quadratic map on `(ℤ/2)²` is determined by its three values on the nonzero
elements, and conversely any three values admissible for the two-torsion of the group occur.
This file makes that presentation available as a construction: given `α β γ : ℚ/ℤ` with
`4α = 4β = 2γ = 0`, `TauCeti.FiniteQuadraticModule.kleinFour` is the finite quadratic module on
`ZMod 2 × ZMod 2` with

```text
q(1, 0) = α,   q(0, 1) = β,   q(1, 1) = α + β + γ,   b((1, 0), (0, 1)) = γ.
```

The construction is a quotient, not a formula in `ZMod.val`: the parameters define an honest
`ℤ`-bilinear map on `ℤ × ℤ`, its associated quadratic map `(m, k) ↦ m²α + k²β + mkγ` has the
kernel of the reduction `ℤ × ℤ → (ℤ/2)²` inside its radical exactly under the three torsion
hypotheses, and `QuadraticMap.lift` descends it.  The torsion hypotheses are therefore not
technical: `4α = 0` is the statement that `q` is well defined on a two-torsion generator, and
`2γ = 0` the corresponding statement for the pairing.

The companion `TauCeti.FiniteQuadraticModule.kleinFourIsometryOfGenerators` turns an additive
equivalence `(ℤ/2)² ≃+ A` matching the three displayed values into an isometry onto `A`, which is
how a discriminant form of order four and exponent two is identified.

The quotient construction is a rank-two adaptation of the private cyclic construction in
`TauCeti/LinearAlgebra/IntegralLattice/RootLattice/TypeE.lean`; the two can be unified when that
construction is promoted to shared API.

## Main declarations

* `TauCeti.FiniteQuadraticModule.kleinFourMap`: the quadratic map on `ZMod 2 × ZMod 2` with the
  displayed generator values.
* `TauCeti.FiniteQuadraticModule.kleinFour`: the resulting finite quadratic module.
* `TauCeti.FiniteQuadraticModule.kleinFourIsometryOfGenerators`: an additive equivalence matching
  the three generator values is an isometry.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1 for
  discriminant forms and §1.8, Proposition 1.8.1 for the forms written `u₁` and `v₁` in the
  full-norm convention.
* W. Ebeling, *Lattices and Codes*, Chapter 1.

This is part of Layer 3 of `TauCetiRoadmap/IntegralLattices/README.md`.
-/

public section

namespace TauCeti

namespace FiniteQuadraticModule

variable (α β γ : AddCircle (1 : ℚ))

/-! ## The presenting quadratic map on `ℤ × ℤ` -/

/-- The bilinear map `((m, k), (m', k')) ↦ mm'α + kk'β + mk'γ` on `ℤ × ℤ`.  It is not symmetric;
only its associated quadratic map is used. -/
private def kleinFourBilin : LinearMap.BilinMap ℤ (ℤ × ℤ) (AddCircle (1 : ℚ)) :=
  LinearMap.mk₂ ℤ (fun u v ↦ (u.1 * v.1) • α + (u.2 * v.2) • β + (u.1 * v.2) • γ)
    (fun u u' v ↦ by
      simp only [Prod.fst_add, Prod.snd_add, add_mul, add_smul]
      abel)
    (fun c u v ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_assoc, mul_smul, smul_add])
    (fun u v v' ↦ by
      simp only [Prod.fst_add, Prod.snd_add, mul_add, add_smul]
      abel)
    (fun c u v ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_left_comm, mul_smul, smul_add])

private theorem kleinFourBilin_apply (u v : ℤ × ℤ) :
    kleinFourBilin α β γ u v =
      (u.1 * v.1) • α + (u.2 * v.2) • β + (u.1 * v.2) • γ := by
  rw [kleinFourBilin, LinearMap.mk₂_apply]

/-- The quadratic map `(m, k) ↦ m²α + k²β + mkγ` on `ℤ × ℤ`. -/
private def kleinFourAux : QuadraticMap ℤ (ℤ × ℤ) (AddCircle (1 : ℚ)) :=
  (kleinFourBilin α β γ).toQuadraticMap

private theorem kleinFourAux_apply (u : ℤ × ℤ) :
    kleinFourAux α β γ u = (u.1 * u.1) • α + (u.2 * u.2) • β + (u.1 * u.2) • γ := by
  rw [kleinFourAux, LinearMap.BilinMap.toQuadraticMap_apply, kleinFourBilin_apply]

private theorem polar_kleinFourAux (u v : ℤ × ℤ) :
    QuadraticMap.polar (kleinFourAux α β γ) u v =
      (2 * (u.1 * v.1)) • α + (2 * (u.2 * v.2)) • β + (u.1 * v.2 + u.2 * v.1) • γ := by
  rw [kleinFourAux, LinearMap.BilinMap.polar_toQuadraticMap, kleinFourBilin_apply,
    kleinFourBilin_apply]
  have e₁ : (2 * (u.1 * v.1) : ℤ) = u.1 * v.1 + v.1 * u.1 := by ring
  have e₂ : (2 * (u.2 * v.2) : ℤ) = u.2 * v.2 + v.2 * u.2 := by ring
  have e₃ : (u.1 * v.2 + u.2 * v.1 : ℤ) = u.1 * v.2 + v.1 * u.2 := by ring
  rw [e₁, e₂, e₃, add_smul, add_smul, add_smul]
  abel

/-! ## Reduction modulo two -/

/-- Coordinatewise reduction `ℤ × ℤ → (ℤ/2)²`. -/
private def zmodTwoPairProj : (ℤ × ℤ) →ₗ[ℤ] ZMod 2 × ZMod 2 :=
  LinearMap.prodMap (Int.castAddHom (ZMod 2)).toIntLinearMap
    (Int.castAddHom (ZMod 2)).toIntLinearMap

private theorem zmodTwoPairProj_apply (m k : ℤ) :
    zmodTwoPairProj (m, k) = ((m : ZMod 2), (k : ZMod 2)) := (rfl)

private theorem zmodTwoPairProj_surjective : Function.Surjective zmodTwoPairProj := by
  rintro ⟨x, y⟩
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective y
  exact ⟨(m, k), rfl⟩

private theorem mem_ker_zmodTwoPairProj_iff (u : ℤ × ℤ) :
    u ∈ LinearMap.ker zmodTwoPairProj ↔ (2 : ℤ) ∣ u.1 ∧ (2 : ℤ) ∣ u.2 := by
  obtain ⟨m, k⟩ := u
  rw [LinearMap.mem_ker, zmodTwoPairProj_apply, Prod.ext_iff]
  simpa using
    and_congr (ZMod.intCast_zmod_eq_zero_iff_dvd m 2) (ZMod.intCast_zmod_eq_zero_iff_dvd k 2)

/-- Under the three torsion hypotheses the kernel of reduction modulo two lies in the radical,
which is what lets the quadratic map descend. -/
private theorem ker_zmodTwoPairProj_le_radical (h₄α : (4 : ℤ) • α = 0) (h₄β : (4 : ℤ) • β = 0)
    (h₂γ : (2 : ℤ) • γ = 0) :
    LinearMap.ker zmodTwoPairProj ≤ (kleinFourAux α β γ).radical := by
  rintro ⟨m, k⟩ hu
  rw [mem_ker_zmodTwoPairProj_iff] at hu
  obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hu
  have hα : ∀ c : ℤ, (c * 4 : ℤ) • α = 0 := fun c ↦ by rw [mul_smul, h₄α, smul_zero]
  have hβ : ∀ c : ℤ, (c * 4 : ℤ) • β = 0 := fun c ↦ by rw [mul_smul, h₄β, smul_zero]
  have hγ : ∀ c : ℤ, (c * 2 : ℤ) • γ = 0 := fun c ↦ by rw [mul_smul, h₂γ, smul_zero]
  constructor
  · rw [kleinFourAux_apply]
    have e₁ : (2 * a * (2 * a) : ℤ) = a * a * 4 := by ring
    have e₂ : (2 * b * (2 * b) : ℤ) = b * b * 4 := by ring
    have e₃ : (2 * a * (2 * b) : ℤ) = 2 * a * b * 2 := by ring
    rw [e₁, e₂, e₃, hα, hβ, hγ, add_zero, add_zero]
  · refine LinearMap.ext fun v ↦ ?_
    rw [LinearMap.zero_apply, QuadraticMap.polarBilin_apply_apply, polar_kleinFourAux]
    have e₁ : (2 * (2 * a * v.1) : ℤ) = a * v.1 * 4 := by ring
    have e₂ : (2 * (2 * b * v.2) : ℤ) = b * v.2 * 4 := by ring
    have e₃ : (2 * a * v.2 + 2 * b * v.1 : ℤ) = (a * v.2 + b * v.1) * 2 := by ring
    rw [e₁, e₂, e₃, hα, hβ, hγ, add_zero, add_zero]

/-! ## The quadratic module -/

variable (h₄α : (4 : ℤ) • α = 0) (h₄β : (4 : ℤ) • β = 0) (h₂γ : (2 : ℤ) • γ = 0)

include h₄α h₄β h₂γ

/-- The quadratic map on `(ℤ/2)²` sending `(1, 0)` to `α`, `(0, 1)` to `β`, and `(1, 1)` to
`α + β + γ`. -/
noncomputable def kleinFourMap : QuadraticMap ℤ (ZMod 2 × ZMod 2) (AddCircle (1 : ℚ)) :=
  ((kleinFourAux α β γ).lift (LinearMap.ker zmodTwoPairProj)
      (ker_zmodTwoPairProj_le_radical α β γ h₄α h₄β h₂γ)).comp
    (zmodTwoPairProj.quotKerEquivOfSurjective zmodTwoPairProj_surjective).symm.toLinearMap

/-- The value of `kleinFourMap` on the reduction of a pair of integers. -/
theorem kleinFourMap_intCast (m k : ℤ) :
    kleinFourMap α β γ h₄α h₄β h₂γ ((m : ZMod 2), (k : ZMod 2)) =
      (m * m) • α + (k * k) • β + (m * k) • γ := by
  have hsymm :
      (zmodTwoPairProj.quotKerEquivOfSurjective zmodTwoPairProj_surjective).symm
          ((m : ZMod 2), (k : ZMod 2)) = Submodule.Quotient.mk (m, k) := by
    rw [← zmodTwoPairProj_apply m k, LinearMap.quotKerEquivOfSurjective_symm_apply]
  rw [kleinFourMap, QuadraticMap.comp_apply, LinearEquiv.coe_coe, hsymm, QuadraticMap.lift_mk,
    kleinFourAux_apply]

@[simp]
theorem kleinFourMap_apply_one_zero : kleinFourMap α β γ h₄α h₄β h₂γ (1, 0) = α := by
  simpa using kleinFourMap_intCast α β γ h₄α h₄β h₂γ 1 0

@[simp]
theorem kleinFourMap_apply_zero_one : kleinFourMap α β γ h₄α h₄β h₂γ (0, 1) = β := by
  simpa using kleinFourMap_intCast α β γ h₄α h₄β h₂γ 0 1

@[simp]
theorem kleinFourMap_apply_one_one :
    kleinFourMap α β γ h₄α h₄β h₂γ (1, 1) = α + β + γ := by
  simpa using kleinFourMap_intCast α β γ h₄α h₄β h₂γ 1 1

/-- The two standard generators of `(ℤ/2)²` pair to `γ`. -/
@[simp]
theorem polar_kleinFourMap_one_zero_zero_one :
    QuadraticMap.polar (kleinFourMap α β γ h₄α h₄β h₂γ) (1, 0) (0, 1) = γ := by
  rw [QuadraticMap.polar, kleinFourMap_apply_one_zero, kleinFourMap_apply_zero_one]
  rw [Prod.mk_add_mk, add_zero, zero_add, kleinFourMap_apply_one_one]
  abel

/-- **The finite quadratic module on `(ℤ/2)²` with generator values `α`, `β` and `α + β + γ`.** -/
@[expose] noncomputable def kleinFour : FiniteQuadraticModule where
  toFiniteBilinearModule := {
    carrier := ZMod 2 × ZMod 2
    pairing := LinearMap.toAddMonoidHom'.comp
      (kleinFourMap α β γ h₄α h₄β h₂γ).polarBilin.toAddMonoidHom
    pairing_comm := fun x y ↦ QuadraticMap.polar_comm (kleinFourMap α β γ h₄α h₄β h₂γ) x y }
  quadratic := kleinFourMap α β γ h₄α h₄β h₂γ
  polar_eq_pairing' := fun _ _ ↦ (rfl)

@[simp]
theorem kleinFour_quadratic (x : ZMod 2 × ZMod 2) :
    (kleinFour α β γ h₄α h₄β h₂γ).quadratic x = kleinFourMap α β γ h₄α h₄β h₂γ x := (rfl)

@[simp]
theorem kleinFour_pairing (x y : ZMod 2 × ZMod 2) :
    (kleinFour α β γ h₄α h₄β h₂γ).toFiniteBilinearModule.pairing x y =
      QuadraticMap.polar (kleinFourMap α β γ h₄α h₄β h₂γ) x y := (rfl)

omit h₄α h₄β h₂γ in
/-- **An additive equivalence from `(ℤ/2)²` matching all three nonzero values is an isometry.**

No hypothesis beyond the three displayed values is needed.  Both forms are stated as bare quadratic
maps so that the construction applies before either is packaged as a finite quadratic module. -/
noncomputable def kleinFourIsometryOfGenerators {A : Type*} [AddCommGroup A]
    (q : QuadraticMap ℤ (ZMod 2 × ZMod 2) (AddCircle (1 : ℚ)))
    (r : QuadraticMap ℤ A (AddCircle (1 : ℚ))) (e : ZMod 2 × ZMod 2 ≃+ A)
    (h₁ : r (e (1, 0)) = q (1, 0)) (h₂ : r (e (0, 1)) = q (0, 1))
    (h₃ : r (e (1, 1)) = q (1, 1)) : q.IsometryEquiv r where
  toLinearEquiv := e.toIntLinearEquiv
  map_app' x := by
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    obtain ⟨c, d⟩ := x
    -- The linear and additive equivalences have definitionally equal coercions, so the named
    -- reflexive theorem `AddEquiv.coe_toIntLinearEquiv` gives `simp` no rewrite step here.
    change r (e (c, d)) = q (c, d)
    rcases hcases c with rfl | rfl <;> rcases hcases d with rfl | rfl
    · rw [Prod.mk_zero_zero, map_zero, map_zero, map_zero]
    · exact h₂
    · exact h₁
    · exact h₃

omit h₄α h₄β h₂γ in
@[simp]
theorem kleinFourIsometryOfGenerators_apply {A : Type*} [AddCommGroup A]
    (q : QuadraticMap ℤ (ZMod 2 × ZMod 2) (AddCircle (1 : ℚ)))
    (r : QuadraticMap ℤ A (AddCircle (1 : ℚ))) (e : ZMod 2 × ZMod 2 ≃+ A)
    (h₁ : r (e (1, 0)) = q (1, 0)) (h₂ : r (e (0, 1)) = q (0, 1))
    (h₃ : r (e (1, 1)) = q (1, 1))
    (x : ZMod 2 × ZMod 2) :
    kleinFourIsometryOfGenerators q r e h₁ h₂ h₃ x = e x := (rfl)

end FiniteQuadraticModule

end TauCeti
