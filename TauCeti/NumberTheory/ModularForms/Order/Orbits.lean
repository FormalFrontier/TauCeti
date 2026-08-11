/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing

import TauCeti.NumberTheory.Modular.Orbits
import TauCeti.NumberTheory.ModularForms.FiniteZeros

/-!
# The vanishing order on `SL(2, ℤ)`-orbits

The vanishing order of a level-one modular form is constant on `SL(2, ℤ)`-orbits of `ℍ`,
so it descends to the orbit space (`TauCeti.ModularForm.orderOfVanishingOnOrbit`), and for a nonzero
form only finitely many orbits carry nonzero order — the summation index of the valence
formula. The generic orbit facts it rides live in `TauCeti.NumberTheory.Modular.Orbits`.

## Main declarations

* `TauCeti.ModularForm.orderOfVanishingOnOrbit`: the order descended to
  `MulAction.orbitRel.Quotient SL(2, ℤ) ℍ`.
* `TauCeti.ModularForm.hasFiniteSupport_orderOfVanishingOnOrbit`: finite support on orbits for a
  nonzero form.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane

open scoped ModularForm MatrixGroups Modular

namespace TauCeti

namespace ModularForm

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] (f : F)


/-- The vanishing order of a level-one form, descended to `SL(2, ℤ)`-orbits of `ℍ`. -/
def orderOfVanishingOnOrbit [SlashInvariantFormClass F 𝒮ℒ k]
    (q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) : ℤ :=
  Quotient.liftOn' q (orderOfVanishingAt f) fun _ b ⟨g, hg⟩ ↦ by
    have hg' : g • b = _ := hg
    rw [← hg', MulAction.compHom_smul_def,
      orderOfVanishingAt_smul f (γ := Matrix.SpecialLinearGroup.mapGL ℝ g)
        (MonoidHom.mem_range.mpr ⟨g, rfl⟩) (by
          rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL]
          exact one_pos) b]

/-- Evaluating the descended order on the orbit of `p` recovers the vanishing order at
`p`. -/
@[simp]
lemma orderOfVanishingOnOrbit_mk [SlashInvariantFormClass F 𝒮ℒ k] (p : ℍ) :
    orderOfVanishingOnOrbit f (Quotient.mk'' p) = orderOfVanishingAt f p := by
  unfold orderOfVanishingOnOrbit
  rfl

/-- For a nonzero level-one form, only finitely many orbits carry nonzero order. -/
lemma hasFiniteSupport_orderOfVanishingOnOrbit [ModularFormClass F 𝒮ℒ k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) : (orderOfVanishingOnOrbit f).HasFiniteSupport := by
  rw [Function.HasFiniteSupport, Function.support]
  choose rep hrep_mk hrep_fd using ModularGroup.exists_rep_mem_fd
  have h_image : rep '' {q | orderOfVanishingOnOrbit f q ≠ 0} ⊆
      {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt f p ≠ 0} := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨hrep_fd q, by rwa [← orderOfVanishingOnOrbit_mk f (rep q), hrep_mk q]⟩
  have h_inj : Set.InjOn rep {q | orderOfVanishingOnOrbit f q ≠ 0} := fun q₁ _ q₂ _ h ↦ by
    rw [← hrep_mk q₁, ← hrep_mk q₂, h]
  exact ((finite_zeros_in_fd hf).subset h_image).of_finite_image h_inj

end ModularForm

end TauCeti

end
