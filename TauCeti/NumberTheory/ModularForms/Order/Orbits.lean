/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
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
* `TauCeti.ModularForm.sum_orderOfVanishingAt_eq_finsum_orbit`: a divisor sum over an arbitrary
  index set, reindexed over the orbits its points represent, given that the index-to-orbit
  composite is injective.
* `TauCeti.ModularForm.sum_orderOfVanishingAt_ofComplex_eq_finsum_orbit`: the same for the
  valence formula's own divisor sum, whose points are complex numbers carrying the interior
  bounds.

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

/-- A divisor sum reindexed over the orbits its points represent. The index set is arbitrary,
mapped into `ℍ` by `p`.

The hypothesis is that the **composite** `a ↦ ⟦p a⟧` is injective on `X`, which is what makes the
reindexing lossless. That is strictly more than asking the orbit map to be injective on `p '' X`:
it also rules out distinct indices with the same `p`, since those would contribute twice on the
left and once on the right.

For `p` injective — `ofComplex` on the upper half plane, say — the composite's injectivity
reduces to the orbit map's, which `ModularGroup.orbit_mk_injOn_fdo.mono` supplies on the **open**
fundamental domain. The open domain is genuinely needed there: on the closed `𝒟` the orbit map is
not injective, since `T` identifies the two vertical edges and `S` the two halves of the arc, so a
set holding two identified boundary representatives would count their common orbit twice. -/
lemma sum_orderOfVanishingAt_eq_finsum_orbit [SlashInvariantFormClass F 𝒮ℒ k] {α : Type*}
    {X : Finset α} (p : α → ℍ)
    (hX : Set.InjOn (fun a ↦ (Quotient.mk'' (p a) :
      MulAction.orbitRel.Quotient SL(2, ℤ) ℍ)) ↑X) :
    ∑ a ∈ X, orderOfVanishingAt f (p a) =
      ∑ᶠ q ∈ (fun a ↦ (Quotient.mk'' (p a) :
          MulAction.orbitRel.Quotient SL(2, ℤ) ℍ)) '' ↑X,
        orderOfVanishingOnOrbit f q := by
  rw [finsum_mem_image hX]
  simp only [orderOfVanishingOnOrbit_mk]
  exact (finsum_mem_coe_finset _ X).symm

/-- The divisor sum of the valence formula, whose points are complex numbers carrying the
interior bounds, reindexed over the orbits they represent — the case `p := ofComplex` of
`sum_orderOfVanishingAt_eq_finsum_orbit`.

The index is a `Set` image rather than a `Finset` one, which keeps the statement free of a
classical `DecidableEq (MulAction.orbitRel.Quotient SL(2, ℤ) ℍ)` instance — the image elements are
orbits, so that, not `DecidableEq ℍ`, is what a `Finset` image would need.

The three hypotheses are the interior bounds the valence formula carries: positivity puts each
point in `ℍ`, and the radial and real-part bounds put it in the open fundamental domain, where
distinct points represent distinct orbits. -/
lemma sum_orderOfVanishingAt_ofComplex_eq_finsum_orbit [SlashInvariantFormClass F 𝒮ℒ k]
    {X : Finset ℂ} (hpos : ∀ z ∈ X, 0 < z.im) (hnorm : ∀ z ∈ X, 1 < ‖z‖)
    (hre : ∀ z ∈ X, |z.re| < 1 / 2) :
    ∑ z ∈ X, orderOfVanishingAt f (ofComplex z) =
      ∑ᶠ q ∈ (fun z : ℂ ↦ (Quotient.mk'' (ofComplex z) :
          MulAction.orbitRel.Quotient SL(2, ℤ) ℍ)) '' ↑X,
        orderOfVanishingOnOrbit f q := by
  have hcoe : ∀ z ∈ X, ((ofComplex z : ℍ) : ℂ) = z := fun z hz =>
    congrArg _ (ofComplex_apply_of_im_pos (hpos z hz))
  refine sum_orderOfVanishingAt_eq_finsum_orbit f ofComplex fun a ha b hb hab => ?_
  have ha' : a ∈ X := by simpa using ha
  have hb' : b ∈ X := by simpa using hb
  have hfdo : ∀ z ∈ X, ofComplex z ∈ 𝒟ᵒ := fun z hz => by
    obtain ⟨τ, hτ, hτz⟩ : z ∈ UpperHalfPlane.coe '' 𝒟ᵒ := by
      rw [ModularGroup.coe_fdo]; exact ⟨hpos z hz, hnorm z hz, hre z hz⟩
    have hof : ofComplex z = τ := UpperHalfPlane.coe_injective ((hcoe z hz).trans hτz.symm)
    rw [hof]
    exact hτ
  have h : ofComplex a = ofComplex b :=
    ModularGroup.orbit_mk_injOn_fdo (hfdo a ha') (hfdo b hb') hab
  exact (hcoe a ha').symm.trans ((congrArg (fun w : ℍ ↦ (w : ℂ)) h).trans (hcoe b hb'))

end ModularForm

end TauCeti

end
