/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.NumberTheory.Modular
public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing

import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.NumberTheory.Modular.Orbits
import TauCeti.NumberTheory.ModularForms.FiniteZeros

/-!
# The vanishing order on `SL(2, ℤ)`-orbits

The vanishing order of a level-one modular form is constant on `SL(2, ℤ)`-orbits of `ℍ`,
so it descends to the orbit space (`TauCeti.ModularForm.orderOfVanishingOnOrbit`), and only
finitely many orbits carry nonzero order — the summation index of the valence formula. No
nonvanishing hypothesis is needed: the zero form has order `0` on every orbit, so its support is
empty. The generic orbit facts it rides live in `TauCeti.NumberTheory.Modular.Orbits`.

## Main declarations

* `TauCeti.ModularForm.orderOfVanishingOnOrbit`: the order descended to
  `MulAction.orbitRel.Quotient SL(2, ℤ) ℍ`.
* `TauCeti.ModularForm.hasFiniteSupport_orderOfVanishingOnOrbit`: finite support on orbits, the
  zero form having empty support.
* `TauCeti.ModularForm.sum_orderOfVanishingAt_eq_finsum_orbit`: a divisor sum over an arbitrary
  index set, reindexed over the orbits its points represent, given that the index-to-orbit
  composite is injective.
* `TauCeti.ModularForm.sum_orderOfVanishingAt_ofComplex_eq_finsum_orbit`: the same for the
  valence formula's own divisor sum, whose points are complex numbers carrying the interior
  bounds.
* `TauCeti.ModularForm.orderOfVanishingOnOrbit_eq_zero_of_notMem`: an orbit outside a set of
  orbits complete for `f`'s nonzero-order points on `𝒟` carries vanishing order zero.
* `TauCeti.ModularForm.NonEllipticOrbit`: the orbits other than those of the elliptic points
  `i` and `ρ` — the index type of the valence formula's divisor sum.
* `TauCeti.ModularForm.hasFiniteSupport_orderOfVanishingOnOrbit_nonElliptic`: the finite
  support restricted to the non-elliptic orbits.

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
        (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
        (det_pos_of_mem_slGL (MonoidHom.mem_range.mpr ⟨g, rfl⟩)) b]

/-- Evaluating the descended order on the orbit of `p` recovers the vanishing order at
`p`. -/
@[simp]
lemma orderOfVanishingOnOrbit_mk [SlashInvariantFormClass F 𝒮ℒ k] (p : ℍ) :
    orderOfVanishingOnOrbit f (Quotient.mk'' p) = orderOfVanishingAt f p := by
  unfold orderOfVanishingOnOrbit
  rfl

/-- Only finitely many orbits of a level-one form carry nonzero order. -/
lemma hasFiniteSupport_orderOfVanishingOnOrbit [ModularFormClass F 𝒮ℒ k] (f : F) :
    (orderOfVanishingOnOrbit f).HasFiniteSupport :=
  -- the `rfl` pattern rewrites `q` to `⟦p⟧`, after which `orderOfVanishingOnOrbit_mk` fires
  (finite_zeros_in_fd (f := f)).of_surjOn Quotient.mk'' fun q hq ↦
    (ModularGroup.exists_rep_mem_fd q).imp fun p ⟨rfl, hfd⟩ ↦ ⟨⟨hfd, by simpa using hq⟩, rfl⟩

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

/-- **The missing completeness step.** An orbit outside a set `S` that catches every
fundamental-domain point of nonzero order carries vanishing order zero. Completeness means `hS`:
every `p ∈ 𝒟` with `orderOfVanishingAt f p ≠ 0` has its orbit `⟦p⟧` inside `S`, the same idiom
`hasFiniteSupport_orderOfVanishingOnOrbit` uses over `𝒟`.

⚠ This does **not** by itself extend `sum_orderOfVanishingAt_ofComplex_eq_finsum_orbit`'s
image-indexed `∑ᶠ` to the whole orbit space. Instantiated at that lemma's orbit map, `hS` ranges
over the *closed* `𝒟`, which holds the elliptic points `i` and `ρ` (`‖i‖ = ‖ρ‖ = 1`), whereas that
lemma confines its divisor set to the *open* `𝒟ᵒ`. For a form of nonzero order at `i` or `ρ` the
two demands cannot both hold — those are exactly the points the valence formula weights by `1/2`
and `1/3` instead of counting into the divisor sum. Reaching the roadmap's non-elliptic orbit
space still needs separate treatment of the elliptic orbits. -/
lemma orderOfVanishingOnOrbit_eq_zero_of_notMem [SlashInvariantFormClass F 𝒮ℒ k]
    {S : Set (MulAction.orbitRel.Quotient SL(2, ℤ) ℍ)}
    (hS : ∀ p ∈ 𝒟, orderOfVanishingAt f p ≠ 0 →
      (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ∈ S)
    {q} (hq : q ∉ S) : orderOfVanishingOnOrbit f q = 0 := by
  -- `q`'s representative `p ∈ 𝒟` (`ModularGroup.exists_rep_mem_fd`) would, if its order were
  -- nonzero, put `q` itself into `S` via `hS` (order is orbit-constant,
  -- `orderOfVanishingOnOrbit_mk`), contradicting `hq`
  by_contra hne
  obtain ⟨p, rfl, hpfd⟩ := ModularGroup.exists_rep_mem_fd q
  rw [orderOfVanishingOnOrbit_mk] at hne
  exact hq (hS p hpfd hne)

/-- The non-elliptic orbits of `SL(2, ℤ)` on `ℍ`: all orbits except the two elliptic ones, of
`i` and of `ρ`. The valence formula's divisor sum is indexed by this type — the elliptic
orbits enter the formula through fractional weights instead. -/
abbrev NonEllipticOrbit : Type :=
  {q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ //
    q ≠ Quotient.mk'' I ∧ q ≠ Quotient.mk'' ρ}

/-- Only finitely many non-elliptic orbits of a level-one form carry nonzero order: the finite
support of `orderOfVanishingOnOrbit`, restricted along the inclusion of the non-elliptic
orbits. -/
lemma hasFiniteSupport_orderOfVanishingOnOrbit_nonElliptic [ModularFormClass F 𝒮ℒ k] (f : F) :
    Function.HasFiniteSupport fun q : NonEllipticOrbit ↦ orderOfVanishingOnOrbit f q.val :=
  Function.HasFiniteSupport.fun_comp_of_injective Subtype.val_injective
    (hasFiniteSupport_orderOfVanishingOnOrbit f)

end ModularForm

end TauCeti

end
