/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import TauCeti.Analysis.Complex.Conformal.Moebius
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Conformal
import TauCeti.Analysis.Complex.Conformal.InverseFunction

/-!
# Conformal equivalence of simply connected domains

The Riemann mapping theorem says that a simply connected open proper subset of `ℂ` is
biholomorphic to the open unit disc. Because the disc is a single fixed model, this immediately
classifies such domains up to biholomorphism: *any two* of them are biholomorphic to each other,
and a single one is biholomorphic to itself in enough ways to move any prescribed point to any
other. This file proves those two statements, and the sharpness of the properness hypothesis.

## Main statements

* `TauCeti.exists_bijOn_differentiableOn_invFunOn_of_isSimplyConnected` — any two simply connected
  open proper subsets of `ℂ` are biholomorphic: there is a holomorphic bijection from one onto the
  other whose inverse is again holomorphic.
* `TauCeti.exists_openPartialHomeomorph_of_isSimplyConnected` and
  `TauCeti.nonempty_homeomorph_of_isSimplyConnected` — the same equivalence packaged as an
  `OpenPartialHomeomorph ℂ ℂ` conformal in both directions, and as a homeomorphism of subtypes.
* `TauCeti.exists_bijOn_self_apply_eq_of_isSimplyConnected` — homogeneity: the biholomorphic
  self-maps of a simply connected open proper `Ω ⊆ ℂ` act transitively on `Ω`.
* `TauCeti.Differentiable.exists_eq_const_of_isSimplyConnected` and
  `TauCeti.not_bijOn_univ_of_isSimplyConnected` — an entire function with values in a simply
  connected open proper set is constant, so `ℂ` itself is biholomorphic to no such set. This is
  why `Ω ≠ Set.univ` cannot be dropped from the statements above.

## Proof outline

Everything runs through the Riemann map. Transporting a domain `Ω` to the disc and a second domain
`Ω'` back off it composes to a biholomorphism `Ω ≃ Ω'`; the inverse of a holomorphic injection on
an open set is holomorphic by `TauCeti.DifferentiableOn.invFunOn`, so the composite inverse needs
no separate argument. Homogeneity inserts, between the two transports of one and the same domain,
a disc Moebius factor `z ↦ (z - a) / (1 - conj a * z)` composed with the factor centred at `-b`;
this disc automorphism carries `a` to `0` and then `0` to `b`. Sharpness is Liouville's theorem:
composing an entire map into `Ω` with the Riemann map of `Ω` gives a bounded entire function.

## Scope

The maps produced here are not canonical and are not asserted to be unique: the equivalences of a
simply connected domain with the disc form a torsor under `Aut(𝔻)`, as recorded in the sibling
`Uniqueness.lean` and `Normalization.lean`. Nothing here normalizes a choice.

## Coordination with upstream Mathlib

The Riemann mapping theorem is being formalized upstream at
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves the
L0–L3 prerequisites internally as private lemmas. These corollaries rest on the L3 shim in
`RiemannMapping/Existence.lean` and are themselves an explicitly **temporary shim**: once the
human-curated Mathlib theorem lands, they should be re-proved on top of it and their downstream
consumers refactored accordingly.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6 §1.
* J. B. Conway, *Functions of One Complex Variable I*, Ch. VII §4.
-/

public section

namespace TauCeti

open Complex Metric Set

variable {Ω Ω' : Set ℂ}

/-- The inverse of a Riemann map, as a bijection of the open unit disc onto the domain. -/
private lemma bijOn_invFunOn_of_bijOn_ball {g : ℂ → ℂ} (hbij : BijOn g Ω (ball 0 1)) :
    BijOn (Function.invFunOn g Ω) (ball 0 1) Ω :=
  BijOn.symm hbij.invOn_invFunOn.symm hbij

/-- A holomorphic bijection of an open set onto its image has a holomorphic inverse there.

This repackages `TauCeti.DifferentiableOn.invFunOn` with the image identified by a `Set.BijOn`
hypothesis, which is the form the constructions in this file produce. -/
private lemma differentiableOn_invFunOn_of_bijOn {f : ℂ → ℂ} (hΩo : IsOpen Ω)
    (hfd : DifferentiableOn ℂ f Ω) (hbij : BijOn f Ω Ω') :
    DifferentiableOn ℂ (Function.invFunOn f Ω) Ω' := by
  have hinv := TauCeti.DifferentiableOn.invFunOn hfd hΩo hbij.injOn
  rwa [hbij.image_eq] at hinv

/-- **Any two simply connected proper domains of `ℂ` are conformally equivalent.** If `Ω` and `Ω'`
are simply connected open proper subsets of `ℂ`, then some holomorphic `f` maps `Ω` bijectively
onto `Ω'`, and its inverse `Function.invFunOn f Ω` is holomorphic on `Ω'`.

Neither domain is required to be bounded, and no normalization is imposed: the map is one of a
whole `Aut(𝔻)`-torsor of such maps. Together with
`TauCeti.not_bijOn_univ_of_isSimplyConnected` this is a complete classification of the simply
connected domains of `ℂ` up to biholomorphism: there are exactly two classes, `ℂ` and everything
else. -/
theorem exists_bijOn_differentiableOn_invFunOn_of_isSimplyConnected
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ)
    (hΩ'o : IsOpen Ω') (hΩ'c : IsSimplyConnected Ω') (hΩ' : Ω' ≠ univ) :
    ∃ f : ℂ → ℂ, BijOn f Ω Ω' ∧ DifferentiableOn ℂ f Ω ∧
      DifferentiableOn ℂ (Function.invFunOn f Ω) Ω' ∧
      LeftInvOn (Function.invFunOn f Ω) f Ω ∧
      RightInvOn (Function.invFunOn f Ω) f Ω' := by
  obtain ⟨g, hgbij, hgd, -⟩ := riemannMapping hΩo hΩc hΩ
  obtain ⟨h, hhbij, -, hhinvd, -, -⟩ :=
    exists_bijOn_ball_differentiableOn_invFunOn hΩ'o hΩ'c hΩ'
  have hbij : BijOn (Function.invFunOn h Ω' ∘ g) Ω Ω' :=
    (bijOn_invFunOn_of_bijOn_ball hhbij).comp hgbij
  have hfd : DifferentiableOn ℂ (Function.invFunOn h Ω' ∘ g) Ω :=
    hhinvd.comp hgd hgbij.mapsTo
  exact ⟨_, hbij, hfd, differentiableOn_invFunOn_of_bijOn hΩo hfd hbij,
    hbij.injOn.leftInvOn_invFunOn, hbij.surjOn.rightInvOn_invFunOn⟩

/-- **Conformal equivalence of simply connected proper domains, packaged.** The biholomorphism of
`TauCeti.exists_bijOn_differentiableOn_invFunOn_of_isSimplyConnected` as an
`OpenPartialHomeomorph ℂ ℂ` whose source is `Ω` and whose target is `Ω'`, holomorphic and conformal
in both directions.

This is the packaged-equivalence companion the generality bar of
`TauCetiRoadmap/ConformalMapping/README.md` asks for, in the same form as
`TauCeti.riemannMapping_openPartialHomeomorph` for the disc. -/
theorem exists_openPartialHomeomorph_of_isSimplyConnected
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ)
    (hΩ'o : IsOpen Ω') (hΩ'c : IsSimplyConnected Ω') (hΩ' : Ω' ≠ univ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      e.source = Ω ∧
      e.target = Ω' ∧
      DifferentiableOn ℂ e Ω ∧
      DifferentiableOn ℂ e.symm Ω' ∧
      (∀ z ∈ Ω, ConformalAt e z) ∧
      ∀ w ∈ Ω', ConformalAt e.symm w := by
  obtain ⟨f, hbij, hfd, -, -, -⟩ :=
    exists_bijOn_differentiableOn_invFunOn_of_isSimplyConnected hΩo hΩc hΩ hΩ'o hΩ'c hΩ'
  refine ⟨TauCeti.DifferentiableOn.toOpenPartialHomeomorph hfd hΩo hbij.injOn,
    TauCeti.DifferentiableOn.toOpenPartialHomeomorph_source hfd hΩo hbij.injOn,
    (TauCeti.DifferentiableOn.toOpenPartialHomeomorph_target hfd hΩo hbij.injOn).trans
      hbij.image_eq, ?_, ?_, ?_, ?_⟩
  · rw [TauCeti.DifferentiableOn.toOpenPartialHomeomorph_coe hfd hΩo hbij.injOn]
    exact hfd
  · have hinv :=
      TauCeti.DifferentiableOn.differentiableOn_toOpenPartialHomeomorph_symm hfd hΩo hbij.injOn
    simpa only [hbij.image_eq] using hinv
  · exact fun z hz =>
      TauCeti.DifferentiableOn.conformalAt_toOpenPartialHomeomorph hfd hΩo hbij.injOn hz
  · exact fun w hw =>
      TauCeti.DifferentiableOn.conformalAt_toOpenPartialHomeomorph_symm hfd hΩo hbij.injOn
        (hbij.image_eq ▸ hw)

/-- **Any two simply connected proper domains of `ℂ` are homeomorphic**, by a homeomorphism of
subtypes induced by a biholomorphism. -/
theorem nonempty_homeomorph_of_isSimplyConnected
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ)
    (hΩ'o : IsOpen Ω') (hΩ'c : IsSimplyConnected Ω') (hΩ' : Ω' ≠ univ) :
    Nonempty (Ω ≃ₜ Ω') := by
  obtain ⟨f, hbij, hfd, -, -, -⟩ :=
    exists_bijOn_differentiableOn_invFunOn_of_isSimplyConnected hΩo hΩc hΩ hΩ'o hΩ'c hΩ'
  exact ⟨TauCeti.DifferentiableOn.toHomeomorphOfBijOn hfd hΩo hbij⟩

/-- A disc automorphism carrying a prescribed point of the open unit disc to another: the Moebius
factor centred at `a`, which sends `a` to `0`, followed by the factor centred at `-b`, which sends
`0` to `b`. -/
private lemma exists_bijOn_ball_apply_eq {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ∃ φ : ℂ → ℂ, BijOn φ (ball 0 1) (ball 0 1) ∧ DifferentiableOn ℂ φ (ball 0 1) ∧ φ a = b := by
  have hnb : ‖(-b : ℂ)‖ < 1 := by simpa using hb
  refine ⟨(fun w : ℂ => (w - (-b)) / (1 - (starRingEnd ℂ) (-b) * w)) ∘
      fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z), ?_, ?_, ?_⟩
  · exact (bijOn_ball_unitDiscMoebiusFormula_of_norm_lt_one hnb).comp
      (bijOn_ball_unitDiscMoebiusFormula_of_norm_lt_one ha)
  · exact (differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one hnb).comp
      (differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one ha)
      (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha)
  · simp

/-- **A simply connected proper domain is homogeneous.** The biholomorphic self-maps of a simply
connected open proper `Ω ⊆ ℂ` act transitively on `Ω`: given `z₀, z₁ ∈ Ω` there is a holomorphic
bijection of `Ω` onto itself, with holomorphic inverse, carrying `z₀` to `z₁`.

Transitivity is inherited from the disc, where the Moebius factors already act transitively; the
Riemann map transports the action. It fails badly without simple connectivity — the punctured disc,
for instance, is not homogeneous. -/
theorem exists_bijOn_self_apply_eq_of_isSimplyConnected
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) {z₀ z₁ : ℂ}
    (hz₀ : z₀ ∈ Ω) (hz₁ : z₁ ∈ Ω) :
    ∃ f : ℂ → ℂ, BijOn f Ω Ω ∧ DifferentiableOn ℂ f Ω ∧
      DifferentiableOn ℂ (Function.invFunOn f Ω) Ω ∧ f z₀ = z₁ := by
  obtain ⟨g, hgbij, hgd, hginvd, hgleft, -⟩ :=
    exists_bijOn_ball_differentiableOn_invFunOn hΩo hΩc hΩ
  have ha : ‖g z₀‖ < 1 := by simpa [mem_ball_zero_iff] using hgbij.mapsTo hz₀
  have hb : ‖g z₁‖ < 1 := by simpa [mem_ball_zero_iff] using hgbij.mapsTo hz₁
  obtain ⟨φ, hφbij, hφd, hφa⟩ := exists_bijOn_ball_apply_eq ha hb
  have hbij : BijOn ((Function.invFunOn g Ω ∘ φ) ∘ g) Ω Ω :=
    ((bijOn_invFunOn_of_bijOn_ball hgbij).comp hφbij).comp hgbij
  have hfd : DifferentiableOn ℂ ((Function.invFunOn g Ω ∘ φ) ∘ g) Ω :=
    (hginvd.comp hφd hφbij.mapsTo).comp hgd hgbij.mapsTo
  refine ⟨_, hbij, hfd, differentiableOn_invFunOn_of_bijOn hΩo hfd hbij, ?_⟩
  simpa [Function.comp_def, hφa] using hgleft hz₁

/-- **An entire function with values in a simply connected proper domain is constant.** Composing
with the Riemann map of `Ω` turns such a function into a bounded entire function, which Liouville's
theorem forces to be constant; the Riemann map is injective, so the original function is constant
too.

For bounded `Ω` this is Liouville's theorem itself, but the statement covers unbounded `Ω` such as
the slit plane, where the Riemann map is doing genuine work. -/
theorem Differentiable.exists_eq_const_of_isSimplyConnected {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) (hmaps : ∀ z, f z ∈ Ω) :
    ∃ c, ∀ z, f z = c := by
  obtain ⟨r, hrbij, hrd, -⟩ := riemannMapping hΩo hΩc hΩ
  have hcomp : Differentiable ℂ (r ∘ f) := fun z =>
    (hrd.differentiableAt (hΩo.mem_nhds (hmaps z))).comp z (hf z)
  have hbdd : Bornology.IsBounded (Set.range (r ∘ f)) :=
    Metric.isBounded_ball.subset (by
      rintro _ ⟨z, rfl⟩
      exact hrbij.mapsTo (hmaps z))
  exact ⟨f 0, fun z =>
    hrbij.injOn (hmaps z) (hmaps 0) (hcomp.apply_eq_apply_of_bounded hbdd z 0)⟩

/-- **`ℂ` is conformally equivalent to no simply connected proper domain.** No entire function maps
`ℂ` bijectively onto a simply connected open proper subset of `ℂ`, since by
`TauCeti.Differentiable.exists_eq_const_of_isSimplyConnected` it would be constant.

So the properness hypothesis in
`TauCeti.exists_bijOn_differentiableOn_invFunOn_of_isSimplyConnected` cannot be dropped: `ℂ` is a
simply connected domain lying in a biholomorphism class of its own. -/
theorem not_bijOn_univ_of_isSimplyConnected {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) :
    ¬ BijOn f univ Ω := by
  intro hbij
  obtain ⟨c, hc⟩ :=
    Differentiable.exists_eq_const_of_isSimplyConnected hf hΩo hΩc hΩ fun z =>
      hbij.mapsTo (mem_univ z)
  exact zero_ne_one (hbij.injOn (mem_univ 0) (mem_univ 1) ((hc 0).trans (hc 1).symm))

end TauCeti
