/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Conformal
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Group
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

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
* `TauCeti.exists_openPartialHomeomorph_of_isSimplyConnected` — the same equivalence packaged as an
  `OpenPartialHomeomorph ℂ ℂ` conformal in both directions.
* `TauCeti.nonempty_homeomorph_of_isSimplyConnected` — any two simply connected open subsets of `ℂ`
  are homeomorphic as subtypes. Merely topologically, properness is not needed: the plane too is
  homeomorphic to the disc.
* `TauCeti.exists_bijOn_self_apply_eq_of_isSimplyConnected` — homogeneity: the biholomorphic
  self-maps of a simply connected open `Ω ⊆ ℂ` act transitively on `Ω`.
* `TauCeti.Differentiable.exists_const_forall_eq_of_isSimplyConnected`,
  `TauCeti.not_injOn_univ_of_isSimplyConnected` and
  `TauCeti.not_bijOn_univ_of_isSimplyConnected` — an entire function with values in a simply
  connected open proper set is constant, hence not injective, so `ℂ` itself is biholomorphic to no
  such set. This is why `Ω ≠ Set.univ` cannot be dropped from the *biholomorphic* equivalence
  statements above. Homogeneity needs no properness hypothesis either: `Ω = Set.univ` is
  homogeneous too, because the translations already act transitively on `ℂ`.

## Proof outline

Everything runs through the Riemann map. Transporting a domain `Ω` to the disc and a second domain
`Ω'` back off it composes to a biholomorphism `Ω ≃ Ω'`; the inverse of a holomorphic injection on
an open set is holomorphic by `TauCeti.DifferentiableOn.invFunOn`, so the composite inverse needs
no separate argument. Homogeneity inserts, between the two transports of one and the same domain,
a disc automorphism carrying one image point to the other; that automorphism is supplied by the
transitivity of `TauCeti.unitDiscAut` and read back as a scalar map. The whole plane, which has no
Riemann map, is handled separately in the two statements that admit it: by a translation for
homogeneity, and by `Homeomorph.unitBall` for the merely topological equivalence. Sharpness is
Liouville's theorem: composing an entire map into `Ω` with the Riemann map of `Ω` gives a bounded
entire function.

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

open _root_.Complex Metric Set

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

/-- **Conformal equivalence of simply connected proper domains, packaged.** A biholomorphism of
`Ω` onto `Ω'` as an `OpenPartialHomeomorph ℂ ℂ` whose source is `Ω` and whose target is `Ω'`,
holomorphic and conformal in both directions. It is the Riemann map of `Ω` followed by the inverse
of the Riemann map of `Ω'`, both taken from `TauCeti.riemannMapping_openPartialHomeomorph`.

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
  obtain ⟨e, hesrc, htgt, hed, hesymmd, hec, hesymmc⟩ :=
    riemannMapping_openPartialHomeomorph hΩo hΩc hΩ
  obtain ⟨e', hesrc', htgt', hed', hesymmd', hec', hesymmc'⟩ :=
    riemannMapping_openPartialHomeomorph hΩ'o hΩ'c hΩ'
  have hmaps : MapsTo e Ω (ball (0 : ℂ) 1) := fun z hz => htgt ▸ e.map_source (hesrc ▸ hz)
  have hmaps' : MapsTo e' Ω' (ball (0 : ℂ) 1) := fun w hw => htgt' ▸ e'.map_source (hesrc' ▸ hw)
  refine ⟨e.trans e'.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, hesrc, htgt']
    exact inter_eq_left.2 hmaps
  · rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.symm_symm, hesrc', htgt]
    exact inter_eq_left.2 hmaps'
  · rw [OpenPartialHomeomorph.coe_trans]
    exact hesymmd'.comp hed hmaps
  · rw [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm]
    exact hesymmd.comp hed' hmaps'
  · intro z hz
    rw [OpenPartialHomeomorph.coe_trans]
    exact ConformalAt.comp z (hesymmc' _ (hmaps hz)) (hec z hz)
  · intro w hw
    rw [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm]
    exact ConformalAt.comp w (hesymmc _ (hmaps' hw)) (hec' w hw)

/-- **Every simply connected domain of `ℂ` is homeomorphic to the disc**, properness included.
For a proper domain this is `TauCeti.riemannMapping_homeomorph`; the whole plane is homeomorphic
to the disc as well, by `Homeomorph.unitBall`, even though it is not biholomorphic to it. -/
private lemma nonempty_homeomorph_unitDisc_of_isSimplyConnected
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) :
    Nonempty (Ω ≃ₜ Complex.UnitDisc) := by
  rcases eq_or_ne Ω univ with rfl | hΩ
  · exact ⟨(Homeomorph.Set.univ ℂ).trans Homeomorph.unitBall⟩
  · exact riemannMapping_homeomorph hΩo hΩc hΩ

/-- **Any two simply connected domains of `ℂ` are homeomorphic**, as subtypes.

Unlike the biholomorphism statements above this needs no properness hypothesis: the plane is not
biholomorphic to the disc, but it is homeomorphic to it. -/
theorem nonempty_homeomorph_of_isSimplyConnected
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω)
    (hΩ'o : IsOpen Ω') (hΩ'c : IsSimplyConnected Ω') :
    Nonempty (Ω ≃ₜ Ω') := by
  obtain ⟨e⟩ := nonempty_homeomorph_unitDisc_of_isSimplyConnected hΩo hΩc
  obtain ⟨e'⟩ := nonempty_homeomorph_unitDisc_of_isSimplyConnected hΩ'o hΩ'c
  exact ⟨e.trans e'.symm⟩

/-- A holomorphic automorphism of the open unit disc carrying a prescribed point to another, as a
scalar map of `Metric.ball 0 1`.

The automorphism comes from the transitivity of `TauCeti.unitDiscAut` on `Complex.UnitDisc`,
namely `TauCeti.exists_mem_unitDiscAut_apply_eq`; the classification
`TauCeti.mem_unitDiscAut_iff` then names its scalar formula, whose holomorphy is
`TauCeti.differentiableOn_unitDiscStandardAutomorphismFormula`. -/
private lemma exists_bijOn_ball_apply_eq {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ∃ φ : ℂ → ℂ, BijOn φ (ball 0 1) (ball 0 1) ∧ DifferentiableOn ℂ φ (ball 0 1) ∧ φ a = b := by
  obtain ⟨e, he, hab⟩ :=
    exists_mem_unitDiscAut_apply_eq (Complex.UnitDisc.mk a ha) (Complex.UnitDisc.mk b hb)
  obtain ⟨u, c, rfl⟩ := mem_unitDiscAut_iff.1 he
  refine ⟨_, bijOn_ball_of_unitDiscEquiv _ (coe_unitDiscStandardAutomorphismEquiv_apply u c),
    differentiableOn_unitDiscStandardAutomorphismFormula u c, ?_⟩
  have hval := coe_unitDiscStandardAutomorphismEquiv_apply u c (Complex.UnitDisc.mk a ha)
  rw [hab] at hval
  simpa using hval.symm

/-- **A simply connected domain is homogeneous.** The biholomorphic self-maps of a simply
connected open `Ω ⊆ ℂ` act transitively on `Ω`: given `z₀, z₁ ∈ Ω` there is a holomorphic
bijection of `Ω` onto itself, with holomorphic inverse, carrying `z₀` to `z₁`.

Unlike the equivalence statements above, this needs no properness hypothesis: for `Ω = Set.univ`
the translation `z ↦ z + (z₁ - z₀)` already does the job. Otherwise transitivity is inherited from
the disc, where `TauCeti.unitDiscAut` already acts transitively, and the Riemann map transports the
action. It fails badly without simple connectivity — the punctured disc, for instance, is not
homogeneous. -/
theorem exists_bijOn_self_apply_eq_of_isSimplyConnected
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) {z₀ z₁ : ℂ}
    (hz₀ : z₀ ∈ Ω) (hz₁ : z₁ ∈ Ω) :
    ∃ f : ℂ → ℂ, BijOn f Ω Ω ∧ DifferentiableOn ℂ f Ω ∧
      DifferentiableOn ℂ (Function.invFunOn f Ω) Ω ∧ f z₀ = z₁ := by
  rcases eq_or_ne Ω univ with rfl | hΩ
  · have hbij : BijOn (· + (z₁ - z₀)) (univ : Set ℂ) univ :=
      (Equiv.addRight (z₁ - z₀)).bijective.bijOn_univ
    have hfd : DifferentiableOn ℂ (· + (z₁ - z₀)) (univ : Set ℂ) :=
      (differentiable_id.add_const _).differentiableOn
    refine ⟨_, hbij, hfd, differentiableOn_invFunOn_of_bijOn hΩo hfd hbij, ?_⟩
    ring
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
theorem Differentiable.exists_const_forall_eq_of_isSimplyConnected {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ)
    (hmaps : ∀ z, f z ∈ Ω) :
    ∃ c, ∀ z, f z = c := by
  obtain ⟨r, hrbij, hrd, -⟩ := riemannMapping hΩo hΩc hΩ
  have hcomp : Differentiable ℂ (r ∘ f) := fun z =>
    (hrd.differentiableAt (hΩo.mem_nhds (hmaps z))).comp z (hf z)
  have hbdd : Bornology.IsBounded (Set.range (r ∘ f)) :=
    Metric.isBounded_ball.subset (by
      rintro _ ⟨z, rfl⟩
      exact hrbij.mapsTo (hmaps z))
  obtain ⟨c, hc⟩ := hcomp.exists_const_forall_eq_of_bounded hbdd
  exact ⟨f 0, fun z => hrbij.injOn (hmaps z) (hmaps 0) ((hc z).trans (hc 0).symm)⟩

/-- **No injective entire function takes its values in a simply connected proper domain.** Such a
function is constant by `TauCeti.Differentiable.exists_const_forall_eq_of_isSimplyConnected`, and a
constant map on `ℂ` is not injective.

Only the values of `f` are constrained, not the image: `f` is not required to cover `Ω`. -/
theorem not_injOn_univ_of_isSimplyConnected {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) (hmaps : MapsTo f univ Ω) :
    ¬ InjOn f univ := by
  intro hinj
  obtain ⟨c, hc⟩ :=
    Differentiable.exists_const_forall_eq_of_isSimplyConnected hf hΩo hΩc hΩ fun z =>
      hmaps (mem_univ z)
  exact zero_ne_one (hinj (mem_univ 0) (mem_univ 1) ((hc 0).trans (hc 1).symm))

/-- **`ℂ` is conformally equivalent to no simply connected proper domain.** No entire function maps
`ℂ` bijectively onto a simply connected open proper subset of `ℂ`: it is already barred from being
injective there by `TauCeti.not_injOn_univ_of_isSimplyConnected`.

So the properness hypothesis in
`TauCeti.exists_bijOn_differentiableOn_invFunOn_of_isSimplyConnected` cannot be dropped: `ℂ` is a
simply connected domain lying in a biholomorphism class of its own. -/
theorem not_bijOn_univ_of_isSimplyConnected {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) :
    ¬ BijOn f univ Ω := fun hbij =>
  not_injOn_univ_of_isSimplyConnected hf hΩo hΩc hΩ hbij.mapsTo hbij.injOn

end TauCeti
