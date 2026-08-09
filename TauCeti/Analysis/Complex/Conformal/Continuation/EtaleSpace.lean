/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.EtaleSpace
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The étalé space of holomorphic germs

The germs of holomorphic functions at all points of the plane at once form a topological space,
the **étalé space** of the sheaf of holomorphic functions, and the map sending a germ to the point
it is a germ at is a local homeomorphism. Analytic continuation of a germ along a path is then
nothing but a continuous lift of that path through this projection, and the classical facts about
continuation — uniqueness along a fixed path, invariance under homotopy — become the general
covering-space facts about lifts.

This file builds that space and supplies the one analytic input the general theory needs, which
`TauCeti/Topology/Sheaves/EtaleSpace.lean` names in its own docstring and leaves open:

> the projection is a **separated map** — two *distinct* germs at one point are separated by
> disjoint neighbourhoods in the étalé space.

Separatedness is the identity theorem in disguise, and it is genuinely analytic rather than
formal — for the sheaf of *continuous* functions the same projection is not separated: the germs
at `0` of the zero function and of `z ↦ (max z.re 0 : ℂ)` are distinct, yet the two functions
agree on the open half plane `z.re < 0`, so they have the *same* germ at every point of it, and
points of that half plane accumulate at `0`; every neighbourhood of the one germ at `0` therefore
meets every neighbourhood of the other. Two germs at `z` are
represented by functions holomorphic on a common ball `B` around `z`; if every neighbourhood of the
first germ met every neighbourhood of the second, the two representatives would share a germ at
some point of `B`, hence agree on a nonempty open subset of `B`, hence — `B` being connected —
agree on all of `B` and already have the same germ at `z`.

With `TauCeti.isLocalHomeomorph_holomorphicGerm_base` (the general étalé-space fact) and
`TauCeti.isSeparatedMap_holomorphicGerm_base` (the analytic one) in place, Mathlib's abstract
lifting theory applies verbatim, and the two statements this file draws from it are
`TauCeti.holomorphicGerm_eqOn_of_base_eqOn` — a lift is determined by its value at one
point — and `TauCeti.monodromy_theorem_holomorphicGerm`, Mathlib's
`IsLocalHomeomorph.monodromy_theorem` at this space.

## What is and is not proved here

The étalé space is not empty of content: `TauCeti.holomorphicGermOf` puts the germ of a function
holomorphic on an open set `U` at each point of `U` into it, and
`TauCeti.continuous_holomorphicGermOf` says that this assignment is continuous, so every
holomorphic function on `U` *is* a lift of `U`, and `TauCeti.exists_holomorphicGermOf_eq` says
that nothing else is in the space. The fibre over a point genuinely has more than one element (the
closing `example`), so separatedness is not the trivial consequence of an injective projection.

What is **not** done here is the bridge to `Conformal/Continuation/Basic.lean`: the predicate
`TauCeti.IsAnalyticContinuationAlong` carries a *family of germs indexed by the parameter*, and
identifying such a family with a continuous lift of the path is a separate translation, not
performed below. Consequently `TauCeti.monodromy_theorem_holomorphicGerm` and
`TauCeti.monodromy_theorem` of `Conformal/Monodromy.lean` are statements about two different
presentations of continuation; neither is proved from the other here, and the germ-family proof in
`Conformal/Monodromy.lean` is untouched.

## Design of the sheaf

The sheaf is `TopCat.subsheafToTypes` applied to the local predicate "is the restriction of a
function holomorphic on `U`" (`TauCeti.holomorphicLocalPredicate`). Phrasing the predicate through
an ambient `g : ℂ → ℂ` rather than through a differentiability notion for maps out of the subtype
`↥U` keeps every proof inside Mathlib's `DifferentiableOn`/`AnalyticOnNhd` API: `U` is open, so
`DifferentiableOn ℂ g U` depends only on the restriction of `g` to `U`, which makes the predicate
well behaved under restriction, and locality is witnessed by extending the given section by zero.

## Generality

The values are scalar `ℂ`, as `TauCetiRoadmap/ConformalMapping/README.md` fixes for every theorem
its layers L0–L6 add. The presheaf machinery would force the choice in any case: a type family
`T : X → Type v` over `X : TopCat.{v}` with `X = TopCat.of ℂ` has `v = 0`, so germs of maps into a
Banach space `E` would require `E : Type 0`, an artificial restriction rather than a
generalisation. The base is the whole plane; a germ on a domain `Ω ⊆ ℂ` is a germ on `ℂ` at a point
of `Ω`, and paths in `Ω` are paths in `ℂ`, so nothing is lost by not carrying `Ω` through the
construction.

## Relation to the roadmap and to Mathlib

`TauCetiRoadmap/ConformalMapping/README.md` layer **L4** asks for analytic continuation and the
monodromy theorem. Mathlib's `IsLocalHomeomorph.monodromy_theorem`
(`Mathlib/Topology/Homotopy/Lifting.lean`) is stated for a separated local homeomorphism and its
docstring names germs of analytic functions as the intended application, observing that the
separatedness is "because two analytic functions agreeing on a nonempty open set agree on the whole
connected component"; that application is what this file makes available. Mathlib has the étalé
space of a presheaf (`Mathlib/Topology/Sheaves/EtaleSpace.lean`) and the local-predicate
construction of a sheaf of functions (`Mathlib/Topology/Sheaves/LocalPredicate.lean`), and neither
Mathlib nor this repository had a sheaf of holomorphic functions before; both are consumed rather
than restated, as is the local-homeomorphism half of the projection's behaviour, from
`TauCeti/Topology/Sheaves/EtaleSpace.lean`. Layer L4 lies outside the roadmap's shim-deletion
clause for the upstream Riemann-mapping effort
(leanprover-community/mathlib4#33505), which contains no continuation or monodromy material.

## Main results

* `TauCeti.holomorphicLocalPredicate` — holomorphy as a local predicate on `ℂ`-valued functions on
  open subsets of the plane.
* `TauCeti.holomorphicSheaf` — the sheaf of holomorphic functions on `ℂ`, and
  `TauCeti.HolomorphicGerm` its étalé space.
* `TauCeti.holomorphicSection_eq_of_germ_eq` — **the identity theorem for sections**: two sections
  over a preconnected open set with a common germ at one point are equal.
* `TauCeti.isSeparatedMap_holomorphicGerm_base` — **the projection is a separated map**, the
  analytic input to the abstract lifting theory.
* `TauCeti.continuous_holomorphicGermOf` — a function holomorphic on `U` lifts `U` continuously
  into the étalé space, and `TauCeti.exists_holomorphicGermOf_eq` — every point of the étalé space
  arises this way.
* `TauCeti.holomorphicGerm_eqOn_of_base_eqOn` — **uniqueness of lifts**: two continuous
  lifts of one map on a preconnected set that agree at a point agree throughout. Along a path this
  is the uniqueness of analytic continuation.
* `TauCeti.monodromy_theorem_holomorphicGerm` — **the monodromy theorem as a lifting property**:
  lifts of the paths of a homotopy rel endpoints, starting at one germ, end at one germ.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX §2–3.
* O. Forster, *Lectures on Riemann Surfaces* (GTM 81), §6 (the sheaf of holomorphic functions and
  its étalé space).
-/

public section

namespace TauCeti

open CategoryTheory Opposite Set TopologicalSpace

noncomputable section

/-! ### The sheaf of holomorphic functions -/

/-- **Holomorphy as a local predicate.** A function `f` on an open set `U ⊆ ℂ` satisfies
`TauCeti.holomorphicLocalPredicate.pred` when it is the restriction to `U` of a function
holomorphic on `U`. -/
@[expose] def holomorphicLocalPredicate : TopCat.LocalPredicate (fun _ : TopCat.of ℂ => ℂ) where
  pred {U} f := ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ x : U, g x = f x
  res := by
    rintro U V i f ⟨g, hg, hgf⟩
    exact ⟨g, hg.mono fun z hz => i.le hz, fun x => hgf ⟨x.1, i.le x.2⟩⟩
  locality := by
    intro U f hf
    -- The ambient function is the extension of the section by zero.
    have hext : ∀ x : U, Function.extend (Subtype.val : U → ℂ) f 0 x = f x := fun x =>
      Subtype.val_injective.extend_apply f 0 x
    refine ⟨Function.extend Subtype.val f 0, ?_, hext⟩
    intro z hz
    obtain ⟨V, hzV, i, g, hg, hgf⟩ := hf ⟨z, hz⟩
    have hVU : (V : Set ℂ) ⊆ (U : Set ℂ) := fun w hw => i.le hw
    have hgext : EqOn (Function.extend (Subtype.val : U → ℂ) f 0) g V := fun w hw =>
      (hext ⟨w, hVU hw⟩).trans (hgf ⟨w, hw⟩).symm
    exact (((hg z hzV).differentiableAt (V.isOpen.mem_nhds hzV)).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (V.isOpen.mem_nhds hzV) hgext)).differentiableWithinAt

/-- **The sheaf of holomorphic functions on the plane.** -/
@[expose] def holomorphicSheaf : TopCat.Sheaf (Type) (TopCat.of ℂ) :=
  TopCat.subsheafToTypes holomorphicLocalPredicate

/-- The section of `TauCeti.holomorphicSheaf` over `U` cut out by a function holomorphic on `U`. -/
@[expose] def holomorphicSectionOf (U : Opens (TopCat.of ℂ)) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g U) : ToType (holomorphicSheaf.presheaf.obj (op U)) :=
  ⟨fun x => g x, g, hg, fun _ => rfl⟩

@[simp]
theorem val_holomorphicSectionOf (U : Opens (TopCat.of ℂ)) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g U) (x : U) : (holomorphicSectionOf U g hg).1 x = g x :=
  rfl

/-- **Extensionality for sections of `TauCeti.holomorphicSheaf`**: two sections over `U` taking the
same value at every point of `U` are equal. -/
theorem holomorphicSection_ext {U : Opens (TopCat.of ℂ)}
    {s t : ToType (holomorphicSheaf.presheaf.obj (op U))} (h : ∀ x : U, s.1 x = t.1 x) : s = t :=
  Subtype.ext (funext h)

/-- Every section of `TauCeti.holomorphicSheaf` over `U` is cut out by a function analytic on a
neighbourhood of each point of `U`; this is the form in which the identity theorem consumes it. -/
theorem exists_analyticOnNhd_of_holomorphicSection {U : Opens (TopCat.of ℂ)}
    (s : ToType (holomorphicSheaf.presheaf.obj (op U))) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ ∀ x : U, g x = s.1 x :=
  let ⟨g, hg, hgs⟩ := s.2
  ⟨g, hg.analyticOnNhd U.isOpen, hgs⟩

/-! ### The identity theorem for sections -/

/-- **The identity theorem for sections of the sheaf of holomorphic functions.** Two sections over
a preconnected open set that agree on a nonempty open subset of it are equal. -/
theorem holomorphicSection_eq_of_eqOn {U : Opens (TopCat.of ℂ)} (hU : IsPreconnected (U : Set ℂ))
    (s t : ToType (holomorphicSheaf.presheaf.obj (op U))) {W : Set ℂ} (hWo : IsOpen W)
    (hWU : W ⊆ (U : Set ℂ)) (hW : W.Nonempty) (h : ∀ x : U, (x : ℂ) ∈ W → s.1 x = t.1 x) :
    s = t := by
  obtain ⟨g, hg, hgs⟩ := exists_analyticOnNhd_of_holomorphicSection s
  obtain ⟨g', hg', hgt⟩ := exists_analyticOnNhd_of_holomorphicSection t
  obtain ⟨w, hw⟩ := hW
  have heq : EqOn g g' (U : Set ℂ) := by
    refine hg.eqOn_of_preconnected_of_eventuallyEq hg' hU (hWU hw) ?_
    filter_upwards [hWo.mem_nhds hw] with v hv
    rw [hgs ⟨v, hWU hv⟩, hgt ⟨v, hWU hv⟩]
    exact h ⟨v, hWU hv⟩ hv
  exact holomorphicSection_ext fun x => by rw [← hgs x, ← hgt x, heq x.2]

/-- **A section over a preconnected open set is determined by its germ at a single point.** This is
the identity theorem in the form the étalé space uses: distinct sections over a connected open set
stay distinct at every one of its points. -/
theorem holomorphicSection_eq_of_germ_eq {U : Opens (TopCat.of ℂ)} (hU : IsPreconnected (U : Set ℂ))
    {w : ℂ} (hw : w ∈ U) (s t : ToType (holomorphicSheaf.presheaf.obj (op U)))
    (h : holomorphicSheaf.presheaf.germ U w hw s = holomorphicSheaf.presheaf.germ U w hw t) :
    s = t := by
  obtain ⟨W, hwW, iU, iV, he⟩ := holomorphicSheaf.presheaf.germ_eq w hw hw s t h
  exact holomorphicSection_eq_of_eqOn hU s t W.isOpen (fun v hv => iU.le hv) ⟨w, hwW⟩
    fun x hx => congr_fun (congrArg Subtype.val he) ⟨x.1, hx⟩

/-! ### The étalé space of holomorphic germs -/

/-- **The étalé space of holomorphic germs on the plane**: pairs of a point of `ℂ` and a germ of a
holomorphic function there, topologised so that the germs of one function at the points of its
domain form an open set. -/
abbrev HolomorphicGerm : Type := holomorphicSheaf.presheaf.EtaleSpace

/-- **The projection of the étalé space of holomorphic germs is a local homeomorphism.** This is
the general fact about étalé spaces, at this sheaf. -/
theorem isLocalHomeomorph_holomorphicGerm_base :
    IsLocalHomeomorph (TopCat.Presheaf.EtaleSpace.base (F := holomorphicSheaf.presheaf)) :=
  TopCat.Presheaf.EtaleSpace.isLocalHomeomorph_base _

/-- **The projection of the étalé space of holomorphic germs is locally injective.** -/
theorem isLocallyInjective_holomorphicGerm_base :
    IsLocallyInjective (TopCat.Presheaf.EtaleSpace.base (F := holomorphicSheaf.presheaf)) :=
  isLocalHomeomorph_holomorphicGerm_base.isLocallyInjective

/-- **The projection of the étalé space of holomorphic germs is a separated map**: two distinct
germs at one and the same point have disjoint neighbourhoods in the étalé space.

This is the analytic input to the abstract lifting theory, and it is the identity theorem. -/
theorem isSeparatedMap_holomorphicGerm_base :
    IsSeparatedMap (TopCat.Presheaf.EtaleSpace.base (F := holomorphicSheaf.presheaf)) := by
  rw [isSeparatedMap_iff_nhds]
  rintro ⟨z, m₁⟩ ⟨z', m₂⟩ hbase hne
  obtain rfl : z = z' := hbase
  obtain ⟨U₁, hz₁, s₁, hs₁⟩ := holomorphicSheaf.presheaf.exists_germ_eq m₁
  obtain ⟨U₂, hz₂, s₂, hs₂⟩ := holomorphicSheaf.presheaf.exists_germ_eq m₂
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.1 U₁.isOpen z hz₁
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.isOpen_iff.1 U₂.isOpen z hz₂
  set B : Opens (TopCat.of ℂ) := ⟨Metric.ball z (min ε₁ ε₂), Metric.isOpen_ball⟩ with hB
  have hzB : z ∈ B := Metric.mem_ball_self (lt_min hε₁ hε₂)
  have hBU₁ : B ≤ U₁ := fun w hw => hball₁ (Metric.ball_subset_ball (min_le_left _ _) hw)
  have hBU₂ : B ≤ U₂ := fun w hw => hball₂ (Metric.ball_subset_ball (min_le_right _ _) hw)
  set t₁ := holomorphicSheaf.presheaf.map (homOfLE hBU₁).op s₁ with ht₁
  set t₂ := holomorphicSheaf.presheaf.map (homOfLE hBU₂).op s₂ with ht₂
  have hg₁ : holomorphicSheaf.presheaf.germ B z hzB t₁ = m₁ := by
    rw [ht₁, holomorphicSheaf.presheaf.germ_res_apply (homOfLE hBU₁) z hzB s₁, hs₁]
  have hg₂ : holomorphicSheaf.presheaf.germ B z hzB t₂ = m₂ := by
    rw [ht₂, holomorphicSheaf.presheaf.germ_res_apply (homOfLE hBU₂) z hzB s₂, hs₂]
  refine ⟨_, TopCat.Presheaf.EtaleSpace.eventually_nhds ⟨z, m₁⟩ hzB t₁ hg₁, _,
    TopCat.Presheaf.EtaleSpace.eventually_nhds ⟨z, m₂⟩ hzB t₂ hg₂, ?_⟩
  rw [Set.disjoint_left]
  rintro g ⟨hw₁, hgerm₁⟩ ⟨hw₂, hgerm₂⟩
  have hst : t₁ = t₂ :=
    holomorphicSection_eq_of_germ_eq (convex_ball z (min ε₁ ε₂)).isPreconnected hw₁ t₁ t₂
      (by rw [← hgerm₁, ← hgerm₂])
  exact hne (by rw [← hg₁, ← hg₂, hst])

/-! ### Holomorphic functions as lifts -/

/-- The germ at `z` of a function holomorphic on an open set `U ∋ z`, as a point of the étalé
space. -/
def holomorphicGermOf (U : Opens (TopCat.of ℂ)) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g U) (z : ℂ) (hz : z ∈ U) : HolomorphicGerm :=
  ⟨z, holomorphicSheaf.presheaf.germ U z hz (holomorphicSectionOf U g hg)⟩

@[simp]
theorem base_holomorphicGermOf (U : Opens (TopCat.of ℂ)) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g U) (z : ℂ) (hz : z ∈ U) :
    (holomorphicGermOf U g hg z hz).base = z := by
  rw [holomorphicGermOf]

/-- The germ component of `TauCeti.holomorphicGermOf`, transported along
`TauCeti.base_holomorphicGermOf` to the stalk at `z`: it is the germ at `z` of the section
`TauCeti.holomorphicSectionOf`. -/
@[simp]
theorem germ_holomorphicGermOf (U : Opens (TopCat.of ℂ)) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g U) (z : ℂ) (hz : z ∈ U) :
    cast (congrArg (fun y : TopCat.of ℂ => ToType (holomorphicSheaf.presheaf.stalk y))
        (base_holomorphicGermOf U g hg z hz)) (holomorphicGermOf U g hg z hz).germ =
      holomorphicSheaf.presheaf.germ U z hz (holomorphicSectionOf U g hg) := by
  rw [cast_eq_iff_heq, holomorphicGermOf]

/-- **A holomorphic function is a lift.** The germs of a function holomorphic on `U`, taken at the
points of `U`, depend continuously on the point; together with
`TauCeti.base_holomorphicGermOf` this says that `U ∋ z ↦` germ of `g` at `z` is a continuous
section of the étalé projection over `U`. -/
theorem continuous_holomorphicGermOf (U : Opens (TopCat.of ℂ)) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g U) :
    Continuous fun z : U => holomorphicGermOf U g hg z z.2 := by
  have h : (fun z : U => holomorphicGermOf U g hg z z.2) =
      TopCat.Presheaf.EtaleSpace.germSection holomorphicSheaf.presheaf U
        (holomorphicSectionOf U g hg) := by
    funext z
    rw [holomorphicGermOf, TopCat.Presheaf.EtaleSpace.germSection_apply]
  rw [h]
  exact TopCat.Presheaf.EtaleSpace.continuous_germSection U (holomorphicSectionOf U g hg)

/-- **Every holomorphic germ is the germ of a holomorphic function.** So
`TauCeti.holomorphicGermOf` exhausts the étalé space, and a statement about all of its points is a
statement about all germs of holomorphic functions. -/
theorem exists_holomorphicGermOf_eq (w : HolomorphicGerm) :
    ∃ (U : Opens (TopCat.of ℂ)) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) (hw : w.base ∈ U),
      holomorphicGermOf U g hg w.base hw = w := by
  obtain ⟨U, hwU, s, hs⟩ := holomorphicSheaf.presheaf.exists_germ_eq w.germ
  obtain ⟨g, hg, hgs⟩ := s.2
  have hsec : holomorphicSectionOf U g hg = s :=
    holomorphicSection_ext fun x => (val_holomorphicSectionOf U g hg x).trans (hgs x)
  exact ⟨U, g, hg, hwU, by rw [holomorphicGermOf, hsec, hs]⟩

/-! ### Uniqueness of lifts, and monodromy -/

/-- **Uniqueness of lifts of holomorphic germs.** Two continuous maps into the étalé space that
project to the same map on a preconnected set and agree at one of its points agree on it.

Along a path this is the uniqueness of analytic continuation: the continuation of a germ along a
fixed path is determined by the germ one starts from. -/
theorem holomorphicGerm_eqOn_of_base_eqOn {A : Type*} [TopologicalSpace A] {s : Set A}
    {g₁ g₂ : A → HolomorphicGerm} (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s)
    (h₂ : ContinuousOn g₂ s) (he : EqOn (fun a => (g₁ a).base) (fun a => (g₂ a).base) s) {a : A}
    (has : a ∈ s) (ha : g₁ a = g₂ a) : EqOn g₁ g₂ s :=
  isSeparatedMap_holomorphicGerm_base.eqOn_of_comp_eqOn isLocallyInjective_holomorphicGerm_base
    hs h₁ h₂ he has ha

/-- **The monodromy theorem for holomorphic germs, as a lifting property of the étalé space.** Let
`γ` be a homotopy rel endpoints between two paths in `ℂ`, and suppose each path `γ (t, ·)` of the
homotopy lifts to a continuous path `Γ t` of holomorphic germs, all the lifts starting from one and
the same germ. Then they all end at the same germ.

This is Mathlib's `IsLocalHomeomorph.monodromy_theorem` at the étalé space of holomorphic germs,
which the separatedness proved above unlocks. It is a statement about *continuous lifts*; the
germ-family form of the same mathematics, proved directly from a metric stability argument, is
`TauCeti.monodromy_theorem` in `Conformal/Monodromy.lean`, and no bridge between the two
presentations is claimed here. -/
theorem monodromy_theorem_holomorphicGerm {γ₀ γ₁ : C(unitInterval, ℂ)}
    (γ : γ₀.HomotopyRel γ₁ {0, 1}) (Γ : unitInterval → C(unitInterval, HolomorphicGerm))
    (hΓ : ∀ t s, (Γ t s).base = γ (t, s)) (hΓ₀ : ∀ t, Γ t 0 = Γ 0 0) (t : unitInterval) :
    Γ t 1 = Γ 0 1 :=
  isLocalHomeomorph_holomorphicGerm_base.monodromy_theorem isSeparatedMap_holomorphicGerm_base
    γ Γ hΓ hΓ₀ t

/-- The fibre of the étalé space over a point has more than one element, so
`TauCeti.isSeparatedMap_holomorphicGerm_base` is not the statement that the projection is
injective: the germs at `0` of the identity and of the zero function are two distinct points of the
étalé space lying over `0`. -/
example :
    holomorphicGermOf ⊤ id differentiable_id.differentiableOn 0 trivial ≠
      holomorphicGermOf ⊤ (fun _ => 0) (differentiableOn_const 0) 0 trivial := by
  intro h
  have hsec := holomorphicSection_eq_of_germ_eq (U := ⊤) (by simpa using isPreconnected_univ)
    (w := 0) trivial (holomorphicSectionOf ⊤ id differentiable_id.differentiableOn)
    (holomorphicSectionOf ⊤ (fun _ => 0) (differentiableOn_const 0))
    (by simpa [holomorphicGermOf] using h)
  simpa using congr_fun (congrArg Subtype.val hsec) ⟨1, trivial⟩

end

end TauCeti
