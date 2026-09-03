/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Sheaves.LocalPredicate
public import TauCeti.Topology.Sheaves.EtaleSpace

/-!
# The sheaf of holomorphic functions on `ℂ`, and its étalé space

Analytic continuation transports *germs*. `Conformal/Continuation/Basic.lean` carries them
concretely — as families of functions compared by `=ᶠ[𝓝 _]` — and records, without proof, that
reading a germ as a point of the **étalé space of holomorphic germs** turns a continuation along a
path into a continuous lift of that path. Neither Mathlib nor this repository had the space that
sentence names. This file builds it, and proves the two facts that make it the right object: the
projection to the base is a local homeomorphism, and it is a **separated map**.

## What is built

The sheaf itself comes from Mathlib's local-predicate machinery
(`Mathlib/Topology/Sheaves/LocalPredicate.lean`): `TauCeti.IsHolomorphicSection` says that a
function on an open `U ⊆ ℂ` is the restriction of a function analytic on a neighbourhood of every
point of `U`, this is stable under restriction and local, and `TauCeti.holomorphicPresheaf` /
`TauCeti.holomorphicSheaf` are the presheaf and the sheaf of such sections, the latter being
Mathlib's `TopCat.subsheafToTypes` at that local predicate. Locality is where the extension by
zero of a section enters: a function given only on `U` has no values elsewhere to be analytic at,
so the witness glued from local ones is `Function.extend Subtype.val`, which agrees with the
section on `U` and is analytic there because analyticity is a local property of an open set. The
same extension names the function underlying a section,
`TauCeti.HolomorphicPresheaf.sectionFun`, and every statement below is phrased against it rather
than against the subtype.

The étalé space is Mathlib's `TopCat.Presheaf.EtaleSpace` — pairs of a base point and a germ over
it — with the chart API of `TauCeti/Topology/Sheaves/EtaleSpace.lean`. On top of it this file adds
the dictionary between germs as stalk elements and germs as eventual equality of functions:

* `TauCeti.HolomorphicPresheaf.germ_eq_iff` — two sections have the same germ at `x` exactly when
  their functions agree near `x`;
* `TauCeti.HolomorphicPresheaf.germAt` — the stalk element carried by a function analytic at a
  point, and `TauCeti.HolomorphicPresheaf.germPoint` the corresponding point of the étalé space;
* `TauCeti.HolomorphicPresheaf.germAt_eq_iff` — that dictionary again, now between two functions
  rather than two sections;
* `TauCeti.HolomorphicPresheaf.repFun` — a holomorphic representative of the germ carried by a
  point of the étalé space, inverse to `germPoint` by
  `TauCeti.HolomorphicPresheaf.germPoint_repFun`.

`germAt` is total: a function that is not analytic at the point in question is sent to the germ of
`0`. The junk value is never inspected — every lemma about `germAt` either supplies analyticity or
is insensitive to it (`TauCeti.HolomorphicPresheaf.germAt_congr` holds for arbitrary functions,
both sides being junk when the common germ is not analytic) — and totality is what lets the germ
map of a family be written as a plain function of the parameter, with no proof argument to
transport.

## The two theorems

`TauCeti.TopCat.Presheaf.EtaleSpace.isLocalHomeomorph_base` is the chart statement of
`TauCeti/Topology/Sheaves/EtaleSpace.lean`: over an open set on which a section is defined, the
germs of that section form an open set carried homeomorphically onto the base.

`TauCeti.HolomorphicPresheaf.isSeparatedMap_base` is the analytic content, and it is the
**identity theorem** in disguise. Two distinct germs at one point `x` are represented by sections
over two open sets; restrict both to one disc about `x`. The two open sets of germs they sweep out
are disjoint, for a point of both would be a point `y` of the disc at which the two
representatives have the same germ, and the identity theorem on the disc — connected, and where
both representatives are analytic — would propagate that agreement from `y` back to `x`, making
the two germs equal. Separatedness is exactly the hypothesis Mathlib's abstract monodromy theorem
`IsLocalHomeomorph.monodromy_theorem` asks for, and its docstring names analytic continuation as
the intended application; `Conformal/Continuation/Etale.lean` supplies the continuation/lift
correspondence needed to apply it.

## Main results

* `TauCeti.holomorphicSheaf` — the sheaf of holomorphic functions on `ℂ`.
* `TauCeti.HolomorphicPresheaf.germ_eq_iff` — germs agree exactly when the functions agree nearby.
* `TauCeti.HolomorphicPresheaf.continuousOn_germPoint` — the germ map of a holomorphic function is
  a continuous section of the étalé projection.
* `TauCeti.HolomorphicPresheaf.isSeparatedMap_base` — **the étalé projection is separated**.

## Generality

The *target* is an arbitrary complex Banach space `E`, the generality at which
`Conformal/Continuation/Basic.lean` states analytic continuation; the scalar case `E = ℂ` is the
one the conformal-mapping consumers instantiate. Both restrictions on `E` are inherited rather
than chosen. It is confined to `Type` rather than `Type*` by Mathlib's étalé space, which is built
for a `C`-valued presheaf on `X : TopCat.{v}` with `[Category.{v} C]`: the base `TopCat.of ℂ`
lives in `TopCat.{0}`, so the values of the presheaf are forced into `Type`. Completeness is asked
for exactly where Mathlib asks for it, from `TauCeti.HolomorphicPresheaf.germAt` on, because
`AnalyticAt.exists_ball_analyticOnNhd` — which names a disc on which a germ has a representative —
is stated for a Banach target. The sheaf, the germ dictionary
`TauCeti.HolomorphicPresheaf.germ_eq_iff` and both theorems about the projection are free of it,
the identity theorem `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` needing no
completeness.

The *source* is `ℂ` rather than a Riemann surface, in accordance with the generality bar of
`ConformalMapping/README.md`, which fixes the scalar domain for the conformal layers L0–L6, and
because the consumer `Conformal/Continuation/Basic.lean` continues germs along paths in `ℂ`. A
Riemann surface source would need a holomorphic atlas to even state the predicate, which the
pinned Mathlib has for complex manifolds but which this area does not use anywhere else.

## Relation to Mathlib

Mathlib has the étalé space of a presheaf (`Mathlib/Topology/Sheaves/EtaleSpace.lean`) and the
local-predicate construction of a sheaf of functions
(`Mathlib/Topology/Sheaves/LocalPredicate.lean`), both consumed here; it has no sheaf of
holomorphic functions and no étalé space of holomorphic germs. The in-progress human-curated
Riemann-mapping effort [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505)
contains no continuation or monodromy material, so nothing here is a shim for it. Mathlib's sheaf
of smooth functions on a manifold (`Mathlib/Geometry/Manifold/Sheaf/Smooth.lean`) reaches the same
`LocalPredicate` interface through the structure-groupoid machinery, but is fixed at smoothness
`∞`; running that route at analytic smoothness would put the charted-space structure of `ℂ` and a
translation between `ContMDiff` and `AnalyticOnNhd` between this file and the identity theorem it
needs, so the predicate is written out directly instead.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX §§1--3.
* O. Forster, *Lectures on Riemann Surfaces* (GTM 81), §6.
-/

public section

namespace TauCeti

open CategoryTheory Metric Opposite Set TopologicalSpace Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### The sheaf -/

/-- A function on an open subset `U` of `ℂ` is a **holomorphic section** when it is the
restriction of a function analytic on a neighbourhood of every point of `U`. -/
def IsHolomorphicSection {U : Opens (TopCat.of ℂ)} (f : U → E) : Prop :=
  ∃ g : ℂ → E, AnalyticOnNhd ℂ g U ∧ ∀ x : U, f x = g x

/-- **Being a holomorphic section is being the restriction of a function analytic on a
neighbourhood of every point.** `TauCeti.IsHolomorphicSection` does not expose its body, so this
is how a consumer of the sheaf introduces or eliminates it. -/
theorem isHolomorphicSection_iff {U : Opens (TopCat.of ℂ)} {f : U → E} :
    IsHolomorphicSection f ↔ ∃ g : ℂ → E, AnalyticOnNhd ℂ g U ∧ ∀ x : U, f x = g x := Iff.rfl

/-- Being holomorphic is stable under restriction to a smaller open set. -/
theorem IsHolomorphicSection.mono {U V : Opens (TopCat.of ℂ)} (h : U ≤ V) {f : V → E}
    (hf : IsHolomorphicSection f) :
    IsHolomorphicSection fun x : U => f ⟨x.1, SetLike.le_def.mp h x.2⟩ := by
  obtain ⟨g, hg, hfg⟩ := hf
  exact ⟨g, hg.mono (SetLike.coe_subset_coe.mpr h), fun x => hfg _⟩

variable (E) in
/-- Being holomorphic is a local condition. -/
private def holomorphicLocal : TopCat.LocalPredicate fun _ : TopCat.of ℂ => E where
  pred f := IsHolomorphicSection f
  res i _ hf := hf.mono i.le
  locality {U} f hloc := by
    refine ⟨Function.extend Subtype.val f (fun _ => 0), fun z hz => ?_, fun x =>
      (Subtype.val_injective.extend_apply f _ x).symm⟩
    obtain ⟨V, hzV, i, g, hg, hfg⟩ := hloc ⟨z, hz⟩
    refine (hg z hzV).congr (Filter.eventuallyEq_of_mem (V.isOpen.mem_nhds hzV) fun y hy => ?_)
    have hyU : y ∈ U := SetLike.le_def.mp i.le hy
    have hext := Subtype.val_injective.extend_apply f (fun _ => (0 : E)) ⟨y, hyU⟩
    simp only at hext
    rw [hext]
    exact (hfg ⟨y, hy⟩).symm

variable (E) in
/-- The presheaf of holomorphic functions on `ℂ` with values in `E`. -/
@[expose] noncomputable def holomorphicPresheaf : (TopCat.of ℂ).Presheaf (Type) :=
  TopCat.subpresheafToTypes
    ({ pred := fun {_} f => IsHolomorphicSection f
       res := fun i _ hf => hf.mono i.le } : TopCat.PrelocalPredicate fun _ : TopCat.of ℂ => E)

variable (E) in
/-- The sheaf of holomorphic functions on `ℂ` with values in `E`. -/
noncomputable def holomorphicSheaf : TopCat.Sheaf (Type) (TopCat.of ℂ) :=
  TopCat.subsheafToTypes (holomorphicLocal E)

/-- The presheaf underlying the sheaf of holomorphic functions. -/
@[simp]
theorem holomorphicSheaf_obj : (holomorphicSheaf E).obj = holomorphicPresheaf E := (rfl)

namespace HolomorphicPresheaf

variable {U V : Opens (TopCat.of ℂ)} {g g' : ℂ → E} {x z : ℂ}

/-! ### Sections as functions -/

/-- The function on `ℂ` underlying a section of `TauCeti.holomorphicPresheaf`, extended by zero
outside its domain. -/
noncomputable def sectionFun (s : (holomorphicPresheaf E).obj (op U)) : ℂ → E :=
  Function.extend Subtype.val s.1 fun _ => 0

/-- On its own domain, the function underlying a section is the section. -/
@[simp]
theorem sectionFun_coe (s : (holomorphicPresheaf E).obj (op U)) (y : U) :
    sectionFun s y = s.1 y :=
  Subtype.val_injective.extend_apply _ _ _

/-- The function underlying a holomorphic section is analytic on a neighbourhood of every point of
its domain. -/
theorem analyticOnNhd_sectionFun (s : (holomorphicPresheaf E).obj (op U)) :
    AnalyticOnNhd ℂ (sectionFun s) U := by
  obtain ⟨g, hg, hfg⟩ := s.2
  intro z hz
  refine (hg z hz).congr (Filter.eventuallyEq_of_mem (U.isOpen.mem_nhds hz) fun y hy => ?_)
  rw [sectionFun_coe s ⟨y, hy⟩]
  exact (hfg ⟨y, hy⟩).symm

/-- Restricting a section along an inclusion of open sets restricts its underlying function. -/
private theorem map_val_apply (i : U ⟶ V) (s : (holomorphicPresheaf E).obj (op V)) (y : U) :
    ((holomorphicPresheaf E).map i.op s).1 y = s.1 ⟨y.1, SetLike.le_def.mp i.le y.2⟩ := rfl

/-- A function analytic on a neighbourhood of every point of `U`, read as a section over `U`. -/
def toSection (U : Opens (TopCat.of ℂ)) (g : ℂ → E) (hg : AnalyticOnNhd ℂ g U) :
    (holomorphicPresheaf E).obj (op U) :=
  ⟨fun y => g y, g, hg, fun _ => rfl⟩

/-- On `U`, the function underlying the section determined by `g` is `g`. -/
@[simp]
theorem sectionFun_toSection (hg : AnalyticOnNhd ℂ g U) :
    EqOn (sectionFun (toSection U g hg)) g U := fun y hy => sectionFun_coe _ ⟨y, hy⟩

/-! ### Germs -/

/-- **Two holomorphic sections have the same germ at a point exactly when their functions agree
near it.** The forward direction is the definition of the stalk as a filtered colimit; the reverse
one restricts both sections to a common open set on which they are equal. -/
theorem germ_eq_iff (hxU : x ∈ U) (hxV : x ∈ V) (s : (holomorphicPresheaf E).obj (op U))
    (t : (holomorphicPresheaf E).obj (op V)) :
    (holomorphicPresheaf E).germ U x hxU s = (holomorphicPresheaf E).germ V x hxV t ↔
      sectionFun s =ᶠ[𝓝 x] sectionFun t := by
  constructor
  · intro h
    obtain ⟨W, hxW, iU, iV, hmap⟩ := (holomorphicPresheaf E).germ_eq x hxU hxV s t h
    refine Filter.eventuallyEq_of_mem (W.isOpen.mem_nhds hxW) fun y hy => ?_
    have hyU : y ∈ U := SetLike.le_def.mp iU.le hy
    have hyV : y ∈ V := SetLike.le_def.mp iV.le hy
    have key := congrArg (fun r : (holomorphicPresheaf E).obj (op W) => r.1 ⟨y, hy⟩) hmap
    rw [sectionFun_coe s ⟨y, hyU⟩, sectionFun_coe t ⟨y, hyV⟩]
    exact key
  · intro h
    obtain ⟨W₀, hW₀sub, hW₀open, hxW₀⟩ := _root_.mem_nhds_iff.mp h
    refine (holomorphicPresheaf E).germ_ext (⟨W₀, hW₀open⟩ ⊓ U ⊓ V)
      (⟨⟨hxW₀, hxU⟩, hxV⟩ : x ∈ W₀ ∩ (U : Set ℂ) ∩ (V : Set ℂ))
      (homOfLE (inf_le_left.trans inf_le_right)) (homOfLE inf_le_right) ?_
    refine Subtype.ext (funext fun y => ?_)
    have hy : (y : ℂ) ∈ W₀ ∩ (U : Set ℂ) ∩ (V : Set ℂ) := y.2
    rw [map_val_apply, map_val_apply, ← sectionFun_coe s ⟨y.1, hy.1.2⟩,
      ← sectionFun_coe t ⟨y.1, hy.2⟩]
    exact hW₀sub hy.1.1

variable [CompleteSpace E]

open scoped Classical in
/-- The germ at `z` of a function analytic there, as an element of the stalk of the sheaf of
holomorphic functions. A function that is not analytic at `z` is sent to the germ of `0`, a junk
value that `TauCeti.HolomorphicPresheaf.germAt_eq_germ_of_eventuallyEq` never sees. -/
noncomputable def germAt (g : ℂ → E) (z : ℂ) : (holomorphicPresheaf E).stalk z :=
  if hg : AnalyticAt ℂ g z then
    (holomorphicPresheaf E).germ ⟨ball z hg.exists_ball_analyticOnNhd.choose, isOpen_ball⟩ z
      (mem_ball_self hg.exists_ball_analyticOnNhd.choose_spec.1)
      (toSection _ g hg.exists_ball_analyticOnNhd.choose_spec.2)
  else
    (holomorphicPresheaf E).germ ⊤ z trivial (toSection ⊤ 0 fun _ _ => analyticAt_const)

/-- **The germ of a function is the germ of any section representing it.** This is the only way
`TauCeti.HolomorphicPresheaf.germAt` is used: it identifies the abstract germ with the concrete
one carried by a section, and the choice of ball made in the definition drops out. -/
theorem germAt_eq_germ_of_eventuallyEq (hzU : z ∈ U) (s : (holomorphicPresheaf E).obj (op U))
    (h : sectionFun s =ᶠ[𝓝 z] g) : germAt g z = (holomorphicPresheaf E).germ U z hzU s := by
  have hg : AnalyticAt ℂ g z := (analyticOnNhd_sectionFun s z hzU).congr h
  rw [germAt, dite_eq_left_of_eq_true (eq_true hg)]
  refine (germ_eq_iff _ hzU _ s).mpr (Filter.EventuallyEq.trans ?_ h.symm)
  exact Filter.eventuallyEq_of_mem
    (isOpen_ball.mem_nhds (mem_ball_self hg.exists_ball_analyticOnNhd.choose_spec.1))
    (sectionFun_toSection hg.exists_ball_analyticOnNhd.choose_spec.2)

/-- The germ of the function underlying a section is the germ of that section. -/
theorem germAt_eq_germ (hzU : z ∈ U) (s : (holomorphicPresheaf E).obj (op U)) :
    germAt (sectionFun s) z = (holomorphicPresheaf E).germ U z hzU s :=
  germAt_eq_germ_of_eventuallyEq hzU s .rfl

/-- **The germ at `z` depends only on the values near `z`.** Functions agreeing near `z` have the
same germ there, analytic or not: when they are not analytic both sides are the same junk value. -/
theorem germAt_congr (h : g =ᶠ[𝓝 z] g') : germAt g z = germAt g' z := by
  by_cases hg : AnalyticAt ℂ g z
  · obtain ⟨r, hr, hball⟩ := hg.exists_ball_analyticOnNhd
    have hzB : z ∈ (⟨ball z r, isOpen_ball⟩ : Opens (TopCat.of ℂ)) := mem_ball_self hr
    have hsec : sectionFun (toSection ⟨ball z r, isOpen_ball⟩ g hball) =ᶠ[𝓝 z] g :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hzB) (sectionFun_toSection hball)
    rw [germAt_eq_germ_of_eventuallyEq hzB _ hsec,
      germAt_eq_germ_of_eventuallyEq hzB _ (hsec.trans h)]
  · have hg' : ¬ AnalyticAt ℂ g' z := fun hg' => hg (hg'.congr h.symm)
    rw [germAt, germAt, dite_eq_right_of_eq_false (eq_false hg),
      dite_eq_right_of_eq_false (eq_false hg')]

/-- **Two functions analytic at `z` have the same germ there exactly when they agree near `z`.**
The reverse implication is `TauCeti.HolomorphicPresheaf.germAt_congr`; the forward one is the
description of the stalk as a colimit, read through
`TauCeti.HolomorphicPresheaf.germ_eq_iff`. -/
theorem germAt_eq_iff (hg : AnalyticAt ℂ g z) (hg' : AnalyticAt ℂ g' z) :
    germAt g z = germAt g' z ↔ g =ᶠ[𝓝 z] g' := by
  refine ⟨fun h => ?_, germAt_congr⟩
  obtain ⟨r, hr, hball⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨r', hr', hball'⟩ := hg'.exists_ball_analyticOnNhd
  have hzB : z ∈ (⟨ball z r, isOpen_ball⟩ : Opens (TopCat.of ℂ)) := mem_ball_self hr
  have hzB' : z ∈ (⟨ball z r', isOpen_ball⟩ : Opens (TopCat.of ℂ)) := mem_ball_self hr'
  have hsec : sectionFun (toSection ⟨ball z r, isOpen_ball⟩ g hball) =ᶠ[𝓝 z] g :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hzB) (sectionFun_toSection hball)
  have hsec' : sectionFun (toSection ⟨ball z r', isOpen_ball⟩ g' hball') =ᶠ[𝓝 z] g' :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hzB') (sectionFun_toSection hball')
  rw [germAt_eq_germ_of_eventuallyEq hzB _ hsec,
    germAt_eq_germ_of_eventuallyEq hzB' _ hsec'] at h
  exact hsec.symm.trans (((germ_eq_iff hzB hzB' _ _).mp h).trans hsec')

/-- The germ of a function analytic at `z`, as a point of the étalé space of holomorphic germs. -/
@[expose] noncomputable def germPoint (g : ℂ → E) (z : ℂ) : (holomorphicPresheaf E).EtaleSpace :=
  ⟨z, germAt g z⟩

/-- The germ point of `g` at `z` sits over `z`. -/
@[simp]
theorem base_germPoint (g : ℂ → E) (z : ℂ) :
    (germPoint g z).base = z := rfl

/-- The germ point of `g` at `z` carries the germ of `g`. -/
@[simp]
theorem germ_germPoint (g : ℂ → E) (z : ℂ) : (germPoint g z).germ = germAt g z := rfl

/-- Functions agreeing near `z` give the same point of the étalé space over `z`. -/
theorem germPoint_congr (h : g =ᶠ[𝓝 z] g') : germPoint g z = germPoint g' z := by
  rw [germPoint, germPoint, germAt_congr h]

/-- **Over an open set on which `g` is analytic, the germ map of `g` is the germ section swept out
by `g`.** This is the comparison between the two descriptions of a point of the étalé space — a
base point paired with `TauCeti.HolomorphicPresheaf.germAt`, and the germ of a section at a point
of its domain — and it is what carries continuity from one to the other. -/
theorem germPoint_eq_germSection (hg : AnalyticOnNhd ℂ g U) (y : U) :
    germPoint g y =
      TopCat.Presheaf.EtaleSpace.germSection (holomorphicPresheaf E) U (toSection U g hg) y := by
  have hgerm : germAt g (y : ℂ) =
      (holomorphicPresheaf E).germ U (y : ℂ) y.2 (toSection U g hg) :=
    germAt_eq_germ_of_eventuallyEq y.2 _
      (Filter.eventuallyEq_of_mem (U.isOpen.mem_nhds y.2) (sectionFun_toSection hg))
  rw [TopCat.Presheaf.EtaleSpace.germSection_apply, germPoint, hgerm]

/-- **The germ map of a holomorphic function is a continuous section of the étalé projection.**
Over its domain it is exactly the section of the étalé space swept out by `g`
(`TauCeti.HolomorphicPresheaf.germPoint_eq_germSection`), so continuity is
`TauCeti.TopCat.Presheaf.EtaleSpace.continuous_germSection`. -/
theorem continuousOn_germPoint (hg : AnalyticOnNhd ℂ g U) : ContinuousOn (germPoint g) U := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hrestr : (U : Set ℂ).domRestrict (germPoint g) =
      TopCat.Presheaf.EtaleSpace.germSection (holomorphicPresheaf E) U (toSection U g hg) := by
    funext y
    rw [Set.domRestrict_apply]
    exact germPoint_eq_germSection hg y
  rw [hrestr]
  exact TopCat.Presheaf.EtaleSpace.continuous_germSection U _

/-! ### Representatives of a point of the étalé space -/

/-- **Every point of the étalé space carries the germ of a function analytic at its base
point.** -/
theorem exists_analyticAt_germAt_eq (p : (holomorphicPresheaf E).EtaleSpace) :
    ∃ g : ℂ → E, AnalyticAt ℂ g p.base ∧ germAt g p.base = p.germ := by
  obtain ⟨U, hU, s, hs⟩ := (holomorphicPresheaf E).exists_germ_eq p.germ
  exact ⟨sectionFun s, analyticOnNhd_sectionFun s _ hU, by rw [germAt_eq_germ hU s, hs]⟩

/-- A holomorphic representative of the germ carried by a point of the étalé space. -/
noncomputable def repFun (p : (holomorphicPresheaf E).EtaleSpace) : ℂ → E :=
  (exists_analyticAt_germAt_eq p).choose

/-- A representative of a point of the étalé space is analytic at its base point. -/
theorem analyticAt_repFun (p : (holomorphicPresheaf E).EtaleSpace) :
    AnalyticAt ℂ (repFun p) p.base :=
  (exists_analyticAt_germAt_eq p).choose_spec.1

/-- A representative of a point of the étalé space carries the germ that point carries. -/
@[simp]
theorem germAt_repFun (p : (holomorphicPresheaf E).EtaleSpace) :
    germAt (repFun p) p.base = p.germ :=
  (exists_analyticAt_germAt_eq p).choose_spec.2

/-- Taking a representative and then its germ point recovers the point of the étalé space. -/
@[simp]
theorem germPoint_repFun (p : (holomorphicPresheaf E).EtaleSpace) :
    germPoint (repFun p) p.base = p := by
  cases p
  rw [germPoint, germAt_repFun]

/-! ### The projection is a separated local homeomorphism -/

omit [CompleteSpace E] in
/-- **The étalé projection of the sheaf of holomorphic functions is a separated map**: two
distinct germs at the same point of `ℂ` have disjoint neighbourhoods in the étalé space.

This is the identity theorem for holomorphic functions, read in the étalé space. Two sections
representing the two germs are restricted to one disc about the common base point; the two open
sets swept out by their germs over that disc are disjoint, because a point of both would be a
point where the two representatives have the same germ, and the identity theorem on the disc —
which is connected — would then propagate that agreement back to the base point. -/
theorem isSeparatedMap_base :
    IsSeparatedMap (_root_.TopCat.Presheaf.EtaleSpace.base (F := holomorphicPresheaf E)) := by
  rintro ⟨x, g₁⟩ ⟨y, g₂⟩ hbase hne
  obtain rfl : x = y := hbase
  obtain ⟨U₁, hxU₁, s₁, hs₁⟩ := (holomorphicPresheaf E).exists_germ_eq g₁
  obtain ⟨U₂, hxU₂, s₂, hs₂⟩ := (holomorphicPresheaf E).exists_germ_eq g₂
  obtain ⟨r, hr, hrU⟩ : ∃ r > 0, ball x r ⊆ (U₁ : Set ℂ) ∩ (U₂ : Set ℂ) :=
    Metric.isOpen_iff.mp (U₁.isOpen.inter U₂.isOpen) x ⟨hxU₁, hxU₂⟩
  set B : Opens (TopCat.of ℂ) := ⟨ball x r, isOpen_ball⟩
  have hxB : x ∈ B := mem_ball_self hr
  have hB₁ : B ≤ U₁ := fun z hz => (hrU hz).1
  have hB₂ : B ≤ U₂ := fun z hz => (hrU hz).2
  set t₁ := (holomorphicPresheaf E).map (homOfLE hB₁).op s₁ with ht₁def
  set t₂ := (holomorphicPresheaf E).map (homOfLE hB₂).op s₂ with ht₂def
  have ht₁ : (holomorphicPresheaf E).germ B x hxB t₁ = g₁ := by
    rw [ht₁def, (holomorphicPresheaf E).germ_res_apply, hs₁]
  have ht₂ : (holomorphicPresheaf E).germ B x hxB t₂ = g₂ := by
    rw [ht₂def, (holomorphicPresheaf E).germ_res_apply, hs₂]
  have hopen₁ : IsOpen (TopCat.Presheaf.EtaleSpace.sectionRange (holomorphicPresheaf E) B t₁) :=
    TopCat.Presheaf.EtaleSpace.isOpen_sectionRange (F := holomorphicPresheaf E) B t₁
  have hopen₂ : IsOpen (TopCat.Presheaf.EtaleSpace.sectionRange (holomorphicPresheaf E) B t₂) :=
    TopCat.Presheaf.EtaleSpace.isOpen_sectionRange (F := holomorphicPresheaf E) B t₂
  refine ⟨_, _, hopen₁, hopen₂,
    TopCat.Presheaf.EtaleSpace.mem_sectionRange_iff (F := holomorphicPresheaf E) |>.mpr
      ⟨hxB, ht₁.symm⟩,
    TopCat.Presheaf.EtaleSpace.mem_sectionRange_iff (F := holomorphicPresheaf E) |>.mpr
      ⟨hxB, ht₂.symm⟩, ?_⟩
  refine Set.disjoint_left.mpr fun p hp₁ hp₂ => ?_
  obtain ⟨hpB, hpt₁⟩ :=
    TopCat.Presheaf.EtaleSpace.mem_sectionRange_iff (F := holomorphicPresheaf E) |>.mp hp₁
  obtain ⟨hpB', hpt₂⟩ :=
    TopCat.Presheaf.EtaleSpace.mem_sectionRange_iff (F := holomorphicPresheaf E) |>.mp hp₂
  have hev : sectionFun t₁ =ᶠ[𝓝 p.base] sectionFun t₂ :=
    (germ_eq_iff hpB hpB' t₁ t₂).mp (hpt₁.symm.trans hpt₂)
  have hEqOn : EqOn (sectionFun t₁) (sectionFun t₂) (B : Set ℂ) :=
    (analyticOnNhd_sectionFun t₁).eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_sectionFun t₂) (convex_ball x r).isPreconnected hpB hev
  have hgerm : (holomorphicPresheaf E).germ B x hxB t₁ = (holomorphicPresheaf E).germ B x hxB t₂ :=
    (germ_eq_iff hxB hxB t₁ t₂).mpr
      (Filter.eventuallyEq_of_mem (B.isOpen.mem_nhds hxB) hEqOn)
  exact hne (by rw [← ht₁, ← ht₂, hgerm])

end HolomorphicPresheaf

end TauCeti
