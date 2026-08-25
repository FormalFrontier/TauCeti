/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# Short exact sequences of discrete modules, and the low-degree connecting maps

A short exact sequence `0 → A → B → C → 0` of **discrete** `G`-modules induces short exact
sequences of *continuous* cochains

```text
0 → Cⁿ(G, A) → Cⁿ(G, B) → Cⁿ(G, C) → 0,
```

and hence connecting homomorphisms `δ⁰ : H⁰(G, C) → H¹(G, A)` and `δ¹ : H¹(G, C) → H²(G, A)` on
the explicit low-degree complex of
`TauCeti/RepresentationTheory/Homological/ContCohomology/LowDegree.lean`. This file builds both.

Surjectivity on cochains is where this file uses discreteness of the coefficients: a continuous
cochain into a discrete `C` is locally constant, so composing it with *any* set-theoretic section
of `B → C` is still continuous
(`TauCeti.ContCohomology.DiscreteShortExact.exists_continuous_lift`). For general topological
coefficients this argument does not apply because a set-theoretic section need not be continuous;
the cochain map can still be surjective when suitable continuous lifts exist. Nothing below is
asserted in that more general setting.

The sequence is carried by a structure rather than by loose hypotheses because every statement
here — and, later, the compatibility of corestriction with the connecting maps — is about the same
sequence and has to name the same two coefficient maps.

## Main definitions

* `TauCeti.ContCohomology.DiscreteShortExact`: a short exact sequence of discrete `G`-modules.
* `TauCeti.ContCohomology.DiscreteShortExact.restrict`: the same sequence over a subgroup.
* `TauCeti.ContCohomology.DiscreteShortExact.retract`: the retraction of `incl` onto its image,
  which turns a cochain into `B` killed by `proj` into a cochain into `A`.
* `TauCeti.ContCohomology.DiscreteShortExact.liftCochain`: the lift of a cochain into `C` along a
  fixed set-theoretic section of `proj`.
* `TauCeti.ContCohomology.DiscreteShortExact.delta0Cochain` and `delta1Cochain`: the cochains
  representing the two connecting maps, together with their classes `delta0Class` and
  `delta1Class` at a variable preimage.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0` and
  `TauCeti.ContCohomology.DiscreteShortExact.explicitDelta1`: the connecting homomorphisms
  `H⁰(G, C) → H¹(G, A)` and `H¹(G, C) → H²(G, A)`.

## Main statements

* `TauCeti.ContCohomology.DiscreteShortExact.exists_continuous_lift`: a continuous cochain on any
  topological space lifts to a continuous cochain into `B`. This is the degree-agnostic form of
  surjectivity of `Cⁿ(G, B) → Cⁿ(G, C)`.
* `TauCeti.ContCohomology.DiscreteShortExact.compLeft_incl_injective`, `C1_map_incl` and
  `C1_map_proj`: exactness of `0 → C¹(X, A) → C¹(X, B) → C¹(X, C) → 0` at its three nodes, with
  `C2_map_incl` and `C2_map_proj` its degree-`2` instances at `X = G × G`.
* `TauCeti.ContCohomology.DiscreteShortExact.delta0Class_congr` and `delta1Class_congr`: the two
  connecting maps do not depend on the chosen preimage.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0_apply` and
  `explicitDelta1_apply`: the two connecting maps evaluated on representatives, in the shape of
  Mathlib's discrete `groupCohomology.δ₀_apply` and `δ₁_apply`.

## Implementation notes

Continuity of `incl` and of `proj` is *not* carried as data: `A` and `B` are discrete, so every
map out of them is continuous. The two facts are supplied as the theorems
`TauCeti.ContCohomology.DiscreteShortExact.incl_continuous` and `proj_continuous`, so that a
consumer writes `S.incl_continuous` exactly as if they were fields. Exactness in the middle is
Mathlib's `Function.Exact`, which is `∀ b, proj b = 0 ↔ b ∈ Set.range incl`.

The cochain maps are Mathlib's `AddMonoidHom.compLeft`, postcomposition on a function space; the
statements of exactness are therefore about the image and kernel of that homomorphism restricted
to the cochain subgroup `C¹ X -`, which is `C¹(G, -)` at `X = G` and `C²(G, -)` at `X = G × G`.
The compatible-pair pullback of Layer 2 is a different map — it moves the group as well as the
coefficients — and is not used here.

Both connecting maps are built from a *variable* preimage first, `delta0Class` and `delta1Class`,
and the independence of the choice is a theorem (`delta0Class_congr`, `delta1Class_congr`) rather
than a definitional accident; only then is the public map defined by choosing a preimage with
`Function.surjInv`. This is what makes `explicitDelta0_apply` and `explicitDelta1_apply` usable
with whatever preimage a computation has in hand.

Everything is stated for a topological monoid `G`, and degree `2` adds a continuous
multiplication, since that is all the differentials and the two quotients need; profiniteness
plays no part in this layer.

This implements the "exactness of cochains" and "the short exact sequence as data" milestones of
Layer 5 of the human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`, together
with the two connecting maps and their descriptions on representatives from that layer's long
exact sequence milestone, whose `Suggested.lean` fixes the names `DiscreteShortExact`,
`DiscreteShortExact.restrict`, `explicitDelta0`, `explicitDelta0_apply`, `explicitDelta1` and
`explicitDelta1_apply`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.3.2): the long
  exact cohomology sequence of a short exact sequence of discrete `G`-modules, whose degree-`≤ 2`
  connecting maps are the ones built here.
-/

public section

namespace TauCeti.ContCohomology

universe u vA vB vC w

/-- A short exact sequence `0 → A → B → C → 0` of discrete `G`-modules.

Discreteness of the three modules is the sufficient hypothesis used here to make arbitrary
set-theoretic lifts of continuous cochains continuous. Continuity of the two maps is a consequence
of it, not data: see
`TauCeti.ContCohomology.DiscreteShortExact.incl_continuous`. -/
structure DiscreteShortExact (G : Type u) [Monoid G]
    (A : Type vA) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A]
    (B : Type vB) [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B]
    (C : Type vC) [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] where
  /-- The inclusion `A → B`. -/
  incl : A →+ B
  /-- The projection `B → C`. -/
  proj : B →+ C
  /-- The inclusion is `G`-equivariant. -/
  incl_equivariant : ∀ (g : G) (a : A), incl (g • a) = g • incl a
  /-- The projection is `G`-equivariant. -/
  proj_equivariant : ∀ (g : G) (b : B), proj (g • b) = g • proj b
  /-- Exactness on the left. -/
  incl_injective : Function.Injective incl
  /-- Exactness on the right. -/
  proj_surjective : Function.Surjective proj
  /-- Exactness in the middle: `proj b = 0` exactly when `b` comes from `A`. -/
  exact : Function.Exact incl proj

namespace DiscreteShortExact

section Basic

variable {G : Type u} [Monoid G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- Two short exact sequences with the same inclusion and projection are equal. -/
@[ext]
theorem ext {S T : DiscreteShortExact G A B C} (hincl : S.incl = T.incl)
    (hproj : S.proj = T.proj) : S = T := by
  cases S
  cases T
  cases hincl
  cases hproj
  rfl

/-- The inclusion is continuous, `A` being discrete. -/
theorem incl_continuous : Continuous S.incl := continuous_of_discreteTopology

/-- The projection is continuous, `B` being discrete. -/
theorem proj_continuous : Continuous S.proj := continuous_of_discreteTopology

/-- The composite `A → B → C` vanishes. -/
@[simp]
theorem proj_incl (a : A) : S.proj (S.incl a) = 0 := S.exact.apply_apply_eq_zero a

/-- An element of `B` killed by the projection comes from `A`. -/
theorem exists_incl_eq {b : B} (hb : S.proj b = 0) : ∃ a : A, S.incl a = b := S.exact b |>.1 hb

end Basic

section Restrict

variable {G : Type u} [Group G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- A short exact sequence of discrete `G`-modules restricts to one of discrete `T`-modules, for
any subgroup `T ≤ G`. The two maps are unchanged; the naturality of the connecting maps under
restriction is stated against this sequence. -/
def restrict (T : Subgroup G) : DiscreteShortExact T A B C where
  incl := S.incl
  proj := S.proj
  incl_equivariant t a := S.incl_equivariant (t : G) a
  proj_equivariant t b := S.proj_equivariant (t : G) b
  incl_injective := S.incl_injective
  proj_surjective := S.proj_surjective
  exact := S.exact

@[simp]
theorem restrict_incl (T : Subgroup G) : (S.restrict T).incl = S.incl := (rfl)

@[simp]
theorem restrict_proj (T : Subgroup G) : (S.restrict T).proj = S.proj := (rfl)

end Restrict

section Retract

variable {G : Type u} [Monoid G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- The retraction of the inclusion onto its image. It is a left inverse of `S.incl` everywhere
(`retract_incl`) and a right inverse of it on the kernel of `S.proj` (`incl_retract`), which is
the only place its value is used: it is what turns a cochain into `B` killed by the projection
into a cochain into `A`. -/
noncomputable def retract : B → A := Function.invFun S.incl

@[simp]
theorem retract_incl (a : A) : S.retract (S.incl a) = a :=
  Function.leftInverse_invFun S.incl_injective a

/-- On the kernel of the projection the retraction is a genuine section of the inclusion. -/
theorem incl_retract {b : B} (hb : S.proj b = 0) : S.incl (S.retract b) = b :=
  Function.invFun_eq (S.exists_incl_eq hb)

/-- The retraction is pinned by `incl_retract`: on the kernel of the projection it is the unique
preimage. Every algebraic identity below is an instance of this and the injectivity of the
inclusion. -/
theorem retract_eq_iff {b : B} (hb : S.proj b = 0) {a : A} : S.retract b = a ↔ b = S.incl a :=
  ⟨fun h => by rw [← h, S.incl_retract hb], fun h => by rw [h, S.retract_incl]⟩

@[simp]
theorem retract_zero : S.retract (0 : B) = 0 := by
  simpa using S.retract_incl 0

theorem retract_add {b b' : B} (hb : S.proj b = 0) (hb' : S.proj b' = 0) :
    S.retract (b + b') = S.retract b + S.retract b' :=
  (S.retract_eq_iff (by rw [map_add, hb, hb', add_zero])).2 <| by
    rw [map_add, S.incl_retract hb, S.incl_retract hb']

theorem retract_sub {b b' : B} (hb : S.proj b = 0) (hb' : S.proj b' = 0) :
    S.retract (b - b') = S.retract b - S.retract b' :=
  (S.retract_eq_iff (by rw [map_sub, hb, hb', sub_zero])).2 <| by
    rw [map_sub, S.incl_retract hb, S.incl_retract hb']

theorem retract_smul (g : G) {b : B} (hb : S.proj b = 0) :
    S.retract (g • b) = g • S.retract b :=
  (S.retract_eq_iff (by rw [S.proj_equivariant, hb, smul_zero])).2 <| by
    rw [S.incl_equivariant, S.incl_retract hb]

/-- The inclusion reflects continuity: both `A` and `B` are discrete and `S.incl` is injective, so
the fibres of a map into `A` are fibres of its composite with the inclusion. -/
theorem continuous_of_incl_comp {X : Type*} [TopologicalSpace X] {a : X → A}
    (h : Continuous fun x => S.incl (a x)) : Continuous a := by
  rw [continuous_def]
  intro s _
  have hs : a ⁻¹' s = (fun x => S.incl (a x)) ⁻¹' (S.incl '' s) := by
    ext x
    simp only [Set.mem_preimage, S.incl_injective.mem_set_image]
  rw [hs]
  exact h.isOpen_preimage _ (isOpen_discrete _)

/-- Retracting a continuous cochain that is killed by the projection leaves it continuous. -/
theorem continuous_retract_comp {X : Type*} [TopologicalSpace X] {φ : X → B} (hφ : Continuous φ)
    (h0 : ∀ x, S.proj (φ x) = 0) : Continuous fun x => S.retract (φ x) :=
  S.continuous_of_incl_comp <| by
    simpa only [fun x => S.incl_retract (h0 x)] using hφ

end Retract

section Cochains

variable {G : Type u} [Monoid G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C) {X : Type w} [TopologicalSpace X]

/-- The lift of a cochain into `C` obtained by composing it with a fixed set-theoretic section of
the projection. It is continuous whenever the cochain is, `C` being discrete. -/
noncomputable def liftCochain (f : X → C) : X → B :=
  fun x => Function.surjInv S.proj_surjective (f x)

omit [TopologicalSpace X] in
@[simp]
theorem proj_liftCochain (f : X → C) (x : X) : S.proj (S.liftCochain f x) = f x :=
  Function.surjInv_eq S.proj_surjective (f x)

/-- The lift of a continuous cochain is continuous: the cochain is locally constant, `C` being
discrete, so composing it with an arbitrary section changes nothing. -/
theorem continuous_liftCochain {f : X → C} (hf : Continuous f) : Continuous (S.liftCochain f) :=
  (continuous_of_discreteTopology (f := Function.surjInv S.proj_surjective)).comp hf

/-- **A continuous cochain lifts.** Discreteness is the sufficient hypothesis used here: `f` is
locally constant, so composing it with any set-theoretic section of the projection is continuous
again. Stated on an arbitrary topological space, hence in every degree at once. -/
theorem exists_continuous_lift {f : X → C} (hf : Continuous f) :
    ∃ e : X → B, Continuous e ∧ ∀ x, S.proj (e x) = f x :=
  ⟨S.liftCochain f, S.continuous_liftCochain hf, S.proj_liftCochain f⟩

/-- A continuous cochain into `B` killed by the projection comes from a continuous cochain into
`A`. The witness is the retraction of the cochain, and there is no other: the inclusion is
injective. -/
theorem exists_continuous_incl_comp_eq {φ : X → B} (hφ : Continuous φ)
    (hzero : ∀ x, S.proj (φ x) = 0) : ∃ a : X → A, Continuous a ∧ ∀ x, S.incl (a x) = φ x :=
  ⟨fun x => S.retract (φ x), S.continuous_retract_comp hφ hzero,
    fun x => S.incl_retract (hzero x)⟩

omit [TopologicalSpace X] in
variable (X) in
/-- Exactness of `0 → C¹(X, A) → C¹(X, B)` at the left node: postcomposition with the inclusion is
injective on all of `X → A`, so a fortiori on the continuous cochains. -/
theorem compLeft_incl_injective : Function.Injective (S.incl.compLeft X) :=
  fun _ _ h => funext fun x => S.incl_injective (congrFun h x)

variable (X) in
/-- Exactness of `0 → C¹(X, A) → C¹(X, B) → C¹(X, C) → 0` at the middle node: a continuous cochain
into `B` is killed by the projection exactly when it is the image of a continuous cochain into
`A`. Taking `X = G` this is degree `1`, and taking `X = G × G` it is degree `2`. -/
theorem C1_map_incl :
    AddSubgroup.map (S.incl.compLeft X) (C1 X A) = C1 X B ⊓ (S.proj.compLeft X).ker := by
  ext f
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha, rfl⟩
    exact AddSubgroup.mem_inf.2 ⟨mem_C1_iff.2 (S.incl_continuous.comp (mem_C1_iff.1 ha)),
      AddMonoidHom.mem_ker.2 (funext fun x => S.proj_incl (a x))⟩
  · intro hf
    obtain ⟨hcont, hker⟩ := AddSubgroup.mem_inf.1 hf
    obtain ⟨a, ha, hincl⟩ := S.exists_continuous_incl_comp_eq (mem_C1_iff.1 hcont)
      fun x => congrFun (AddMonoidHom.mem_ker.1 hker) x
    exact ⟨a, mem_C1_iff.2 ha, funext hincl⟩

variable (X) in
/-- Exactness of `C¹(X, B) → C¹(X, C) → 0` at the right node: every continuous cochain into `C`
lifts, by `TauCeti.ContCohomology.DiscreteShortExact.exists_continuous_lift`. -/
theorem C1_map_proj : AddSubgroup.map (S.proj.compLeft X) (C1 X B) = C1 X C := by
  ext f
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨e, he, rfl⟩
    exact mem_C1_iff.2 (S.proj_continuous.comp (mem_C1_iff.1 he))
  · obtain ⟨e, he, hef⟩ := S.exists_continuous_lift (mem_C1_iff.1 hf)
    exact ⟨e, mem_C1_iff.2 he, funext hef⟩

end Cochains

section LowDegreeCochains

variable {G : Type u} [Monoid G] [TopologicalSpace G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- Exactness of `0 → C²(G, A) → C²(G, B) → C²(G, C) → 0` in the middle: the degree-`2` instance
of `TauCeti.ContCohomology.DiscreteShortExact.C1_map_incl`, at `X = G × G`. -/
theorem C2_map_incl :
    AddSubgroup.map (S.incl.compLeft (G × G)) (C2 G A) =
      C2 G B ⊓ (S.proj.compLeft (G × G)).ker := by
  simp only [C2_eq_C1]
  exact S.C1_map_incl (G × G)

/-- Exactness of `0 → C²(G, A) → C²(G, B) → C²(G, C) → 0` on the right: the degree-`2` instance of
`TauCeti.ContCohomology.DiscreteShortExact.C1_map_proj`, at `X = G × G`. -/
theorem C2_map_proj : AddSubgroup.map (S.proj.compLeft (G × G)) (C2 G B) = C2 G C := by
  simp only [C2_eq_C1]
  exact S.C1_map_proj (G × G)

end LowDegreeCochains

section Delta0Cochain

variable {G : Type u} [Monoid G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- The projection carries `d⁰` to `d⁰`. -/
theorem proj_d0_apply (b : B) (g : G) : S.proj (d0 G B b g) = d0 G C (S.proj b) g := by
  simp only [d0_apply, map_sub, S.proj_equivariant]

/-- The `1`-cochain attached to an element `b : B` whose image in `C` is invariant: the retraction
of `d⁰ b`, which is killed by the projection exactly because that image is invariant. -/
noncomputable def delta0Cochain (b : B) : G → A := fun g => S.retract (d0 G B b g)

variable {S}

/-- The coboundary of a preimage of an invariant is killed by the projection. This is what makes
`TauCeti.ContCohomology.DiscreteShortExact.delta0Cochain` well defined. -/
theorem proj_d0_eq_zero {b : B} (hb : ∀ g : G, g • S.proj b = S.proj b) (g : G) :
    S.proj (d0 G B b g) = 0 := by
  rw [S.proj_d0_apply, d0_apply, hb g, sub_self]

/-- The defining property of `TauCeti.ContCohomology.DiscreteShortExact.delta0Cochain`: it is the
unique cochain into `A` whose image in `B` is `d⁰ b`. -/
theorem incl_delta0Cochain {b : B} (hb : ∀ g : G, g • S.proj b = S.proj b) (g : G) :
    S.incl (S.delta0Cochain b g) = g • b - b :=
  (S.incl_retract (proj_d0_eq_zero hb g)).trans (d0_apply b g)

/-- The cochain of a sum of preimages is the sum of their cochains. -/
theorem delta0Cochain_add {b b' : B} (hb : ∀ g : G, g • S.proj b = S.proj b)
    (hb' : ∀ g : G, g • S.proj b' = S.proj b') :
    S.delta0Cochain (b + b') = S.delta0Cochain b + S.delta0Cochain b' := by
  have hbb' : ∀ g : G, g • S.proj (b + b') = S.proj (b + b') := fun g => by
    rw [map_add, smul_add, hb, hb']
  refine funext fun g => S.incl_injective ?_
  rw [incl_delta0Cochain hbb', Pi.add_apply, map_add, incl_delta0Cochain hb,
    incl_delta0Cochain hb', smul_add]
  abel

end Delta0Cochain

section Delta0

variable {G : Type u} [Monoid G] [TopologicalSpace G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A]
    [ContinuousSMul G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B]
    [ContinuousSMul G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C]
  {S : DiscreteShortExact G A B C}

omit [ContinuousSMul G A] in
/-- The cochain attached to a preimage of an invariant is a continuous `1`-cocycle. Continuity is
`continuous_retract_comp` applied to the continuous cochain `d⁰ b`, and the cocycle identity is
the one satisfied by `d⁰ b` in `B`, transported by the injectivity of the inclusion. -/
theorem delta0Cochain_mem_Z1 {b : B} (hb : ∀ g : G, g • S.proj b = S.proj b) :
    S.delta0Cochain b ∈ Z1 G A := by
  refine mem_Z1_iff.2 ⟨S.continuous_retract_comp (continuous_d0_apply b) (proj_d0_eq_zero hb),
    fun g h => S.incl_injective ?_⟩
  rw [incl_delta0Cochain hb, map_add, S.incl_equivariant, incl_delta0Cochain hb,
    incl_delta0Cochain hb, smul_sub, ← mul_smul]
  abel

variable (S) in
/-- The class in `H¹(G, A)` of the cochain attached to a chosen preimage. The public connecting
map is this class at the preimage `Function.surjInv S.proj_surjective`; the choice does not matter
by `TauCeti.ContCohomology.DiscreteShortExact.delta0Class_congr`. -/
noncomputable def delta0Class (b : B) (hb : ∀ g : G, g • S.proj b = S.proj b) : H1 G A :=
  H1pi G A ⟨S.delta0Cochain b, delta0Cochain_mem_Z1 hb⟩

/-- Two preimages of the same invariant of `C` give the same class: their difference comes from
`A`, and the two cochains differ by its coboundary. -/
theorem delta0Class_congr {b b' : B} (hb : ∀ g : G, g • S.proj b = S.proj b)
    (hb' : ∀ g : G, g • S.proj b' = S.proj b') (h : S.proj b = S.proj b') :
    S.delta0Class b hb = S.delta0Class b' hb' := by
  obtain ⟨a₀, ha₀⟩ := S.exists_incl_eq (b := b' - b) (by rw [map_sub, h, sub_self])
  refine H1pi_eq_iff.2 (mem_B1_iff.2 ⟨-a₀, fun g => S.incl_injective ?_⟩)
  have h₁ : S.incl (S.delta0Cochain b g) = g • b - b := incl_delta0Cochain hb g
  have h₂ : S.incl (S.delta0Cochain b' g) = g • b' - b' := incl_delta0Cochain hb' g
  simp only [Pi.sub_apply]
  rw [map_sub, S.incl_equivariant, map_neg, ha₀, map_sub, h₁, h₂, smul_neg, smul_sub]
  abel

/-- The class attached to a sum of preimages is the sum of the classes. -/
theorem delta0Class_add {b b' : B} (hb : ∀ g : G, g • S.proj b = S.proj b)
    (hb' : ∀ g : G, g • S.proj b' = S.proj b')
    (hbb' : ∀ g : G, g • S.proj (b + b') = S.proj (b + b')) :
    S.delta0Class (b + b') hbb' = S.delta0Class b hb + S.delta0Class b' hb' := by
  rw [delta0Class, delta0Class, delta0Class, ← map_add]
  exact congrArg (H1pi G A) (Subtype.ext (delta0Cochain_add hb hb'))

variable (S)

omit [TopologicalSpace G] [ContinuousSMul G A] [ContinuousSMul G B] in
/-- The chosen preimage of an invariant of `C` has invariant image, tautologically. -/
theorem surjInv_invariant (c : H0 G C) (g : G) :
    g • S.proj (Function.surjInv S.proj_surjective (c : C)) =
      S.proj (Function.surjInv S.proj_surjective (c : C)) := by
  rw [Function.surjInv_eq S.proj_surjective]
  exact (FixedPoints.mem_addSubgroup G C (c : C)).1 c.2 g

/-- **The connecting homomorphism `δ⁰ : H⁰(G, C) → H¹(G, A)`.** Choose a preimage in `B` of an
invariant of `C` and take the class of the retraction of its coboundary. -/
noncomputable def explicitDelta0 : H0 G C →+ H1 G A :=
  AddMonoidHom.mk' (fun c => S.delta0Class _ (S.surjInv_invariant c)) fun c c' => by
    have hsum : ∀ g : G, g • S.proj (Function.surjInv S.proj_surjective (c : C) +
        Function.surjInv S.proj_surjective (c' : C)) =
        S.proj (Function.surjInv S.proj_surjective (c : C) +
          Function.surjInv S.proj_surjective (c' : C)) := fun g => by
      rw [map_add, smul_add, S.surjInv_invariant c g, S.surjInv_invariant c' g]
    rw [← delta0Class_add (S.surjInv_invariant c) (S.surjInv_invariant c') hsum]
    exact delta0Class_congr _ hsum (by
      rw [Function.surjInv_eq S.proj_surjective, map_add, Function.surjInv_eq S.proj_surjective,
        Function.surjInv_eq S.proj_surjective, AddSubgroup.coe_add])

/-- **`δ⁰` on representatives.** For *any* preimage `b` of an invariant `c` and any continuous
`1`-cocycle `a` with `incl ∘ a = d⁰ b`, the class of `a` is `δ⁰ c`. This mirrors the shape of
Mathlib's discrete `groupCohomology.δ₀_apply`. -/
theorem explicitDelta0_apply (c : H0 G C) {b : B} (hb : S.proj b = (c : C)) {a : G → A}
    (ha : a ∈ Z1 G A) (hab : ∀ g : G, S.incl (a g) = g • b - b) :
    S.explicitDelta0 c = H1pi G A ⟨a, ha⟩ := by
  have hbinv : ∀ g : G, g • S.proj b = S.proj b := fun g => by
    rw [hb]
    exact (FixedPoints.mem_addSubgroup G C (c : C)).1 c.2 g
  have hcochain : a = S.delta0Cochain b :=
    funext fun g => S.incl_injective (by rw [hab, incl_delta0Cochain hbinv])
  rw [explicitDelta0, AddMonoidHom.mk'_apply,
    delta0Class_congr (S.surjInv_invariant c) hbinv
      (by rw [Function.surjInv_eq S.proj_surjective, hb]), delta0Class]
  exact congrArg (H1pi G A) (Subtype.ext hcochain.symm)

end Delta0

section Delta1Cochain

variable {G : Type u} [Monoid G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- The projection carries `d¹` to `d¹`. -/
theorem proj_d1_apply (e : G → B) (g h : G) :
    S.proj (d1 G B e (g, h)) = d1 G C (fun x => S.proj (e x)) (g, h) := by
  simp only [d1_apply, map_add, map_sub, S.proj_equivariant]

/-- The inclusion carries `d¹` to `d¹`. -/
theorem incl_d1_apply (u : G → A) (g h : G) :
    S.incl (d1 G A u (g, h)) = d1 G B (fun x => S.incl (u x)) (g, h) := by
  simp only [d1_apply, map_add, map_sub, S.incl_equivariant]

/-- The `2`-cochain attached to a lift `e : G → B` of a `1`-cocycle on `C`: the retraction of
`d¹ e`, which is killed by the projection exactly because the cocycle is one. -/
noncomputable def delta1Cochain (e : G → B) : G × G → A := fun p => S.retract (d1 G B e p)

variable {S}

/-- The `d¹` of a lift of a `1`-cocycle is killed by the projection. This is what makes
`TauCeti.ContCohomology.DiscreteShortExact.delta1Cochain` well defined. -/
theorem proj_d1_eq_zero {e : G → B} {f : G → C} (he : ∀ g, S.proj (e g) = f g)
    (hf : groupCohomology.IsCocycle₁ f) (p : G × G) : S.proj (d1 G B e p) = 0 := by
  obtain ⟨g, h⟩ := p
  rw [S.proj_d1_apply]
  simp only [d1_apply, he, hf g h]
  abel

/-- The defining property of `TauCeti.ContCohomology.DiscreteShortExact.delta1Cochain`: it is the
unique cochain into `A` whose image in `B` is `d¹ e`. -/
theorem incl_delta1Cochain {e : G → B} {f : G → C} (he : ∀ g, S.proj (e g) = f g)
    (hf : groupCohomology.IsCocycle₁ f) (p : G × G) :
    S.incl (S.delta1Cochain e p) = d1 G B e p :=
  S.incl_retract (proj_d1_eq_zero he hf p)

end Delta1Cochain

section Delta1

variable {G : Type u} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A]
    [ContinuousSMul G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B]
    [ContinuousSMul G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C]
  {S : DiscreteShortExact G A B C}

omit [ContinuousSMul G A] in
/-- The cochain attached to a lift of a continuous `1`-cocycle is a continuous `2`-cocycle: the
degree-`2` cocycle identity is `d² ∘ d¹ = 0` in `B`, transported by the injectivity of the
inclusion. -/
theorem delta1Cochain_mem_Z2 {e : G → B} (hc : Continuous e) {f : G → C}
    (he : ∀ g, S.proj (e g) = f g) (hf : groupCohomology.IsCocycle₁ f) :
    S.delta1Cochain e ∈ Z2 G A := by
  refine mem_Z2_iff.2 ⟨S.continuous_retract_comp (continuous_d1_apply hc)
    (proj_d1_eq_zero he hf), fun g h j => S.incl_injective ?_⟩
  rw [map_add, map_add, S.incl_equivariant, incl_delta1Cochain he hf, incl_delta1Cochain he hf,
    incl_delta1Cochain he hf, incl_delta1Cochain he hf]
  exact d2_apply_eq_zero_iff.1 (d2_comp_d1_apply e) g h j

variable (S) in
/-- The class in `H²(G, A)` of the cochain attached to a chosen continuous lift of a continuous
`1`-cocycle on `C`. The choice of lift does not matter, by
`TauCeti.ContCohomology.DiscreteShortExact.delta1Class_congr`. -/
noncomputable def delta1Class {e : G → B} (hc : Continuous e) {f : G → C}
    (he : ∀ g, S.proj (e g) = f g) (hf : groupCohomology.IsCocycle₁ f) : H2 G A :=
  H2pi G A ⟨S.delta1Cochain e, delta1Cochain_mem_Z2 hc he hf⟩

/-- Two continuous lifts of the same continuous `1`-cocycle give the same class: their difference
is the image of a continuous `1`-cochain on `A`, and the two `2`-cochains differ by its
coboundary. -/
theorem delta1Class_congr {e e' : G → B} (hc : Continuous e) (hc' : Continuous e')
    {f f' : G → C} (he : ∀ g, S.proj (e g) = f g) (he' : ∀ g, S.proj (e' g) = f' g)
    (hf : groupCohomology.IsCocycle₁ f) (hf' : groupCohomology.IsCocycle₁ f') (hff : f = f') :
    S.delta1Class hc he hf = S.delta1Class hc' he' hf' := by
  subst hff
  have hzero : ∀ g : G, S.proj (e' g - e g) = 0 := fun g => by
    rw [map_sub, he, he', sub_self]
  obtain ⟨u, hu, hincl⟩ :=
    S.exists_continuous_incl_comp_eq (hc'.sub hc) hzero
  refine H2pi_eq_iff.2 (mem_B2_iff.2 ⟨-u, hu.neg, funext fun p => ?_⟩)
  obtain ⟨g, h⟩ := p
  have hne : ∀ x : G, S.incl ((-u) x) = e x - e' x := fun x => by
    rw [Pi.neg_apply, map_neg, hincl, Pi.sub_apply]
    abel
  refine S.incl_injective ?_
  rw [incl_d1_apply]
  simp only [d1_apply, hne, Pi.sub_apply, map_sub S.incl, incl_delta1Cochain he hf,
    incl_delta1Cochain he' hf', smul_sub]
  abel

/-- The class attached to a sum of lifts is the sum of the classes. -/
theorem delta1Class_add {e e' : G → B} (hc : Continuous e) (hc' : Continuous e') {f f' : G → C}
    (he : ∀ g, S.proj (e g) = f g) (he' : ∀ g, S.proj (e' g) = f' g)
    (hf : groupCohomology.IsCocycle₁ f) (hf' : groupCohomology.IsCocycle₁ f')
    (hsum : ∀ g, S.proj ((e + e') g) = (f + f') g)
    (hfsum : groupCohomology.IsCocycle₁ (f + f')) :
    S.delta1Class (hc.add hc') hsum hfsum = S.delta1Class hc he hf + S.delta1Class hc' he' hf' := by
  rw [delta1Class, delta1Class, delta1Class, ← map_add]
  refine congrArg (H2pi G A) (Subtype.ext (funext fun p => S.incl_injective ?_))
  rw [incl_delta1Cochain hsum hfsum, AddSubgroup.coe_add, Pi.add_apply, map_add S.incl,
    incl_delta1Cochain he hf, incl_delta1Cochain he' hf']
  exact congrFun (map_add (d1 G B) e e') p

variable [ContinuousSMul G C]

omit [ContinuousMul G] [ContinuousSMul G A] [ContinuousSMul G B] [ContinuousSMul G C] in
/-- The canonical continuous lift of a continuous `1`-cocycle on `C`. -/
theorem continuous_liftCochain_coe (f : Z1 G C) : Continuous (S.liftCochain (f : G → C)) :=
  S.continuous_liftCochain (mem_Z1_iff.1 f.2).1

omit [ContinuousMul G] [ContinuousSMul G A] [ContinuousSMul G B] [ContinuousSMul G C] in
/-- The underlying function of a continuous `1`-cocycle satisfies the `1`-cocycle identity. -/
theorem isCocycle_coe (f : Z1 G C) : groupCohomology.IsCocycle₁ (f : G → C) :=
  (mem_Z1_iff.1 f.2).2

variable (S) in
/-- `δ¹` before descending to cohomology: the class in `H²(G, A)` attached to a continuous
`1`-cocycle on `C`, through its canonical lift. -/
noncomputable def delta1Hom : Z1 G C →+ H2 G A :=
  AddMonoidHom.mk'
    (fun f => S.delta1Class (S.continuous_liftCochain_coe f) (S.proj_liftCochain (f : G → C))
      (isCocycle_coe f))
    fun f f' => by
      have hsum : ∀ g : G, S.proj ((S.liftCochain (f : G → C) + S.liftCochain (f' : G → C)) g) =
          ((f : G → C) + (f' : G → C)) g := fun g => by
        rw [Pi.add_apply, map_add, S.proj_liftCochain, S.proj_liftCochain, Pi.add_apply]
      refine (delta1Class_congr _ ((S.continuous_liftCochain_coe f).add
        (S.continuous_liftCochain_coe f')) _ hsum _ (isCocycle_coe (f + f')) rfl).trans ?_
      exact delta1Class_add _ _ _ _ (isCocycle_coe f) (isCocycle_coe f') hsum
        (isCocycle_coe (f + f'))

omit [ContinuousSMul G C] in
/-- `δ¹` kills the coboundaries: a `1`-coboundary on `C` lifts to a `1`-coboundary on `B`, whose
`d¹` vanishes. -/
theorem delta1Hom_eq_zero_of_mem_B1 (f : Z1 G C) (hf : (f : G → C) ∈ B1 G C) :
    S.delta1Hom f = 0 := by
  obtain ⟨c, hc⟩ := mem_B1_iff.1 hf
  obtain ⟨b, hpb⟩ := S.proj_surjective c
  have he : ∀ g : G, S.proj (d0 G B b g) = (f : G → C) g := fun g => by
    rw [S.proj_d0_apply, hpb, d0_apply, hc g]
  have hzero : S.delta1Cochain (d0 G B b) = 0 := funext fun p => by
    rw [delta1Cochain, congrFun (d1_comp_d0_apply (G := G) b) p]
    exact S.retract_zero
  have hsubtype :
      (⟨S.delta1Cochain (d0 G B b),
          delta1Cochain_mem_Z2 (continuous_d0_apply (G := G) b) he (isCocycle_coe f)⟩ :
        Z2 G A) = 0 :=
    Subtype.ext hzero
  rw [delta1Hom, AddMonoidHom.mk'_apply,
    delta1Class_congr _ (continuous_d0_apply (G := G) b) _ he _ (isCocycle_coe f) rfl,
    delta1Class, hsubtype]
  exact map_zero _

variable (S) in
/-- **The connecting homomorphism `δ¹ : H¹(G, C) → H²(G, A)`.** Lift a continuous `1`-cocycle on
`C` to a continuous `1`-cochain on `B` and take the class of the retraction of its `d¹`. -/
noncomputable def explicitDelta1 : H1 G C →+ H2 G A :=
  QuotientAddGroup.lift ((B1 G C).addSubgroupOf (Z1 G C)) S.delta1Hom fun f hf =>
    S.delta1Hom_eq_zero_of_mem_B1 f (AddSubgroup.mem_addSubgroupOf.1 hf)

/-- **`δ¹` on representatives.** For *any* continuous lift `e` of a continuous `1`-cocycle `f` on
`C` and any continuous `2`-cocycle `a` with `incl ∘ a = d¹ e`, the class of `a` is `δ¹` of the
class of `f`. This mirrors the shape of Mathlib's discrete `groupCohomology.δ₁_apply`. -/
theorem explicitDelta1_apply (f : Z1 G C) {e : G → B} (hc : Continuous e)
    (he : ∀ g, S.proj (e g) = (f : G → C) g) {a : G × G → A} (ha : a ∈ Z2 G A)
    (hae : ∀ g h : G, S.incl (a (g, h)) = g • e h - e (g * h) + e g) :
    S.explicitDelta1 (H1pi G C f) = H2pi G A ⟨a, ha⟩ := by
  have hcochain : a = S.delta1Cochain e := funext fun p => by
    obtain ⟨g, h⟩ := p
    exact S.incl_injective (((hae g h).trans (d1_apply e g h).symm).trans
      (incl_delta1Cochain he (isCocycle_coe f) (g, h)).symm)
  have hlift : S.explicitDelta1 (H1pi G C f) = S.delta1Hom f := rfl
  rw [hlift, delta1Hom, AddMonoidHom.mk'_apply,
    delta1Class_congr _ hc _ he _ (isCocycle_coe f) rfl, delta1Class]
  exact congrArg (H2pi G A) (Subtype.ext hcochain.symm)

end Delta1

end DiscreteShortExact

end TauCeti.ContCohomology
