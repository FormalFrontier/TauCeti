/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Topology.LocallyConstant.Basic
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

Discreteness of the coefficients is used twice, once at each of the two ends of the sequence.
Discreteness of `C` gives surjectivity on cochains: a continuous cochain into `C` is locally
constant, so composing it with *any* set-theoretic section of `B → C` is still continuous
(`TauCeti.ContCohomology.exists_continuous_lift`). Discreteness of `A` and of `B` gives exactness
in the middle: an injection of discrete spaces reflects continuity
(`TauCeti.ContCohomology.continuous_of_injective_comp`), so a continuous cochain into `B` that the
projection kills retracts to a *continuous* cochain into `A`
(`TauCeti.ContCohomology.DiscreteShortExact.exists_continuous_incl_comp_eq`, whence
`C1_map_incl_eq_inf_ker`); it is also what makes `incl` and `proj` continuous. For general
topological coefficients neither argument applies, since a set-theoretic section need not be
continuous and a continuous cochain need not be locally constant; the cochain sequence can still
be exact when suitable continuous lifts exist. Nothing below is asserted in that more general
setting.

The sequence is carried by a structure rather than by loose hypotheses because every statement
here — and, later, the compatibility of corestriction with the connecting maps — is about the same
sequence and has to name the same two coefficient maps.

## Main definitions

* `TauCeti.ContCohomology.DiscreteShortExact`: a short exact sequence of discrete `G`-modules.
* `TauCeti.ContCohomology.DiscreteShortExact.restrict`: the same sequence over a subgroup.
* `TauCeti.ContCohomology.DiscreteShortExact.inclDistribMulActionHom` and
  `TauCeti.ContCohomology.DiscreteShortExact.projDistribMulActionHom`: the inclusion and projection
  bundled as equivariant additive homomorphisms, suitable as inputs to `explicitCoeff0`.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0` and
  `TauCeti.ContCohomology.DiscreteShortExact.explicitDelta1`: the connecting homomorphisms
  `H⁰(G, C) → H¹(G, A)` and `H¹(G, C) → H²(G, A)`.

## Main statements

* `TauCeti.ContCohomology.exists_continuous_lift`: a continuous cochain on any topological space
  lifts along any surjection onto a discrete space. This is the degree-agnostic form of
  surjectivity of `Cⁿ(G, B) → Cⁿ(G, C)`.
* `TauCeti.ContCohomology.continuous_of_injective_comp`: an injection of discrete spaces reflects
  continuity. This is the degree-agnostic form of exactness in the middle.
* `TauCeti.ContCohomology.DiscreteShortExact.compLeft_incl_injective`,
  `C1_map_incl_eq_inf_ker` and `C1_map_proj_eq_C1`: exactness of
  `0 → C¹(X, A) → C¹(X, B) → C¹(X, C) → 0` at its left, middle and right nodes, with
  `C2_map_incl_eq_inf_ker` and `C2_map_proj_eq_C2` the degree-`2` instances of the last two.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0_apply` and
  `explicitDelta1_apply`: the two connecting maps evaluated on representatives, in the shape of
  Mathlib's discrete `groupCohomology.δ₀_apply` and `δ₁_apply`. They hold for an *arbitrary*
  preimage and an arbitrary representing cocycle, so they are also the public form of the
  well-definedness of the two maps. Their cocycle hypotheses are discharged by
  `TauCeti.ContCohomology.DiscreteShortExact.mem_Z1_of_incl_comp_eq_d0` and
  `mem_Z2_of_incl_comp_eq_d1`, which need no cocycle input of their own.

## Implementation notes

Continuity of `incl` and of `proj` is *not* carried as data: `A` and `B` are discrete, so every
map out of them is continuous. Exactness in the middle is Mathlib's `Function.Exact`, which is
`∀ b, proj b = 0 ↔ b ∈ Set.range incl`.

The cochain maps are Mathlib's `AddMonoidHom.compLeft`, postcomposition on a function space; the
statements of exactness are therefore about the image and kernel of that homomorphism restricted
to the cochain subgroup `C¹ X -`, which is `C¹(G, -)` at `X = G` and `C²(G, -)` at `X = G × G`.
The compatible-pair pullback of Layer 2 is a different map — it moves the group as well as the
coefficients — and is not used here.

Both connecting maps are built from a *variable* preimage first, and the independence of the
choice is a theorem rather than a definitional accident; only then is the map defined by choosing
a preimage with `Function.surjInv`. The cochain-level constructions this passes through are
private, including the retraction used on the kernel of the projection, since they depend on
choices the mathematical statements must not mention; the public interface to them is
`explicitDelta0_apply` and `explicitDelta1_apply`, which hold with whatever preimage a computation
has in hand.

The cochain sequences are stated for a topological monoid `G`. The two connecting maps ask in
addition that the coefficients be discrete `G`-modules with a *continuous* action,
`[ContinuousSMul G A]` and `[ContinuousSMul G B]`: without it `B¹ ≤ Z¹` and `B² ≤ Z²` fail and the
quotients `H1` and `H2` cannot be formed. `δ¹` asks moreover for a continuous multiplication on
`G`, which is what carries continuity through `d¹`. `DiscreteShortExact.restrict` is the one
exception in the other direction: restricting the sequence to a subgroup asks `G` to be a group.
Profiniteness plays no part in this layer.

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

/-! ### Cochain lifting and descent

The two inputs from topology that make the continuous cochain sequences exact. Neither uses the
group, the action or the sequence, so both are stated for bare maps of topological spaces. -/

section Lift

variable {X : Type w} {B : Type vB} {C : Type vC} {p : B → C}

/-- The canonical lift of a cochain along a surjection: compose it with `Function.surjInv`. -/
private noncomputable def liftCochain (hp : Function.Surjective p) (f : X → C) : X → B :=
  fun x => Function.surjInv hp (f x)

/-- The canonical lift lies over the cochain it lifts. Not a `simp` lemma: the head of its
left-hand side is the variable `p`. -/
private theorem apply_liftCochain (hp : Function.Surjective p) (f : X → C) (x : X) :
    p (liftCochain hp f x) = f x := Function.surjInv_eq hp (f x)

variable [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace C] [DiscreteTopology C]

/-- The canonical lift of a continuous cochain is continuous, the target being discrete. -/
private theorem continuous_liftCochain (hp : Function.Surjective p) {f : X → C}
    (hf : Continuous f) : Continuous (liftCochain hp f) :=
  (continuous_of_discreteTopology (f := Function.surjInv hp)).comp hf

/-- **A continuous cochain lifts along any surjection onto a discrete space.** Discreteness of the
target is the sufficient hypothesis used here: `f` is locally constant, so composing it with any
set-theoretic section of `p` is continuous again. Stated on an arbitrary topological space and for
a bare surjection, hence in every degree at once. -/
theorem exists_continuous_lift (hp : Function.Surjective p) {f : X → C} (hf : Continuous f) :
    ∃ e : X → B, Continuous e ∧ ∀ x, p (e x) = f x :=
  ⟨liftCochain hp f, continuous_liftCochain hp hf, apply_liftCochain hp f⟩

end Lift

section Descent

variable {X : Type w} [TopologicalSpace X] {A : Type vA} [TopologicalSpace A] [DiscreteTopology A]
  {B : Type vB} [TopologicalSpace B] [DiscreteTopology B]

/-- **An injective map of discrete spaces reflects continuity.** Continuity into the discrete `A`
and `B` is local constancy, and local constancy descends along an injection. -/
theorem continuous_of_injective_comp {f : A → B} (hf : Function.Injective f) {a : X → A}
    (h : Continuous fun x => f (a x)) : Continuous a :=
  (IsLocallyConstant.iff_continuous a).1 <|
    IsLocallyConstant.desc a f ((IsLocallyConstant.iff_continuous _).2 h) hf

end Descent

/-- A short exact sequence `0 → A → B → C → 0` of discrete `G`-modules.

Discreteness of the three modules is what makes the continuous cochain sequences exact:
discreteness of `C` makes arbitrary set-theoretic lifts of continuous cochains continuous, and
discreteness of `A` and `B` makes the inclusion reflect continuity, which is what retracts a
continuous cochain killed by the projection. Continuity of the two maps is a further consequence
of it, not data. -/
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

/-- The composite `A → B → C` vanishes. -/
@[simp]
theorem proj_incl (a : A) : S.proj (S.incl a) = 0 := S.exact.apply_apply_eq_zero a

/-- The inclusion of a short exact sequence, bundled as an equivariant additive homomorphism. -/
def inclDistribMulActionHom : A →+[G] B where
  toAddMonoidHom := S.incl
  map_smul' := S.incl_equivariant

/-- The projection of a short exact sequence, bundled as an equivariant additive homomorphism. -/
def projDistribMulActionHom : B →+[G] C where
  toAddMonoidHom := S.proj
  map_smul' := S.proj_equivariant

@[simp]
theorem inclDistribMulActionHom_apply (a : A) : S.inclDistribMulActionHom a = S.incl a := (rfl)

@[simp]
theorem projDistribMulActionHom_apply (b : B) : S.projDistribMulActionHom b = S.proj b := (rfl)

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
private noncomputable def retract : B → A := Function.invFun S.incl

@[simp]
private theorem retract_incl (a : A) : S.retract (S.incl a) = a :=
  Function.leftInverse_invFun S.incl_injective a

/-- On the kernel of the projection the retraction is a genuine section of the inclusion. -/
private theorem incl_retract {b : B} (hb : S.proj b = 0) : S.incl (S.retract b) = b :=
  Function.invFun_eq (S.exists_incl_eq hb)

@[simp]
private theorem retract_zero : S.retract (0 : B) = 0 := by
  simpa using S.retract_incl 0

/-- Retracting a continuous cochain that is killed by the projection leaves it continuous. -/
private theorem continuous_retract_comp {X : Type*} [TopologicalSpace X] {φ : X → B}
    (hφ : Continuous φ) (h0 : ∀ x, S.proj (φ x) = 0) :
    Continuous fun x => S.retract (φ x) :=
  continuous_of_injective_comp S.incl_injective <| by
    simpa only [fun x => S.incl_retract (h0 x)] using hφ

end Retract

section Cochains

variable {G : Type u} [Monoid G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C) {X : Type w} [TopologicalSpace X]

/-- A continuous cochain into `B` killed by the projection comes from a continuous cochain into
`A`, obtained by retracting the cochain pointwise. -/
theorem exists_continuous_incl_comp_eq {φ : X → B} (hφ : Continuous φ)
    (hzero : ∀ x, S.proj (φ x) = 0) : ∃ a : X → A, Continuous a ∧ ∀ x, S.incl (a x) = φ x :=
  ⟨fun x => S.retract (φ x), S.continuous_retract_comp hφ hzero,
    fun x => S.incl_retract (hzero x)⟩

omit [TopologicalSpace X] in
variable (X) in
/-- Exactness of `0 → C¹(X, A) → C¹(X, B)` at the left node: postcomposition with the inclusion is
injective on all cochains, hence in particular on the continuous ones `C¹(X, A)`. The statement
does not mention the cochain subgroups, so the degree-`2` node is this theorem at `X = G × G` and
needs no separate `C²` form. -/
theorem compLeft_incl_injective : Function.Injective (S.incl.compLeft X) :=
  S.incl_injective.comp_left

variable (X) in
/-- Exactness of `0 → C¹(X, A) → C¹(X, B) → C¹(X, C) → 0` at the middle node: a continuous cochain
into `B` is killed by the projection exactly when it is the image of a continuous cochain into
`A`. Taking `X = G` this is degree `1`, and taking `X = G × G` it is degree `2`. -/
theorem C1_map_incl_eq_inf_ker :
    AddSubgroup.map (S.incl.compLeft X) (C1 X A) = C1 X B ⊓ (S.proj.compLeft X).ker := by
  ext f
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha, rfl⟩
    exact AddSubgroup.mem_inf.2 ⟨mem_C1_iff.2
      ((continuous_of_discreteTopology (f := S.incl)).comp (mem_C1_iff.1 ha)),
      AddMonoidHom.mem_ker.2 (funext fun x => S.proj_incl (a x))⟩
  · intro hf
    obtain ⟨hcont, hker⟩ := AddSubgroup.mem_inf.1 hf
    obtain ⟨a, ha, hincl⟩ := S.exists_continuous_incl_comp_eq (mem_C1_iff.1 hcont)
      fun x => congrFun (AddMonoidHom.mem_ker.1 hker) x
    exact ⟨a, mem_C1_iff.2 ha, funext hincl⟩

variable (X) in
/-- Exactness of `C¹(X, B) → C¹(X, C) → 0` at the right node: every continuous cochain into `C`
lifts, by `TauCeti.ContCohomology.exists_continuous_lift`. -/
theorem C1_map_proj_eq_C1 : AddSubgroup.map (S.proj.compLeft X) (C1 X B) = C1 X C := by
  ext f
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨e, he, rfl⟩
    exact mem_C1_iff.2
      ((continuous_of_discreteTopology (f := S.proj)).comp (mem_C1_iff.1 he))
  · obtain ⟨e, he, hef⟩ := exists_continuous_lift S.proj_surjective (mem_C1_iff.1 hf)
    exact ⟨e, mem_C1_iff.2 he, funext hef⟩

end Cochains

section LowDegreeCochains

variable {G : Type u} [Monoid G] [TopologicalSpace G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- Exactness of `0 → C²(G, A) → C²(G, B) → C²(G, C) → 0` in the middle: the degree-`2` instance
of `TauCeti.ContCohomology.DiscreteShortExact.C1_map_incl_eq_inf_ker`, at `X = G × G`. -/
theorem C2_map_incl_eq_inf_ker :
    AddSubgroup.map (S.incl.compLeft (G × G)) (C2 G A) =
      C2 G B ⊓ (S.proj.compLeft (G × G)).ker := by
  simp only [C2_eq_C1]
  exact S.C1_map_incl_eq_inf_ker (G × G)

/-- Exactness of `0 → C²(G, A) → C²(G, B) → C²(G, C) → 0` on the right: the degree-`2` instance of
`TauCeti.ContCohomology.DiscreteShortExact.C1_map_proj_eq_C1`, at `X = G × G`. -/
theorem C2_map_proj_eq_C2 : AddSubgroup.map (S.proj.compLeft (G × G)) (C2 G B) = C2 G C := by
  simp only [C2_eq_C1]
  exact S.C1_map_proj_eq_C1 (G × G)

end LowDegreeCochains

section Delta0Cochain

variable {G : Type u} [Monoid G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- The `1`-cochain attached to an element `b : B` whose image in `C` is invariant: the retraction
of `d⁰ b`, which is killed by the projection exactly because that image is invariant. -/
private noncomputable def delta0Cochain (b : B) : G → A := fun g => S.retract (d0 G B b g)

/-- The value of the cochain representing `δ⁰` at a chosen preimage. -/
@[simp]
private theorem delta0Cochain_apply (b : B) (g : G) :
    S.delta0Cochain b g = S.retract (d0 G B b g) := (rfl)

variable {S}

/-- If the image of `b` in `C` is `G`-invariant then its coboundary `d⁰ b` is killed by the
projection, hence — the sequence being exact in the middle — comes from `A`. -/
theorem proj_d0_eq_zero {b : B} (hb : S.proj b ∈ H0 G C) (g : G) : S.proj (d0 G B b g) = 0 := by
  rw [map_d0_apply S.proj S.proj_equivariant, d0_apply,
    (FixedPoints.mem_addSubgroup G C (S.proj b)).1 hb g, sub_self]

/-- The image in `B` of the cochain representing `δ⁰` is `d⁰ b`. -/
private theorem incl_delta0Cochain {b : B} (hb : S.proj b ∈ H0 G C) (g : G) :
    S.incl (S.delta0Cochain b g) = g • b - b := by
  rw [S.delta0Cochain_apply, S.incl_retract (proj_d0_eq_zero hb g), d0_apply]

/-- The sum of two elements with invariant image again has invariant image. -/
private theorem proj_add_mem_H0 {b b' : B} (hb : S.proj b ∈ H0 G C) (hb' : S.proj b' ∈ H0 G C) :
    S.proj (b + b') ∈ H0 G C := by
  rw [map_add]
  exact add_mem hb hb'

/-- The cochain of a sum of preimages is the sum of their cochains. -/
private theorem delta0Cochain_add {b b' : B} (hb : S.proj b ∈ H0 G C)
    (hb' : S.proj b' ∈ H0 G C) :
    S.delta0Cochain (b + b') = S.delta0Cochain b + S.delta0Cochain b' := by
  refine funext fun g => S.incl_injective ?_
  rw [incl_delta0Cochain (proj_add_mem_H0 hb hb'), Pi.add_apply, map_add,
    incl_delta0Cochain hb, incl_delta0Cochain hb', smul_add]
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
variable (S) in
/-- **A cochain on `A` lying over a coboundary of `B` is a continuous `1`-cocycle.** No cocycle
hypothesis is needed: `d¹ ∘ d⁰ = 0` gives the identity and the injection reflects continuity. This
is what discharges the hypothesis `ha` of
`TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0_apply`, whose `hab` it takes verbatim. -/
theorem mem_Z1_of_incl_comp_eq_d0 {b : B} {a : G → A}
    (hab : ∀ g : G, S.incl (a g) = g • b - b) : a ∈ Z1 G A := by
  have hd : (fun g => S.incl (a g)) = d0 G B b := by
    funext g
    rw [hab, d0_apply]
  have hcont : Continuous fun g => S.incl (a g) := by
    rw [hd]
    exact continuous_d0_apply b
  refine mem_Z1_iff.2
    ⟨continuous_of_injective_comp S.incl_injective hcont, fun g h => S.incl_injective ?_⟩
  have hcocycle : d0 G B b (g * h) = g • d0 G B b h + d0 G B b g :=
    d1_apply_eq_zero_iff.1 (d1_comp_d0_apply (G := G) b) g h
  simp only [d0_apply] at hcocycle
  rw [hab, map_add, S.incl_equivariant, hab, hab]
  exact hcocycle

omit [ContinuousSMul G A] in
/-- The cochain attached to a preimage of an invariant is a continuous `1`-cocycle. -/
private theorem delta0Cochain_mem_Z1 {b : B} (hb : S.proj b ∈ H0 G C) :
    S.delta0Cochain b ∈ Z1 G A :=
  S.mem_Z1_of_incl_comp_eq_d0 (incl_delta0Cochain hb)

variable (S) in
/-- The class in `H¹(G, A)` of the cochain attached to a chosen preimage. The public connecting
map is this class at the preimage `Function.surjInv S.proj_surjective`; the choice does not matter
by `TauCeti.ContCohomology.DiscreteShortExact.delta0Class_congr`. -/
private noncomputable def delta0Class (b : B) (hb : S.proj b ∈ H0 G C) : H1 G A :=
  H1pi G A ⟨S.delta0Cochain b, delta0Cochain_mem_Z1 hb⟩

/-- The class attached to a preimage is represented by its `δ⁰` cochain. -/
@[simp]
private theorem delta0Class_def (b : B) (hb : S.proj b ∈ H0 G C) :
    S.delta0Class b hb = H1pi G A ⟨S.delta0Cochain b, delta0Cochain_mem_Z1 hb⟩ := (rfl)

/-- Two preimages of the same invariant of `C` give the same class: their difference comes from
`A`, and the two cochains differ by its coboundary. -/
private theorem delta0Class_congr {b b' : B} (hb : S.proj b ∈ H0 G C)
    (hb' : S.proj b' ∈ H0 G C) (h : S.proj b = S.proj b') :
    S.delta0Class b hb = S.delta0Class b' hb' := by
  obtain ⟨a₀, ha₀⟩ := S.exists_incl_eq (b := b' - b) (by rw [map_sub, h, sub_self])
  refine H1pi_eq_iff.2 (mem_B1_iff.2 ⟨-a₀, fun g => S.incl_injective ?_⟩)
  have h₁ : S.incl (S.delta0Cochain b g) = g • b - b := incl_delta0Cochain hb g
  have h₂ : S.incl (S.delta0Cochain b' g) = g • b' - b' := incl_delta0Cochain hb' g
  simp only [Pi.sub_apply]
  rw [map_sub, S.incl_equivariant, map_neg, ha₀, map_sub, h₁, h₂, smul_neg, smul_sub]
  abel

/-- The class attached to a sum of preimages is the sum of the classes. -/
private theorem delta0Class_add {b b' : B} (hb : S.proj b ∈ H0 G C)
    (hb' : S.proj b' ∈ H0 G C) :
    S.delta0Class (b + b') (proj_add_mem_H0 hb hb') =
      S.delta0Class b hb + S.delta0Class b' hb' := by
  rw [delta0Class_def, delta0Class_def, delta0Class_def, ← map_add]
  exact congrArg (H1pi G A) (Subtype.ext (delta0Cochain_add hb hb'))

variable (S)

omit [TopologicalSpace G] [ContinuousSMul G A] [ContinuousSMul G B] in
/-- The chosen preimage of an invariant of `C` has invariant image, tautologically. -/
private theorem proj_surjInv_mem_H0 (c : H0 G C) :
    S.proj (Function.surjInv S.proj_surjective (c : C)) ∈ H0 G C := by
  rw [Function.surjInv_eq S.proj_surjective]
  exact c.2

/-- **The connecting homomorphism `δ⁰ : H⁰(G, C) → H¹(G, A)`.** Choose a preimage in `B` of an
invariant of `C` and take the class of the retraction of its coboundary. -/
noncomputable def explicitDelta0 : H0 G C →+ H1 G A :=
  AddMonoidHom.mk' (fun c => S.delta0Class _ (S.proj_surjInv_mem_H0 c)) fun c c' => by
    rw [← delta0Class_add (S.proj_surjInv_mem_H0 c) (S.proj_surjInv_mem_H0 c')]
    exact delta0Class_congr _ (proj_add_mem_H0 (S.proj_surjInv_mem_H0 c)
      (S.proj_surjInv_mem_H0 c')) (by
      rw [Function.surjInv_eq S.proj_surjective, map_add, Function.surjInv_eq S.proj_surjective,
        Function.surjInv_eq S.proj_surjective, AddSubgroup.coe_add])

/-- **`δ⁰` on representatives.** For *any* preimage `b` of an invariant `c` and any continuous
`1`-cocycle `a` with `incl ∘ a = d⁰ b`, the class of `a` is `δ⁰ c`. This mirrors the shape of
Mathlib's discrete `groupCohomology.δ₀_apply`. The hypothesis `ha` is discharged from `hab` by
`TauCeti.ContCohomology.DiscreteShortExact.mem_Z1_of_incl_comp_eq_d0`. -/
theorem explicitDelta0_apply (c : H0 G C) {b : B} (hb : S.proj b = (c : C)) {a : G → A}
    (ha : a ∈ Z1 G A) (hab : ∀ g : G, S.incl (a g) = g • b - b) :
    S.explicitDelta0 c = H1pi G A ⟨a, ha⟩ := by
  have hbinv : S.proj b ∈ H0 G C := by
    rw [hb]
    exact c.2
  have hcochain : a = S.delta0Cochain b :=
    funext fun g => S.incl_injective (by rw [hab, incl_delta0Cochain hbinv])
  rw [explicitDelta0, AddMonoidHom.mk'_apply,
    delta0Class_congr (S.proj_surjInv_mem_H0 c) hbinv
      (by rw [Function.surjInv_eq S.proj_surjective, hb]), delta0Class_def]
  exact congrArg (H1pi G A) (Subtype.ext hcochain.symm)

end Delta0

section Delta1Cochain

variable {G : Type u} [Monoid G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- The `2`-cochain attached to a lift `e : G → B` of a `1`-cocycle on `C`: the retraction of
`d¹ e`, which is killed by the projection exactly because the cocycle is one. -/
private noncomputable def delta1Cochain (e : G → B) : G × G → A := fun p => S.retract (d1 G B e p)

/-- The value of the cochain representing `δ¹` at a chosen lift. -/
@[simp]
private theorem delta1Cochain_apply (e : G → B) (p : G × G) :
    S.delta1Cochain e p = S.retract (d1 G B e p) := (rfl)

variable {S}

/-- If `e` lies over a `1`-cocycle `f` on `C` then its coboundary `d¹ e` is killed by the
projection, hence — the sequence being exact in the middle — comes from `A`. -/
theorem proj_d1_eq_zero {e : G → B} {f : G → C} (he : ∀ g, S.proj (e g) = f g)
    (hf : groupCohomology.IsCocycle₁ f) (p : G × G) : S.proj (d1 G B e p) = 0 := by
  obtain ⟨g, h⟩ := p
  rw [map_d1_apply S.proj S.proj_equivariant]
  simp only [he]
  exact congrFun (d1_apply_eq_zero_iff.2 hf) (g, h)

/-- The image in `B` of the cochain representing `δ¹` is `d¹ e`. -/
private theorem incl_delta1Cochain {e : G → B} {f : G → C} (he : ∀ g, S.proj (e g) = f g)
    (hf : groupCohomology.IsCocycle₁ f) (p : G × G) :
    S.incl (S.delta1Cochain e p) = d1 G B e p := by
  rw [S.delta1Cochain_apply, S.incl_retract (proj_d1_eq_zero he hf p)]

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
variable (S) in
/-- **A cochain on `A` lying over a coboundary of `B` is a continuous `2`-cocycle.** No cocycle
hypothesis on `e` is needed: `d² ∘ d¹ = 0` gives the identity and the injection reflects
continuity. This is what discharges the hypothesis `ha` of
`TauCeti.ContCohomology.DiscreteShortExact.explicitDelta1_apply`, whose `hae` it takes verbatim. -/
theorem mem_Z2_of_incl_comp_eq_d1 {e : G → B} (hc : Continuous e) {a : G × G → A}
    (hae : ∀ g h : G, S.incl (a (g, h)) = g • e h - e (g * h) + e g) : a ∈ Z2 G A := by
  have hd : (fun p => S.incl (a p)) = d1 G B e := by
    funext p
    obtain ⟨g, h⟩ := p
    rw [hae, d1_apply]
  have hcont : Continuous fun p => S.incl (a p) := by
    rw [hd]
    exact continuous_d1_apply hc
  refine mem_Z2_iff.2
    ⟨continuous_of_injective_comp S.incl_injective hcont, fun g h j => S.incl_injective ?_⟩
  have hcocycle : d1 G B e (g * h, j) + d1 G B e (g, h) =
      g • d1 G B e (h, j) + d1 G B e (g, h * j) :=
    d2_apply_eq_zero_iff.1 (d2_comp_d1_apply e) g h j
  simp only [d1_apply] at hcocycle
  rw [map_add, map_add, S.incl_equivariant, hae, hae, hae, hae]
  exact hcocycle

omit [ContinuousSMul G A] in
/-- The cochain attached to a lift of a continuous `1`-cocycle is a continuous `2`-cocycle. -/
private theorem delta1Cochain_mem_Z2 {e : G → B} (hc : Continuous e) {f : G → C}
    (he : ∀ g, S.proj (e g) = f g) (hf : groupCohomology.IsCocycle₁ f) :
    S.delta1Cochain e ∈ Z2 G A :=
  S.mem_Z2_of_incl_comp_eq_d1 hc fun g h => by
    rw [incl_delta1Cochain he hf, d1_apply]

variable (S) in
/-- The class in `H²(G, A)` of the cochain attached to a chosen continuous lift of a continuous
`1`-cocycle on `C`. The choice of lift does not matter, by
`TauCeti.ContCohomology.DiscreteShortExact.delta1Class_congr`. -/
private noncomputable def delta1Class {e : G → B} (hc : Continuous e)
    (hf : groupCohomology.IsCocycle₁ fun g => S.proj (e g)) : H2 G A :=
  H2pi G A ⟨S.delta1Cochain e, delta1Cochain_mem_Z2 hc (fun _ => rfl) hf⟩

/-- The class attached to a lift is represented by its `δ¹` cochain. -/
@[simp]
private theorem delta1Class_def {e : G → B} (hc : Continuous e)
    (hf : groupCohomology.IsCocycle₁ fun g => S.proj (e g)) :
    S.delta1Class hc hf =
      H2pi G A ⟨S.delta1Cochain e, delta1Cochain_mem_Z2 hc (fun _ => rfl) hf⟩ := (rfl)

/-- Two continuous lifts of the same continuous `1`-cocycle give the same class: their difference
is the image of a continuous `1`-cochain on `A`, and the two `2`-cochains differ by its
coboundary. -/
private theorem delta1Class_congr {e e' : G → B} (hc : Continuous e) (hc' : Continuous e')
    (hf : groupCohomology.IsCocycle₁ fun g => S.proj (e g))
    (hf' : groupCohomology.IsCocycle₁ fun g => S.proj (e' g))
    (hproj : (fun g => S.proj (e g)) = fun g => S.proj (e' g)) :
    S.delta1Class hc hf = S.delta1Class hc' hf' := by
  have hzero : ∀ g : G, S.proj (e' g - e g) = 0 := fun g => by
    rw [map_sub, ← congrFun hproj g, sub_self]
  obtain ⟨u, hu, hincl⟩ :=
    S.exists_continuous_incl_comp_eq (hc'.sub hc) hzero
  have hne : (fun x => S.incl ((-u) x)) = e - e' := by
    funext x
    simp only [Pi.neg_apply, map_neg, hincl, Pi.sub_apply]
    abel
  refine H2pi_eq_iff.2 (mem_B2_iff.2 ⟨-u, hu.neg, funext fun p => ?_⟩)
  obtain ⟨g, h⟩ := p
  refine S.incl_injective ?_
  rw [Pi.sub_apply, map_sub S.incl, incl_delta1Cochain (fun _ => rfl) hf,
    incl_delta1Cochain (fun _ => rfl) hf', map_d1_apply S.incl S.incl_equivariant, hne,
    map_sub (d1 G B), Pi.sub_apply]

omit [TopologicalSpace G] [ContinuousMul G] [ContinuousSMul G A] [ContinuousSMul G B] in
/-- The sum of two lifts of `1`-cocycles again lies over a `1`-cocycle. -/
private theorem isCocycle₁_proj_add {e e' : G → B}
    (hf : groupCohomology.IsCocycle₁ fun g => S.proj (e g))
    (hf' : groupCohomology.IsCocycle₁ fun g => S.proj (e' g)) :
    groupCohomology.IsCocycle₁ fun g => S.proj ((e + e') g) := by
  intro g h
  simp only [Pi.add_apply, map_add, hf g h, hf' g h, smul_add]
  abel

/-- The class attached to a sum of lifts is the sum of the classes. -/
private theorem delta1Class_add {e e' : G → B} (hc : Continuous e) (hc' : Continuous e')
    (hf : groupCohomology.IsCocycle₁ fun g => S.proj (e g))
    (hf' : groupCohomology.IsCocycle₁ fun g => S.proj (e' g)) :
    S.delta1Class (hc.add hc') (isCocycle₁_proj_add hf hf') =
      S.delta1Class hc hf + S.delta1Class hc' hf' := by
  rw [delta1Class_def (hc.add hc') (isCocycle₁_proj_add hf hf'), delta1Class_def hc hf,
    delta1Class_def hc' hf', ← map_add]
  refine congrArg (H2pi G A) (Subtype.ext (funext fun p => S.incl_injective ?_))
  rw [incl_delta1Cochain (fun _ => rfl) (isCocycle₁_proj_add hf hf'), AddSubgroup.coe_add,
    Pi.add_apply, map_add S.incl, incl_delta1Cochain (fun _ => rfl) hf,
    incl_delta1Cochain (fun _ => rfl) hf']
  exact congrFun (map_add (d1 G B) e e') p

variable [ContinuousSMul G C]

omit [ContinuousMul G] [ContinuousSMul G A] [ContinuousSMul G B] [ContinuousSMul G C] in
/-- The canonical lift of a continuous `1`-cocycle on `C` is continuous. -/
private theorem continuous_liftCochain_coe (f : Z1 G C) :
    Continuous (liftCochain S.proj_surjective (f : G → C)) :=
  continuous_liftCochain S.proj_surjective (mem_Z1_iff.1 f.2).1

omit [ContinuousMul G] [ContinuousSMul G A] [ContinuousSMul G B] [ContinuousSMul G C] in
/-- The canonical lift of a continuous `1`-cocycle on `C` lies over that cocycle. -/
private theorem isCocycle₁_liftCochain (f : Z1 G C) :
    groupCohomology.IsCocycle₁ fun g =>
      S.proj (liftCochain S.proj_surjective (f : G → C) g) := by
  simpa only [apply_liftCochain S.proj_surjective] using (mem_Z1_iff.1 f.2).2

omit [ContinuousSMul G C] in
variable (S) in
/-- `δ¹` before descending to cohomology: the class in `H²(G, A)` attached to a continuous
`1`-cocycle on `C`, through its canonical lift. -/
private noncomputable def delta1Hom : Z1 G C →+ H2 G A :=
  AddMonoidHom.mk'
    (fun f => S.delta1Class (S.continuous_liftCochain_coe f) (S.isCocycle₁_liftCochain f))
    fun f f' => by
      refine (delta1Class_congr _ ((S.continuous_liftCochain_coe f).add
        (S.continuous_liftCochain_coe f')) (S.isCocycle₁_liftCochain (f + f'))
        (isCocycle₁_proj_add (S.isCocycle₁_liftCochain f) (S.isCocycle₁_liftCochain f'))
        (funext fun g => by
          rw [apply_liftCochain S.proj_surjective, Pi.add_apply, map_add,
            apply_liftCochain S.proj_surjective, apply_liftCochain S.proj_surjective,
            AddSubgroup.coe_add, Pi.add_apply])).trans ?_
      exact delta1Class_add _ _ (S.isCocycle₁_liftCochain f) (S.isCocycle₁_liftCochain f')

omit [ContinuousSMul G C] in
/-- Before descent to `H¹`, `δ¹` is the class of the cochain obtained from the canonical lift. -/
@[simp]
private theorem delta1Hom_apply (f : Z1 G C) :
    S.delta1Hom f =
      S.delta1Class (S.continuous_liftCochain_coe f) (S.isCocycle₁_liftCochain f) := (rfl)

omit [ContinuousSMul G C] in
/-- `δ¹` before descent to cohomology kills the `1`-coboundaries. -/
private theorem delta1Hom_eq_zero_of_mem_B1 (f : Z1 G C) (hf : (f : G → C) ∈ B1 G C) :
    S.delta1Hom f = 0 := by
  obtain ⟨c, hc⟩ := mem_B1_iff.1 hf
  obtain ⟨b, hpb⟩ := S.proj_surjective c
  have he : ∀ g : G, S.proj (d0 G B b g) = (f : G → C) g := fun g => by
    rw [map_d0_apply S.proj S.proj_equivariant, hpb, d0_apply, hc g]
  have hzero : S.delta1Cochain (d0 G B b) = 0 := funext fun p => by
    rw [delta1Cochain_apply, congrFun (d1_comp_d0_apply (G := G) b) p]
    exact S.retract_zero
  have hsubtype :
      (⟨S.delta1Cochain (d0 G B b),
          delta1Cochain_mem_Z2 (continuous_d0_apply (G := G) b) he
            (mem_Z1_iff.1 f.2).2⟩ :
        Z2 G A) = 0 :=
    Subtype.ext hzero
  have hd0 : groupCohomology.IsCocycle₁ fun g => S.proj (d0 G B b g) := by
    simpa only [he] using (mem_Z1_iff.1 f.2).2
  have hproj : (fun g => S.proj (liftCochain S.proj_surjective (f : G → C) g)) =
      fun g => S.proj (d0 G B b g) := funext fun g => by
    rw [apply_liftCochain S.proj_surjective, he]
  rw [delta1Hom_apply, delta1Class_congr _ (continuous_d0_apply (G := G) b)
      (S.isCocycle₁_liftCochain f) hd0 hproj, delta1Class_def, hsubtype]
  exact map_zero _

variable (S) in
/-- **The connecting homomorphism `δ¹ : H¹(G, C) → H²(G, A)`.** Lift a continuous `1`-cocycle on
`C` to a continuous `1`-cochain on `B` and take the class of the retraction of its `d¹`. -/
noncomputable def explicitDelta1 : H1 G C →+ H2 G A :=
  QuotientAddGroup.lift ((B1 G C).addSubgroupOf (Z1 G C)) S.delta1Hom fun f hf =>
    S.delta1Hom_eq_zero_of_mem_B1 f (AddSubgroup.mem_addSubgroupOf.1 hf)

/-- The quotient lift defining `explicitDelta1` computes to `delta1Hom` on a representative. -/
private theorem explicitDelta1_H1pi (f : Z1 G C) :
    S.explicitDelta1 (f : H1 G C) = S.delta1Hom f := by
  rw [explicitDelta1]
  exact QuotientAddGroup.lift_mk' _ _ f

variable (S) in
/-- **`δ¹` on representatives.** For *any* continuous lift `e` of a continuous `1`-cocycle `f` on
`C` and any continuous `2`-cocycle `a` with `incl ∘ a = d¹ e`, the class of `a` is `δ¹` of the
class of `f`. This mirrors the shape of Mathlib's discrete `groupCohomology.δ₁_apply`. The
hypothesis `ha` is discharged from `hae` by
`TauCeti.ContCohomology.DiscreteShortExact.mem_Z2_of_incl_comp_eq_d1`. -/
theorem explicitDelta1_apply (f : Z1 G C) {e : G → B} (hc : Continuous e)
    (he : ∀ g, S.proj (e g) = (f : G → C) g) {a : G × G → A} (ha : a ∈ Z2 G A)
    (hae : ∀ g h : G, S.incl (a (g, h)) = g • e h - e (g * h) + e g) :
    S.explicitDelta1 (H1pi G C f) = H2pi G A ⟨a, ha⟩ := by
  have hcochain : a = S.delta1Cochain e := funext fun p => by
    obtain ⟨g, h⟩ := p
    exact S.incl_injective (((hae g h).trans (d1_apply e g h).symm).trans
      (incl_delta1Cochain he (mem_Z1_iff.1 f.2).2 (g, h)).symm)
  have he' : groupCohomology.IsCocycle₁ fun g => S.proj (e g) := by
    simpa only [he] using (mem_Z1_iff.1 f.2).2
  have hproj : (fun g => S.proj (liftCochain S.proj_surjective (f : G → C) g)) =
      fun g => S.proj (e g) := funext fun g => by
    rw [apply_liftCochain S.proj_surjective, he]
  rw [QuotientAddGroup.mk'_apply, explicitDelta1_H1pi, delta1Hom_apply,
    delta1Class_congr _ hc (S.isCocycle₁_liftCochain f) he' hproj, delta1Class_def]
  exact congrArg (H2pi G A) (Subtype.ext hcochain.symm)

end Delta1

end DiscreteShortExact

end TauCeti.ContCohomology
