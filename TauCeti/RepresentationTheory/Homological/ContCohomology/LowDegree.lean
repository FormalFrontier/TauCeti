/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.ContinuousMap.Algebra

import Mathlib.Tactic.Abel

/-!
# The explicit low-degree complex of continuous cochains

Continuous cochain cohomology of a topological group `G` acting on a topological module `M` is
computed in low degrees by an explicit complex of *plain functions carrying continuity as a
predicate*: `C¹` is the additive subgroup of continuous elements of `G → M` and `C²` the
subgroup of continuous elements of `G × G → M`. This file builds that complex, its differentials,
its cocycles and coboundaries, and the three low-degree cohomology groups

```text
H⁰(G, M) = M^G,   H¹(G, M) = Z¹/B¹,   H²(G, M) = Z²/B².
```

## Main definitions

* `TauCeti.ContCohomology.C1`, `TauCeti.ContCohomology.C2`: the continuous cochains.
* `TauCeti.ContCohomology.d0`, `d1`, `d2`: the inhomogeneous differentials, as additive
  homomorphisms of the ambient function groups.
* `TauCeti.ContCohomology.Z1`, `Z2`: the continuous cocycles, `Cⁱ ⊓ ker dⁱ`.
* `TauCeti.ContCohomology.B1`, `B2`: the coboundaries, `range d⁰` and the image `d¹(C¹)` of the
  *continuous* `1`-cochains.
* `TauCeti.ContCohomology.H0`, `H1`, `H2`, their class maps `H1pi`, `H2pi`, and the discrete
  carriers `DiscreteH1`, `DiscreteH2` used by the comparison with canonical cohomology, together
  with their identifications `discreteH1Equiv`, `discreteH2Equiv` with `H1` and `H2`.

## Main statements

* `TauCeti.ContCohomology.d1_comp_d0` and `TauCeti.ContCohomology.d2_comp_d1`: `d ∘ d = 0`.
* `TauCeti.ContCohomology.B1_le_Z1` and `TauCeti.ContCohomology.B2_le_Z2`: the form of `d ∘ d = 0`
  that the two quotients need, coboundaries being continuous.
* `TauCeti.ContCohomology.H1EquivOfSmulEqSelf`: for a trivial action, `H¹(G, M)` is the group of
  continuous homomorphisms `G →ₜ* Multiplicative M`. This is the statement that makes `H¹` of a
  profinite group computable, and it is false without continuity.

## Implementation notes

The differentials and the cocycle identities follow the conventions of Mathlib's
`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`:

```text
(d⁰ m) g       = g • m - m,
(d¹ f) (g, h)  = g • f h - f (g * h) + f g,
(d² f) (g, h, j) = g • f (h, j) - f (g * h, j) + f (g, h * j) - f (g, h).
```

The cocycle conditions are spelled by Mathlib's unbundled predicates
`groupCohomology.IsCocycle₁` and `groupCohomology.IsCocycle₂`, and
`TauCeti.ContCohomology.d1_apply_eq_zero_iff` and `d2_apply_eq_zero_iff` identify them with the
vanishing of the differentials, so that `Zⁱ = Cⁱ ⊓ ker dⁱ` — which is how `Z1` and `Z2` are
*defined*, taking their closure under the group operations from `AddMonoidHom.ker` — is stated in
that spelling by `mem_Z1_iff` and `mem_Z2_iff`.

Mathlib's bundled `groupCohomology.cocycles₁` and `cocycles₂` are *not* reused here: they are
stated for `Rep k G`, which forces the coefficient ring and the group into a single universe, and
the coefficient modules of a profinite group have to be allowed to live in the group's universe
with a small coefficient ring such as `ℤ`. The unbundled `IsCocycle₁`/`IsCocycle₂` predicates,
which Mathlib provides for exactly this purpose, carry no such constraint and are consumed
directly. The cochain groups themselves are Mathlib's `continuousAddSubgroup`.

The trivial-action results are the continuous analogues of Mathlib's
`groupCohomology.cocycles₁IsoOfIsTrivial`, `groupCohomology.coboundaries₁_eq_bot_of_isTrivial` and
`groupCohomology.H1IsoOfIsTrivial`, in the same order and with the same proof plan; they are
restated for the unbundled classes because the Mathlib versions are stated for `Rep k G`.

Cochains are not normalised: `f 1 = 0` in degree `1` and the degree-`2` normalisations are the
lemmas `map_one_of_mem_Z1`, `map_one_fst_of_mem_Z2` and `map_one_snd_of_mem_Z2`, never
definitional conditions.

`H1` and `H2` divide `Z¹` and `Z²` by the coboundaries *viewed inside the cocycles*, in the
`AddSubgroup.addSubgroupOf` spelling the roadmap fixes, so that no proof term enters either quotient
subgroup. Each carrier retains the hypotheses of `TauCeti.ContCohomology.B1_le_Z1`, respectively
`B2_le_Z2`, through that inclusion theorem, so the subgroup divided out is always the whole of
`B¹`, respectively `B²`, and never the intersection `B ⊓ Z` that `addSubgroupOf` would cut out at a
weaker generality; `AddSubgroup.map_addSubgroupOf_eq_of_le` turns those inclusions into that
identity whenever a consumer needs it spelled out. The two carriers therefore sit in separate
sections:
`H¹` needs `G` to be a monoid acting continuously, and `H²` needs a continuous multiplication on
`G` besides, because `d¹` has to preserve continuity for `B² = d¹(C¹)` to consist of cocycles.

This implements the "the complex" milestone of Layer 2 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`, whose §3 fixes every convention above and whose
`Suggested.lean` fixes the names `C1`, `C2`, `d0`, `d1`, `Z1`, `Z2`, `B1`, `B2`, `H0`, `H1`, `H2`,
`H1pi`, `H2pi`, `B1_le_Z1` and `B2_le_Z2`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2: the
  cohomology of a profinite group computed by the inhomogeneous complex of continuous cochains,
  which is the complex built here in degrees `≤ 2`.
-/

public section

namespace TauCeti.ContCohomology

universe u v

section Cochains

variable (G : Type u) [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- The continuous `1`-cochains: the additive subgroup of continuous elements of `G → M`.

Continuity is a predicate on a plain function rather than a bundled `C(G, M)`, matching the shape
of Mathlib's `groupCohomology.cocycles₁ : Submodule k (G → A)`. -/
def C1 : AddSubgroup (G → M) := continuousAddSubgroup G M

/-- The continuous `2`-cochains: the continuous `1`-cochains of the domain `G × G`. -/
def C2 : AddSubgroup (G × G → M) := C1 (G × G) M

variable {G M}

/-- Membership in `C¹` is continuity. -/
@[simp]
theorem mem_C1_iff {f : G → M} : f ∈ C1 G M ↔ Continuous f := (Iff.rfl)

/-- Membership in `C²` is continuity. -/
@[simp]
theorem mem_C2_iff {f : G × G → M} : f ∈ C2 G M ↔ Continuous f := mem_C1_iff

end Cochains

section Differentials

section Degree0

/-! Degree `0` needs nothing of `G` but a distributive scalar action. -/

variable (G : Type u) (M : Type v) [AddCommGroup M] [DistribSMul G M]

/-- The degree-`0` differential `(d⁰ m) g = g • m - m`. -/
def d0 : M →+ (G → M) where
  toFun m := fun g => g • m - m
  map_zero' := by ext g; simp
  map_add' m m' := by ext g; simp only [Pi.add_apply, smul_add]; abel

/-- The `1`-coboundaries `B¹ = range d⁰`, defined as an algebraic range. Under a continuous
action, `TauCeti.ContCohomology.B1_le_C1` shows that these cochains are continuous. -/
def B1 : AddSubgroup (G → M) := (d0 G M).range

variable {G M}

/-- The defining formula for `d⁰`. -/
@[simp]
theorem d0_apply (m : M) (g : G) : d0 G M m g = g • m - m := (rfl)

/-- Membership in `B¹` is Mathlib's unbundled `1`-coboundary condition. -/
@[simp]
theorem mem_B1_iff {f : G → M} : f ∈ B1 G M ↔ groupCohomology.IsCoboundary₁ f := by
  simp only [B1, AddMonoidHom.mem_range, groupCohomology.IsCoboundary₁, funext_iff, d0_apply]

section TrivialAction

variable (htriv : ∀ (g : G) (m : M), g • m = m)
include htriv

/-- For a trivial action `d⁰` vanishes. -/
theorem d0_eq_zero_of_smul_eq_self : d0 G M = 0 :=
  AddMonoidHom.ext fun m => funext fun g => by simp [htriv g m]

/-- For a trivial action there are no nonzero `1`-coboundaries. -/
theorem B1_eq_bot_of_smul_eq_self : B1 G M = ⊥ := by
  refine eq_bot_iff.2 fun f hf => ?_
  obtain ⟨m, rfl⟩ := AddMonoidHom.mem_range.1 hf
  simp [d0_eq_zero_of_smul_eq_self htriv]

end TrivialAction

end Degree0

section CocycleConditions

/-! The higher differentials and the cocycle conditions they cut out need a multiplication on `G`
and no more, which is the level at which Mathlib states `groupCohomology.IsCocycle₁` and
`IsCocycle₂`. -/

variable (G : Type u) [Mul G] (M : Type v) [AddCommGroup M] [DistribSMul G M]

/-- The degree-`1` differential `(d¹ f) (g, h) = g • f h - f (g * h) + f g`. -/
def d1 : (G → M) →+ (G × G → M) where
  toFun f := fun q => q.1 • f q.2 - f (q.1 * q.2) + f q.1
  map_zero' := by ext q; simp
  map_add' f f' := by ext q; simp only [Pi.add_apply, smul_add]; abel

/-- The degree-`2` differential
`(d² f) (g, h, j) = g • f (h, j) - f (g * h, j) + f (g, h * j) - f (g, h)`. -/
def d2 : (G × G → M) →+ (G × G × G → M) where
  toFun f := fun q => q.1 • f (q.2.1, q.2.2) - f (q.1 * q.2.1, q.2.2) + f (q.1, q.2.1 * q.2.2)
    - f (q.1, q.2.1)
  map_zero' := by ext q; simp
  map_add' f f' := by ext q; simp only [Pi.add_apply, smul_add]; abel

variable {G M}

/-- The defining formula for `d¹`. -/
@[simp]
theorem d1_apply (f : G → M) (g h : G) : d1 G M f (g, h) = g • f h - f (g * h) + f g := (rfl)

/-- The defining formula for `d²`. -/
@[simp]
theorem d2_apply (f : G × G → M) (g h j : G) :
    d2 G M f (g, h, j) = g • f (h, j) - f (g * h, j) + f (g, h * j) - f (g, h) := (rfl)

/-- A `1`-cochain is killed by `d¹` exactly when it is a `1`-cocycle. Together with Mathlib's
`AddMonoidHom.mem_ker` this is the description of `ker d¹` that `Z¹` is built from. -/
@[simp]
theorem d1_apply_eq_zero_iff {f : G → M} :
    d1 G M f = 0 ↔ groupCohomology.IsCocycle₁ f := by
  simp only [funext_iff, Prod.forall, groupCohomology.IsCocycle₁]
  refine forall_congr' fun g => forall_congr' fun h => ?_
  rw [d1_apply, Pi.zero_apply]
  constructor
  · intro hgh
    calc
      f (g * h) = f (g * h) + (g • f h - f (g * h) + f g) := by rw [hgh, add_zero]
      _ = g • f h + f g := by abel
  · intro hgh
    rw [hgh]
    abel

/-- A `2`-cochain is killed by `d²` exactly when it is a `2`-cocycle. -/
@[simp]
theorem d2_apply_eq_zero_iff {f : G × G → M} :
    d2 G M f = 0 ↔ groupCohomology.IsCocycle₂ f := by
  simp only [funext_iff, Prod.forall, groupCohomology.IsCocycle₂]
  refine forall_congr' fun g => forall_congr' fun h => forall_congr' fun j => ?_
  rw [d2_apply, Pi.zero_apply]
  constructor
  · intro hghj
    calc
      f (g * h, j) + f (g, h) =
          f (g * h, j) + f (g, h) +
            (g • f (h, j) - f (g * h, j) + f (g, h * j) - f (g, h)) := by
              rw [hghj, add_zero]
      _ = g • f (h, j) + f (g, h * j) := by abel
  · intro hghj
    calc
      g • f (h, j) - f (g * h, j) + f (g, h * j) - f (g, h) =
          (g • f (h, j) + f (g, h * j)) - (f (g * h, j) + f (g, h)) := by abel
      _ = 0 := by rw [← hghj, sub_self]

end CocycleConditions

section Complex

/-! `d ∘ d = 0` and degree `0` of the complex need the action to be associative and unital; only
the degree-`1` inverse formula further on needs inverses. -/

variable (G : Type u) [Monoid G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-- `d¹ ∘ d⁰ = 0`. -/
theorem d1_comp_d0 : (d1 G M).comp (d0 G M) = 0 := by
  refine AddMonoidHom.ext fun m => funext fun q => ?_
  obtain ⟨g, h⟩ := q
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, d1_apply, d0_apply,
    AddMonoidHom.zero_apply, Pi.zero_apply, smul_sub, ← mul_smul]
  abel

/-- `d² ∘ d¹ = 0`. -/
theorem d2_comp_d1 : (d2 G M).comp (d1 G M) = 0 := by
  refine AddMonoidHom.ext fun f => funext fun q => ?_
  obtain ⟨g, h, j⟩ := q
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, d2_apply, d1_apply,
    AddMonoidHom.zero_apply, Pi.zero_apply, smul_sub, smul_add, ← mul_smul, mul_assoc]
  abel

/-- Degree `0` of the explicit complex: the invariants `M^G`. Unlike `H¹` and `H²` this is a
subgroup and not a quotient. It is named because the low-degree corestriction, the connecting
maps and the `(0, q)` and `(q, 0)` cup shapes all need a degree-`0` carrier to be stated
against. Membership is exposed by Mathlib's `FixedPoints.mem_addSubgroup`, which applies directly
to this abbreviation. -/
abbrev H0 : AddSubgroup M := FixedPoints.addSubgroup G M

variable {G M}

/-- `d¹ ∘ d⁰ = 0`, evaluated at a `0`-cochain. This is the form a consumer of the complex uses;
the composed form needs unfolding before it can rewrite. -/
@[simp]
theorem d1_comp_d0_apply (m : M) : d1 G M (d0 G M m) = 0 :=
  DFunLike.congr_fun (d1_comp_d0 G M) m

/-- `d² ∘ d¹ = 0`, evaluated at a `1`-cochain. -/
@[simp]
theorem d2_comp_d1_apply (f : G → M) : d2 G M (d1 G M f) = 0 :=
  DFunLike.congr_fun (d2_comp_d1 G M) f

/-- For a trivial action `H⁰(G, M) = M`. -/
theorem H0_eq_top_of_smul_eq_self (htriv : ∀ (g : G) (m : M), g • m = m) : H0 G M = ⊤ :=
  eq_top_iff.2 fun m _ => (FixedPoints.mem_addSubgroup G M m).2 fun g => htriv g m

end Complex

end Differentials

section Cocycles

variable (G : Type u) [Mul G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribSMul G M]

/-- The continuous `1`-cocycles `Z¹ = C¹ ⊓ ker d¹`; the closure of the cocycle condition under
the group operations is the one `AddMonoidHom.ker` already carries.
`TauCeti.ContCohomology.mem_Z1_iff` restates membership with the kernel spelled by Mathlib's
`groupCohomology.IsCocycle₁`. -/
def Z1 : AddSubgroup (G → M) := C1 G M ⊓ (d1 G M).ker

/-- The continuous `2`-cocycles `Z² = C² ⊓ ker d²`. -/
def Z2 : AddSubgroup (G × G → M) := C2 G M ⊓ (d2 G M).ker

/-- The `2`-coboundaries `B² = d¹(C¹)`, the image of the **continuous** `1`-cochains. The
restriction to `C¹` is what the complex asks for: `B²` has to be the image of the cochains the
complex is built from for `Z²/B²` to be the cohomology of the *continuous* complex, whereas the
image of all of `G → M` is the coboundaries of the abstract complex. -/
def B2 : AddSubgroup (G × G → M) := AddSubgroup.map (d1 G M) (C1 G M)

variable {G M}

/-- A cochain is a continuous `1`-cocycle exactly when it is continuous and satisfies the
`1`-cocycle identity. -/
@[simp]
theorem mem_Z1_iff {f : G → M} :
    f ∈ Z1 G M ↔ Continuous f ∧ groupCohomology.IsCocycle₁ f :=
  AddSubgroup.mem_inf.trans
    (and_congr mem_C1_iff (AddMonoidHom.mem_ker.trans d1_apply_eq_zero_iff))

/-- A cochain is a continuous `2`-cocycle exactly when it is continuous and satisfies the
`2`-cocycle identity. -/
@[simp]
theorem mem_Z2_iff {f : G × G → M} :
    f ∈ Z2 G M ↔ Continuous f ∧ groupCohomology.IsCocycle₂ f :=
  AddSubgroup.mem_inf.trans
    (and_congr mem_C2_iff (AddMonoidHom.mem_ker.trans d2_apply_eq_zero_iff))

/-- Membership in `B²` exhibits a *continuous* primitive. -/
@[simp]
theorem mem_B2_iff {f : G × G → M} :
    f ∈ B2 G M ↔ ∃ c : G → M, Continuous c ∧ d1 G M c = f := by
  simp only [B2, AddSubgroup.mem_map, mem_C1_iff]

/-- Membership in `B²`, with the primitive spelled out pointwise as in Mathlib's unbundled
`2`-coboundary condition. This is the degree-`2` counterpart of
`TauCeti.ContCohomology.mem_B1_iff`, which can be stated with `groupCohomology.IsCoboundary₁`
itself because `B¹` carries no continuity restriction on the primitive. -/
theorem mem_B2_iff' {f : G × G → M} :
    f ∈ B2 G M ↔ ∃ c : G → M, Continuous c ∧ ∀ g h : G, g • c h - c (g * h) + c g = f (g, h) := by
  simp only [mem_B2_iff, funext_iff, Prod.forall, d1_apply]

/-- A continuous `2`-coboundary satisfies Mathlib's unbundled `2`-coboundary condition. -/
theorem isCoboundary₂_of_mem_B2 {f : G × G → M} (hf : f ∈ B2 G M) :
    groupCohomology.IsCoboundary₂ f := by
  obtain ⟨c, -, hc⟩ := mem_B2_iff'.1 hf
  exact ⟨c, hc⟩

variable (G M)

/-- Continuous `1`-cocycles are continuous `1`-cochains. -/
theorem Z1_le_C1 : Z1 G M ≤ C1 G M := inf_le_left

/-- Continuous `2`-cocycles are continuous `2`-cochains. -/
theorem Z2_le_C2 : Z2 G M ≤ C2 G M := inf_le_left

end Cocycles

section Normalizations

variable {G : Type u} [Monoid G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

/-- A continuous `1`-cocycle vanishes at `1`. This is a lemma and not part of the definition of
`Z¹`: cochains here are not normalised. -/
theorem map_one_of_mem_Z1 {f : G → M} (hf : f ∈ Z1 G M) : f 1 = 0 :=
  groupCohomology.map_one_of_isCocycle₁ (mem_Z1_iff.1 hf).2

/-- The first degree-`2` normalisation. -/
theorem map_one_fst_of_mem_Z2 {f : G × G → M} (hf : f ∈ Z2 G M) (g : G) : f (1, g) = f (1, 1) :=
  groupCohomology.map_one_fst_of_isCocycle₂ (mem_Z2_iff.1 hf).2 g

/-- The second degree-`2` normalisation. -/
theorem map_one_snd_of_mem_Z2 {f : G × G → M} (hf : f ∈ Z2 G M) (g : G) :
    f (g, 1) = g • f (1, 1) :=
  groupCohomology.map_one_snd_of_isCocycle₂ (mem_Z2_iff.1 hf).2 g

end Normalizations

section Inverse

variable {G : Type u} [Group G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

/-- The inverse formula for a continuous `1`-cocycle. -/
@[scoped simp]
theorem map_inv_of_mem_Z1 {f : G → M} (hf : f ∈ Z1 G M) (g : G) : g • f g⁻¹ = -f g :=
  groupCohomology.map_inv_of_isCocycle₁ (mem_Z1_iff.1 hf).2 g

end Inverse

section Continuity

variable {G : Type u} [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribSMul G M] [ContinuousSMul G M]

/-- Every `1`-coboundary is continuous. -/
theorem continuous_d0_apply (m : M) : Continuous (d0 G M m) :=
  (continuous_id.smul continuous_const).sub continuous_const

variable (G M)

/-- `1`-coboundaries are continuous `1`-cochains. -/
theorem B1_le_C1 : B1 G M ≤ C1 G M := by
  intro f hf
  obtain ⟨m, rfl⟩ := AddMonoidHom.mem_range.1 hf
  exact continuous_d0_apply m

end Continuity

section ContinuityMul

/-! `d¹` preserves continuity already at the level at which `d¹` itself is defined: a
multiplication on `G` and a distributive scalar action, with no unit and no associativity. -/

variable {G : Type u} [Mul G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribSMul G M] [ContinuousSMul G M]

/-- `d¹` preserves continuity. -/
theorem continuous_d1_apply {f : G → M} (hf : Continuous f) : Continuous (d1 G M f) :=
  ((continuous_fst.smul (hf.comp continuous_snd)).sub
    (hf.comp (continuous_fst.mul continuous_snd))).add (hf.comp continuous_fst)

variable (G M)

/-- `2`-coboundaries are continuous `2`-cochains. -/
theorem B2_le_C2 : B2 G M ≤ C2 G M := by
  intro f hf
  obtain ⟨c, hc, rfl⟩ := mem_B2_iff.1 hf
  exact continuous_d1_apply hc

end ContinuityMul

section ContinuityAction

variable (G : Type u) [Monoid G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- `d ∘ d = 0` in the form the degree-`1` quotient needs. -/
theorem B1_le_Z1 : B1 G M ≤ Z1 G M := by
  intro f hf
  obtain ⟨m, rfl⟩ := AddMonoidHom.mem_range.1 hf
  exact mem_Z1_iff.2 ⟨continuous_d0_apply m, d1_apply_eq_zero_iff.1 (d1_comp_d0_apply m)⟩

end ContinuityAction

section ContinuityMulAction

variable (G : Type u) [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- `d ∘ d = 0` in the form the degree-`2` quotient needs. -/
theorem B2_le_Z2 : B2 G M ≤ Z2 G M := by
  intro f hf
  obtain ⟨c, hc, rfl⟩ := mem_B2_iff.1 hf
  exact mem_Z2_iff.2 ⟨continuous_d1_apply hc, d2_apply_eq_zero_iff.1 (d2_comp_d1_apply c)⟩

end ContinuityMulAction

section CohomologyDegree1

/-! Degree `1` of the cohomology is formed exactly where `TauCeti.ContCohomology.B1_le_Z1` holds:
under a weaker action `B¹` need not consist of cocycles and the quotient below would silently be
by `B¹ ⊓ Z¹`. -/

variable (G : Type u) [Monoid G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [hcont : ContinuousSMul G M]

/-- The first continuous cohomology group `H¹(G, M) = Z¹/B¹`.

The denominator is `B¹` viewed inside `Z¹`, in Mathlib's `AddSubgroup.addSubgroupOf` spelling the
roadmap fixes, so that no proof term enters the quotient subgroup. The hypotheses in force are
those of
`TauCeti.ContCohomology.B1_le_Z1`, so the subgroup divided out really is the whole of `B¹`:
`AddSubgroup.map_addSubgroupOf_eq_of_le (B1_le_Z1 G M)` says its image in `G → M` is `B¹` itself.

`H¹` is used as a bare additive group. It does inherit a quotient topology from the *pointwise*
topology on `G → M`, and that topology is not the intended one: it need not be discrete, the
roadmap's witness being trivial `ZMod 2` coefficients on a product of infinitely many copies of
`C₂`, where no finite set of evaluations isolates the zero character. The comparison of Layer 3 is
therefore stated against `DiscreteH1`. -/
abbrev H1 :=
  let _h := B1_le_Z1 G M
  (Z1 G M) ⧸ ((B1 G M).addSubgroupOf (Z1 G M))

/-- The class map in degree `1`. -/
abbrev H1pi : (Z1 G M) →+ H1 G M := QuotientAddGroup.mk' _

/-- `H¹(G, M)` equipped with the discrete topology used by the comparison with canonical
continuous cohomology. -/
def DiscreteH1 : Type _ := H1 G M

noncomputable instance : AddCommGroup (DiscreteH1 G M) :=
  inferInstanceAs (AddCommGroup (H1 G M))

instance : TopologicalSpace (DiscreteH1 G M) := ⊥

instance : DiscreteTopology (DiscreteH1 G M) := ⟨rfl⟩

/-- The identity as an additive equivalence, so that the quotient-class computations on
representatives stay available after passing to the discrete object. -/
noncomputable def discreteH1Equiv : DiscreteH1 G M ≃+ H1 G M :=
  AddEquiv.refl _

variable {G M}

omit hcont in
/-- A continuous `1`-cocycle has trivial class exactly when it is a coboundary. -/
theorem H1pi_eq_zero_iff {f : Z1 G M} :
    (f : H1 G M) = 0 ↔ (f : G → M) ∈ B1 G M := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

omit hcont in
/-- Two continuous `1`-cocycles have the same class exactly when they differ by a coboundary. -/
@[simp]
theorem H1pi_eq_iff {f f' : Z1 G M} :
    (f : H1 G M) = (f' : H1 G M) ↔ (f : G → M) - f' ∈ B1 G M := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]

end CohomologyDegree1

section CohomologyDegree2

/-! Degree `2` needs a continuous multiplication on `G` besides, this being what makes `d¹`
preserve continuity and hence what
`TauCeti.ContCohomology.B2_le_Z2` — the inclusion the quotient below divides by — asks for. -/

variable (G : Type u) [Monoid G] [TopologicalSpace G] [hcontMul : ContinuousMul G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [hcontSmul : ContinuousSMul G M]

/-- The second continuous cohomology group `H²(G, M) = Z²/B²`.

As for `H¹` the denominator is `B²` viewed inside `Z²`, and the hypotheses in force are those of
`TauCeti.ContCohomology.B2_le_Z2`, so the subgroup divided out really is the whole of `B²`. The
inherited quotient topology is again not the intended one, and `H²` is used as a bare additive
group. -/
abbrev H2 :=
  let _h := B2_le_Z2 G M
  (Z2 G M) ⧸ ((B2 G M).addSubgroupOf (Z2 G M))

/-- The class map in degree `2`. -/
abbrev H2pi : (Z2 G M) →+ H2 G M := QuotientAddGroup.mk' _

/-- `H²(G, M)` equipped with the discrete topology used by the comparison with canonical
continuous cohomology. -/
def DiscreteH2 : Type _ := H2 G M

noncomputable instance : AddCommGroup (DiscreteH2 G M) :=
  inferInstanceAs (AddCommGroup (H2 G M))

instance : TopologicalSpace (DiscreteH2 G M) := ⊥

instance : DiscreteTopology (DiscreteH2 G M) := ⟨rfl⟩

/-- The degree-`2` counterpart of `TauCeti.ContCohomology.discreteH1Equiv`. -/
noncomputable def discreteH2Equiv : DiscreteH2 G M ≃+ H2 G M :=
  AddEquiv.refl _

variable {G M}

omit hcontMul hcontSmul in
/-- A continuous `2`-cocycle has trivial class exactly when it is a coboundary. -/
theorem H2pi_eq_zero_iff {f : Z2 G M} :
    (f : H2 G M) = 0 ↔ (f : G × G → M) ∈ B2 G M := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

omit hcontMul hcontSmul in
/-- Two continuous `2`-cocycles have the same class exactly when they differ by a coboundary. -/
@[simp]
theorem H2pi_eq_iff {f f' : Z2 G M} :
    (f : H2 G M) = (f' : H2 G M) ↔ (f : G × G → M) - f' ∈ B2 G M := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]

end CohomologyDegree2

section TrivialAction

variable {G : Type u} [Monoid G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] (htriv : ∀ (g : G) (m : M), g • m = m)

include htriv

/-- For a trivial action a continuous `1`-cocycle is additive: the cocycle identity loses its
scalar and becomes `f (a * b) = f a + f b`. -/
theorem map_mul_of_smul_eq_self_of_mem_Z1 {f : G → M} (hf : f ∈ Z1 G M) (a b : G) :
    f (a * b) = f a + f b := by
  have h := (mem_Z1_iff.1 hf).2 a b
  rw [htriv a (f b)] at h
  exact h.trans (add_comm _ _)

/-- For a trivial action the pointwise `Multiplicative.toAdd` of a continuous homomorphism
`G → Multiplicative M` is a continuous `1`-cocycle. -/
theorem mem_Z1_of_smul_eq_self_of_continuousMonoidHom
    (φ : ContinuousMonoidHom G (Multiplicative M)) :
    (fun g => Multiplicative.toAdd (φ g)) ∈ Z1 G M :=
  mem_Z1_iff.2 ⟨map_continuous φ, fun a b => by
    simp only [htriv a (Multiplicative.toAdd (φ b)), map_mul φ a b, toAdd_mul]
    exact add_comm _ _⟩

/-- For a trivial action the continuous `1`-cocycles are exactly the continuous homomorphisms
`G → Multiplicative M`. This is the continuous analogue of Mathlib's
`groupCohomology.cocycles₁IsoOfIsTrivial`. -/
def Z1EquivOfSmulEqSelf : Z1 G M ≃+ Additive (ContinuousMonoidHom G (Multiplicative M)) where
  toFun f := Additive.ofMul
    { toMonoidHom :=
        MonoidHom.mk' (fun g => Multiplicative.ofAdd ((f : G → M) g)) fun a b => by
          rw [map_mul_of_smul_eq_self_of_mem_Z1 htriv f.2 a b, ofAdd_add]
      continuous_toFun := (mem_Z1_iff.1 f.2).1 }
  invFun φ :=
    ⟨fun g => Multiplicative.toAdd ((Additive.toMul φ) g),
      mem_Z1_of_smul_eq_self_of_continuousMonoidHom htriv (Additive.toMul φ)⟩
  left_inv f := Subtype.ext rfl
  right_inv φ := Additive.toMul.injective (DFunLike.ext _ _ fun _ => rfl)
  map_add' f g := Additive.toMul.injective (DFunLike.ext _ _ fun _ => rfl)

/-- The homomorphism attached to a continuous `1`-cocycle by `Z1EquivOfSmulEqSelf` is the cocycle
itself. -/
@[simp]
theorem Z1EquivOfSmulEqSelf_apply (f : Z1 G M) (g : G) :
    Additive.toMul (Z1EquivOfSmulEqSelf htriv f) g = Multiplicative.ofAdd ((f : G → M) g) := (rfl)

/-- The continuous `1`-cocycle attached to a continuous homomorphism by `Z1EquivOfSmulEqSelf` is
the homomorphism itself. -/
@[simp]
theorem Z1EquivOfSmulEqSelf_symm_apply
    (φ : Additive (ContinuousMonoidHom G (Multiplicative M))) (g : G) :
    (((Z1EquivOfSmulEqSelf htriv).symm φ : Z1 G M) : G → M) g =
      Multiplicative.toAdd ((Additive.toMul φ) g) := (rfl)

end TrivialAction

section TrivialCohomology

variable {G : Type u} [Monoid G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] (htriv : ∀ (g : G) (m : M), g • m = m)

include htriv

/-- For a trivial action `H¹(G, M)` is the group of continuous homomorphisms
`G →ₜ* Multiplicative M`. This is the continuous analogue of Mathlib's
`groupCohomology.H1IsoOfIsTrivial`.

Continuity is what makes this useful rather than decorative: without it the right-hand side is the
group of abstract homomorphisms, which for a profinite group is enormous. -/
noncomputable def H1EquivOfSmulEqSelf :
    H1 G M ≃+ Additive (ContinuousMonoidHom G (Multiplicative M)) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (M := (B1 G M).addSubgroupOf (Z1 G M)) (N := ⊥) (by
        rw [B1_eq_bot_of_smul_eq_self htriv]
        exact AddSubgroup.bot_addSubgroupOf _)).trans
    (QuotientAddGroup.quotientBot.trans (Z1EquivOfSmulEqSelf htriv))

/-- `H1EquivOfSmulEqSelf` sends the class of a continuous `1`-cocycle to the homomorphism it
is. -/
@[simp]
theorem H1EquivOfSmulEqSelf_mk (f : Z1 G M) :
    H1EquivOfSmulEqSelf htriv (f : H1 G M) = Z1EquivOfSmulEqSelf htriv f := by
  simp only [H1EquivOfSmulEqSelf, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  -- `quotientBot` takes the class of a cocycle back to the cocycle definitionally.
  rfl

/-- The class of the continuous `1`-cocycle attached to a continuous homomorphism by
`H1EquivOfSmulEqSelf`. -/
@[simp]
theorem H1EquivOfSmulEqSelf_symm_apply
    (φ : Additive (ContinuousMonoidHom G (Multiplicative M))) :
    (H1EquivOfSmulEqSelf htriv).symm φ = ((Z1EquivOfSmulEqSelf htriv).symm φ : H1 G M) :=
  (H1EquivOfSmulEqSelf htriv).symm_apply_eq.2
    (((Z1EquivOfSmulEqSelf htriv).apply_symm_apply φ).symm.trans
      (H1EquivOfSmulEqSelf_mk htriv _).symm)

end TrivialCohomology

end TauCeti.ContCohomology
