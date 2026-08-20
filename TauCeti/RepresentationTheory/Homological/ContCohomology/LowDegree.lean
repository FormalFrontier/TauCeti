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
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction

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
* `TauCeti.ContCohomology.H0`, `H1`, `H2` and the class maps `H1pi`, `H2pi`.

## Main statements

* `TauCeti.ContCohomology.d1_comp_d0` and `TauCeti.ContCohomology.d2_comp_d1`: `d ∘ d = 0`.
* `TauCeti.ContCohomology.B1_le_Z1` and `TauCeti.ContCohomology.B2_le_Z2`: the form of `d ∘ d = 0`
  that the two quotients need, coboundaries being continuous.
* `TauCeti.ContCohomology.trivialH1Equiv`: for a trivial action, `H¹(G, M)` is the group of
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
`TauCeti.ContCohomology.mem_ker_d1_iff` and `mem_ker_d2_iff` identify them with the kernels of the
differentials, so that `Zⁱ = Cⁱ ⊓ ker dⁱ` is a theorem about this spelling rather than a second
convention.

Mathlib's bundled `groupCohomology.cocycles₁` and `cocycles₂` are *not* reused here: they are
stated for `Rep k G`, which forces the coefficient ring and the group into a single universe, and
the coefficient modules of a profinite group have to be allowed to live in the group's universe
with a small coefficient ring such as `ℤ`. The unbundled `IsCocycle₁`/`IsCocycle₂` predicates,
which Mathlib provides for exactly this purpose, carry no such constraint and are consumed
directly.

Cochains are not normalised: `f 1 = 0` in degree `1` and the degree-`2` normalisations are the
lemmas `map_one_of_mem_Z1`, `map_one_fst_of_mem_Z2` and `map_one_snd_of_mem_Z2`, never
definitional conditions.

This implements the "the complex" milestone of Layer 2 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`, whose §3 fixes every convention above and whose
`Suggested.lean` fixes the names `C1`, `C2`, `d0`, `d1`, `Z1`, `Z2`, `B1`, `B2`, `H0`, `H1`, `H2`,
`H1pi`, `H2pi`, `B1_le_Z1` and `B2_le_Z2`.

## References

* [Milne, *Arithmetic Duality Theorems*][milneADT]
* [Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*][NeukirchSchmidtWingberg2008]
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
def C1 : AddSubgroup (G → M) where
  carrier := {f | Continuous f}
  add_mem' hf hg := hf.add hg
  zero_mem' := continuous_const
  neg_mem' hf := hf.neg

/-- The continuous `2`-cochains. -/
def C2 : AddSubgroup (G × G → M) where
  carrier := {f | Continuous f}
  add_mem' hf hg := hf.add hg
  zero_mem' := continuous_const
  neg_mem' hf := hf.neg

variable {G M}

/-- Membership in `C¹` is continuity. -/
@[simp]
theorem mem_C1 {f : G → M} : f ∈ C1 G M ↔ Continuous f := (Iff.rfl)

/-- Membership in `C²` is continuity. -/
@[simp]
theorem mem_C2 {f : G × G → M} : f ∈ C2 G M ↔ Continuous f := (Iff.rfl)

end Cochains

section Differentials

variable (G : Type u) [Group G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-- The degree-`0` differential `(d⁰ m) g = g • m - m`. -/
def d0 : M →+ (G → M) where
  toFun m := fun g => g • m - m
  map_zero' := by ext g; simp
  map_add' m m' := by ext g; simp only [Pi.add_apply, smul_add]; abel

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

/-- The defining formula for `d⁰`. -/
@[simp]
theorem d0_apply (m : M) (g : G) : d0 G M m g = g • m - m := (rfl)

/-- The defining formula for `d¹`. -/
@[simp]
theorem d1_apply (f : G → M) (g h : G) : d1 G M f (g, h) = g • f h - f (g * h) + f g := (rfl)

/-- The defining formula for `d²`. -/
@[simp]
theorem d2_apply (f : G × G → M) (g h j : G) :
    d2 G M f (g, h, j) = g • f (h, j) - f (g * h, j) + f (g, h * j) - f (g, h) := (rfl)

variable (G M)

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

variable {G M}

/-- A `1`-cochain is killed by `d¹` exactly when it is a `1`-cocycle. -/
@[simp]
theorem d1_eq_zero_iff {f : G → M} :
    d1 G M f = 0 ↔ groupCohomology.IsCocycle₁ f := by
  simp only [funext_iff, Prod.forall, groupCohomology.IsCocycle₁]
  refine forall_congr' fun g => forall_congr' fun h => ?_
  rw [d1_apply, Pi.zero_apply]
  constructor
  · intro h'
    calc
      f (g * h) = f (g * h) + (g • f h - f (g * h) + f g) := by rw [h', add_zero]
      _ = g • f h + f g := by abel
  · intro h'
    rw [h']
    abel

/-- The kernel of `d¹` consists of the `1`-cocycles. -/
theorem mem_ker_d1_iff {f : G → M} :
    f ∈ (d1 G M).ker ↔ groupCohomology.IsCocycle₁ f := by
  simpa only [AddMonoidHom.mem_ker] using
    (d1_eq_zero_iff (G := G) (M := M) (f := f))

/-- A `2`-cochain is killed by `d²` exactly when it is a `2`-cocycle. -/
@[simp]
theorem d2_eq_zero_iff {f : G × G → M} :
    d2 G M f = 0 ↔ groupCohomology.IsCocycle₂ f := by
  simp only [funext_iff, Prod.forall, groupCohomology.IsCocycle₂]
  refine forall_congr' fun g => forall_congr' fun h => forall_congr' fun j => ?_
  rw [d2_apply, Pi.zero_apply]
  constructor
  · intro h'
    calc
      f (g * h, j) + f (g, h) =
          f (g * h, j) + f (g, h) +
            (g • f (h, j) - f (g * h, j) + f (g, h * j) - f (g, h)) := by
              rw [h', add_zero]
      _ = g • f (h, j) + f (g, h * j) := by abel
  · intro h'
    calc
      g • f (h, j) - f (g * h, j) + f (g, h * j) - f (g, h) =
          (g • f (h, j) + f (g, h * j)) - (f (g * h, j) + f (g, h)) := by abel
      _ = 0 := sub_eq_zero.mpr h'.symm

/-- The kernel of `d²` consists of the `2`-cocycles. -/
theorem mem_ker_d2_iff {f : G × G → M} :
    f ∈ (d2 G M).ker ↔ groupCohomology.IsCocycle₂ f := by
  simpa only [AddMonoidHom.mem_ker] using
    (d2_eq_zero_iff (G := G) (M := M) (f := f))

variable (G M)

/-- The `1`-coboundaries `B¹ = range d⁰`, defined as an algebraic range. Under a continuous
action, `TauCeti.ContCohomology.B1_le_C1` shows that these cochains are continuous. -/
def B1 : AddSubgroup (G → M) := (d0 G M).range

/-- Degree `0` of the explicit complex: the invariants `M^G`. Unlike `H¹` and `H²` this is a
subgroup and not a quotient. It is named because the low-degree corestriction, the connecting
maps and the `(0, q)` and `(q, 0)` cup shapes all need a degree-`0` carrier to be stated
against. -/
abbrev H0 : AddSubgroup M := FixedPoints.addSubgroup G M

variable {G M}

/-- Membership in `B¹` is Mathlib's unbundled `1`-coboundary condition. -/
@[simp]
theorem mem_B1_iff {f : G → M} : f ∈ B1 G M ↔ groupCohomology.IsCoboundary₁ f := by
  simp only [B1, AddMonoidHom.mem_range, groupCohomology.IsCoboundary₁, funext_iff, d0_apply]

section TrivialAction

variable (htriv : ∀ (g : G) (m : M), g • m = m)
include htriv

/-- For a trivial action `d⁰` vanishes. -/
theorem d0_eq_zero_of_smul_eq_self (m : M) : d0 G M m = 0 := by
  ext g
  simp [htriv g m]

/-- For a trivial action there are no nonzero `1`-coboundaries. -/
theorem B1_eq_bot_of_smul_eq_self : B1 G M = ⊥ := by
  refine eq_bot_iff.2 fun f hf => ?_
  obtain ⟨m, rfl⟩ := AddMonoidHom.mem_range.1 hf
  simpa using d0_eq_zero_of_smul_eq_self htriv m

/-- For a trivial action `H⁰(G, M) = M`. -/
theorem H0_eq_top_of_smul_eq_self : H0 G M = ⊤ :=
  eq_top_iff.2 fun m _ g => htriv g m

end TrivialAction

end Differentials

section Cocycles

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

/-- The continuous `1`-cocycles `Z¹ = C¹ ⊓ ker d¹`, with the kernel spelled by Mathlib's
`groupCohomology.IsCocycle₁`; `TauCeti.ContCohomology.Z1_eq_inf_ker` proves the two agree. -/
def Z1 : AddSubgroup (G → M) :=
  C1 G M ⊓
    { carrier := {f | groupCohomology.IsCocycle₁ f}
      add_mem' := fun {a b} ha hb g h => by
        simp only [Pi.add_apply, ha g h, hb g h, smul_add]; abel
      zero_mem' := fun g h => by simp
      neg_mem' := fun {a} ha g h => by
        simp only [Pi.neg_apply, ha g h, smul_neg]; abel }

/-- The continuous `2`-cocycles `Z² = C² ⊓ ker d²`. -/
def Z2 : AddSubgroup (G × G → M) :=
  C2 G M ⊓
    { carrier := {f | groupCohomology.IsCocycle₂ f}
      add_mem' := fun {a b} ha hb g h j => by
        simp only [Pi.add_apply, smul_add]
        rw [add_add_add_comm, ha g h j, hb g h j, add_add_add_comm]
      zero_mem' := fun g h j => by simp
      neg_mem' := fun {a} ha g h j => by
        simp only [Pi.neg_apply, smul_neg, ← neg_add]
        exact congrArg Neg.neg (ha g h j) }

/-- The `2`-coboundaries `B² = d¹(C¹)`, the image of the **continuous** `1`-cochains. Taking the
image of all of `G → M` can give a strictly larger subgroup for a group with a discontinuous
`1`-cochain, and the resulting quotient would not be continuous cohomology. -/
def B2 : AddSubgroup (G × G → M) := AddSubgroup.map (d1 G M) (C1 G M)

variable {G M}

/-- A cochain is a continuous `1`-cocycle exactly when it is continuous and satisfies the
`1`-cocycle identity. -/
@[simp]
theorem mem_Z1_iff {f : G → M} :
    f ∈ Z1 G M ↔ Continuous f ∧ groupCohomology.IsCocycle₁ f := (Iff.rfl)

/-- A cochain is a continuous `2`-cocycle exactly when it is continuous and satisfies the
`2`-cocycle identity. -/
@[simp]
theorem mem_Z2_iff {f : G × G → M} :
    f ∈ Z2 G M ↔ Continuous f ∧ groupCohomology.IsCocycle₂ f := (Iff.rfl)

/-- Membership in `B²` exhibits a *continuous* primitive. -/
@[simp]
theorem mem_B2_iff {f : G × G → M} :
    f ∈ B2 G M ↔ ∃ c : G → M, Continuous c ∧ d1 G M c = f := by
  simp only [B2, AddSubgroup.mem_map, mem_C1]

variable (G M)

/-- `Z¹` is the intersection of the continuous cochains with the kernel of `d¹`. -/
theorem Z1_eq_inf_ker : Z1 G M = C1 G M ⊓ (d1 G M).ker :=
  SetLike.ext fun _ => by rw [mem_Z1_iff, AddSubgroup.mem_inf, mem_C1, mem_ker_d1_iff]

/-- `Z²` is the intersection of the continuous cochains with the kernel of `d²`. -/
theorem Z2_eq_inf_ker : Z2 G M = C2 G M ⊓ (d2 G M).ker :=
  SetLike.ext fun _ => by rw [mem_Z2_iff, AddSubgroup.mem_inf, mem_C2, mem_ker_d2_iff]

/-- Continuous `1`-cocycles are continuous `1`-cochains. -/
theorem Z1_le_C1 : Z1 G M ≤ C1 G M := fun _ hf => hf.1

/-- Continuous `2`-cocycles are continuous `2`-cochains. -/
theorem Z2_le_C2 : Z2 G M ≤ C2 G M := fun _ hf => hf.1

variable {G M}

/-- A continuous `1`-cocycle vanishes at `1`. This is a lemma and not part of the definition of
`Z¹`: cochains here are not normalised. -/
theorem map_one_of_mem_Z1 {f : G → M} (hf : f ∈ Z1 G M) : f 1 = 0 :=
  groupCohomology.map_one_of_isCocycle₁ hf.2

/-- The inverse formula for a continuous `1`-cocycle. -/
theorem smul_map_inv_of_mem_Z1 {f : G → M} (hf : f ∈ Z1 G M) (g : G) : g • f g⁻¹ = -f g :=
  groupCohomology.map_inv_of_isCocycle₁ hf.2 g

/-- The first degree-`2` normalisation. -/
theorem map_one_fst_of_mem_Z2 {f : G × G → M} (hf : f ∈ Z2 G M) (g : G) : f (1, g) = f (1, 1) :=
  groupCohomology.map_one_fst_of_isCocycle₂ hf.2 g

/-- The second degree-`2` normalisation. -/
theorem map_one_snd_of_mem_Z2 {f : G × G → M} (hf : f ∈ Z2 G M) (g : G) :
    f (g, 1) = g • f (1, 1) :=
  groupCohomology.map_one_snd_of_isCocycle₂ hf.2 g

variable (G M)

/-- The first continuous cohomology group `H¹(G, M) = Z¹/B¹`. -/
abbrev H1 := (Z1 G M) ⧸ ((B1 G M).addSubgroupOf (Z1 G M))

/-- The second continuous cohomology group `H²(G, M) = Z²/B²`. -/
abbrev H2 := (Z2 G M) ⧸ ((B2 G M).addSubgroupOf (Z2 G M))

/-- The class map in degree `1`. -/
abbrev H1pi : (Z1 G M) →+ H1 G M := QuotientAddGroup.mk' _

/-- The class map in degree `2`. -/
abbrev H2pi : (Z2 G M) →+ H2 G M := QuotientAddGroup.mk' _

/-- Every class in `H¹` is represented by a continuous `1`-cocycle. -/
theorem H1pi_surjective : Function.Surjective (H1pi G M) :=
  QuotientAddGroup.mk'_surjective _

/-- Every class in `H²` is represented by a continuous `2`-cocycle. -/
theorem H2pi_surjective : Function.Surjective (H2pi G M) :=
  QuotientAddGroup.mk'_surjective _

variable {G M}

/-- A continuous `1`-cocycle has trivial class exactly when it is a coboundary. -/
theorem H1pi_eq_zero_iff {f : Z1 G M} : H1pi G M f = 0 ↔ (f : G → M) ∈ B1 G M := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

/-- A continuous `2`-cocycle has trivial class exactly when it is a coboundary. -/
theorem H2pi_eq_zero_iff {f : Z2 G M} : H2pi G M f = 0 ↔ (f : G × G → M) ∈ B2 G M := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

end Cocycles

section Continuity

variable {G : Type u} [Group G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- Every `1`-coboundary is continuous. -/
theorem continuous_d0 (m : M) : Continuous (d0 G M m) :=
  (continuous_id.smul continuous_const).sub continuous_const

variable (G M)

/-- `1`-coboundaries are continuous `1`-cochains. -/
theorem B1_le_C1 : B1 G M ≤ C1 G M := by
  intro f hf
  obtain ⟨m, rfl⟩ := AddMonoidHom.mem_range.1 hf
  exact continuous_d0 m

/-- `d ∘ d = 0` in the form the degree-`1` quotient needs. -/
theorem B1_le_Z1 : B1 G M ≤ Z1 G M := by
  intro f hf
  obtain ⟨m, rfl⟩ := AddMonoidHom.mem_range.1 hf
  refine mem_Z1_iff.2 ⟨continuous_d0 m, mem_ker_d1_iff.1 ?_⟩
  simpa [AddMonoidHom.mem_ker] using congrArg (fun φ => φ m) (d1_comp_d0 G M)

end Continuity

section ContinuityMul

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- `d¹` preserves continuity. -/
theorem continuous_d1 {f : G → M} (hf : Continuous f) : Continuous (d1 G M f) :=
  ((continuous_fst.smul (hf.comp continuous_snd)).sub
    (hf.comp (continuous_fst.mul continuous_snd))).add (hf.comp continuous_fst)

variable (G M)

/-- `d ∘ d = 0` in the form the degree-`2` quotient needs. -/
theorem B2_le_Z2 : B2 G M ≤ Z2 G M := by
  intro f hf
  obtain ⟨c, hc, rfl⟩ := mem_B2_iff.1 hf
  refine mem_Z2_iff.2 ⟨continuous_d1 hc, mem_ker_d2_iff.1 ?_⟩
  simpa [AddMonoidHom.mem_ker] using congrArg (fun φ => φ c) (d2_comp_d1 G M)

/-- `2`-coboundaries are continuous `2`-cochains. -/
theorem B2_le_C2 : B2 G M ≤ C2 G M := (B2_le_Z2 G M).trans (Z2_le_C2 G M)

end ContinuityMul

section TrivialAction

variable {G : Type u} [Group G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] (htriv : ∀ (g : G) (m : M), g • m = m)

include htriv

/-- For a trivial action the continuous `1`-cocycles are exactly the continuous homomorphisms
`G → Multiplicative M`. -/
def trivialZ1Equiv : Z1 G M ≃+ Additive (ContinuousMonoidHom G (Multiplicative M)) where
  toFun f := Additive.ofMul
    { toMonoidHom :=
        MonoidHom.mk' (fun g => Multiplicative.ofAdd ((f : G → M) g)) fun a b => by
          have h := (mem_Z1_iff.1 f.2).2 a b
          rw [htriv a ((f : G → M) b)] at h
          exact h.trans (add_comm _ _)
      continuous_toFun := (mem_Z1_iff.1 f.2).1 }
  invFun φ :=
    ⟨fun g => Multiplicative.toAdd ((Additive.toMul φ) g),
      mem_Z1_iff.2 ⟨map_continuous (Additive.toMul φ), fun a b => by
        rw [htriv a (Multiplicative.toAdd ((Additive.toMul φ) b))]
        exact (congrArg Multiplicative.toAdd (map_mul (Additive.toMul φ) a b)).trans
          (add_comm _ _)⟩⟩
  left_inv f := Subtype.ext rfl
  right_inv φ := Additive.toMul.injective (DFunLike.ext _ _ fun _ => rfl)
  map_add' f g := Additive.toMul.injective (DFunLike.ext _ _ fun _ => rfl)

/-- The homomorphism attached to a continuous `1`-cocycle by `trivialZ1Equiv` is the cocycle
itself. -/
@[simp]
theorem trivialZ1Equiv_apply (f : Z1 G M) (g : G) :
    Additive.toMul (trivialZ1Equiv htriv f) g = Multiplicative.ofAdd ((f : G → M) g) := (rfl)

/-- The continuous `1`-cocycle attached to a continuous homomorphism by `trivialZ1Equiv` is the
homomorphism itself. -/
@[simp]
theorem trivialZ1Equiv_symm_apply
    (φ : Additive (ContinuousMonoidHom G (Multiplicative M))) (g : G) :
    (((trivialZ1Equiv htriv).symm φ : Z1 G M) : G → M) g =
      Multiplicative.toAdd ((Additive.toMul φ) g) := (rfl)

/-- For a trivial action `H¹(G, M)` is the group of continuous homomorphisms
`G →ₜ* Multiplicative M`.

Continuity is what makes this useful rather than decorative: without it the right-hand side is the
group of abstract homomorphisms, which for a profinite group is enormous. -/
noncomputable def trivialH1Equiv :
    H1 G M ≃+ Additive (ContinuousMonoidHom G (Multiplicative M)) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (M := (B1 G M).addSubgroupOf (Z1 G M)) (N := ⊥) (by
        rw [B1_eq_bot_of_smul_eq_self htriv]
        exact AddSubgroup.bot_addSubgroupOf _)).trans
    (QuotientAddGroup.quotientBot.trans (trivialZ1Equiv htriv))

/-- `trivialH1Equiv` sends the class of a continuous `1`-cocycle to the homomorphism it is. -/
@[simp]
theorem trivialH1Equiv_apply (f : Z1 G M) :
    trivialH1Equiv htriv (f : H1 G M) = trivialZ1Equiv htriv f := by
  simp only [trivialH1Equiv, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  -- Expose `quotientBot` as its kernel lift so its representative rule applies explicitly.
  change trivialZ1Equiv htriv
      ((QuotientAddGroup.kerLift (AddMonoidHom.id (Z1 G M)))
        (↑f : (Z1 G M) ⧸ (AddMonoidHom.id (Z1 G M)).ker)) = trivialZ1Equiv htriv f
  rw [QuotientAddGroup.kerLift_mk]
  rfl

end TrivialAction

end TauCeti.ContCohomology
