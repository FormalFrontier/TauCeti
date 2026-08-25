/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# The explicit continuous complex of a discrete group is Mathlib's inhomogeneous complex

For a group `G` carrying the *discrete* topology every continuity condition in the explicit
low-degree complex of continuous cochains is vacuous, so that complex is literally Mathlib's
complex of inhomogeneous cochains of the representation `Rep.ofDistribMulAction ℤ G M`. This file
proves that, degree by degree, and concludes with the three additive isomorphisms

```text
H⁰(G, M) ≃+ H⁰_grp(G, M),   H¹(G, M) ≃+ H¹_grp(G, M),   H²(G, M) ≃+ H²_grp(G, M).
```

## Main definitions

* `TauCeti.ContCohomology.explicitH0IsoGroupCohomology`,
  `TauCeti.ContCohomology.explicitH1IsoGroupCohomology` and
  `TauCeti.ContCohomology.explicitH2IsoGroupCohomology`: the three comparison isomorphisms.
* `TauCeti.ContCohomology.H0AddEquivInvariants`,
  `TauCeti.ContCohomology.Z1AddEquivCocycles₁` and
  `TauCeti.ContCohomology.Z2AddEquivCocycles₂`: the underlying identifications of the numerators,
  which is where the mathematical content sits; the two isomorphisms in degrees `1` and `2` are
  the induced maps on the subquotients, and in degree `0` there is no denominator to divide by.

Degree `0` needs no topological hypothesis whatever, and degree `1` needs discreteness only for
the cocycles: `B¹` is the image of *all* of `M`, so it never sees a continuity condition. It is
degree `2` where discreteness enters the denominator, `B²` being the image of the continuous
`1`-cochains.

## Main statements

* `TauCeti.ContCohomology.C1_eq_top` and `TauCeti.ContCohomology.C2_eq_top`: over a discrete group
  every cochain is continuous.
* `TauCeti.ContCohomology.d0_apply_eq_d₀₁_hom_apply` and its degree-`1` and degree-`2`
  counterparts: the explicit differentials are Mathlib's, on the nose.
* `TauCeti.ContCohomology.mem_cocycles₁_iff_mem_Z1`,
  `TauCeti.ContCohomology.mem_coboundaries₁_iff_mem_B1` and their degree-`2` and degree-`0`
  counterparts: the dictionary between the two sets of cocycles and coboundaries.

## Implementation notes

The universes are pinned by the pin and not by the mathematics. Mathlib's low-degree
`groupCohomology` comparison API forces the group and coefficient module into `Type 0` when the
coefficient ring is `ℤ`. Thus the three final comparison isomorphisms carry `G M : Type`, while the
differentials, membership dictionaries, and numerator equivalences keep every universe not
constrained by Mathlib's representation API arbitrary. `C1_eq_top` and `C2_eq_top` mention nothing
of Mathlib's theory and are fully polymorphic. When the pin drops these restrictions the binders
here can simply be widened.

The isomorphisms are built as `AddEquiv`s and not as isomorphisms in `ModuleCat ℤ`. The explicit
`H¹` and `H²` are bare additive groups by construction, their inherited quotient topology being the
wrong one; `TauCeti.ContCohomology.DiscreteH1` and `DiscreteH2` are the carriers used when a
topology is wanted, and the comparison with the *canonical* continuous cohomology is where that
choice matters. Against `groupCohomology` there is no topology on either side, so an additive
isomorphism is the whole statement.

`Rep.ofDistribMulAction ℤ G M` is Mathlib's translation of an unbundled `DistribMulAction` into
`Rep ℤ G`; the `ℤ`-linearity of the comparison is automatic and is not restated, because the
explicit complex is a complex of additive groups. Mathlib's `cocyclesOfIsCocycle₁`,
`isCocycle₁_of_mem_cocycles₁` and their siblings prove the same dictionary as the four membership
lemmas here, but they are stated for `{k G A : Type u}` — all three in one universe — so they are
not reused; the proofs below go through `groupCohomology.mem_cocycles₁_iff` and
`mem_cocycles₂_iff`, which carry no such constraint.

This implements the "continuous against discrete" milestone of Layer 3 of the human-authored
roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`, whose `Suggested.lean` fixes the names
`explicitH0IsoGroupCohomology`, `explicitH1IsoGroupCohomology` and `explicitH2IsoGroupCohomology`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2: the
  cohomology of a profinite group is computed by the complex of continuous cochains, which for a
  discrete group is the abstract inhomogeneous complex.
-/

public section

namespace TauCeti.ContCohomology

universe u v

open groupCohomology

section Differentials

variable (G : Type) [Group G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/- `Rep.ofDistribMulAction ℤ G M` has carrier definitionally equal to `M`, and its action is
definitionally the original `G`-action. The comparison proofs below use those definitional
identifications; the named Mathlib formulas record the two sides being identified. -/

/-- The explicit degree-`0` differential is Mathlib's `d₀₁`. -/
theorem d0_apply_eq_d₀₁_hom_apply (m : M) :
    d0 G M m = (groupCohomology.d₀₁ (Rep.ofDistribMulAction ℤ G M)).hom m :=
  funext fun g =>
    (d0_apply m g).trans (d₀₁_hom_apply (A := Rep.ofDistribMulAction ℤ G M) m g).symm

/-- The explicit degree-`1` differential is Mathlib's `d₁₂`. -/
theorem d1_apply_eq_d₁₂_hom_apply (f : G → M) :
    d1 G M f = (groupCohomology.d₁₂ (Rep.ofDistribMulAction ℤ G M)).hom f :=
  funext fun q =>
    (d1_apply f q.1 q.2).trans (d₁₂_hom_apply (A := Rep.ofDistribMulAction ℤ G M) f q).symm

/-- The explicit degree-`2` differential is Mathlib's `d₂₃`. -/
theorem d2_apply_eq_d₂₃_hom_apply (f : G × G → M) :
    d2 G M f = (groupCohomology.d₂₃ (Rep.ofDistribMulAction ℤ G M)).hom f :=
  funext fun q =>
    (d2_apply f q.1 q.2.1 q.2.2).trans
      (d₂₃_hom_apply (A := Rep.ofDistribMulAction ℤ G M) f q).symm

end Differentials

section DictionaryDegree0

variable {G : Type u} [Group G] {M : Type v} [AddCommGroup M] [DistribMulAction G M]

/-- Degree `0`: the invariants of the induced representation are the explicit `H⁰ = M^G`. -/
@[simp]
theorem mem_invariants_iff_mem_H0 (m : M) :
    m ∈ (Rep.ofDistribMulAction ℤ G M).ρ.invariants ↔ m ∈ H0 G M :=
  ⟨fun h => (FixedPoints.mem_addSubgroup G M m).2 fun g => h g,
    fun h g => (FixedPoints.mem_addSubgroup G M m).1 h g⟩

end DictionaryDegree0

section DictionaryPositiveDegree

variable {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

/-- Degree `1`, cocycles: over a discrete group the continuity half of `Z¹` is free, so the
continuous `1`-cocycles are Mathlib's `1`-cocycles. -/
@[simp]
theorem mem_cocycles₁_iff_mem_Z1 (f : G → M) :
    f ∈ cocycles₁ (Rep.ofDistribMulAction ℤ G M) ↔ f ∈ Z1 G M :=
  ⟨fun h => mem_Z1_iff.2 ⟨continuous_of_discreteTopology,
      fun g h' => (mem_cocycles₁_iff (A := Rep.ofDistribMulAction ℤ G M) f).1 h g h'⟩,
    fun h => (mem_cocycles₁_iff (A := Rep.ofDistribMulAction ℤ G M) f).2
      fun g h' => (mem_Z1_iff.1 h).2 g h'⟩

omit [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace M] [IsTopologicalAddGroup M] in
/-- Degree `1`, coboundaries: `B¹` carries no continuity condition on its primitive, so the two
definitions agree over any topological group; discreteness is not used. -/
@[simp]
theorem mem_coboundaries₁_iff_mem_B1 (f : G → M) :
    f ∈ coboundaries₁ (Rep.ofDistribMulAction ℤ G M) ↔ f ∈ B1 G M :=
  ⟨fun ⟨m, hm⟩ => mem_B1_iff.2 ⟨m, fun g => congrFun hm g⟩,
    fun h => (mem_B1_iff.1 h).elim fun m hm => ⟨m, funext hm⟩⟩

/-- Degree `2`, cocycles: as in degree `1`, over a discrete group the continuity half of `Z²` is
free, `G × G` being discrete as well. -/
@[simp]
theorem mem_cocycles₂_iff_mem_Z2 (f : G × G → M) :
    f ∈ cocycles₂ (Rep.ofDistribMulAction ℤ G M) ↔ f ∈ Z2 G M :=
  ⟨fun h => mem_Z2_iff.2 ⟨continuous_of_discreteTopology,
      fun g h' j => (mem_cocycles₂_iff (A := Rep.ofDistribMulAction ℤ G M) f).1 h g h' j⟩,
    fun h => (mem_cocycles₂_iff (A := Rep.ofDistribMulAction ℤ G M) f).2
      fun g h' j => (mem_Z2_iff.1 h).2 g h' j⟩

/-- Degree `2`, coboundaries. Here discreteness *is* used: `B²` is by definition the image of the
**continuous** `1`-cochains, and over a discrete group those are all of them. -/
@[simp]
theorem mem_coboundaries₂_iff_mem_B2 (f : G × G → M) :
    f ∈ coboundaries₂ (Rep.ofDistribMulAction ℤ G M) ↔ f ∈ B2 G M :=
  ⟨fun ⟨c, hc⟩ => mem_B2_iff'.2 ⟨c, continuous_of_discreteTopology,
      fun g h => congrFun hc (g, h)⟩,
    fun h => (mem_B2_iff'.1 h).elim fun c hc => ⟨c, funext fun p => hc.2 p.1 p.2⟩⟩

end DictionaryPositiveDegree

section NumeratorDegree0

/-! Degree `0` is the one degree where the comparison needs no hypothesis on the topology at all:
both sides are the invariants, and continuity constrains no `0`-cochain. -/

variable (G : Type u) [Group G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-- Degree `0`, on the carriers: the explicit `H⁰(G, M) = M^G` is the submodule of invariants of
the induced representation. -/
def H0AddEquivInvariants : H0 G M ≃+ (Rep.ofDistribMulAction ℤ G M).ρ.invariants where
  toFun m := ⟨m.1, (mem_invariants_iff_mem_H0 m.1).2 m.2⟩
  invFun m := ⟨m.1, (mem_invariants_iff_mem_H0 (G := G) (M := M) m.1).1 m.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem H0AddEquivInvariants_val (m : H0 G M) : (H0AddEquivInvariants G M m).1 = m.1 := (rfl)

@[simp]
theorem H0AddEquivInvariants_symm_val (m : (Rep.ofDistribMulAction ℤ G M).ρ.invariants) :
    ((H0AddEquivInvariants G M).symm m).1 = m.1 := (rfl)

end NumeratorDegree0

section ComparisonDegree0

variable (G : Type) [Group G] (M : Type) [AddCommGroup M] [DistribMulAction G M]

/-- **Layer 3, degree 0 against Mathlib's discrete group cohomology.** The explicit `H⁰(G, M)` is
Mathlib's `H⁰` of the representation attached to the action. -/
noncomputable def explicitH0IsoGroupCohomology :
    H0 G M ≃+ groupCohomology (Rep.ofDistribMulAction ℤ G M) 0 :=
  (H0AddEquivInvariants G M).trans
    (groupCohomology.H0Iso (Rep.ofDistribMulAction ℤ G M)).toLinearEquiv.symm.toAddEquiv

@[simp]
theorem explicitH0IsoGroupCohomology_apply (m : H0 G M) :
    explicitH0IsoGroupCohomology G M m =
      (groupCohomology.H0Iso (Rep.ofDistribMulAction ℤ G M)).inv (H0AddEquivInvariants G M m) :=
  (rfl)

@[simp]
theorem explicitH0IsoGroupCohomology_symm_apply
    (x : groupCohomology (Rep.ofDistribMulAction ℤ G M) 0) :
    (explicitH0IsoGroupCohomology G M).symm x =
      (H0AddEquivInvariants G M).symm
        ((groupCohomology.H0Iso (Rep.ofDistribMulAction ℤ G M)).hom x) :=
  (rfl)

end ComparisonDegree0

section NumeratorDegree1

variable (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

/-- Degree `1`, on the numerators: the continuous `1`-cocycles are Mathlib's `1`-cocycles. -/
def Z1AddEquivCocycles₁ : Z1 G M ≃+ cocycles₁ (Rep.ofDistribMulAction ℤ G M) where
  toFun z := ⟨z.1, (mem_cocycles₁_iff_mem_Z1 z.1).2 z.2⟩
  invFun c := ⟨c.1, (mem_cocycles₁_iff_mem_Z1 (G := G) (M := M) c.1).1 c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem Z1AddEquivCocycles₁_coe (z : Z1 G M) :
    ⇑(Z1AddEquivCocycles₁ G M z) = (z : G → M) := (rfl)

@[simp]
theorem Z1AddEquivCocycles₁_symm_coe (c : cocycles₁ (Rep.ofDistribMulAction ℤ G M)) :
    (((Z1AddEquivCocycles₁ G M).symm c : Z1 G M) : G → M) = ⇑c := (rfl)

end NumeratorDegree1

section ComparisonDegree1

variable (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

variable [ContinuousSMul G M]

/-- **Layer 3, degree 1 against Mathlib's discrete group cohomology.** Every continuity condition
is vacuous for a discrete group, so this identifies subquotients of the same function space.
Layer 4 uses it at every finite level. -/
noncomputable def explicitH1IsoGroupCohomology :
    H1 G M ≃+ groupCohomology (Rep.ofDistribMulAction ℤ G M) 1 := by
  let φ := (groupCohomology.H1π (Rep.ofDistribMulAction ℤ G M)).hom.toAddMonoidHom.comp
    (Z1AddEquivCocycles₁ G M).toAddMonoidHom
  have hφ : Function.Surjective φ := fun y => by
    induction y using groupCohomology.H1_induction_on with
    | h c => exact ⟨((Z1AddEquivCocycles₁ G M).symm c : Z1 G M), rfl⟩
  have hker : (B1 G M).addSubgroupOf (Z1 G M) = φ.ker := by
    ext z
    constructor
    · exact fun hz => (groupCohomology.H1π_eq_zero_iff _).2
        ((mem_coboundaries₁_iff_mem_B1 z.1).2 hz)
    · exact fun hz => (mem_coboundaries₁_iff_mem_B1 z.1).1
        ((groupCohomology.H1π_eq_zero_iff _).1 hz)
  exact QuotientAddGroup.liftEquiv _ hφ hker

@[simp]
theorem explicitH1IsoGroupCohomology_mk (z : Z1 G M) :
    explicitH1IsoGroupCohomology G M (z : H1 G M) =
      groupCohomology.H1π _ (Z1AddEquivCocycles₁ G M z) :=
  (rfl)

@[simp]
theorem explicitH1IsoGroupCohomology_symm_H1π
    (c : cocycles₁ (Rep.ofDistribMulAction ℤ G M)) :
    (explicitH1IsoGroupCohomology G M).symm (groupCohomology.H1π _ c) =
      (((Z1AddEquivCocycles₁ G M).symm c : Z1 G M) : H1 G M) := by
  rw [AddEquiv.symm_apply_eq, explicitH1IsoGroupCohomology_mk, AddEquiv.apply_symm_apply]

end ComparisonDegree1

section NumeratorDegree2

variable (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

/-- Degree `2`, on the numerators: the continuous `2`-cocycles are Mathlib's `2`-cocycles. -/
def Z2AddEquivCocycles₂ : Z2 G M ≃+ cocycles₂ (Rep.ofDistribMulAction ℤ G M) where
  toFun z := ⟨z.1, (mem_cocycles₂_iff_mem_Z2 z.1).2 z.2⟩
  invFun c := ⟨c.1, (mem_cocycles₂_iff_mem_Z2 (G := G) (M := M) c.1).1 c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem Z2AddEquivCocycles₂_coe (z : Z2 G M) :
    ⇑(Z2AddEquivCocycles₂ G M z) = (z : G × G → M) := (rfl)

@[simp]
theorem Z2AddEquivCocycles₂_symm_coe (c : cocycles₂ (Rep.ofDistribMulAction ℤ G M)) :
    (((Z2AddEquivCocycles₂ G M).symm c : Z2 G M) : G × G → M) = ⇑c := (rfl)

end NumeratorDegree2

section ComparisonDegree2

variable (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

variable [ContinuousSMul G M]

/-- **Layer 3, degree 2 against Mathlib's discrete group cohomology.** The denominator is where
discreteness is used twice over: `B²` is the image of the *continuous* `1`-cochains, and over a
discrete group those exhaust `G → M`. -/
noncomputable def explicitH2IsoGroupCohomology :
    H2 G M ≃+ groupCohomology (Rep.ofDistribMulAction ℤ G M) 2 := by
  let φ := (groupCohomology.H2π (Rep.ofDistribMulAction ℤ G M)).hom.toAddMonoidHom.comp
    (Z2AddEquivCocycles₂ G M).toAddMonoidHom
  have hφ : Function.Surjective φ := fun y => by
    induction y using groupCohomology.H2_induction_on with
    | h c => exact ⟨((Z2AddEquivCocycles₂ G M).symm c : Z2 G M), rfl⟩
  have hker : (B2 G M).addSubgroupOf (Z2 G M) = φ.ker := by
    ext z
    constructor
    · exact fun hz => (groupCohomology.H2π_eq_zero_iff _).2
        ((mem_coboundaries₂_iff_mem_B2 z.1).2 hz)
    · exact fun hz => (mem_coboundaries₂_iff_mem_B2 z.1).1
        ((groupCohomology.H2π_eq_zero_iff _).1 hz)
  exact QuotientAddGroup.liftEquiv _ hφ hker

@[simp]
theorem explicitH2IsoGroupCohomology_mk (z : Z2 G M) :
    explicitH2IsoGroupCohomology G M (z : H2 G M) =
      groupCohomology.H2π _ (Z2AddEquivCocycles₂ G M z) :=
  (rfl)

@[simp]
theorem explicitH2IsoGroupCohomology_symm_H2π
    (c : cocycles₂ (Rep.ofDistribMulAction ℤ G M)) :
    (explicitH2IsoGroupCohomology G M).symm (groupCohomology.H2π _ c) =
      (((Z2AddEquivCocycles₂ G M).symm c : Z2 G M) : H2 G M) := by
  rw [AddEquiv.symm_apply_eq, explicitH2IsoGroupCohomology_mk, AddEquiv.apply_symm_apply]

end ComparisonDegree2

end TauCeti.ContCohomology
