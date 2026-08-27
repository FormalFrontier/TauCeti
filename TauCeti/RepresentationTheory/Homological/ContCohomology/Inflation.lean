/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Invariants

/-!
# Inflation and the inflation-restriction sequence

Inflation is the third named instance of the compatible-pair pullback on the explicit low-degree
complex: for a normal subgroup `N` of a topological group `G` it is the pullback along the
quotient homomorphism `G → G ⧸ N` paired with the inclusion `M ^ N ↪ M` of the invariants, which
is equivariant along that homomorphism. This file defines inflation in degrees `1` and `2` and
proves the exactness of

```text
0 → H¹(G ⧸ N, M ^ N) → H¹(G, M) → H¹(N, M)
```

at its two nodes.

## Main definitions

* `TauCeti.ContCohomology.explicitInfl1` and `TauCeti.ContCohomology.explicitInfl2`: inflation on
  the explicit model in degrees `1` and `2`.

## Main statements

* `TauCeti.ContCohomology.explicitRes1_comp_explicitInfl1` and
  `TauCeti.ContCohomology.explicitRes2_comp_explicitInfl2`: restricting an inflated class back to
  `N` gives zero.
* `TauCeti.ContCohomology.explicitInfl1_injective`: inflation is injective in degree `1`.
* `TauCeti.ContCohomology.explicitInfRes_exact`: the image of inflation is exactly the kernel of
  restriction in degree `1`.

## Implementation notes

Inflation lives here rather than beside `explicitRes1` and `explicitCoeff1` in
`ExplicitFunctoriality.lean` because it is the one of the three named instances whose coefficients
change — it needs the invariants and their quotient action — and because the exactness statements
below are about that same map and belong with it.

The coefficients over the quotient group are Mathlib's `FixedPoints.addSubgroup N M`, with the
`G ⧸ N`-action and the coercion lemmas supplied by
`TauCeti/GroupTheory/GroupAction/FixedPoints.lean`; no second name for `M ^ N` is introduced.
Continuity of that action is carried as the instance hypothesis
`[ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]` rather than deduced from discreteness of
`M`, because nothing below uses discreteness for anything else;
`TauCeti.continuousSMulQuotientFixedPointsOfContinuousSMul` discharges it for a discrete `M`, which
is the case the roadmap's arithmetic consumers instantiate.

Everything here holds for an arbitrary topological group `G` and an arbitrary normal subgroup `N`;
neither profiniteness nor closedness of `N` is used. Closedness would only make `G ⧸ N` Hausdorff,
and the descent argument in `TauCeti.ContCohomology.explicitInfRes_exact` needs nothing but the
quotient topology: a cochain on `G` that is constant on the cosets of `N` descends to a
*continuous* cochain on `G ⧸ N` precisely because `G ⧸ N` carries that topology.

The exactness proof is the classical cochain argument. After subtracting the coboundary that
trivialises a cocycle on `N`, the corrected cocycle vanishes on `N`, hence is constant on the
cosets of `N` and takes its values in `M ^ N`, so it is the inflation of a continuous `1`-cocycle
on `G ⧸ N`. This is the continuous counterpart of Mathlib's discrete `groupCohomology.H1InfRes`
and `groupCohomology.H1InfRes_exact`, which are stated for `Rep k G` and so are unavailable at the
universe-polymorphic unbundled generality used here.

This implements the inflation part of the "three instances, in all three degrees" milestone of
Layer 2, and the "inflation-restriction" milestone of Layer 5, of the human-authored roadmap
`TauCetiRoadmap/ProfiniteCohomology/README.md`, whose `Suggested.lean` fixes the names
`explicitInfl1`, `explicitInfl2`, `explicitInfl1_injective` and `explicitInfRes_exact`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.7): the
  inflation-restriction sequence, whose first three terms are the exact sequence proved here.
-/

public section

namespace TauCeti.ContCohomology

universe u v

section Cosets

variable {G : Type u} [Group G] {N : Subgroup G} [N.Normal]

/-- The coset of an element of `N` is trivial. This is the form in which the cocycle computations
below evaluate an inflated cochain on `N`. -/
private theorem quotientMk_coe_eq_one (n : N) : ((n : G) : G ⧸ N) = 1 :=
  (QuotientGroup.eq_one_iff (n : G)).2 n.2

end Cosets

section CompatiblePair

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (N : Subgroup G) [N.Normal]

/-- The inclusion `M ^ N ↪ M` is equivariant along the quotient homomorphism `G → G ⧸ N`: the
`G ⧸ N`-action on an invariant element, read in `M`, is the `G`-action. This is the
compatible-pair hypothesis that inflation is the instance of `explicitMap1` and `explicitMap2`
at. -/
theorem subtype_quotientMk_smul (g : G) (m : FixedPoints.addSubgroup N M) :
    (FixedPoints.addSubgroup N M).subtype (ContinuousMonoidHom.quotientMk N g • m) =
      g • (FixedPoints.addSubgroup N M).subtype m := by
  simp only [ContinuousMonoidHom.quotientMk_apply, AddSubgroup.coe_subtype,
    coe_quotient_smul_fixedPoints_addSubgroup, coe_smul_fixedPoints_addSubgroup]

end CompatiblePair

section DegreeOne

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]

/-- **Inflation in degree one**: the compatible-pair pullback along the quotient homomorphism
`G → G ⧸ N`, with the invariants `M ^ N` as coefficients. -/
noncomputable def explicitInfl1 :
    H1 (G ⧸ N) (FixedPoints.addSubgroup N M) →+ H1 G M :=
  explicitMap1 (G ⧸ N) (FixedPoints.addSubgroup N M) G M (ContinuousMonoidHom.quotientMk N)
    (FixedPoints.addSubgroup N M).subtype (continuous_fixedPoints_addSubgroup_subtype G M N)
    (subtype_quotientMk_smul G M N)

/-- Inflation sends the class of a continuous `1`-cocycle on `G ⧸ N` to the class of the cocycle
it inflates to; `TauCeti.ContCohomology.cocyclesMap1_apply` evaluates the latter. -/
@[simp]
theorem explicitInfl1_mk (c : Z1 (G ⧸ N) (FixedPoints.addSubgroup N M)) :
    explicitInfl1 G M N (c : H1 (G ⧸ N) (FixedPoints.addSubgroup N M)) =
      (cocyclesMap1 (G ⧸ N) (FixedPoints.addSubgroup N M) G M (ContinuousMonoidHom.quotientMk N)
        (FixedPoints.addSubgroup N M).subtype (continuous_fixedPoints_addSubgroup_subtype G M N)
        (subtype_quotientMk_smul G M N) c : H1 G M) :=
  explicitMap1_mk _ _ _ _ _ _ _ _ c

/-- **Restriction to `N` kills inflation in degree one**, the first half of the
inflation-restriction sequence: the inflation of a cocycle restricts to the zero cochain on `N`,
because a continuous `1`-cocycle vanishes at `1`. -/
theorem explicitRes1_comp_explicitInfl1 :
    (explicitRes1 G M N).comp (explicitInfl1 G M N) = 0 := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [AddMonoidHom.comp_apply, explicitInfl1_mk, explicitRes1_mk, AddMonoidHom.zero_apply,
      H1pi_eq_zero_iff, mem_B1_iff]
    refine ⟨0, fun n => ?_⟩
    rw [cocyclesMap1_apply, cocyclesMap1_apply]
    simp [quotientMk_coe_eq_one n, map_one_of_mem_Z1 c.2]

/-- **Inflation is injective in degree one.** A cocycle on `G ⧸ N` whose inflation is the
coboundary of `m : M` has `m` fixed by `N`, so it is already the coboundary of `m` viewed in
`M ^ N`. -/
theorem explicitInfl1_injective : Function.Injective (explicitInfl1 G M N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitInfl1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hx
    obtain ⟨m, hm⟩ := hx
    have hmem : m ∈ FixedPoints.addSubgroup N M := by
      refine (FixedPoints.mem_addSubgroup N M m).2 fun n => ?_
      have h := hm (n : G)
      rw [cocyclesMap1_apply] at h
      simp only [ContinuousMonoidHom.quotientMk_apply, quotientMk_coe_eq_one,
        map_one_of_mem_Z1 c.2, AddSubgroup.coe_subtype, ZeroMemClass.coe_zero, sub_eq_zero] at h
      exact h
    rw [H1pi_eq_zero_iff, mem_B1_iff]
    refine ⟨⟨m, hmem⟩, fun q => ?_⟩
    induction q using QuotientGroup.induction_on with
    | H g =>
      have h := hm g
      rw [cocyclesMap1_apply] at h
      refine Subtype.ext ?_
      rw [AddSubgroup.coe_sub, coe_quotient_smul_fixedPoints_addSubgroup,
        coe_smul_fixedPoints_addSubgroup]
      simpa using h

variable {G M N}

omit [ContinuousSMul G M] [N.Normal]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)] in
/-- A continuous `1`-cocycle vanishing on `N` is constant on the cosets of `N`. -/
private theorem apply_mul_eq_self_of_vanishing {z : Z1 G M}
    (hz : ∀ n : N, (z : G → M) (n : G) = 0) (g : G) (n : N) :
    (z : G → M) (g * (n : G)) = (z : G → M) g := by
  rw [(mem_Z1_iff.1 z.2).2 g (n : G), hz n, smul_zero, zero_add]

omit [ContinuousSMul G M] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)] in
/-- The values of a continuous `1`-cocycle vanishing on `N` are fixed by `N`: the cocycle identity
computes `z (n * g)` as `n • z g`, and `n * g = g * (g⁻¹ * n * g)` has its second factor in the
normal subgroup `N`. -/
private theorem smul_apply_eq_self_of_vanishing {z : Z1 G M}
    (hz : ∀ n : N, (z : G → M) (n : G) = 0) (g : G) (n : N) :
    (n : G) • (z : G → M) g = (z : G → M) g := by
  have h := (mem_Z1_iff.1 z.2).2 (n : G) g
  rw [hz n, add_zero] at h
  have hconj : ((n : G) * g) = g * (g⁻¹ * (n : G) * g) := by group
  rw [hconj, apply_mul_eq_self_of_vanishing hz g ⟨g⁻¹ * (n : G) * g,
    ‹N.Normal›.conj_mem' (n : G) n.2 g⟩] at h
  exact h.symm

/-- The descent to `G ⧸ N` of a continuous `1`-cocycle vanishing on `N`. It is well defined by
`apply_mul_eq_self_of_vanishing`, takes its values in `M ^ N` by
`smul_apply_eq_self_of_vanishing`, and is continuous because `G ⧸ N` carries the quotient
topology. -/
private def descendZ1 (z : Z1 G M) (hz : ∀ n : N, (z : G → M) (n : G) = 0) :
    Z1 (G ⧸ N) (FixedPoints.addSubgroup N M) :=
  ⟨fun q => Quotient.liftOn' q
      (fun g => (⟨(z : G → M) g,
        (FixedPoints.mem_addSubgroup N M _).2 (smul_apply_eq_self_of_vanishing hz g)⟩ :
          FixedPoints.addSubgroup N M))
      fun a b hab => Subtype.ext <| by
        simpa using
          (apply_mul_eq_self_of_vanishing hz a ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.1 hab⟩).symm,
    mem_Z1_iff.2 ⟨(QuotientGroup.isQuotientMap_mk N).continuous_iff.2
        (((mem_Z1_iff.1 z.2).1).subtype_mk _), fun q q' => by
      induction q using QuotientGroup.induction_on with
      | H a =>
        induction q' using QuotientGroup.induction_on with
        | H b =>
          refine Subtype.ext ?_
          rw [AddSubgroup.coe_add, coe_quotient_smul_fixedPoints_addSubgroup,
            coe_smul_fixedPoints_addSubgroup]
          exact (mem_Z1_iff.1 z.2).2 a b⟩⟩

omit [ContinuousSMul G M] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)] in
/-- The descent takes on the coset of `g` the value the original cocycle takes at `g`. This is the
computation rule of `Quotient.liftOn'` at a representative, so it is a `rfl`; isolating it here is
what lets `explicitInfl1_descendZ1` below be a rewrite rather than a definitional unfolding. -/
private theorem coe_descendZ1_apply_mk (z : Z1 G M) (hz : ∀ n : N, (z : G → M) (n : G) = 0)
    (g : G) :
    ((descendZ1 z hz : (G ⧸ N) → FixedPoints.addSubgroup N M) (g : G ⧸ N) : M) =
      (z : G → M) g :=
  rfl

/-- Inflating the descent of a continuous `1`-cocycle vanishing on `N` returns its class. -/
private theorem explicitInfl1_descendZ1 (z : Z1 G M) (hz : ∀ n : N, (z : G → M) (n : G) = 0) :
    explicitInfl1 G M N (descendZ1 z hz : H1 (G ⧸ N) (FixedPoints.addSubgroup N M)) =
      (z : H1 G M) := by
  rw [explicitInfl1_mk]
  refine congrArg (fun w : Z1 G M => (w : H1 G M)) (Subtype.ext (funext fun g => ?_))
  rw [cocyclesMap1_apply, ContinuousMonoidHom.quotientMk_apply, AddSubgroup.coe_subtype,
    coe_descendZ1_apply_mk]

variable (G M N)

/-- **Exactness of the inflation-restriction sequence at `H¹(G, M)`**: a continuous `1`-cocycle on
`G` that becomes a coboundary on `N` is, after subtracting that coboundary, inflated from
`G ⧸ N`. -/
theorem explicitInfRes_exact :
    (explicitInfl1 G M N).range = (explicitRes1 G M N).ker := by
  refine le_antisymm ((AddMonoidHom.range_le_ker_iff _ _).2
    (explicitRes1_comp_explicitInfl1 G M N)) fun x hx => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [AddMonoidHom.mem_ker, explicitRes1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hx
    obtain ⟨m, hm⟩ := hx
    -- Subtract the coboundary of `m`, so that the corrected cocycle `z` vanishes on `N`.
    have hmB1 : d0 G M m ∈ B1 G M := mem_B1_iff.2 ⟨m, fun g => (d0_apply m g).symm⟩
    set z : Z1 G M := c - ⟨d0 G M m, B1_le_Z1 G M hmB1⟩ with hzdef
    have hzc : (z : H1 G M) = (c : H1 G M) := by
      rw [H1pi_eq_iff, hzdef]
      simpa using neg_mem hmB1
    have hzN : ∀ n : N, (z : G → M) (n : G) = 0 := by
      intro n
      -- The `↥N`-action on `M` is the restriction of the `G`-action, so `hm n` may be read with
      -- the ambient scalar; Mathlib's `Submonoid.smul_def` is stated for a `Submonoid` and does
      -- not fire on a `Subgroup`.
      have h : (n : G) • m - m = (c : G → M) (n : G) := by
        have hn := hm n
        rw [cocyclesMap1_apply] at hn
        simp only [ContinuousMonoidHom.subgroupSubtype_apply, AddMonoidHom.id_apply] at hn
        exact hn
      simp [hzdef, ← h]
    exact ⟨(descendZ1 z hzN : H1 (G ⧸ N) (FixedPoints.addSubgroup N M)),
      (explicitInfl1_descendZ1 z hzN).trans hzc⟩

end DegreeOne

section DegreeTwo

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]

/-- **Inflation in degree two.** It is not a variant of degree one: it is the last map of the
five-term exact sequence. -/
noncomputable def explicitInfl2 :
    H2 (G ⧸ N) (FixedPoints.addSubgroup N M) →+ H2 G M :=
  explicitMap2 (G ⧸ N) (FixedPoints.addSubgroup N M) G M (ContinuousMonoidHom.quotientMk N)
    (FixedPoints.addSubgroup N M).subtype (continuous_fixedPoints_addSubgroup_subtype G M N)
    (subtype_quotientMk_smul G M N)

/-- Inflation sends the class of a continuous `2`-cocycle on `G ⧸ N` to the class of the cocycle
it inflates to; `TauCeti.ContCohomology.cocyclesMap2_apply` evaluates the latter. -/
@[simp]
theorem explicitInfl2_mk (c : Z2 (G ⧸ N) (FixedPoints.addSubgroup N M)) :
    explicitInfl2 G M N (c : H2 (G ⧸ N) (FixedPoints.addSubgroup N M)) =
      (cocyclesMap2 (G ⧸ N) (FixedPoints.addSubgroup N M) G M (ContinuousMonoidHom.quotientMk N)
        (FixedPoints.addSubgroup N M).subtype (continuous_fixedPoints_addSubgroup_subtype G M N)
        (subtype_quotientMk_smul G M N) c : H2 G M) :=
  explicitMap2_mk _ _ _ _ _ _ _ _ c

/-- **Restriction to `N` kills inflation in degree two.** The inflated cocycle restricts to the
constant cochain with value `c (1, 1)`, and since `N` fixes that value the constant is the
coboundary of the constant `1`-cochain with the same value. -/
theorem explicitRes2_comp_explicitInfl2 :
    (explicitRes2 G M N).comp (explicitInfl2 G M N) = 0 := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [AddMonoidHom.comp_apply, explicitInfl2_mk, explicitRes2_mk, AddMonoidHom.zero_apply,
      H2pi_eq_zero_iff, mem_B2_iff']
    set m₀ : FixedPoints.addSubgroup N M :=
      (c : (G ⧸ N) × (G ⧸ N) → FixedPoints.addSubgroup N M) (1, 1) with hm₀
    refine ⟨fun _ => (m₀ : M), continuous_const, fun n n' => ?_⟩
    have hfix := (FixedPoints.mem_addSubgroup N M (m₀ : M)).1 m₀.2 n
    rw [cocyclesMap2_apply, cocyclesMap2_apply]
    simp only [ContinuousMonoidHom.subgroupSubtype_apply, ContinuousMonoidHom.quotientMk_apply,
      quotientMk_coe_eq_one, AddMonoidHom.id_apply, AddSubgroup.coe_subtype, ← hm₀, hfix]
    abel

end DegreeTwo

end TauCeti.ContCohomology
