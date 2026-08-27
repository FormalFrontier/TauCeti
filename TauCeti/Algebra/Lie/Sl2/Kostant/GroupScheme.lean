/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Kostant.RootSubgroup
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus

/-!
# The full-weight rank-one Kostant carrier

The standard two-dimensional `sl₂` module has weights `1` and `-1`.  In particular, unlike the
adjoint representation with weights `0`, `2`, and `-2`, its weights generate the full rank-one
weight lattice rather than only the root lattice.  This file feeds that admissible integral
lattice into the toral Kostant construction and names the resulting rank-one group scheme, its
two root subgroups, and its split torus.

The carrier is completely explicit.  It is the smallest closed subgroup scheme of `GL₂` containing
the upper and lower elementary transvections and the diagonal matrices

```text
diag(s, s⁻¹).
```

The root operators have weights `2` and `-2`, so conjugation by the torus multiplies their
parameters by `s²` and `s⁻²`, respectively.  Thus the represented torus is the coroot torus and its
characters are the full simply connected type-`A₁` character lattice.

This is the first non-adjoint carrier in the explicit Chevalley--Demazure construction requested
by Layer 9 of the ReductiveGroups roadmap.  The same full-weight admissible-lattice step remains
for the higher-rank types whose root and weight lattices differ.  Identifying this carrier with
the standard special-linear group scheme, and assembling a Borel into a pinning, are separate
scheme-theoretic steps.

## Main declarations

* `TauCeti.Sl2Std.rankOneWeight`: the two weights `1` and `-1` of the integral basis.
* `TauCeti.Sl2Std.span_range_rankOneWeight_eq_top`: these weights generate the full character
  lattice `Fin 1 → ℤ`.
* `TauCeti.Sl2Std.rankOneGroupScheme`: the toral Kostant closure for the standard integral
  lattice.
* `TauCeti.Sl2Std.rankOneRootSubgroup` and `TauCeti.Sl2Std.rankOneWeightTorus`: the two root
  subgroups and the closed split torus in that carrier.
* `TauCeti.Sl2Std.rankOneTorusMatrix`: the associated torus representation.
* `TauCeti.Sl2Std.rankOneTorusMatrix_apply`: its matrix equation `diag(s, s⁻¹)`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv

namespace TauCeti.Sl2Std

open TauCeti.UniversalEnvelopingAlgebra

universe u

local notation "e" => ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1]
local notation "h" => ![slFinTwoBasis ℚ 2]
local notation "ρ" => repEnveloping ℚ 1
local notation "M" => Submodule.toAddSubgroup (integralLattice 1)
local notation "b" => integralLatticeAddSubgroupBasis 1
local notation "hnil" => isNilpotent_repEnveloping_root ℚ 1
local notation "hM" => kostantForm_apply_mem_integralLattice 1

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

/-! ## The full rank-one weight lattice -/

/-- The integral weight of the `i`th standard basis vector of the two-dimensional `sl₂` module:
`v₀` has weight `1` and `v₁` has weight `-1`. -/
def rankOneWeight (i : Fin 2) : Fin 1 → ℤ :=
  fun _ => if i = 0 then 1 else -1

@[simp]
theorem rankOneWeight_zero : rankOneWeight 0 = ![1] := by
  funext j
  fin_cases j
  simp [rankOneWeight]

@[simp]
theorem rankOneWeight_one : rankOneWeight 1 = ![-1] := by
  funext j
  fin_cases j
  simp [rankOneWeight]

/-- Each vector of the standard integral basis is a weight vector of its recorded rank-one
weight. -/
theorem isCartanWeightVector_integralLatticeAddSubgroupBasis (i : Fin 2) :
    IsCartanWeightVector h ρ (rankOneWeight i) ((b i : M) : Sl2Std ℚ 1) := by
  rw [isCartanWeightVector_iff]
  intro j
  fin_cases j
  -- After specializing to the unique Cartan generator, expose the enveloping-algebra action
  -- and the integral-basis coercion that the representation lemmas describe.
  change ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (slFinTwoBasis ℚ 2))
      ((b i : M) : Sl2Std ℚ 1) = ((rankOneWeight i 0 : ℤ) : ℚ) • (b i : Sl2Std ℚ 1)
  rw [repEnveloping_ι_slFinTwoBasis, coe_integralLatticeAddSubgroupBasis_apply]
  -- The preceding rewrites identify the action with `diag`; unfold only the remaining
  -- basis-vector coercion so that `diag_basis` applies.
  change diag ℚ 1 (basis ℚ 1 i) = _
  rw [diag_basis]
  fin_cases i <;> norm_num [rankOneWeight]

/-- The two standard weights generate the full character lattice `Fin 1 → ℤ`.  In fact the
highest-weight basis vector already has the primitive weight `1`. -/
theorem span_range_rankOneWeight_eq_top :
    Submodule.span ℤ (Set.range rankOneWeight) = ⊤ := by
  rw [eq_top_iff]
  intro μ _
  have hμ : μ = μ 0 • rankOneWeight 0 := by
    funext j
    fin_cases j
    simp
  rw [hμ]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self (0 : Fin 2)))

/-- The weight of the `i`th root operator: the raising operator has weight `2` and the lowering
operator has weight `-2`.  These are the two roots inside the full weight lattice generated by
`rankOneWeight`. -/
def rankOneRootWeight (i : Fin 2) : Fin 1 → ℤ :=
  fun _ => if i = 0 then 2 else -2

@[simp]
theorem rankOneRootWeight_zero : rankOneRootWeight 0 = ![2] := by
  funext j
  fin_cases j
  simp [rankOneRootWeight]

@[simp]
theorem rankOneRootWeight_one : rankOneRootWeight 1 = ![-2] := by
  funext j
  fin_cases j
  simp [rankOneRootWeight]

/-- A character of a rank-one split torus evaluates to the corresponding integral power of its
unique parameter. -/
@[simp]
theorem torusCharacter_singleton {A : Type*} [CommRing A]
    (s : Fin 1 → Aˣ) (n : ℤ) :
    torusCharacter s ![n] = (s 0) ^ n := by
  rw [torusCharacter_def]
  simp

/-- The two distinguished root vectors have weights `2` and `-2` for the rank-one Cartan
generator. -/
theorem lie_cartan_root_eq_smul (i : Fin 2) (j : Fin 1) :
    ⁅h j, e i⁆ = ((rankOneRootWeight i j : ℤ) : ℚ) • e i := by
  fin_cases j
  fin_cases i
  · simp [rankOneRootWeight]
  · simp [rankOneRootWeight]

/-! ## The explicit carrier and its pinned generators -/

/-- The rank-one Chevalley carrier obtained from the full-weight standard integral `sl₂` lattice:
the closed subgroup scheme of `GL₂` generated by its two root subgroups and its represented split
torus. -/
noncomputable def rankOneGroupScheme :
    Grp (Over (Spec (CommRingCat.of ℤ))) :=
  kostantToralGroupScheme e h ρ M hM hnil b rankOneWeight

private theorem rankOneGroupScheme_eq_def :
    rankOneGroupScheme = kostantToralGroupScheme e h ρ M hM hnil b rankOneWeight :=
  rfl

/-- The rank-one carrier is the toral Kostant group scheme for the standard integral lattice. -/
theorem rankOneGroupScheme_def :
    rankOneGroupScheme = kostantToralGroupScheme e h ρ M hM hnil b rankOneWeight :=
  rankOneGroupScheme_eq_def

/-- The closed immersion of the rank-one carrier into `GL₂`. -/
noncomputable def rankOneGroupSchemeι :
    rankOneGroupScheme ⟶ GeneralLinear.groupScheme ℤ 2 :=
  eqToHom rankOneGroupScheme_def ≫
    kostantToralGroupSchemeι e h ρ M hM hnil b rankOneWeight

private theorem rankOneGroupSchemeι_eq_def :
    rankOneGroupSchemeι =
      eqToHom rankOneGroupScheme_def ≫
        kostantToralGroupSchemeι e h ρ M hM hnil b rankOneWeight :=
  rfl

/-- The inclusion of the rank-one carrier is the generic toral Kostant inclusion, transported
along its defining equality. -/
theorem rankOneGroupSchemeι_def :
    rankOneGroupSchemeι =
      eqToHom rankOneGroupScheme_def ≫
        kostantToralGroupSchemeι e h ρ M hM hnil b rankOneWeight :=
  rankOneGroupSchemeι_eq_def

/-- The inclusion of the rank-one carrier into `GL₂` is a closed immersion. -/
instance isClosedImmersion_rankOneGroupSchemeι :
    IsClosedImmersion rankOneGroupSchemeι.hom.hom.left :=
  isClosedImmersion_kostantToralGroupSchemeι e h ρ M hM hnil b rankOneWeight

/-- The root subgroup indexed by `0` or `1` in the rank-one carrier. -/
noncomputable def rankOneRootSubgroup (i : Fin 2) :
    AdditiveGroup.groupScheme ℤ ⟶ rankOneGroupScheme :=
  kostantRootSubgroupToToral e h ρ M hM hnil b rankOneWeight i ≫
    eqToHom rankOneGroupScheme_def.symm

private theorem rankOneRootSubgroup_eq_def (i : Fin 2) :
    rankOneRootSubgroup i =
      kostantRootSubgroupToToral e h ρ M hM hnil b rankOneWeight i ≫
        eqToHom rankOneGroupScheme_def.symm :=
  rfl

/-- A rank-one root subgroup is the generic toral Kostant root subgroup, transported into the
named carrier. -/
theorem rankOneRootSubgroup_def (i : Fin 2) :
    rankOneRootSubgroup i =
      kostantRootSubgroupToToral e h ρ M hM hnil b rankOneWeight i ≫
        eqToHom rankOneGroupScheme_def.symm :=
  rankOneRootSubgroup_eq_def i

/-- The represented split torus in the rank-one carrier. -/
noncomputable def rankOneWeightTorus :
    SplitTorus.groupScheme ℤ (Fin 1) ⟶ rankOneGroupScheme :=
  kostantWeightTorusToToral e h ρ M hM hnil b rankOneWeight ≫
    eqToHom rankOneGroupScheme_def.symm

private theorem rankOneWeightTorus_eq_def :
    rankOneWeightTorus =
      kostantWeightTorusToToral e h ρ M hM hnil b rankOneWeight ≫
        eqToHom rankOneGroupScheme_def.symm :=
  rfl

/-- The rank-one weight torus is the generic toral Kostant weight torus, transported into the
named carrier. -/
theorem rankOneWeightTorus_def :
    rankOneWeightTorus =
      kostantWeightTorusToToral e h ρ M hM hnil b rankOneWeight ≫
        eqToHom rankOneGroupScheme_def.symm :=
  rankOneWeightTorus_eq_def

/-- Including a root subgroup into `GL₂` recovers its represented Kostant root subgroup. -/
@[simp]
theorem rankOneRootSubgroup_comp_ι (i : Fin 2) :
    rankOneRootSubgroup i ≫ rankOneGroupSchemeι =
      kostantRootSubgroup e h ρ M hM i (hnil i) b :=
  kostantRootSubgroupToToral_comp_ι e h ρ M hM hnil b rankOneWeight i

/-- Including the rank-one weight torus into `GL₂` recovers its diagonal weight
representation. -/
@[simp]
theorem rankOneWeightTorus_comp_ι :
    rankOneWeightTorus ≫ rankOneGroupSchemeι =
      GeneralLinear.weightTorus (R := ℤ) rankOneWeight :=
  kostantWeightTorusToToral_comp_ι e h ρ M hM hnil b rankOneWeight

/-- The rank-one weight torus is a closed immersion into the carrier because its two weights
generate the full character lattice. -/
instance isClosedImmersion_rankOneWeightTorus :
    IsClosedImmersion rankOneWeightTorus.hom.hom.left :=
  isClosedImmersion_kostantWeightTorusToToral e h ρ M hM hnil b rankOneWeight
    span_range_rankOneWeight_eq_top

/-- The rank-one split torus as a closed subgroup scheme of the carrier. -/
noncomputable def rankOneWeightTorusInGroupScheme :
    ClosedSubgroupScheme rankOneGroupScheme :=
  ClosedSubgroupScheme.mk rankOneWeightTorus

/-- The subobject underlying the closed rank-one weight torus is represented by its inclusion. -/
@[simp]
theorem coe_rankOneWeightTorusInGroupScheme :
    (rankOneWeightTorusInGroupScheme).1 = Subobject.mk rankOneWeightTorus := by
  rw [rankOneWeightTorusInGroupScheme]
  exact ClosedSubgroupScheme.coe_mk _

/-- Each root subgroup is a closed immersion into the rank-one carrier. -/
instance isClosedImmersion_rankOneRootSubgroup (i : Fin 2) :
    IsClosedImmersion (rankOneRootSubgroup i).hom.hom.left := by
  have hcomp : IsClosedImmersion
      ((rankOneRootSubgroup i ≫ rankOneGroupSchemeι).hom.hom.left) := by
    rw [rankOneRootSubgroup_comp_ι]
    exact isClosedImmersion_kostantRootSubgroup_one i
  exact @IsClosedImmersion.of_comp _ _ _
    (rankOneRootSubgroup i).hom.hom.left rankOneGroupSchemeι.hom.hom.left hcomp inferInstance

/-! ## Matrix equations -/

/-- The represented split torus on `A`-points, written in the integral basis. -/
noncomputable def rankOneTorusMatrix {A : Type*} [CommRing A] :
    ((Fin 1 → Aˣ) →* Matrix.GeneralLinearGroup (Fin 2) A) :=
  kostantTorusMatrix M b rankOneWeight

/-- A rank-one torus point is the diagonal matrix `diag(s, s⁻¹)`. -/
@[simp]
theorem rankOneTorusMatrix_apply {A : Type*} [CommRing A] (s : Fin 1 → Aˣ) :
    rankOneTorusMatrix s = diagGL ![s 0, (s 0)⁻¹] := by
  rw [rankOneTorusMatrix, kostantTorusMatrix_apply]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneWeight, torusCharacter_def]

/-- The represented rank-one weight torus on points of a value algebra. -/
noncomputable def rankOneTorusPoints (A : CommAlgCat.{u} ℤ) :
    (Fin 1 → Aˣ) →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M) :=
  kostantTorusPoints M b rankOneWeight A

/-- The parametrized root subgroup for one of the two rank-one root generators. -/
noncomputable def rankOneRootSubgroupParam (i : Fin 2) (A : CommAlgCat.{u} ℤ) :
    Multiplicative A →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M) :=
  kostantRootSubgroupParam e h ρ M hM i (hnil i) A

/-- A rank-one torus point scales each base-changed basis vector by its recorded weight
character. -/
@[simp]
theorem rankOneTorusPoints_apply_baseChange_basis
    {A : Type u} [CommRing A] (s : Fin 1 → Aˣ) (i : Fin 2) :
    (rankOneTorusPoints (CommAlgCat.of ℤ A) s).val (1 ⊗ₜ[ℤ] b i) =
      (torusCharacter s (rankOneWeight i) : A) • (b).baseChange A i := by
  rw [Module.Basis.baseChange_apply, rankOneTorusPoints, kostantTorusPoints_tmul_basis]
  simp [smul_tmul']

/-- A parametrized rank-one root element adds `t` times the `i`th basis vector to the opposite
basis vector and fixes the other basis vector. -/
@[simp]
theorem rankOneRootSubgroupParam_apply_baseChange_basis
    {A : Type u} [CommRing A] (i s : Fin 2) (t : Multiplicative A) :
    (rankOneRootSubgroupParam i (CommAlgCat.of ℤ A) t).val (1 ⊗ₜ[ℤ] b s) =
      (b).baseChange A s +
        if s = i.rev then Multiplicative.toAdd t • (b).baseChange A i else 0 := by
  rw [rankOneRootSubgroupParam, kostantRootSubgroupParam_apply]
  simpa using kostantRootSubgroupPoints_apply_baseChange_basis_one i s
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t)

/-- **The rank-one pinning equation on points.** Conjugation by the full-weight torus sends the
root element `xᵢ(t)` to `xᵢ(αᵢ(s)t)`, where `α₀ = 2` and `α₁ = -2`. -/
theorem rankOneTorusPoints_conj_rootSubgroupParam
    (A : CommAlgCat.{u} ℤ) (s : Fin 1 → Aˣ) (i : Fin 2) (t : Multiplicative A) :
    rankOneTorusPoints A s * rankOneRootSubgroupParam i A t *
        (rankOneTorusPoints A s)⁻¹ =
      rankOneRootSubgroupParam i A
        (Multiplicative.ofAdd
          ((torusCharacter s (rankOneRootWeight i) : A) * Multiplicative.toAdd t)) :=
  by
    simpa only [rankOneTorusPoints, rankOneRootSubgroupParam] using
      kostantTorusPoints_conj_kostantRootSubgroupParam e h ρ M hM b rankOneWeight
        isCartanWeightVector_integralLatticeAddSubgroupBasis (lie_cartan_root_eq_smul i) (hnil i)
          A s t

end TauCeti.Sl2Std
