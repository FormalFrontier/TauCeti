/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Analysis.Semigroups.Group.Generator
-- Non-public: differentiation of the inner product turns preservation by the group into
-- skew-symmetry of the generator.
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Semigroups.Dissipative.Basic

/-!
# Unitary strongly continuous groups

A strongly continuous group on a complex Hilbert space is represented by real continuous linear
maps, in accordance with the real-Banach-first convention of the semigroup development. Such a
group is **unitary** when every operator preserves the complex inner product. Inner-product
preservation forces the real-linear operators to be complex-linear, and the same is true of the
infinitesimal generator on its natural domain.

This file packages that complex generator without replacing the real generator. Its domain has the
same carrier as `TauCeti.Semigroups.StronglyContinuousGroup.domain`, now regarded as a complex
submodule, and its values are exactly those of the existing generator. Differentiating preservation
of the inner product gives the infinitesimal unitary identity

`⟪A x, y⟫ = -⟪x, A y⟫`.

The resolvent-range theorems for the forward and reversed contraction semigroups then identify
the adjoint domain and upgrade this identity to `A† = -A`: the generator is skew-adjoint. This
completes the generator direction of Stone's theorem. Constructing the converse unitary group
from a self-adjoint operator is not claimed here.

## Main declarations

* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary`: every group operator preserves the
  complex inner product.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.map_smul`: a unitary group represented
  real-linearly is automatically complex-linear.
* `TauCeti.Semigroups.StronglyContinuousGroup.complexDomain`: the generator domain as a complex
  submodule.
* `TauCeti.Semigroups.StronglyContinuousGroup.complexGenerator`: the generator as a complex
  `LinearPMap`.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.complexGenerator_isFormalAdjoint_neg`:
  the generator is skew-symmetric.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.complexGenerator_adjoint_eq_neg`:
  the generator is skew-adjoint.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Theorem VIII.8.
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section II.3.11.
* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part A (C₀-groups and Stone's
  theorem stretch target).
-/

public section

noncomputable section

open Filter
open scoped InnerProductSpace Topology

namespace TauCeti.Semigroups

namespace StronglyContinuousGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A strongly continuous group on a complex Hilbert space is unitary when every operator
preserves the complex inner product. Although the underlying group is represented by real-linear
operators, this condition forces complex linearity; see `IsUnitary.map_smul`. -/
def IsUnitary (U : StronglyContinuousGroup H) : Prop :=
  ∀ t x y, ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ

namespace IsUnitary

variable {U : StronglyContinuousGroup H}

/-- Construct a unitary group from inner-product preservation by each of its operators. -/
theorem intro (hU : ∀ t x y, ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ) : U.IsUnitary :=
  hU

/-- Every operator of a unitary strongly continuous group preserves the complex inner product. -/
@[simp]
theorem inner_map_map (hU : U.IsUnitary) (t : ℝ) (x y : H) :
    ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ :=
  hU t x y

/-- Every operator of a unitary strongly continuous group preserves norms. -/
@[simp]
theorem norm_map (hU : U.IsUnitary) (t : ℝ) (x : H) : ‖U t x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg (U t x)) (norm_nonneg x)).mp
  have h := hU.inner_map_map t x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- Every operator of a unitary strongly continuous group is an isometry. -/
theorem isometry (hU : U.IsUnitary) (t : ℝ) : Isometry (U t) :=
  AddMonoidHomClass.isometry_of_norm _ (hU.norm_map t)

/-- Every operator of a unitary strongly continuous group has operator norm at most one. -/
theorem opNorm_le_one (hU : U.IsUnitary) (t : ℝ) : ‖U t‖ ≤ 1 :=
  (U t).opNorm_le_bound zero_le_one fun x => by
    rw [hU.norm_map]
    exact (le_refl ‖x‖).trans_eq (one_mul ‖x‖).symm

/-- A unitary strongly continuous group has the sharp two-sided growth bound `(0, 1)`. -/
theorem hasGrowthBound_zero_one (hU : U.IsUnitary) : U.HasGrowthBound 0 1 :=
  U.hasGrowthBound_zero_one_iff.mpr fun t => hU.opNorm_le_one t

/-- The time reversal of a unitary strongly continuous group is unitary. -/
theorem reflect (hU : U.IsUnitary) : U.reflect.IsUnitary := by
  intro t x y
  simpa only [StronglyContinuousGroup.reflect_apply] using hU.inner_map_map (-t) x y

/-- Inner-product preservation forces every operator of a unitary strongly continuous group to be
complex-linear, even though `StronglyContinuousGroup` represents it as a real-linear map. -/
@[simp]
theorem map_smul (hU : U.IsUnitary) (t : ℝ) (z : ℂ) (x : H) :
    U t (z • x) = z • U t x := by
  apply ext_inner_right ℂ
  intro y
  calc
    ⟪U t (z • x), y⟫_ℂ = ⟪U t (z • x), U t (U (-t) y)⟫_ℂ := by
      rw [U.map_apply_map_neg_apply]
    _ = ⟪z • x, U (-t) y⟫_ℂ := hU.inner_map_map t _ _
    _ = (starRingEnd ℂ) z * ⟪x, U (-t) y⟫_ℂ := inner_smul_left _ _ _
    _ = (starRingEnd ℂ) z * ⟪U t x, U t (U (-t) y)⟫_ℂ := by
      rw [hU.inner_map_map]
    _ = ⟪z • U t x, y⟫_ℂ := by
      rw [U.map_apply_map_neg_apply, inner_smul_left]

/-- Multiplying a generator-domain vector by a complex scalar keeps it in the generator domain,
and its difference quotient converges to the correspondingly scaled generator value. -/
private theorem tendsto_genQuot_smul (hU : U.IsUnitary) (x : U.domain) (z : ℂ) :
    Tendsto (fun t : ℝ => (1 / t) • (U t (z • (x : H)) - z • (x : H)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (z • U.generator ⟨(x : H), by rw [U.generator_domain]; exact x.property⟩)) := by
  refine (U.generator_tendsto x).const_smul z |>.congr' ?_
  filter_upwards with t
  rw [hU.map_smul]
  module

/-- The real generator domain of a unitary strongly continuous group is closed under complex
scalar multiplication. -/
theorem smul_mem_domain (hU : U.IsUnitary) (x : U.domain) (z : ℂ) :
    z • (x : H) ∈ U.domain :=
  (U.mem_domain_iff_tendsto _).mpr
    ⟨z • U.generator ⟨(x : H), by rw [U.generator_domain]; exact x.property⟩,
      hU.tendsto_genQuot_smul x z⟩

/-- The real generator of a unitary strongly continuous group commutes with complex scalar
multiplication on its domain. -/
theorem generator_smul (hU : U.IsUnitary) (x : U.domain) (z : ℂ) :
    U.generator
        ⟨z • (x : H), by rw [U.generator_domain]; exact hU.smul_mem_domain x z⟩ =
      z • U.generator ⟨(x : H), by rw [U.generator_domain]; exact x.property⟩ :=
  U.generator_eq_of_tendsto (hU.smul_mem_domain x z) (hU.tendsto_genQuot_smul x z)

end IsUnitary

/-- The generator domain of a unitary strongly continuous group, regarded as a complex submodule.
Its carrier is definitionally the real generator domain. -/
def complexDomain (U : StronglyContinuousGroup H) (hU : U.IsUnitary) : Submodule ℂ H where
  carrier := U.domain
  zero_mem' := U.domain.zero_mem
  add_mem' hx hy := U.domain.add_mem hx hy
  smul_mem' z _ hx := hU.smul_mem_domain ⟨_, hx⟩ z

@[simp]
theorem mem_complexDomain_iff (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (x : H) :
    x ∈ U.complexDomain hU ↔ x ∈ U.domain :=
  Iff.rfl

/-- The complex generator domain has the real generator domain as its underlying set. -/
@[simp]
theorem coe_complexDomain (U : StronglyContinuousGroup H) (hU : U.IsUnitary) :
    (U.complexDomain hU : Set H) = (U.domain : Set H) := (rfl)

/-- The generator domain of a unitary strongly continuous group is dense, also when regarded as a
complex submodule. -/
theorem dense_complexDomain [CompleteSpace H] (U : StronglyContinuousGroup H) (hU : U.IsUnitary) :
    Dense (U.complexDomain hU : Set H) := by
  rw [U.coe_complexDomain hU, U.domain_def]
  exact U.toSemigroup.dense_domain

/-- The infinitesimal generator of a unitary strongly continuous group as a complex-linear
partially defined map. It has the same domain and values as the existing real generator. -/
def complexGenerator (U : StronglyContinuousGroup H) (hU : U.IsUnitary) : H →ₗ.[ℂ] H where
  domain := U.complexDomain hU
  toFun :=
    { toFun := fun x =>
        U.generator ⟨(x : H), by rw [U.generator_domain]; exact x.property⟩
      map_add' := fun x y => by
        convert U.generator.map_add
          ⟨(x : H), by rw [U.generator_domain]; exact x.property⟩
          ⟨(y : H), by rw [U.generator_domain]; exact y.property⟩ using 1
        congr 1
      map_smul' := fun z x => by
        simpa only [Submodule.coe_smul_of_tower, RingHom.id_apply] using
          hU.generator_smul ⟨(x : H), x.property⟩ z }

@[simp]
theorem complexGenerator_domain (U : StronglyContinuousGroup H) (hU : U.IsUnitary) :
    (U.complexGenerator hU).domain = U.complexDomain hU := (rfl)

@[simp]
theorem complexGenerator_apply (U : StronglyContinuousGroup H) (hU : U.IsUnitary)
    (x : (U.complexGenerator hU).domain) :
    U.complexGenerator hU x =
      U.generator ⟨(x : H), by
        rw [U.generator_domain, ← U.mem_complexDomain_iff hU, ← U.complexGenerator_domain hU]
        exact x.property⟩ :=
  (rfl)

/-- Membership in the complex generator domain implies membership in the original real generator
domain; the two domains have the same carrier. -/
private theorem complexGenerator_mem_domain (U : StronglyContinuousGroup H) (hU : U.IsUnitary)
    (x : (U.complexGenerator hU).domain) : (x : H) ∈ U.domain := by
  apply (U.mem_complexDomain_iff hU x).mp
  rw [← U.complexGenerator_domain hU]
  exact x.property

namespace IsUnitary

variable {U : StronglyContinuousGroup H}

/-- **The infinitesimal generator of a unitary strongly continuous group is skew-symmetric.**
For vectors `x` and `y` in its natural complex domain,
`inner (A x) y = -inner x (A y)`. -/
theorem inner_complexGenerator_eq_neg (hU : U.IsUnitary)
    (x y : (U.complexGenerator hU).domain) :
    ⟪U.complexGenerator hU x, (y : H)⟫_ℂ =
      -⟪(x : H), U.complexGenerator hU y⟫_ℂ := by
  let xr : U.domain := ⟨x, U.complexGenerator_mem_domain hU x⟩
  let yr : U.domain := ⟨y, U.complexGenerator_mem_domain hU y⟩
  let xs : U.toSemigroup.domain := ⟨x, by rw [← U.domain_def]; exact xr.property⟩
  let ys : U.toSemigroup.domain := ⟨y, by rw [← U.domain_def]; exact yr.property⟩
  have generator_eq_toSemigroup (z : U.domain) :
      U.generator ⟨(z : H), by rw [U.generator_domain]; exact z.property⟩ =
        U.toSemigroup.generator ⟨(z : H), by
          rw [U.toSemigroup.generator_domain, ← U.domain_def]
          exact z.property⟩ := by
    simpa only using
      ((LinearPMap.ext_iff.mp U.generator_def).2 (x := (z : H))
        (hf := by rw [U.generator_domain]; exact z.property)
        (hg := by
          rw [U.toSemigroup.generator_domain, ← U.domain_def]
          exact z.property))
  have hgenx := generator_eq_toSemigroup xr
  have hgeny := generator_eq_toSemigroup yr
  have hderiv :=
    ((U.toSemigroup.realOperator_hasDerivWithinAt_zero xs).congr_of_mem
      (fun t ht => by rw [U.toSemigroup_realOperator_of_nonneg ht]) Set.self_mem_Ici).inner ℂ
    ((U.toSemigroup.realOperator_hasDerivWithinAt_zero ys).congr_of_mem
      (fun t ht => by rw [U.toSemigroup_realOperator_of_nonneg ht]) Set.self_mem_Ici)
  have hfun : (fun t : ℝ => ⟪U t (xr : H), U t (yr : H)⟫_ℂ) =
      fun _ : ℝ => ⟪(x : H), (y : H)⟫_ℂ := by
    funext t
    exact hU.inner_map_map t xr yr
  rw [hfun] at hderiv
  have hzero :
      ⟪(x : H), U.complexGenerator hU y⟫_ℂ +
        ⟪U.complexGenerator hU x, (y : H)⟫_ℂ = 0 := by
    simpa only [U.map_zero_apply, complexGenerator_apply, xr, yr, xs, ys, hgenx, hgeny] using
      UniqueDiffWithinAt.eq_deriv (Set.Ici (0 : ℝ)) (uniqueDiffWithinAt_Ici 0) hderiv
        (hasDerivWithinAt_const (0 : ℝ) _ ⟪(x : H), (y : H)⟫_ℂ)
  exact eq_neg_of_add_eq_zero_right hzero

/-- The complex generator of a unitary strongly continuous group is a formal adjoint of its
negative, Mathlib's unbounded-operator formulation of skew-symmetry. -/
theorem complexGenerator_isFormalAdjoint_neg (hU : U.IsUnitary) :
    (U.complexGenerator hU).IsFormalAdjoint (-U.complexGenerator hU) := by
  intro x y
  rw [LinearPMap.neg_apply, inner_neg_right]
  exact hU.inner_complexGenerator_eq_neg x y

variable [CompleteSpace H]

/-- The range of `1 - A` is the whole Hilbert space. This is the forward semigroup's resolvent
range, transported from the real generator to the complex generator. -/
private theorem one_sub_complexGenerator_surjective (hU : U.IsUnitary) :
    Function.Surjective fun x : (U.complexGenerator hU).domain =>
      (x : H) - U.complexGenerator hU x := by
  have hr := U.toSemigroup.smul_sub_generator_surjective
    hU.hasGrowthBound_zero_one.toSemigroup (by norm_num : (0 : ℝ) < 1)
  rw [← U.generator_def] at hr
  intro y
  obtain ⟨x, hx⟩ := hr y
  have hxU : (x : H) ∈ U.domain := by
    rw [← U.generator_domain]
    exact x.property
  let xc : (U.complexGenerator hU).domain :=
    ⟨x, by rw [U.complexGenerator_domain]; exact hxU⟩
  refine ⟨xc, ?_⟩
  simpa only [xc, one_smul, U.complexGenerator_apply hU] using hx

/-- The range of `1 + A` is the whole Hilbert space. This is the reversed semigroup's resolvent
range, transported from the real generator to the complex generator. -/
private theorem one_add_complexGenerator_surjective (hU : U.IsUnitary) :
    Function.Surjective fun x : (U.complexGenerator hU).domain =>
      (x : H) + U.complexGenerator hU x := by
  have hr := U.reflect.toSemigroup.smul_sub_generator_surjective
    hU.reflect.hasGrowthBound_zero_one.toSemigroup (by norm_num : (0 : ℝ) < 1)
  rw [← U.reflect.generator_def, U.reflect_generator] at hr
  intro y
  obtain ⟨x, hx⟩ := hr y
  have hxU : (x : H) ∈ U.domain := by
    rw [← U.generator_domain]
    exact x.property
  let xc : (U.complexGenerator hU).domain :=
    ⟨x, by rw [U.complexGenerator_domain]; exact hxU⟩
  refine ⟨xc, ?_⟩
  have hgen : U.complexGenerator hU xc = U.generator x := by
    rw [U.complexGenerator_apply]
    congr 1
  simp only
  rw [hgen]
  simpa only [one_smul, LinearPMap.neg_apply, sub_neg_eq_add] using hx

/-- **The infinitesimal generator of a unitary strongly continuous group is skew-adjoint.**
Its Hilbert-space adjoint is its negative. The reverse inclusion of adjoint domains uses the
surjectivity of both `1 - A` and `1 + A`, supplied by the resolvents of the forward and reversed
contraction semigroups. -/
@[simp]
theorem complexGenerator_adjoint_eq_neg (hU : U.IsUnitary) :
    (U.complexGenerator hU).adjoint = -U.complexGenerator hU := by
  have hdense : Dense ((U.complexGenerator hU).domain : Set H) := by
    rw [U.complexGenerator_domain]
    exact U.dense_complexDomain hU
  have hformal := hU.complexGenerator_isFormalAdjoint_neg
  have hle : -U.complexGenerator hU ≤ (U.complexGenerator hU).adjoint :=
    hformal.le_adjoint hdense
  have hdom_le : (U.complexGenerator hU).adjoint.domain ≤
      (-U.complexGenerator hU).domain := by
    intro y hy
    let ya : (U.complexGenerator hU).adjoint.domain := ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hU.one_add_complexGenerator_surjective
      ((y : H) - (U.complexGenerator hU).adjoint ya)
    have hyx : (y : H) = (x : H) := by
      apply ext_inner_left ℂ
      intro w
      obtain ⟨v, hv⟩ := hU.one_sub_complexGenerator_surjective w
      rw [← hv]
      calc
        ⟪(v : H) - U.complexGenerator hU v, (y : H)⟫_ℂ =
            ⟪(v : H), (y : H)⟫_ℂ - ⟪U.complexGenerator hU v, (y : H)⟫_ℂ :=
          inner_sub_left _ _ _
        _ = ⟪(v : H), (y : H)⟫_ℂ -
            ⟪(v : H), (U.complexGenerator hU).adjoint ya⟫_ℂ := by
          rw [(LinearPMap.adjoint_isFormalAdjoint hdense).symm v ya]
        _ = ⟪(v : H), (y : H) - (U.complexGenerator hU).adjoint ya⟫_ℂ := by
          rw [inner_sub_right]
        _ = ⟪(v : H), (x : H) + U.complexGenerator hU x⟫_ℂ := by
          exact congrArg (fun z : H => ⟪(v : H), z⟫_ℂ) hx.symm
        _ = ⟪(v : H), (x : H)⟫_ℂ + ⟪(v : H), U.complexGenerator hU x⟫_ℂ :=
          inner_add_right _ _ _
        _ = ⟪(v : H), (x : H)⟫_ℂ - ⟪U.complexGenerator hU v, (x : H)⟫_ℂ := by
          rw [hU.inner_complexGenerator_eq_neg]
          simp
        _ = ⟪(v : H) - U.complexGenerator hU v, (x : H)⟫_ℂ := by
          rw [inner_sub_left]
    rw [LinearPMap.neg_domain]
    simpa only [hyx] using x.property
  apply LinearPMap.ext (le_antisymm hdom_le hle.1)
  intro y hy hy'
  exact (hle.2 (x := ⟨y, hy'⟩) (y := ⟨y, hy⟩) rfl).symm

end IsUnitary

end StronglyContinuousGroup

end TauCeti.Semigroups

end
