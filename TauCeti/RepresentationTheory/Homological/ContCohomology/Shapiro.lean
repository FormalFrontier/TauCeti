/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality

import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import TauCeti.Topology.CompactOpen

/-!
# Shapiro's lemma in degrees zero, one and two

For a profinite group `G`, a **closed** subgroup `U` and a discrete `U`-module `A`, the coinduced
module `Coind_U^G A` of `TauCeti.DiscreteCoind` computes the cohomology of `U`:

```text
H⁰(G, Coind_U^G A) ≅ H⁰(U, A),   H¹(G, Coind_U^G A) ≅ H¹(U, A),
H²(G, Coind_U^G A) ≅ H²(U, A).
```

All three isomorphisms are *evaluation at `1`* composed with restriction to `U`, so in degrees one
and two the forward map is the compatible-pair pullback `TauCeti.ContCohomology.explicitMap1`,
respectively `TauCeti.ContCohomology.explicitMap2`, along the pair consisting of the inclusion
`U ↪ G` and the counit `TauCeti.DiscreteCoind.eval`; nothing about it depends on a choice. The
choice enters only in proving that this map is bijective, and what it uses is Layer 0's continuous
section of `G → G ⧸ U`
(`TauCeti.exists_continuous_rightCosetFactorization`, Ribes-Zalesskii Prop. 2.2.2): writing
`g = w g * r g` with `w : G → U` continuous and `w (u * g) = u * w g`, a continuous `1`-cocycle
`c` of `U` is spread over `G` as

```text
(a g) x = c (w (x * g)) - c (w x),
```

which is `TauCeti.ContCohomology.coindCochain1`. This is a continuous `1`-cocycle of `G` with
values in `Coind_U^G A` whose Shapiro image is `c` up to the explicit coboundary `d⁰ (c (w 1))`
(`TauCeti.ContCohomology.shapiroCocycles1_coindCocycle1`), and conversely every continuous
`1`-cocycle `f` of `G` differs from the cochain rebuilt from its Shapiro image by an explicit
coboundary (`TauCeti.ContCohomology.sub_coindCochain1_mem_B1`). Those two identities make the
forward map bijective, and because the isomorphism is pinned by its forward direction the section
formula for the inverse (`TauCeti.ContCohomology.explicitShapiro1_symm_apply`) holds for *every*
such factorization, so there is no separate independence statement to prove.

## Main definitions

* `TauCeti.ContCohomology.constCoind` and `TauCeti.ContCohomology.explicitShapiro0`: the constant
  coinduced element at a `U`-invariant coefficient, and `H⁰(G, Coind_U^G A) ≃+ H⁰(U, A)`.
* `TauCeti.ContCohomology.shapiroCocycles1` and `TauCeti.ContCohomology.explicitShapiroMap1`: the
  forward Shapiro map on continuous `1`-cocycles and on `H¹`.
* `TauCeti.ContCohomology.shapiroLift`, `TauCeti.ContCohomology.coindCochain1` and
  `TauCeti.ContCohomology.coindCocycle1`: the inverse cochain built from a continuous right-coset
  factorization.
* `TauCeti.ContCohomology.explicitShapiro1`: `H¹(G, Coind_U^G A) ≃+ H¹(U, A)`.
* `TauCeti.ContCohomology.shapiroCocycles2` and `TauCeti.ContCohomology.explicitShapiroMap2`: the
  forward Shapiro map on continuous `2`-cocycles and on `H²`.
* `TauCeti.ContCohomology.coindCochain2` and `TauCeti.ContCohomology.coindCocycle2`: the inverse
  cochain in degree two, built from a continuous right-coset factorization.
* `TauCeti.ContCohomology.explicitShapiro2`: `H²(G, Coind_U^G A) ≃+ H²(U, A)`.

## Implementation notes

Degree zero needs no topological hypothesis beyond a continuous multiplication on `G`: a
`G`-invariant element of the coinduced module is constant, and the constant it takes is
`U`-invariant. Degrees one and two are where profiniteness and closedness of `U` are used, through
the continuous factorization; for an *open* `U` the finite transversal `Quotient.out` would already
suffice, but openness is not assumed anywhere here.

Degree two is organised through the **homogeneous form** `hom2 f a b c = a • f (a⁻¹ b, b⁻¹ c)` of
an inhomogeneous `2`-cochain, which is a private helper of this file. In that form the `2`-cocycle
identity becomes the simplicial relation
`hom2 f a c d + hom2 f a b c = hom2 f b c d + hom2 f a b d`, which is stable under precomposing all
three arguments with an arbitrary map. So a continuous `2`-cocycle `c` of `U` spreads over `G` as
`(g, h) ↦ (x ↦ hom2 c (w x) (w (x * g)) (w (x * g * h)))`, and the two `2`-cocycles compared by
Shapiro's lemma differ by the *prism homotopy* `β x y = Φ (w x) x y - Φ (w x) (w y) y` attached to
the pair of maps `id` and `w`, whose coboundary is `Φ - Φ ∘ (w × w × w)`.

This is the "Shapiro's lemma" milestone of Layer 7 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`, whose `Suggested.lean` fixes the names
`explicitShapiro0`, `explicitShapiro1` and `explicitShapiro2`, and whose §5 fixes the direction of
the isomorphism — that of Mathlib's discrete `groupCohomology.coindIso` — and the forward map.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.4). Note the
  terminology trap flagged in the footnote on p. 61: NSW writes `Ind` for what is here the
  *coinduced* functor.
* L. Ribes, P. Zalesskii, *Profinite Groups*, Thm. 6.10.5, which uses `Coind` by that name.
-/

public section

namespace TauCeti.ContCohomology

universe u v

section DegreeZero

variable {G : Type u} [Group G] [TopologicalSpace G] {U : Subgroup G}
  {A : Type v} [AddCommGroup A] [DistribMulAction U A]

variable (G) in
/-- The constant function at a `U`-invariant coefficient, as an element of `Coind_U^G A`. It is
the inverse of the degree-zero Shapiro map. -/
def constCoind (a : H0 U A) : DiscreteCoind G U A :=
  DiscreteCoind.mk G U A (fun _ => (a : A)) (IsLocallyConstant.const _)
    (fun u _ => ((FixedPoints.mem_addSubgroup U A (a : A)).1 a.2 u).symm)

@[simp]
theorem constCoind_apply (a : H0 U A) (g : G) : constCoind G a g = (a : A) := (rfl)

variable [ContinuousMul G]

/-- A `G`-invariant element of `Coind_U^G A` is a constant function: right translation moves `1`
to every point of `G`. -/
theorem apply_eq_apply_one_of_mem_H0 (f : H0 G (DiscreteCoind G U A)) (g : G) :
    (f : DiscreteCoind G U A) g = (f : DiscreteCoind G U A) 1 := by
  have h := (FixedPoints.mem_addSubgroup G (DiscreteCoind G U A)
    (f : DiscreteCoind G U A)).1 f.2 g
  calc (f : DiscreteCoind G U A) g
      = (g • (f : DiscreteCoind G U A)) 1 := by rw [DiscreteCoind.coe_smul, one_mul]
    _ = (f : DiscreteCoind G U A) 1 := by rw [h]

/-- The constant coinduced element is `G`-invariant. -/
theorem constCoind_mem_H0 (a : H0 U A) : constCoind G a ∈ H0 G (DiscreteCoind G U A) :=
  (FixedPoints.mem_addSubgroup G (DiscreteCoind G U A) (constCoind G a)).2 fun _ =>
    DiscreteCoind.ext fun _ => by simp

variable (G U A) in
/-- **Shapiro's lemma in degree zero**, `H⁰(G, Coind_U^G A) ≅ H⁰(U, A)`, by evaluation at `1`.

A `G`-invariant element of the coinduced module is constant and the constant it takes is
`U`-invariant; conversely a `U`-invariant `a : A` is `TauCeti.ContCohomology.constCoind`. Only
continuity of the multiplication on `G` is used: neither compactness of `G` nor closedness of `U`
enters in this degree. -/
def explicitShapiro0 : H0 G (DiscreteCoind G U A) ≃+ H0 U A where
  toFun f := ⟨(f : DiscreteCoind G U A) 1, (FixedPoints.mem_addSubgroup U A _).2 fun u => by
    rw [← DiscreteCoind.apply_coe, apply_eq_apply_one_of_mem_H0 f]⟩
  invFun a := ⟨constCoind G a, constCoind_mem_H0 a⟩
  left_inv f := Subtype.ext (DiscreteCoind.ext fun g => by
    rw [constCoind_apply, apply_eq_apply_one_of_mem_H0 f])
  right_inv a := Subtype.ext (constCoind_apply a 1)
  map_add' _ _ := (rfl)

@[simp]
theorem explicitShapiro0_apply (f : H0 G (DiscreteCoind G U A)) :
    (explicitShapiro0 G U A f : A) = (f : DiscreteCoind G U A) 1 := (rfl)

@[simp]
theorem explicitShapiro0_symm_apply (a : H0 U A) :
    ((explicitShapiro0 G U A).symm a : DiscreteCoind G U A) = constCoind G a := (rfl)

end DegreeZero

section Lift

variable {G : Type u} [Group G] {U : Subgroup G} {A : Type v} (w : G → U) (c : U → A)

/-- The `0`-cochain `y ↦ c (w y)` transporting a `1`-cocycle `c` of `U` along a factorization `w`
of `G` over the right cosets of `U`. Its failure of `U`-equivariance is `c` itself
(`TauCeti.ContCohomology.shapiroLift_mul`), which is why its right-translation differences carry a
nonzero class. -/
def shapiroLift : G → A := fun y => c (w y)

@[simp]
theorem shapiroLift_apply (y : G) : shapiroLift w c y = c (w y) := (rfl)

theorem continuous_shapiroLift [TopologicalSpace G] [TopologicalSpace A] (hw : Continuous w)
    (hc : Continuous c) : Continuous (shapiroLift w c) := hc.comp hw

/-- The failure of `U`-equivariance of the lift of a `1`-cocycle is the cocycle itself. -/
theorem shapiroLift_mul [AddCommGroup A] [DistribMulAction U A]
    (hwmul : ∀ (u : U) (g : G), w ((u : G) * g) = u * w g)
    (hc : groupCohomology.IsCocycle₁ c) (u : U) (y : G) :
    shapiroLift w c ((u : G) * y) = u • shapiroLift w c y + c u := by
  simp only [shapiroLift_apply, hwmul u y, hc u (w y)]

end Lift

section DegreeOne

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G) (A : Type v) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A] [ContinuousSMul U A]

omit [CompactSpace G] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul U A] in
/-- Evaluation at `1` is a compatible coefficient map for the inclusion `U ↪ G`: this is the
hypothesis of `TauCeti.ContCohomology.explicitMap1` that the Shapiro map is the instance of. It is
a named theorem rather than an inline use of `TauCeti.DiscreteCoind.eval_smul` because the
inclusion has to be spelled as `ContinuousMonoidHom.subgroupSubtype`. Degree two uses it too, for
`TauCeti.ContCohomology.explicitMap2`. -/
theorem eval_subgroupSubtype_smul (u : U) (f : DiscreteCoind G U A) :
    DiscreteCoind.eval G U A (ContinuousMonoidHom.subgroupSubtype U u • f) =
      u • DiscreteCoind.eval G U A f :=
  DiscreteCoind.eval_smul u f

/-- **The forward Shapiro map on continuous `1`-cocycles**: restrict a continuous `1`-cocycle of
`G` with coefficients in `Coind_U^G A` to `U`, and evaluate its values at `1`. -/
noncomputable abbrev shapiroCocycles1 : Z1 G (DiscreteCoind G U A) →+ Z1 U A :=
  cocyclesMap1 G (DiscreteCoind G U A) U A (ContinuousMonoidHom.subgroupSubtype U)
    (DiscreteCoind.eval G U A) DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)

omit [CompactSpace G] [ContinuousSMul U A] in
@[simp]
theorem shapiroCocycles1_apply (f : Z1 G (DiscreteCoind G U A)) (u : U) :
    (shapiroCocycles1 G U A f : U → A) u = (f : G → DiscreteCoind G U A) (u : G) 1 := by
  simp [cocyclesMap1_apply]

/-- **The forward Shapiro map on `H¹`**, the compatible-pair pullback along the inclusion `U ↪ G`
and evaluation at `1`. `TauCeti.ContCohomology.explicitShapiro1` upgrades it to an isomorphism. -/
noncomputable abbrev explicitShapiroMap1 : H1 G (DiscreteCoind G U A) →+ H1 U A :=
  explicitMap1 G (DiscreteCoind G U A) U A (ContinuousMonoidHom.subgroupSubtype U)
    (DiscreteCoind.eval G U A) DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)

section Factorization

variable {G U A} (w : G → U) (c : U → A) (hw : Continuous w)
  (hwmul : ∀ (u : U) (g : G), w ((u : G) * g) = u * w g) (hccont : Continuous c)
  (hccoc : groupCohomology.IsCocycle₁ c)

omit [CompactSpace G] [DistribMulAction U A] [ContinuousSMul U A] in
include hw hccont in
private theorem continuous_shapiroLift_sub (g : G) :
    Continuous fun x : G => shapiroLift w c (x * g) - shapiroLift w c x :=
  ((continuous_shapiroLift w c hw hccont).comp (continuous_mul_const g)).sub
    (continuous_shapiroLift w c hw hccont)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TopologicalSpace A]
  [DiscreteTopology A] [ContinuousSMul U A] in
include hwmul hccoc in
private theorem shapiroLift_sub_mul (g : G) (u : U) (x : G) :
    shapiroLift w c ((u : G) * x * g) - shapiroLift w c ((u : G) * x) =
      u • (shapiroLift w c (x * g) - shapiroLift w c x) := by
  rw [mul_assoc, shapiroLift_mul w c hwmul hccoc u (x * g), shapiroLift_mul w c hwmul hccoc u x,
    smul_sub]
  abel

/-- **The inverse Shapiro cochain in degree one.** From a continuous `1`-cocycle `c` of `U` and a
continuous factorization `w` of `G` over the right cosets of `U`, the `1`-cochain of `G` with
coefficients in `Coind_U^G A` whose value at `g` is the right-translation difference
`x ↦ c (w (x * g)) - c (w x)` of `TauCeti.ContCohomology.shapiroLift`. -/
noncomputable def coindCochain1 (g : G) : DiscreteCoind G U A :=
  DiscreteCoind.mk G U A (fun x => shapiroLift w c (x * g) - shapiroLift w c x)
    ((IsLocallyConstant.iff_continuous _).2 (continuous_shapiroLift_sub w c hw hccont g))
    (shapiroLift_sub_mul w c hwmul hccoc g)

omit [CompactSpace G] [ContinuousSMul U A] in
@[simp]
theorem coindCochain1_apply (g x : G) :
    coindCochain1 w c hw hwmul hccont hccoc g x = c (w (x * g)) - c (w x) := (rfl)

omit [ContinuousSMul U A] in
/-- The inverse Shapiro cochain is a continuous `1`-cocycle. It is locally constant because the
lift is *uniformly* locally constant on the compact group `G`
(`TauCeti.isOpen_rightTranslationStabilizer`), and the cocycle identity is the telescoping of its
right-translation differences. -/
theorem coindCochain1_mem_Z1 :
    coindCochain1 w c hw hwmul hccont hccoc ∈ Z1 G (DiscreteCoind G U A) := by
  have hlc : IsLocallyConstant (coindCochain1 w c hw hwmul hccont hccoc) := by
    have hS : IsOpen (rightTranslationStabilizer (shapiroLift w c) : Set G) :=
      isOpen_rightTranslationStabilizer
        ((IsLocallyConstant.iff_continuous _).2 (continuous_shapiroLift w c hw hccont))
    refine (IsLocallyConstant.iff_exists_open _).2 fun g₀ =>
      ⟨(fun g => g₀⁻¹ * g) ⁻¹' (rightTranslationStabilizer (shapiroLift w c) : Set G),
        hS.preimage (continuous_const.mul continuous_id), by simp, fun g hg => ?_⟩
    refine DiscreteCoind.ext fun x => ?_
    have hx := (mem_rightTranslationStabilizer.1 hg) (x * g₀)
    rw [show x * g₀ * (g₀⁻¹ * g) = x * g by group] at hx
    simp only [coindCochain1_apply, ← shapiroLift_apply w c, hx]
  refine mem_Z1_iff.2 ⟨(IsLocallyConstant.iff_continuous _).1 hlc, fun g h => ?_⟩
  refine DiscreteCoind.ext fun x => ?_
  simp only [DiscreteCoind.coe_add, Pi.add_apply, DiscreteCoind.coe_smul, coindCochain1_apply,
    ← mul_assoc]
  abel

/-- **The inverse Shapiro cochain, as a continuous `1`-cocycle.** -/
noncomputable def coindCocycle1 : Z1 G (DiscreteCoind G U A) :=
  ⟨coindCochain1 w c hw hwmul hccont hccoc, coindCochain1_mem_Z1 w c hw hwmul hccont hccoc⟩

omit [ContinuousSMul U A] in
@[simp]
theorem coe_coindCocycle1 :
    (coindCocycle1 w c hw hwmul hccont hccoc : G → DiscreteCoind G U A) =
      coindCochain1 w c hw hwmul hccont hccoc := (rfl)

omit [ContinuousSMul U A] in
/-- **The Shapiro image of the inverse cochain is the cocycle it was built from**, up to the
explicit coboundary of `c (w 1)`. That correction term is what makes a normalisation `w 1 = 1`
unnecessary: it is a coboundary whatever the factorization does at `1`. -/
theorem shapiroCocycles1_coindCocycle1 :
    (shapiroCocycles1 G U A (coindCocycle1 w c hw hwmul hccont hccoc) : U → A) =
      c + d0 U A (c (w 1)) := by
  funext u
  have h : c (w (u : G)) = u • c (w 1) + c u := by
    simpa using shapiroLift_mul w c hwmul hccoc u 1
  rw [shapiroCocycles1_apply, coe_coindCocycle1, coindCochain1_apply, one_mul, Pi.add_apply,
    d0_apply, h]
  abel

omit [CompactSpace G] in
include hw hwmul in
/-- The inverse Shapiro cochain of a `1`-coboundary of `U` is a `1`-coboundary of `G`, with the
primitive `x ↦ w x • α` in `Coind_U^G A`. This is what makes the inverse construction descend to
cohomology. -/
theorem coindCochain1_mem_B1_of_mem_B1 (hcB : c ∈ B1 U A) :
    coindCochain1 w c hw hwmul hccont hccoc ∈ B1 G (DiscreteCoind G U A) := by
  obtain ⟨α, hα⟩ := mem_B1_iff.1 hcB
  refine mem_B1_iff.2 ⟨DiscreteCoind.mk G U A (fun x => w x • α)
    ((IsLocallyConstant.iff_continuous _).2 (continuous_smul.comp (hw.prodMk continuous_const)))
    (fun u x => by rw [hwmul u x, mul_smul]), fun g => DiscreteCoind.ext fun x => ?_⟩
  simp only [DiscreteCoind.coe_sub, Pi.sub_apply, DiscreteCoind.coe_smul,
    DiscreteCoind.mk_apply, coindCochain1_apply, ← hα]
  abel

omit [CompactSpace G] [ContinuousSMul U A] in
/-- **Every continuous `1`-cocycle of `G` is rebuilt from its Shapiro image**, up to the explicit
coboundary whose primitive is `y ↦ (f y) 1 - c (w y)`, where `c` is the Shapiro image of `f`. With
`TauCeti.ContCohomology.shapiroCocycles1_coindCocycle1` this is what makes the Shapiro map
bijective. -/
theorem sub_coindCochain1_mem_B1 (f : Z1 G (DiscreteCoind G U A))
    (hfc : (shapiroCocycles1 G U A f : U → A) = c) :
    (f : G → DiscreteCoind G U A) - coindCochain1 w c hw hwmul hccont hccoc ∈
      B1 G (DiscreteCoind G U A) := by
  have hfcoc := (mem_Z1_iff.1 f.2).2
  have hval : ∀ (u : U) (y : G), (f : G → DiscreteCoind G U A) ((u : G) * y) 1 =
      u • (f : G → DiscreteCoind G U A) y 1 + c u := fun u y => by
    rw [hfcoc (u : G) y]
    simp [← hfc]
  refine mem_B1_iff.2 ⟨DiscreteCoind.mk G U A
    (fun y => (f : G → DiscreteCoind G U A) y 1 - shapiroLift w c y)
    ((IsLocallyConstant.iff_continuous _).2
      (((DiscreteCoind.continuous_apply G U A 1).comp (mem_Z1_iff.1 f.2).1).sub
        (continuous_shapiroLift w c hw hccont)))
    (fun u y => by
      rw [hval u y, shapiroLift_mul w c hwmul hccoc u y, smul_sub]
      abel), fun g => DiscreteCoind.ext fun x => ?_⟩
  have hkey : (f : G → DiscreteCoind G U A) (x * g) 1 =
      (f : G → DiscreteCoind G U A) g x + (f : G → DiscreteCoind G U A) x 1 := by
    rw [hfcoc x g]
    simp
  simp only [DiscreteCoind.coe_sub, Pi.sub_apply, DiscreteCoind.coe_smul,
    DiscreteCoind.mk_apply, coindCochain1_apply, shapiroLift_apply, hkey]
  abel

end Factorization

section Equivalence

variable [TotallyDisconnectedSpace G]

/-- **The forward Shapiro map in degree one is bijective**, which is Shapiro's lemma. Surjectivity
is `TauCeti.ContCohomology.shapiroCocycles1_coindCocycle1` and injectivity combines
`TauCeti.ContCohomology.sub_coindCochain1_mem_B1` with
`TauCeti.ContCohomology.coindCochain1_mem_B1_of_mem_B1`; both run on a continuous right-coset
factorization, which is where closedness of `U` and profiniteness of `G` are used. -/
theorem bijective_explicitShapiroMap1 (hU : IsClosed (U : Set G)) :
    Function.Bijective (explicitShapiroMap1 G U A) := by
  obtain ⟨w, -, hw, -, -, hwmul, -, -⟩ := exists_continuous_rightCosetFactorization U hU
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    induction x using QuotientAddGroup.induction_on with
    | _ f =>
      rw [explicitMap1_mk] at hx
      have h1 := coindCochain1_mem_B1_of_mem_B1 w ((shapiroCocycles1 G U A f : U → A)) hw hwmul
        (mem_Z1_iff.1 (shapiroCocycles1 G U A f).2).1
        (mem_Z1_iff.1 (shapiroCocycles1 G U A f).2).2 (H1pi_eq_zero_iff.1 hx)
      have h2 := sub_coindCochain1_mem_B1 w ((shapiroCocycles1 G U A f : U → A)) hw hwmul
        (mem_Z1_iff.1 (shapiroCocycles1 G U A f).2).1
        (mem_Z1_iff.1 (shapiroCocycles1 G U A f).2).2 f rfl
      exact H1pi_eq_zero_iff.2 (by simpa using (B1 G (DiscreteCoind G U A)).add_mem h2 h1)
  · intro y
    induction y using QuotientAddGroup.induction_on with
    | _ c =>
      refine ⟨(coindCocycle1 w (c : U → A) hw hwmul (mem_Z1_iff.1 c.2).1 (mem_Z1_iff.1 c.2).2 :
        H1 G (DiscreteCoind G U A)), ?_⟩
      rw [explicitMap1_mk]
      refine H1pi_eq_iff.2 ?_
      have hsub : (shapiroCocycles1 G U A
          (coindCocycle1 w (c : U → A) hw hwmul (mem_Z1_iff.1 c.2).1 (mem_Z1_iff.1 c.2).2) :
            U → A) - (c : U → A) = d0 U A ((c : U → A) (w 1)) := by
        rw [shapiroCocycles1_coindCocycle1]
        abel
      rw [hsub]
      exact mem_B1_iff.2 ⟨_, fun g => (d0_apply _ g).symm⟩

/-- **Shapiro's lemma in degree one**, `H¹(G, Coind_U^G A) ≅ H¹(U, A)`, for a profinite `G` and a
closed subgroup `U`. The forward map is restriction to `U` followed by evaluation at `1`, and it
involves no choice; the continuous section of `G → G ⧸ U` is used only to prove it bijective. -/
noncomputable def explicitShapiro1 (hU : IsClosed (U : Set G)) :
    H1 G (DiscreteCoind G U A) ≃+ H1 U A :=
  AddEquiv.ofBijective (explicitShapiroMap1 G U A) (bijective_explicitShapiroMap1 G U A hU)

@[simp]
theorem explicitShapiro1_apply (hU : IsClosed (U : Set G)) (x : H1 G (DiscreteCoind G U A)) :
    explicitShapiro1 G U A hU x = explicitShapiroMap1 G U A x := (rfl)

/-- The inverse of the Shapiro isomorphism is the section formula, for **every** continuous
right-coset factorization of `G` over `U`. Since the equivalence is pinned by its forward
direction, independence of the factorization needs no separate proof. -/
theorem explicitShapiro1_symm_apply (hU : IsClosed (U : Set G)) {w : G → U} (hw : Continuous w)
    (hwmul : ∀ (u : U) (g : G), w ((u : G) * g) = u * w g) (c : Z1 U A) :
    (explicitShapiro1 G U A hU).symm (c : H1 U A) =
      (coindCocycle1 w (c : U → A) hw hwmul (mem_Z1_iff.1 c.2).1 (mem_Z1_iff.1 c.2).2 :
        H1 G (DiscreteCoind G U A)) := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [explicitShapiro1_apply, explicitMap1_mk]
  refine H1pi_eq_iff.2 ?_
  have hsub : (c : U → A) - (shapiroCocycles1 G U A
      (coindCocycle1 w (c : U → A) hw hwmul (mem_Z1_iff.1 c.2).1 (mem_Z1_iff.1 c.2).2) : U → A) =
      -d0 U A ((c : U → A) (w 1)) := by
    rw [shapiroCocycles1_coindCocycle1]
    abel
  rw [hsub]
  exact (B1 U A).neg_mem (mem_B1_iff.2 ⟨_, fun g => (d0_apply _ g).symm⟩)

end Equivalence

end DegreeOne

section Homogeneous

variable {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [DistribMulAction Γ M]

/-- The **homogeneous form** of an inhomogeneous `2`-cochain `f`. It is the composite of the
standard identification of inhomogeneous with homogeneous cochains with evaluation at `1`, and it
is used here to organise the degree-two Shapiro computation: in this form the cocycle identity is
the simplicial relation of `TauCeti.ContCohomology.hom2_add_hom2`, which is stable under
precomposing the three arguments with an arbitrary map. -/
private def hom2 (f : Γ × Γ → M) (a b c : Γ) : M := a • f (a⁻¹ * b, b⁻¹ * c)

private theorem hom2_def (f : Γ × Γ → M) (a b c : Γ) :
    hom2 f a b c = a • f (a⁻¹ * b, b⁻¹ * c) := (rfl)

/-- The `2`-cocycle identity in homogeneous form: the four faces of a `3`-simplex balance in
alternating pairs. -/
private theorem hom2_add_hom2 {f : Γ × Γ → M} (hf : groupCohomology.IsCocycle₂ f) (a b c d : Γ) :
    hom2 f a c d + hom2 f a b c = hom2 f b c d + hom2 f a b d := by
  have hb : a • ((a⁻¹ * b) • f (b⁻¹ * c, c⁻¹ * d)) = b • f (b⁻¹ * c, c⁻¹ * d) := by
    rw [← mul_smul, mul_inv_cancel_left]
  have h := congrArg (fun m : M => a • m) (hf (a⁻¹ * b) (b⁻¹ * c) (c⁻¹ * d))
  simp only [smul_add, show a⁻¹ * b * (b⁻¹ * c) = a⁻¹ * c by group,
    show b⁻¹ * c * (c⁻¹ * d) = b⁻¹ * d by group, hb] at h
  simpa only [hom2_def] using h

/-- **The prism homotopy in degree two.** For a function `Φ` of three variables satisfying the
simplicial relation of `TauCeti.ContCohomology.hom2_add_hom2` and an arbitrary `v`, the difference
`Φ - Φ ∘ (v × v × v)` is the
coboundary of the `1`-cochain `β x y = Φ (v x) x y - Φ (v x) (v y) y`, the alternating sum over the
two ways of inserting `v` into a `1`-simplex. Nothing here uses the group structure: it is the
simplicial homotopy between the identity and `v`. -/
private theorem prism2 {Y : Type*} {N : Type*} [AddCommGroup N] (Φ : Y → Y → Y → N)
    (halt : ∀ a b c d : Y, Φ a c d + Φ a b c = Φ b c d + Φ a b d) (v : Y → Y) (x y z : Y) :
    Φ (v y) y z - Φ (v y) (v z) z - (Φ (v x) x z - Φ (v x) (v z) z) +
        (Φ (v x) x y - Φ (v x) (v y) y) = Φ x y z - Φ (v x) (v y) (v z) := by
  linear_combination (norm := abel)
    halt (v x) x y z - halt (v x) (v y) y z + halt (v x) (v y) (v z) z

end Homogeneous

section UniformLocalConstancy

/-- A function of a parameter and a **compact** variable that is jointly continuous is locally
constant in the parameter, as a map into the space of *all* functions of the compact variable: its
currying takes values in `C(Y, B)`, which is discrete. This is the uniformity that makes the
degree-two Shapiro cochains continuous; degree one uses the group-theoretic form of the same
phenomenon, `TauCeti.isOpen_rightTranslationStabilizer`. -/
private theorem isLocallyConstant_of_continuous_uncurry {X Y B : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace B] [DiscreteTopology B]
    {F : X → Y → B} (hF : Continuous fun q : X × Y => F q.1 q.2) : IsLocallyConstant F := by
  have hcurry : IsLocallyConstant (ContinuousMap.curry (⟨_, hF⟩ : C(X × Y, B))) :=
    (IsLocallyConstant.iff_continuous _).2 (ContinuousMap.curry _).continuous
  refine (IsLocallyConstant.iff_eventually_eq F).2 fun x₀ => ?_
  filter_upwards [hcurry.eventually_eq x₀] with x hx
  exact funext fun y => by simpa using DFunLike.congr_fun hx y

end UniformLocalConstancy

section CoindOfFun

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {U : Subgroup G} {A : Type v} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A] [ContinuousSMul U A] {P : Type*} [TopologicalSpace P]
  (F : P → G → A) (hF : Continuous fun q : P × G => F q.1 q.2)
  (hFsmul : ∀ (u : U) (p : P) (x : G), F p ((u : G) * x) = u • F p x)

/-- A family of elements of `Coind_U^G A` indexed by a parameter space `P`, built from a jointly
continuous `F : P → G → A` that is `U`-equivariant in its second variable. This packages the two
topological conditions the degree-two Shapiro cochains have to meet: each `F p` is locally
constant, and — `G` being compact — the family is locally constant in `p`. -/
private def coindOfFun (p : P) : DiscreteCoind G U A :=
  DiscreteCoind.mk G U A (F p)
    ((IsLocallyConstant.iff_continuous _).2 (hF.comp (continuous_const.prodMk continuous_id)))
    (fun u x => hFsmul u p x)

omit [IsTopologicalGroup G] [CompactSpace G] [ContinuousSMul U A] in
private theorem coindOfFun_apply (p : P) (x : G) : coindOfFun F hF hFsmul p x = F p x := (rfl)

omit [IsTopologicalGroup G] [ContinuousSMul U A] in
/-- Such a family is continuous, because a jointly continuous function of a parameter and a point
of the compact group `G` is locally constant in the parameter. -/
private theorem continuous_coindOfFun : Continuous (coindOfFun F hF hFsmul) := by
  refine (IsLocallyConstant.iff_continuous _).1 ((IsLocallyConstant.iff_eventually_eq _).2 ?_)
  intro p₀
  filter_upwards [(isLocallyConstant_of_continuous_uncurry hF).eventually_eq p₀] with p hp
  exact DiscreteCoind.ext (congrFun hp)

end CoindOfFun

section DegreeTwo

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G) (A : Type v) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A] [ContinuousSMul U A]

/-- **The forward Shapiro map on continuous `2`-cocycles**: restrict a continuous `2`-cocycle of
`G` with coefficients in `Coind_U^G A` to `U`, and evaluate its values at `1`. -/
noncomputable abbrev shapiroCocycles2 : Z2 G (DiscreteCoind G U A) →+ Z2 U A :=
  cocyclesMap2 G (DiscreteCoind G U A) U A (ContinuousMonoidHom.subgroupSubtype U)
    (DiscreteCoind.eval G U A) DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)

omit [CompactSpace G] [ContinuousSMul U A] in
@[simp]
theorem shapiroCocycles2_apply (f : Z2 G (DiscreteCoind G U A)) (u v : U) :
    (shapiroCocycles2 G U A f : U × U → A) (u, v) =
      (f : G × G → DiscreteCoind G U A) ((u : G), (v : G)) 1 := by
  simp [cocyclesMap2_apply]

/-- **The forward Shapiro map on `H²`**, the compatible-pair pullback along the inclusion `U ↪ G`
and evaluation at `1`. `TauCeti.ContCohomology.explicitShapiro2` upgrades it to an isomorphism. -/
noncomputable abbrev explicitShapiroMap2 : H2 G (DiscreteCoind G U A) →+ H2 U A :=
  explicitMap2 G (DiscreteCoind G U A) U A (ContinuousMonoidHom.subgroupSubtype U)
    (DiscreteCoind.eval G U A) DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)

section Factorization

variable {G U A} (w : G → U) (c : U × U → A) (hw : Continuous w)
  (hwmul : ∀ (u : U) (g : G), w ((u : G) * g) = u * w g) (hccont : Continuous c)

omit [CompactSpace G] [DiscreteTopology A] in
include hw hccont in
/-- The defining function of the degree-two inverse Shapiro cochain, as a function of the pair and
of the point of `G` at once. -/
private theorem continuous_coindFun2 :
    Continuous fun q : (G × G) × G => w q.2 • c ((w q.2)⁻¹ * w (q.2 * q.1.1),
      (w (q.2 * q.1.1))⁻¹ * w (q.2 * q.1.1 * q.1.2)) := by
  have e1 : Continuous fun q : (G × G) × G => w (q.2 * q.1.1) :=
    hw.comp (continuous_snd.mul continuous_fst.fst)
  have e2 : Continuous fun q : (G × G) × G => w (q.2 * q.1.1 * q.1.2) :=
    hw.comp ((continuous_snd.mul continuous_fst.fst).mul continuous_fst.snd)
  exact (hw.comp continuous_snd).smul
    (hccont.comp ((((hw.comp continuous_snd).inv).mul e1).prodMk (e1.inv.mul e2)))

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TopologicalSpace A]
  [DiscreteTopology A] [ContinuousSMul U A] in
include hwmul in
/-- The defining function of the degree-two inverse Shapiro cochain is `U`-equivariant: the
factorization word `(w x)⁻¹ * w (x * g)` is unchanged by left translation of `x` by `U`, and the
leading factor `w x` picks up exactly one `u`. -/
private theorem coindFun2_smul (g h : G) (u : U) (x : G) :
    w ((u : G) * x) • c ((w ((u : G) * x))⁻¹ * w ((u : G) * x * g),
        (w ((u : G) * x * g))⁻¹ * w ((u : G) * x * g * h)) =
      u • (w x • c ((w x)⁻¹ * w (x * g), (w (x * g))⁻¹ * w (x * g * h))) := by
  have e1 : w ((u : G) * x) = u * w x := hwmul u x
  have e2 : w ((u : G) * x * g) = u * w (x * g) := by
    rw [show (u : G) * x * g = (u : G) * (x * g) by group, hwmul]
  have e3 : w ((u : G) * x * g * h) = u * w (x * g * h) := by
    rw [show (u : G) * x * g * h = (u : G) * (x * g * h) by group, hwmul]
  rw [e1, e2, e3, show (u * w x)⁻¹ * (u * w (x * g)) = (w x)⁻¹ * w (x * g) by group,
    show (u * w (x * g))⁻¹ * (u * w (x * g * h)) = (w (x * g))⁻¹ * w (x * g * h) by group, mul_smul]

/-- **The inverse Shapiro cochain in degree two.** From a continuous `2`-cochain `c` of `U` and a
continuous factorization `w` of `G` over the right cosets of `U`, the `2`-cochain of `G` with
coefficients in `Coind_U^G A` whose value at `(g, h)` is the function
`x ↦ w x • c ((w x)⁻¹ * w (x * g), (w (x * g))⁻¹ * w (x * g * h))`, that is, the homogeneous form of
`c` evaluated at the three points `w x`, `w (x * g)` and `w (x * g * h)`. -/
noncomputable def coindCochain2 (p : G × G) : DiscreteCoind G U A :=
  coindOfFun (fun p x => w x • c ((w x)⁻¹ * w (x * p.1), (w (x * p.1))⁻¹ * w (x * p.1 * p.2)))
    (continuous_coindFun2 w c hw hccont) (fun u p x => coindFun2_smul w c hwmul p.1 p.2 u x) p

omit [CompactSpace G] in
@[simp]
theorem coindCochain2_apply (p : G × G) (x : G) :
    coindCochain2 w c hw hwmul hccont p x =
      w x • c ((w x)⁻¹ * w (x * p.1), (w (x * p.1))⁻¹ * w (x * p.1 * p.2)) := (rfl)

/-- The inverse Shapiro cochain is a *continuous* `2`-cochain: it is locally constant in the pair
`(g, h)` because its defining function is continuous in the pair and the point of `G` jointly and
`G` is compact. -/
theorem continuous_coindCochain2 : Continuous (coindCochain2 w c hw hwmul hccont) :=
  continuous_coindOfFun _ (continuous_coindFun2 w c hw hccont)
    (fun u p x => coindFun2_smul w c hwmul p.1 p.2 u x)

variable (hccoc : groupCohomology.IsCocycle₂ c)

include hccoc in
/-- The inverse Shapiro cochain is a continuous `2`-cocycle: in homogeneous form the cocycle
identity for `coindCochain2` at the four points `x`, `x * g`, `x * g * h`, `x * g * h * k` is
exactly the cocycle identity for `c` at the three factorization words between them. -/
theorem coindCochain2_mem_Z2 :
    coindCochain2 w c hw hwmul hccont ∈ Z2 G (DiscreteCoind G U A) := by
  refine mem_Z2_iff.2 ⟨continuous_coindCochain2 w c hw hwmul hccont, fun g h k => ?_⟩
  refine DiscreteCoind.ext fun x => ?_
  have key := hom2_add_hom2 hccoc (w x) (w (x * g)) (w (x * g * h)) (w (x * g * h * k))
  simp only [hom2_def] at key
  simp only [DiscreteCoind.coe_add, Pi.add_apply, DiscreteCoind.coe_smul, coindCochain2_apply,
    mul_assoc] at key ⊢
  exact key

/-- **The inverse Shapiro cochain in degree two, as a continuous `2`-cocycle.** -/
noncomputable def coindCocycle2 : Z2 G (DiscreteCoind G U A) :=
  ⟨coindCochain2 w c hw hwmul hccont, coindCochain2_mem_Z2 w c hw hwmul hccont hccoc⟩

@[simp]
theorem coe_coindCocycle2 :
    (coindCocycle2 w c hw hwmul hccont hccoc : G × G → DiscreteCoind G U A) =
      coindCochain2 w c hw hwmul hccont := (rfl)

include hwmul in
/-- **The Shapiro image of the inverse cochain is the cocycle it was built from**, for a
factorization normalized by `w 1 = 1`. That normalization is what makes the composite the identity
on the nose: it forces `w` to restrict to the identity on `U`, so all three factorization words
occurring at `x = 1` are the arguments of `c` themselves. -/
theorem shapiroCocycles2_coindCocycle2 (hw1 : w 1 = 1) :
    (shapiroCocycles2 G U A (coindCocycle2 w c hw hwmul hccont hccoc) : U × U → A) = c := by
  have hwu : ∀ u : U, w (u : G) = u := fun u => by
    rw [show (u : G) = (u : G) * 1 by rw [mul_one], hwmul, hw1, mul_one]
  refine funext fun p => ?_
  obtain ⟨u, v⟩ := p
  have e2 : w ((u : G) * (v : G)) = u * v := by rw [hwmul u (v : G), hwu v]
  rw [shapiroCocycles2_apply, coe_coindCocycle2, coindCochain2_apply]
  simp only [one_mul, hw1, hwu, e2, inv_one, one_smul, inv_mul_cancel_left]

include hw hwmul in
/-- The inverse Shapiro cochain of a `2`-coboundary of `U` is a `2`-coboundary of `G`, with the
primitive `x ↦ w x • β ((w x)⁻¹ * w (x * g))` in `Coind_U^G A`. This is what makes the inverse
construction descend to cohomology. -/
theorem coindCochain2_mem_B2_of_mem_B2 (hcB : c ∈ B2 U A) :
    coindCochain2 w c hw hwmul hccont ∈ B2 G (DiscreteCoind G U A) := by
  obtain ⟨β, hβcont, hβ⟩ := mem_B2_iff.1 hcB
  obtain ⟨Q, hQ⟩ : ∃ Q : G → G → A, Q = fun g x => w x • β ((w x)⁻¹ * w (x * g)) := ⟨_, rfl⟩
  have hQcont : Continuous fun q : G × G => Q q.1 q.2 := by
    have e1 : Continuous fun q : G × G => w (q.2 * q.1) :=
      hw.comp (continuous_snd.mul continuous_fst)
    rw [hQ]
    exact (hw.comp continuous_snd).smul (hβcont.comp ((hw.comp continuous_snd).inv.mul e1))
  have hQsmul : ∀ (u : U) (g x : G), Q g ((u : G) * x) = u • Q g x := fun u g x => by
    simp only [hQ, hwmul u x, show (u : G) * x * g = (u : G) * (x * g) by group, hwmul,
      show (u * w x)⁻¹ * (u * w (x * g)) = (w x)⁻¹ * w (x * g) by group, mul_smul]
  refine mem_B2_iff.2 ⟨coindOfFun Q hQcont hQsmul, continuous_coindOfFun Q hQcont hQsmul, ?_⟩
  refine funext fun p => DiscreteCoind.ext fun x => ?_
  obtain ⟨g, h⟩ := p
  have hcancel : ∀ y z : G, w y * ((w y)⁻¹ * w z) = w z := fun y z => by group
  have hcomp : ∀ y z t : G, (w y)⁻¹ * w z * ((w z)⁻¹ * w t) = (w y)⁻¹ * w t :=
    fun y z t => by group
  simp only [d1_apply, DiscreteCoind.coe_sub, DiscreteCoind.coe_add, Pi.sub_apply, Pi.add_apply,
    DiscreteCoind.coe_smul, coindOfFun_apply, coindCochain2_apply, hQ, ← hβ, d1_apply, smul_sub,
    smul_add, ← mul_smul, hcancel, hcomp, mul_assoc]

include hw hwmul in
/-- **Every continuous `2`-cocycle of `G` is rebuilt from its Shapiro image**, up to an explicit
coboundary. The primitive is the prism homotopy `x ↦ β (x, x * g)` of
`TauCeti.ContCohomology.prism2` for the homogeneous form of `f` and the map `w`, and with
`TauCeti.ContCohomology.shapiroCocycles2_coindCocycle2` it is what makes the Shapiro map
bijective. -/
theorem sub_coindCochain2_mem_B2 (f : Z2 G (DiscreteCoind G U A))
    (hfc : (shapiroCocycles2 G U A f : U × U → A) = c) :
    (f : G × G → DiscreteCoind G U A) - coindCochain2 w c hw hwmul hccont ∈
      B2 G (DiscreteCoind G U A) := by
  -- Three steps: the homogeneous form `Φ` of `f` and its two evaluations `hΦid` and `hΦw`, which
  -- identify the two `2`-cocycles being compared; the prism homotopy `P` of `Φ` along `w`, with
  -- its continuity and equivariance; and `prism2`, which says its coboundary is the difference.
  obtain ⟨F, hF⟩ : ∃ F : G × G → DiscreteCoind G U A,
    F = (f : G × G → DiscreteCoind G U A) := ⟨_, rfl⟩
  have hFcont : Continuous F := by rw [hF]; exact (mem_Z2_iff.1 f.2).1
  have hFcoc : groupCohomology.IsCocycle₂ F := by rw [hF]; exact (mem_Z2_iff.1 f.2).2
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G → G → G → A, Φ = fun a b d => hom2 F a b d 1 := ⟨_, rfl⟩
  have halt : ∀ a b d e : G, Φ a d e + Φ a b d = Φ b d e + Φ a b e := fun a b d e => by
    simpa only [hΦ, DiscreteCoind.coe_add, Pi.add_apply] using
      congrArg (fun m : DiscreteCoind G U A => m 1) (hom2_add_hom2 hFcoc a b d e)
  have hΦval : ∀ a b d : G, Φ a b d = F (a⁻¹ * b, b⁻¹ * d) a := fun a b d => by
    simp only [hΦ, hom2_def, DiscreteCoind.coe_smul, one_mul]
  have hΦid : ∀ g h x : G, Φ x (x * g) (x * g * h) = F (g, h) x := fun g h x => by
    rw [hΦval, show x⁻¹ * (x * g) = g by group, show (x * g)⁻¹ * (x * g * h) = h by group]
  have hΦw : ∀ a b d : G, Φ (w a) (w b) (w d) = w a • c ((w a)⁻¹ * w b, (w b)⁻¹ * w d) :=
    fun a b d => by
      rw [hΦval, show ((w a : G))⁻¹ * (w b : G) = (((w a)⁻¹ * w b : U) : G) by simp,
        show ((w b : G))⁻¹ * (w d : G) = (((w b)⁻¹ * w d : U) : G) by simp,
        DiscreteCoind.apply_coe, hF, ← hfc, shapiroCocycles2_apply]
  -- the prism homotopy of `TauCeti.ContCohomology.prism2`, as a function of `(g, x)`
  obtain ⟨P, hP⟩ : ∃ P : G → G → A, P = fun g x => w x • (F (((w x : G))⁻¹ * x, g) 1 -
      F (((w x : G))⁻¹ * (w (x * g) : G), ((w (x * g) : G))⁻¹ * (x * g)) 1) := ⟨_, rfl⟩
  have hPval : ∀ g x : G, P g x = Φ (w x) x (x * g) - Φ (w x) (w (x * g)) (x * g) :=
    fun g x => by
      simp only [hP, hΦval, inv_mul_cancel_left, DiscreteCoind.apply_coe, smul_sub]
  have hPcont : Continuous fun q : G × G => P q.1 q.2 := by
    have hev := DiscreteCoind.continuous_apply G U A 1
    have hwx : Continuous fun q : G × G => (w q.2 : G) :=
      continuous_subtype_val.comp (hw.comp continuous_snd)
    have hwxg : Continuous fun q : G × G => (w (q.2 * q.1) : G) :=
      continuous_subtype_val.comp (hw.comp (continuous_snd.mul continuous_fst))
    simp only [hP]
    exact (hw.comp continuous_snd).smul
      ((hev.comp (hFcont.comp ((hwx.inv.mul continuous_snd).prodMk continuous_fst))).sub
        (hev.comp (hFcont.comp ((hwx.inv.mul hwxg).prodMk
          (hwxg.inv.mul (continuous_snd.mul continuous_fst))))))
  have hPsmul : ∀ (u : U) (g x : G), P g ((u : G) * x) = u • P g x := fun u g x => by
    have e2 : w ((u : G) * x * g) = u * w (x * g) := by
      rw [show (u : G) * x * g = (u : G) * (x * g) by group, hwmul]
    simp only [hP, hwmul u x, e2, Subgroup.coe_mul,
      show ((u : G) * (w x : G))⁻¹ * ((u : G) * x) = ((w x : G))⁻¹ * x by group,
      show ((u : G) * (w x : G))⁻¹ * ((u : G) * (w (x * g) : G))
        = ((w x : G))⁻¹ * (w (x * g) : G) by group,
      show ((u : G) * (w (x * g) : G))⁻¹ * ((u : G) * x * g)
        = ((w (x * g) : G))⁻¹ * (x * g) by group, mul_smul]
  refine mem_B2_iff.2 ⟨coindOfFun P hPcont hPsmul, continuous_coindOfFun P hPcont hPsmul, ?_⟩
  refine funext fun p => DiscreteCoind.ext fun x => ?_
  obtain ⟨g, h⟩ := p
  have key := prism2 Φ halt (fun a => (w a : G)) x (x * g) (x * g * h)
  rw [hΦid, hΦw] at key
  simp only [d1_apply, DiscreteCoind.coe_sub, DiscreteCoind.coe_add, Pi.sub_apply, Pi.add_apply,
    DiscreteCoind.coe_smul, coindOfFun_apply, hPval, coindCochain2_apply, hF, mul_assoc] at key ⊢
  linear_combination (norm := abel) key

end Factorization

section Equivalence

variable [TotallyDisconnectedSpace G]

/-- **The forward Shapiro map in degree two is bijective**, which is Shapiro's lemma. Surjectivity
is `TauCeti.ContCohomology.shapiroCocycles2_coindCocycle2` and injectivity combines
`TauCeti.ContCohomology.sub_coindCochain2_mem_B2` with
`TauCeti.ContCohomology.coindCochain2_mem_B2_of_mem_B2`; both run on a continuous right-coset
factorization, which is where closedness of `U` and profiniteness of `G` are used. -/
theorem bijective_explicitShapiroMap2 (hU : IsClosed (U : Set G)) :
    Function.Bijective (explicitShapiroMap2 G U A) := by
  obtain ⟨w, -, hw, -, -, hwmul, -, hw1⟩ := exists_continuous_rightCosetFactorization U hU
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    induction x using QuotientAddGroup.induction_on with
    | _ f =>
      rw [explicitMap2_mk] at hx
      have hcont := (mem_Z2_iff.1 (shapiroCocycles2 G U A f).2).1
      have h1 := coindCochain2_mem_B2_of_mem_B2 w ((shapiroCocycles2 G U A f : U × U → A)) hw
        hwmul hcont (H2pi_eq_zero_iff.1 hx)
      have h2 := sub_coindCochain2_mem_B2 w ((shapiroCocycles2 G U A f : U × U → A)) hw hwmul
        hcont f rfl
      exact H2pi_eq_zero_iff.2 (by simpa using (B2 G (DiscreteCoind G U A)).add_mem h2 h1)
  · intro y
    induction y using QuotientAddGroup.induction_on with
    | _ d =>
      refine ⟨(coindCocycle2 w (d : U × U → A) hw hwmul (mem_Z2_iff.1 d.2).1 (mem_Z2_iff.1 d.2).2 :
        H2 G (DiscreteCoind G U A)), ?_⟩
      rw [explicitMap2_mk, show shapiroCocycles2 G U A (coindCocycle2 w (d : U × U → A) hw hwmul
        (mem_Z2_iff.1 d.2).1 (mem_Z2_iff.1 d.2).2) = d from
        Subtype.ext (shapiroCocycles2_coindCocycle2 w (d : U × U → A) hw hwmul _ _ hw1)]

/-- **Shapiro's lemma in degree two**, `H²(G, Coind_U^G A) ≅ H²(U, A)`, for a profinite `G` and a
closed subgroup `U`. The forward map is restriction to `U` followed by evaluation at `1`, and it
involves no choice; the continuous section of `G → G ⧸ U` is used only to prove it bijective. -/
noncomputable def explicitShapiro2 (hU : IsClosed (U : Set G)) :
    H2 G (DiscreteCoind G U A) ≃+ H2 U A :=
  AddEquiv.ofBijective (explicitShapiroMap2 G U A) (bijective_explicitShapiroMap2 G U A hU)

@[simp]
theorem explicitShapiro2_apply (hU : IsClosed (U : Set G)) (x : H2 G (DiscreteCoind G U A)) :
    explicitShapiro2 G U A hU x = explicitShapiroMap2 G U A x := (rfl)

/-- The inverse of the degree-two Shapiro isomorphism is the section formula, for **every**
continuous right-coset factorization of `G` over `U` normalized by `w 1 = 1`. Since the equivalence
is pinned by its forward direction, independence of the factorization needs no separate proof. -/
theorem explicitShapiro2_symm_apply (hU : IsClosed (U : Set G)) {w : G → U} (hw : Continuous w)
    (hwmul : ∀ (u : U) (g : G), w ((u : G) * g) = u * w g) (hw1 : w 1 = 1) (d : Z2 U A) :
    (explicitShapiro2 G U A hU).symm (d : H2 U A) =
      (coindCocycle2 w (d : U × U → A) hw hwmul (mem_Z2_iff.1 d.2).1 (mem_Z2_iff.1 d.2).2 :
        H2 G (DiscreteCoind G U A)) := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [explicitShapiro2_apply, explicitMap2_mk,
    show shapiroCocycles2 G U A (coindCocycle2 w (d : U × U → A) hw hwmul (mem_Z2_iff.1 d.2).1
      (mem_Z2_iff.1 d.2).2) = d from
      Subtype.ext (shapiroCocycles2_coindCocycle2 w (d : U × U → A) hw hwmul _ _ hw1)]

end Equivalence

end DegreeTwo

end TauCeti.ContCohomology
