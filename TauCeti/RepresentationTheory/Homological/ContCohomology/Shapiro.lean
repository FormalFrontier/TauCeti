/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality

/-!
# Shapiro's lemma in degrees zero and one

For a profinite group `G`, a **closed** subgroup `U` and a discrete `U`-module `A`, the coinduced
module `Coind_U^G A` of `TauCeti.DiscreteCoind` computes the cohomology of `U`:

```text
H⁰(G, Coind_U^G A) ≅ H⁰(U, A),   H¹(G, Coind_U^G A) ≅ H¹(U, A).
```

Both isomorphisms are *evaluation at `1`* composed with restriction to `U`, so in degree one the
forward map is the compatible-pair pullback `TauCeti.ContCohomology.explicitMap1` along the pair
consisting of the inclusion `U ↪ G` and the counit `TauCeti.DiscreteCoind.eval`; nothing about it
depends on a choice. The choice enters only in proving that this map is bijective, and what it uses
is Layer 0's continuous section of `G → G ⧸ U`
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

## Implementation notes

Degree zero needs no topological hypothesis beyond a continuous multiplication on `G`: a
`G`-invariant element of the coinduced module is constant, and the constant it takes is
`U`-invariant. Degree one is where profiniteness and closedness of `U` are used, through the
continuous factorization; for an *open* `U` the finite transversal `Quotient.out` would already
suffice, but openness is not assumed anywhere here.

This is the degree-`0` and degree-`1` part of the "Shapiro's lemma" milestone of Layer 7 of the
human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`, whose `Suggested.lean`
fixes the names `explicitShapiro0` and `explicitShapiro1`, and whose §5 fixes the direction of the
isomorphism — that of Mathlib's discrete `groupCohomology.coindIso` — and the forward map.

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
inclusion has to be spelled as `ContinuousMonoidHom.subgroupSubtype`. -/
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
  obtain ⟨w, -, hw, -, -, hwmul, -⟩ := exists_continuous_rightCosetFactorization U hU
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

end TauCeti.ContCohomology
