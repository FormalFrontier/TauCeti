/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality

/-!
# The conjugation action on the explicit cohomology of a normal subgroup

For a normal subgroup `N` of a topological group `G` acting on a topological module `M`, an
element `g : G` acts on the continuous cochains of `N` through the compatible pair consisting of
conjugation `n ↦ g⁻¹ * n * g` on the group and the action of `g` on the coefficients:

```text
(g · c) n       = g • c (g⁻¹ * n * g),
(g · c) (n, k)  = g • c (g⁻¹ * n * g, g⁻¹ * k * g).
```

This file builds the resulting maps on `H¹(N, M)` and `H²(N, M)`, proves that they form a left
action of `G`, and proves that an element of `N` itself acts trivially. That last statement is
what makes the action factor through `G ⧸ N`, and hence what makes the third term
`H¹(N, M)^{G ⧸ N}` of the five-term inflation-restriction-transgression sequence well defined.

## Main definitions

* `TauCeti.ContCohomology.conjCocycles1`, `conjCocycles2`: conjugation on continuous cocycles.
* `TauCeti.ContCohomology.explicitConj1`, `explicitConj2`: conjugation on `H¹` and `H²`.
* `TauCeti.ContCohomology.conjHomotopy2`: the degree-two chain homotopy `b` below.

## Main statements

* `TauCeti.ContCohomology.explicitConj1_mul` and `explicitConj2_mul`, with `explicitConj1_one`
  and `explicitConj2_one`: conjugation is a left action of `G`.
* `TauCeti.ContCohomology.explicitConj1_eq_id_of_mem` and `explicitConj2_eq_id_of_mem`: inner
  automorphisms act trivially.

## Implementation notes

Degree zero needs nothing from this file: `H⁰(N, M)` is `TauCeti.FixedPoints.addSubgroup N M`,
already a `G`-module by `TauCeti.distribMulActionFixedPointsAddSubgroup` and already a
`G ⧸ N`-module by `TauCeti.distribMulActionQuotientFixedPointsAddSubgroup`, both for normal `N`.
The content in positive degrees is that the corresponding statements hold only *after* passing to
cohomology classes: conjugation by an element `γ` of `N` is not the identity on cocycles, and the
witnesses that it becomes the identity on classes are `conjCocycles1_sub_eq_d0`, which exhibits the
`1`-coboundary `d⁰ (c γ)`, and `conjCocycles2_sub_eq_d1`, which exhibits the `2`-coboundary `d¹ b`
for the explicit continuous `1`-cochain

```text
b n = c (γ, γ⁻¹ * n * γ) - c (n, γ).
```

Both are stated as identities of cochains before anything is quotiented, since the roadmap's
five-term sequence needs the primitives and not only the vanishing of the classes. Both are also
stated for a conjugating element `γ : N` rather than for `g : G` together with a proof of
`g ∈ N`, so that the value `c γ` can be written down at all.

Conjugation is taken to be `n ↦ g⁻¹ * n * g`, that is, Mathlib's `MulAut.conjNormal g⁻¹`; this
is the convention already used for the algebraic conjugate representation
`TauCeti.conjNormalRep` in `TauCeti/RepresentationTheory/Induction/Conjugate.lean`, and it is the
one that makes `g ↦ (g · -)` a *left* action.

The two degrees share the compatible-pair machinery of
`TauCeti/RepresentationTheory/Homological/ContCohomology/ExplicitFunctoriality.lean`, so the only
inputs proved here are the compatibility identity `smul_conjNormal_inv_smul` of the conjugation
pair, the multiplicativity `toAddMonoidHom_one` and `toAddMonoidHom_mul` of its coefficient half,
and the two homotopies. Continuity of conjugation is `TauCeti.ContinuousMonoidHom.conjNormal`.

This implements the "conjugation" milestone of Layer 2 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`, whose `Suggested.lean` fixes the names
`explicitConj1` and `explicitConj1_eq_id_of_mem`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Ch. I, §0, Prop. 0.15: conjugation by an
  element of a group acts trivially on the cohomology of that group.
* K. S. Brown, *Cohomology of Groups*, Springer GTM 87, Ch. III, §8: the chain homotopy behind
  the triviality of inner automorphisms, of which `conjHomotopy2` is the inhomogeneous shadow in
  degree two.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.7): the
  five-term sequence, whose third term is the `G ⧸ N`-invariants of `H¹(N, M)`.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM

section CompatiblePair

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [MulAction G M] (N : Subgroup G) [N.Normal]

/-- The compatibility identity of the conjugation pair: conjugation `n ↦ g⁻¹ * n * g` on `N`
together with the action of `g` on `M` is a compatible pair in the sense of `explicitMap1`. -/
theorem smul_conjNormal_inv_smul (g : G) (n : N) (m : M) :
    g • ((ContinuousMonoidHom.conjNormal N g⁻¹ n : N) • m) = (n : N) • (g • m) := by
  simp only [Subgroup.smul_def, ContinuousMonoidHom.coe_conjNormal_apply, inv_inv, ← mul_smul]
  group

end CompatiblePair

section Coefficients

variable (G : Type uG) [Monoid G] (M : Type uM) [AddMonoid M] [DistribMulAction G M]

-- The coefficient half of the conjugation pair is `DistribSMul.toAddMonoidHom M g`; the two
-- lemmas below are the unbundled `map_one` and `map_mul` of `DistribMulAction.toAddMonoidEnd`,
-- in the `M →+ M` form in which `cocyclesMap1` and friends take their coefficient map.
/-- The identity acts on the coefficients by the identity homomorphism. -/
@[simp]
theorem toAddMonoidHom_one : DistribSMul.toAddMonoidHom M (1 : G) = AddMonoidHom.id M :=
  map_one (DistribMulAction.toAddMonoidEnd G M)

/-- Acting on the coefficients by a product is acting by the two factors in turn. -/
@[simp]
theorem toAddMonoidHom_mul (g g' : G) :
    DistribSMul.toAddMonoidHom M (g * g') =
      (DistribSMul.toAddMonoidHom M g).comp (DistribSMul.toAddMonoidHom M g') :=
  map_mul (DistribMulAction.toAddMonoidEnd G M) g g'

end Coefficients

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal]

section Degree1

/-- **Conjugation on continuous `1`-cocycles**, `(g · c) n = g • c (g⁻¹ * n * g)`. -/
noncomputable def conjCocycles1 (g : G) : Z1 N M →+ Z1 N M :=
  cocyclesMap1 N M N M (ContinuousMonoidHom.conjNormal N g⁻¹)
    (DistribSMul.toAddMonoidHom M g) (continuous_const_smul g)
    (smul_conjNormal_inv_smul G M N g)

variable {G M N}

/-- The defining formula for conjugation on continuous `1`-cocycles. -/
@[simp]
theorem conjCocycles1_apply (g : G) (c : Z1 N M) (n : N) :
    (conjCocycles1 G M N g c : N → M) n =
      g • (c : N → M) (ContinuousMonoidHom.conjNormal N g⁻¹ n) :=
  cocyclesMap1_apply N M N M _ _ _ _ c n

variable (G M N)

/-- The identity of `G` acts trivially on continuous `1`-cocycles. -/
@[simp]
theorem conjCocycles1_one : conjCocycles1 G M N 1 = AddMonoidHom.id (Z1 N M) := by
  unfold conjCocycles1
  simp only [inv_one, ContinuousMonoidHom.conjNormal_one, toAddMonoidHom_one]
  exact cocyclesMap1_id N M _

/-- Conjugation on continuous `1`-cocycles is a left action of `G`. -/
@[simp]
theorem conjCocycles1_mul (g g' : G) :
    conjCocycles1 G M N (g * g') = (conjCocycles1 G M N g).comp (conjCocycles1 G M N g') := by
  unfold conjCocycles1
  simp only [mul_inv_rev, ContinuousMonoidHom.conjNormal_mul, toAddMonoidHom_mul]
  exact cocyclesMap1_comp N M N M (ContinuousMonoidHom.conjNormal N g'⁻¹)
    (DistribSMul.toAddMonoidHom M g') _ (smul_conjNormal_inv_smul G M N g')
    N M (ContinuousMonoidHom.conjNormal N g⁻¹) (DistribSMul.toAddMonoidHom M g) _
    (smul_conjNormal_inv_smul G M N g) _

/-- **Conjugation on the explicit first cohomology group.** For a normal subgroup `N` of `G`, the
compatible pair `(n ↦ g⁻¹ * n * g, m ↦ g • m)` pulls a class of `H¹(N, M)` back to a class of
`H¹(N, M)`. -/
noncomputable def explicitConj1 (g : G) : H1 N M →+ H1 N M :=
  explicitMap1 N M N M (ContinuousMonoidHom.conjNormal N g⁻¹)
    (DistribSMul.toAddMonoidHom M g) (continuous_const_smul g)
    (smul_conjNormal_inv_smul G M N g)

variable {G M N}

/-- Conjugation sends the class of a continuous `1`-cocycle to the class of its conjugate. -/
@[simp]
theorem explicitConj1_mk (g : G) (c : Z1 N M) :
    explicitConj1 G M N g (c : H1 N M) = (conjCocycles1 G M N g c : H1 N M) :=
  explicitMap1_mk N M N M (ContinuousMonoidHom.conjNormal N g⁻¹)
    (DistribSMul.toAddMonoidHom M g) (continuous_const_smul g)
    (smul_conjNormal_inv_smul G M N g) c

variable (G M N)

/-- The identity of `G` acts trivially on `H¹(N, M)`. -/
@[simp]
theorem explicitConj1_one : explicitConj1 G M N 1 = AddMonoidHom.id (H1 N M) := by
  unfold explicitConj1
  simp only [inv_one, ContinuousMonoidHom.conjNormal_one, toAddMonoidHom_one]
  exact explicitMap1_id N M _

/-- Conjugation on `H¹(N, M)` is a left action of `G`. -/
@[simp]
theorem explicitConj1_mul (g g' : G) :
    explicitConj1 G M N (g * g') = (explicitConj1 G M N g).comp (explicitConj1 G M N g') := by
  unfold explicitConj1
  simp only [mul_inv_rev, ContinuousMonoidHom.conjNormal_mul, toAddMonoidHom_mul]
  exact explicitMap1_comp N M N M (ContinuousMonoidHom.conjNormal N g'⁻¹)
    (DistribSMul.toAddMonoidHom M g') _ (smul_conjNormal_inv_smul G M N g')
    N M (ContinuousMonoidHom.conjNormal N g⁻¹) (DistribSMul.toAddMonoidHom M g) _
    (smul_conjNormal_inv_smul G M N g) _

variable {G M N}

/-- **The degree-one homotopy.** Conjugating a continuous `1`-cocycle of `N` by an element `γ` of
`N` moves it by the coboundary of its own value at `γ`. -/
theorem conjCocycles1_sub_eq_d0 (γ : N) (c : Z1 N M) :
    (conjCocycles1 G M N (γ : G) c : N → M) - (c : N → M) = d0 N M ((c : N → M) γ) := by
  have hc : groupCohomology.IsCocycle₁ (c : N → M) := (mem_Z1_iff.1 c.2).2
  ext n
  -- Expand `c (γ⁻¹ * n * γ)` by two applications of the `1`-cocycle law.
  have hstep : (c : N → M) (γ⁻¹ * n * γ) =
      (γ⁻¹ * n) • (c : N → M) γ + (γ⁻¹ • (c : N → M) n + (c : N → M) γ⁻¹) := by
    rw [hc, hc]
  rw [Pi.sub_apply, conjCocycles1_apply, ContinuousMonoidHom.conjNormal_inv_coe, hstep,
    ← Subgroup.smul_def, d0_apply, smul_add, smul_add, ← mul_smul,
    ← mul_smul, mul_inv_cancel_left, mul_inv_cancel, one_smul, map_inv_of_mem_Z1 c.2 γ]
  abel

variable (G M N)

/-- **Inner automorphisms act trivially on `H¹`** (Milne, *Arithmetic Duality Theorems*,
Prop. 0.15). This is what makes the conjugation action of `G` on `H¹(N, M)` descend to `G ⧸ N`. -/
theorem explicitConj1_eq_id_of_mem (g : G) (hg : g ∈ N) :
    explicitConj1 G M N g = AddMonoidHom.id (H1 N M) := by
  obtain ⟨γ, rfl⟩ : ∃ γ : N, (γ : G) = g := ⟨⟨g, hg⟩, rfl⟩
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitConj1_mk, AddMonoidHom.id_apply]
    refine H1pi_eq_iff.2 ?_
    rw [conjCocycles1_sub_eq_d0 γ c]
    exact mem_B1_iff.2 ⟨(c : N → M) γ, fun n => (d0_apply ((c : N → M) γ) n).symm⟩

end Degree1

section Degree2

/-- **Conjugation on continuous `2`-cocycles**,
`(g · c) (n, k) = g • c (g⁻¹ * n * g, g⁻¹ * k * g)`. -/
noncomputable def conjCocycles2 (g : G) : Z2 N M →+ Z2 N M :=
  cocyclesMap2 N M N M (ContinuousMonoidHom.conjNormal N g⁻¹)
    (DistribSMul.toAddMonoidHom M g) (continuous_const_smul g)
    (smul_conjNormal_inv_smul G M N g)

variable {G M N}

/-- The defining formula for conjugation on continuous `2`-cocycles. -/
@[simp]
theorem conjCocycles2_apply (g : G) (c : Z2 N M) (n k : N) :
    (conjCocycles2 G M N g c : N × N → M) (n, k) =
      g • (c : N × N → M)
        (ContinuousMonoidHom.conjNormal N g⁻¹ n, ContinuousMonoidHom.conjNormal N g⁻¹ k) :=
  cocyclesMap2_apply N M N M _ _ _ _ c n k

variable (G M N)

/-- The identity of `G` acts trivially on continuous `2`-cocycles. -/
@[simp]
theorem conjCocycles2_one : conjCocycles2 G M N 1 = AddMonoidHom.id (Z2 N M) := by
  unfold conjCocycles2
  simp only [inv_one, ContinuousMonoidHom.conjNormal_one, toAddMonoidHom_one]
  exact cocyclesMap2_id N M

/-- Conjugation on continuous `2`-cocycles is a left action of `G`. -/
@[simp]
theorem conjCocycles2_mul (g g' : G) :
    conjCocycles2 G M N (g * g') = (conjCocycles2 G M N g).comp (conjCocycles2 G M N g') := by
  unfold conjCocycles2
  simp only [mul_inv_rev, ContinuousMonoidHom.conjNormal_mul, toAddMonoidHom_mul]
  exact cocyclesMap2_comp N M N M (ContinuousMonoidHom.conjNormal N g'⁻¹)
    (DistribSMul.toAddMonoidHom M g') _ (smul_conjNormal_inv_smul G M N g')
    N M (ContinuousMonoidHom.conjNormal N g⁻¹) (DistribSMul.toAddMonoidHom M g) _
    (smul_conjNormal_inv_smul G M N g)

omit [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] [N.Normal] in
/-- The degree-two chain homotopy `b n = c (γ, γ⁻¹ * n * γ) - c (n, γ)`, with the conjugate formed
in `N` itself. Conjugating a continuous `2`-cocycle `c` by `γ ∈ N` moves it by `d¹ b`. -/
def conjHomotopy2 (γ : N) (c : N × N → M) : N → M := fun n =>
  c (γ, γ⁻¹ * n * γ) - c (n, γ)

variable {G M N}

omit [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] [N.Normal] in
/-- The defining formula for the degree-two chain homotopy. -/
@[simp]
theorem conjHomotopy2_apply (γ : N) (c : N × N → M) (n : N) :
    conjHomotopy2 G M N γ c n = c (γ, γ⁻¹ * n * γ) - c (n, γ) :=
  (rfl)

omit [ContinuousMul G] [DistribMulAction G M] [ContinuousSMul G M] [N.Normal] in
/-- The degree-two chain homotopy is a *continuous* `1`-cochain, which is what membership in `B²`
requires of a primitive. -/
theorem continuous_conjHomotopy2 [ContinuousMul N] (γ : N) {c : N × N → M} (hc : Continuous c) :
    Continuous (conjHomotopy2 G M N γ c) :=
  (hc.comp (continuous_const.prodMk
      ((continuous_const.mul continuous_id).mul continuous_const))).sub
    (hc.comp (continuous_id.prodMk continuous_const))

/-- **The degree-two homotopy.** Conjugating a continuous `2`-cocycle of `N` by an element `γ` of
`N` moves it by the coboundary of `conjHomotopy2`. -/
theorem conjCocycles2_sub_eq_d1 (γ : N) (c : Z2 N M) :
    (conjCocycles2 G M N (γ : G) c : N × N → M) - (c : N × N → M) =
      d1 N M (conjHomotopy2 G M N γ (c : N × N → M)) := by
  have hc : groupCohomology.IsCocycle₂ (c : N × N → M) := (mem_Z2_iff.1 c.2).2
  ext p
  obtain ⟨n, k⟩ := p
  -- Instantiating the `2`-cocycle law leaves the products it forms in their literal shapes
  -- `γ * (γ⁻¹ * n * γ)` and `γ⁻¹ * n * γ * (γ⁻¹ * k * γ)`, whereas the goal and the remaining
  -- instances of the law use the cancelled shapes below. Both shapes occur only as *arguments of*
  -- `c`, where no cocycle or module lemma applies, so they can be exchanged only by rewriting with
  -- these group identities, each of which `group` discharges.
  have hnγ : γ * (γ⁻¹ * n * γ) = n * γ := by group
  have hkγ : γ * (γ⁻¹ * k * γ) = k * γ := by group
  have hnkγ : γ⁻¹ * n * γ * (γ⁻¹ * k * γ) = γ⁻¹ * (n * k) * γ := by group
  -- The `2`-cocycle law at `(γ, γ⁻¹nγ, γ⁻¹kγ)`, at `(n, γ, γ⁻¹kγ)` and at `(n, k, γ)`, each
  -- solved for the term the goal has to eliminate.
  have hA : γ • (c : N × N → M) (γ⁻¹ * n * γ, γ⁻¹ * k * γ) =
      (c : N × N → M) (n * γ, γ⁻¹ * k * γ) + (c : N × N → M) (γ, γ⁻¹ * n * γ) -
        (c : N × N → M) (γ, γ⁻¹ * (n * k) * γ) := by
    have h := hc γ (γ⁻¹ * n * γ) (γ⁻¹ * k * γ)
    rw [hnγ, hnkγ] at h
    exact eq_sub_of_add_eq h.symm
  have hB : (c : N × N → M) (n * γ, γ⁻¹ * k * γ) =
      n • (c : N × N → M) (γ, γ⁻¹ * k * γ) + (c : N × N → M) (n, k * γ) -
        (c : N × N → M) (n, γ) := by
    have h := hc n γ (γ⁻¹ * k * γ)
    rw [hkγ] at h
    exact eq_sub_of_add_eq h
  have hC : (c : N × N → M) (n, k * γ) =
      (c : N × N → M) (n * k, γ) + (c : N × N → M) (n, k) -
        n • (c : N × N → M) (k, γ) :=
    eq_sub_of_add_eq' (hc n k γ).symm
  rw [Pi.sub_apply, conjCocycles2_apply]
  simp only [ContinuousMonoidHom.conjNormal_inv_coe]
  rw [← Subgroup.smul_def, hA, hB, hC, d1_apply, conjHomotopy2_apply, conjHomotopy2_apply,
    conjHomotopy2_apply, smul_sub]
  abel

variable (G M N)
variable [ContinuousMul N]

/-- **Conjugation on the explicit second cohomology group.** -/
noncomputable def explicitConj2 (g : G) : H2 N M →+ H2 N M :=
  explicitMap2 N M N M (ContinuousMonoidHom.conjNormal N g⁻¹)
    (DistribSMul.toAddMonoidHom M g) (continuous_const_smul g)
    (smul_conjNormal_inv_smul G M N g)

variable {G M N}

/-- Conjugation sends the class of a continuous `2`-cocycle to the class of its conjugate. -/
@[simp]
theorem explicitConj2_mk (g : G) (c : Z2 N M) :
    explicitConj2 G M N g (c : H2 N M) = (conjCocycles2 G M N g c : H2 N M) :=
  explicitMap2_mk N M N M (ContinuousMonoidHom.conjNormal N g⁻¹)
    (DistribSMul.toAddMonoidHom M g) (continuous_const_smul g)
    (smul_conjNormal_inv_smul G M N g) c

variable (G M N)

/-- The identity of `G` acts trivially on `H²(N, M)`. -/
@[simp]
theorem explicitConj2_one : explicitConj2 G M N 1 = AddMonoidHom.id (H2 N M) := by
  unfold explicitConj2
  simp only [inv_one, ContinuousMonoidHom.conjNormal_one, toAddMonoidHom_one]
  exact explicitMap2_id N M

/-- Conjugation on `H²(N, M)` is a left action of `G`. -/
@[simp]
theorem explicitConj2_mul (g g' : G) :
    explicitConj2 G M N (g * g') = (explicitConj2 G M N g).comp (explicitConj2 G M N g') := by
  unfold explicitConj2
  simp only [mul_inv_rev, ContinuousMonoidHom.conjNormal_mul, toAddMonoidHom_mul]
  exact explicitMap2_comp N M N M (ContinuousMonoidHom.conjNormal N g'⁻¹)
    (DistribSMul.toAddMonoidHom M g') _ (smul_conjNormal_inv_smul G M N g')
    N M (ContinuousMonoidHom.conjNormal N g⁻¹) (DistribSMul.toAddMonoidHom M g) _
    (smul_conjNormal_inv_smul G M N g)

/-- **Inner automorphisms act trivially on `H²`** (Milne, *Arithmetic Duality Theorems*,
Prop. 0.15). -/
theorem explicitConj2_eq_id_of_mem (g : G) (hg : g ∈ N) :
    explicitConj2 G M N g = AddMonoidHom.id (H2 N M) := by
  obtain ⟨γ, rfl⟩ : ∃ γ : N, (γ : G) = g := ⟨⟨g, hg⟩, rfl⟩
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitConj2_mk, AddMonoidHom.id_apply]
    refine H2pi_eq_iff.2 ?_
    rw [conjCocycles2_sub_eq_d1 γ c]
    exact mem_B2_iff.2 ⟨_, continuous_conjHomotopy2 γ (mem_Z2_iff.1 c.2).1, rfl⟩

end Degree2

end TauCeti.ContCohomology
