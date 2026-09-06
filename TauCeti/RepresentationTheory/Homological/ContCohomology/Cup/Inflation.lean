/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation

/-!
# Inflation preserves explicit low-degree cup products

Let `N` be a normal subgroup of `G`. An equivariant pairing `M × A → P` restricts to a pairing
`Mᴺ × Aᴺ → Pᴺ` on the invariant coefficients over `G ⧸ N`. Inflation preserves each of the six
explicit cup products:

```text
inf (a ⌣ b) = inf a ⌣ inf b.
```

The equality already holds on cocycle representatives: inflation precomposes cochains with the
quotient map and includes their invariant values into the ambient coefficient modules.

## Main statements

* `TauCeti.ContCohomology.explicitInfl0_explicitCup00`,
  `explicitInfl1_explicitCup01`, `explicitInfl1_explicitCup10`,
  `explicitInfl2_explicitCup02`, `explicitInfl2_explicitCup11`, and
  `explicitInfl2_explicitCup20`: inflation preserves the corresponding explicit cup product.

## Reference

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.3)(iii).
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uA uP

section DegreeZero

variable (G : Type uG) [Group G]
  (M : Type uM) [AddCommGroup M] [DistribMulAction G M]
  (A : Type uA) [AddCommGroup A] [DistribMulAction G A]
  (P : Type uP) [AddCommGroup P] [DistribMulAction G P]
  (N : Subgroup G) [N.Normal]
  (μ : M →+ A →+ P)
  (hequiv : ∀ (g : G) (m : M) (a : A), μ (g • m) (g • a) = g • μ m a)

/-- **Inflation preserves the `(0,0)` cup product.** -/
@[simp]
theorem explicitInfl0_explicitCup00
    (a : H0 (G ⧸ N) (FixedPoints.addSubgroup N M))
    (b : H0 (G ⧸ N) (FixedPoints.addSubgroup N A)) :
    explicitInfl0 G P N
        (explicitCup00 (G ⧸ N) (FixedPoints.addSubgroup N M)
          (FixedPoints.addSubgroup N A) (FixedPoints.addSubgroup N P)
          (fixedPointsPairing N μ hequiv)
          (fixedPointsPairing_quotient_smul N μ hequiv) a b) =
      explicitCup00 G M A P μ hequiv
        (explicitInfl0 G M N a) (explicitInfl0 G A N b) := by
  apply Subtype.ext
  simp only [coe_explicitInfl0, coe_explicitCup00, coe_fixedPointsPairing]

end DegreeZero

section PositiveDegree

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (A : Type uA) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A] [ContinuousSMul G A]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (N : Subgroup G) [N.Normal]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N A)]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N P)]
  (μ : M →+ A →+ P) (hμ : Continuous fun p : M × A => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (a : A), μ (g • m) (g • a) = g • μ m a)

local notation "μᴺ" => fixedPointsPairing N μ hequiv

include hμ hequiv

omit [IsTopologicalAddGroup M] [ContinuousSMul G M]
    [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)] [IsTopologicalGroup G] in
/-- **Inflation preserves the `(0,1)` cup product.** -/
@[simp]
theorem explicitInfl1_explicitCup01
    (a : H0 (G ⧸ N) (FixedPoints.addSubgroup N M))
    (b : H1 (G ⧸ N) (FixedPoints.addSubgroup N A)) :
    explicitInfl1 G P N
        (explicitCup01 (G ⧸ N) (FixedPoints.addSubgroup N M)
          (FixedPoints.addSubgroup N A) (FixedPoints.addSubgroup N P) μᴺ
          (continuous_fixedPointsPairing N μ hequiv hμ)
          (fixedPointsPairing_quotient_smul N μ hequiv) a b) =
      explicitCup01 G M A P μ hμ hequiv
        (explicitInfl0 G M N a) (explicitInfl1 G A N b) := by
  induction b using QuotientAddGroup.induction_on with
  | _ b =>
      rw [explicitCup01_mk, explicitInfl1_mk, explicitInfl1_mk, explicitCup01_mk]
      exact congrArg (fun z : Z1 G P => (z : H1 G P)) <| Subtype.ext <| funext fun g => by
        simp [cocyclesMap1_coe]

omit [IsTopologicalAddGroup A] [ContinuousSMul G A]
    [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N A)] [IsTopologicalGroup G] in
/-- **Inflation preserves the `(1,0)` cup product.** -/
@[simp]
theorem explicitInfl1_explicitCup10
    (a : H1 (G ⧸ N) (FixedPoints.addSubgroup N M))
    (b : H0 (G ⧸ N) (FixedPoints.addSubgroup N A)) :
    explicitInfl1 G P N
        (explicitCup10 (G ⧸ N) (FixedPoints.addSubgroup N M)
          (FixedPoints.addSubgroup N A) (FixedPoints.addSubgroup N P) μᴺ
          (continuous_fixedPointsPairing N μ hequiv hμ)
          (fixedPointsPairing_quotient_smul N μ hequiv) a b) =
      explicitCup10 G M A P μ hμ hequiv
        (explicitInfl1 G M N a) (explicitInfl0 G A N b) := by
  induction a using QuotientAddGroup.induction_on with
  | _ a =>
      rw [explicitCup10_mk, explicitInfl1_mk, explicitInfl1_mk, explicitCup10_mk]
      exact congrArg (fun z : Z1 G P => (z : H1 G P)) <| Subtype.ext <| funext fun g => by
        simp [cocyclesMap1_coe]

omit [IsTopologicalAddGroup M] [ContinuousSMul G M]
    [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)] in
/-- **Inflation preserves the `(0,2)` cup product.** -/
@[simp]
theorem explicitInfl2_explicitCup02
    (a : H0 (G ⧸ N) (FixedPoints.addSubgroup N M))
    (b : H2 (G ⧸ N) (FixedPoints.addSubgroup N A)) :
    explicitInfl2 G P N
        (explicitCup02 (G ⧸ N) (FixedPoints.addSubgroup N M)
          (FixedPoints.addSubgroup N A) (FixedPoints.addSubgroup N P) μᴺ
          (continuous_fixedPointsPairing N μ hequiv hμ)
          (fixedPointsPairing_quotient_smul N μ hequiv) a b) =
      explicitCup02 G M A P μ hμ hequiv
        (explicitInfl0 G M N a) (explicitInfl2 G A N b) := by
  induction b using QuotientAddGroup.induction_on with
  | _ b =>
      rw [explicitCup02_mk, explicitInfl2_mk, explicitInfl2_mk, explicitCup02_mk]
      exact congrArg (fun z : Z2 G P => (z : H2 G P)) <| Subtype.ext <| funext fun q => by
        obtain ⟨g, h⟩ := q
        simp [cocyclesMap2_coe]

/-- **Inflation preserves the `(1,1)` cup product.** -/
@[simp]
theorem explicitInfl2_explicitCup11
    (a : H1 (G ⧸ N) (FixedPoints.addSubgroup N M))
    (b : H1 (G ⧸ N) (FixedPoints.addSubgroup N A)) :
    explicitInfl2 G P N
        (explicitCup11 (G ⧸ N) (FixedPoints.addSubgroup N M)
          (FixedPoints.addSubgroup N A) (FixedPoints.addSubgroup N P) μᴺ
          (continuous_fixedPointsPairing N μ hequiv hμ)
          (fixedPointsPairing_quotient_smul N μ hequiv) a b) =
      explicitCup11 G M A P μ hμ hequiv
        (explicitInfl1 G M N a) (explicitInfl1 G A N b) := by
  induction a using QuotientAddGroup.induction_on with
  | _ a =>
      induction b using QuotientAddGroup.induction_on with
      | _ b =>
          rw [explicitCup11_mk, explicitInfl2_mk, explicitInfl1_mk, explicitInfl1_mk,
            explicitCup11_mk]
          exact congrArg (fun z : Z2 G P => (z : H2 G P)) <| Subtype.ext <| funext fun q => by
            obtain ⟨g, h⟩ := q
            simp [cocyclesMap1_coe, cocyclesMap2_coe]

omit [IsTopologicalAddGroup A] [ContinuousSMul G A]
    [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N A)] in
/-- **Inflation preserves the `(2,0)` cup product.** -/
@[simp]
theorem explicitInfl2_explicitCup20
    (a : H2 (G ⧸ N) (FixedPoints.addSubgroup N M))
    (b : H0 (G ⧸ N) (FixedPoints.addSubgroup N A)) :
    explicitInfl2 G P N
        (explicitCup20 (G ⧸ N) (FixedPoints.addSubgroup N M)
          (FixedPoints.addSubgroup N A) (FixedPoints.addSubgroup N P) μᴺ
          (continuous_fixedPointsPairing N μ hequiv hμ)
          (fixedPointsPairing_quotient_smul N μ hequiv) a b) =
      explicitCup20 G M A P μ hμ hequiv
        (explicitInfl2 G M N a) (explicitInfl0 G A N b) := by
  induction a using QuotientAddGroup.induction_on with
  | _ a =>
      rw [explicitCup20_mk, explicitInfl2_mk, explicitInfl2_mk, explicitCup20_mk]
      exact congrArg (fun z : Z2 G P => (z : H2 G P)) <| Subtype.ext <| funext fun q => by
        obtain ⟨g, h⟩ := q
        have hsmul :
            (((((g : G ⧸ N) * (h : G ⧸ N)) •
              (b : FixedPoints.addSubgroup N A)) : FixedPoints.addSubgroup N A) : A) =
              (g * h) • (b : A) := by
          calc
            _ = ((((g : G ⧸ N) • ((h : G ⧸ N) •
                (b : FixedPoints.addSubgroup N A))) : FixedPoints.addSubgroup N A) : A) :=
              congrArg Subtype.val (mul_smul (g : G ⧸ N) (h : G ⧸ N)
                (b : FixedPoints.addSubgroup N A))
            _ = (((g : G) • ((h : G ⧸ N) •
                (b : FixedPoints.addSubgroup N A))) : FixedPoints.addSubgroup N A) :=
              congrArg Subtype.val <| coe_quotient_smul_fixedPoints_addSubgroup (H := N) g _
            _ = g • ((((h : G ⧸ N) •
                (b : FixedPoints.addSubgroup N A)) : FixedPoints.addSubgroup N A) : A) :=
              coe_smul_fixedPoints_addSubgroup g _
            _ = g • (((h : G) •
                (b : FixedPoints.addSubgroup N A) : FixedPoints.addSubgroup N A) : A) :=
              congrArg (fun x : A => g • x) <| congrArg Subtype.val <|
                coe_quotient_smul_fixedPoints_addSubgroup (H := N) h
                  (b : FixedPoints.addSubgroup N A)
            _ = g • (h • (b : A)) := congrArg (fun x : A => g • x)
              (coe_smul_fixedPoints_addSubgroup h (b : FixedPoints.addSubgroup N A))
            _ = (g * h) • (b : A) := (mul_smul g h (b : A)).symm
        simpa [cocyclesMap2_coe] using congrArg (μ (↑((a : (G ⧸ N) × (G ⧸ N) →
          FixedPoints.addSubgroup N M) ((g : G ⧸ N), (h : G ⧸ N))) : M))
            hsmul

end PositiveDegree

end TauCeti.ContCohomology
