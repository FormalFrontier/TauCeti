/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.Torus

/-!
# Weyl representatives in the Kostant toral closure

The Weyl element attached to an `sl₂` root pair is the product

```text
nᵢ = xᵢ(1) x₋ᵢ(-1) xᵢ(1).
```

Each factor is a point of the Kostant toral closure, so this product gives a canonical point of
the assembled Chevalley carrier over every commutative ring. This file packages that point in the
carrier, identifies its matrix with the integral Weyl automorphism of the admissible lattice, and
proves that it normalizes the represented split torus. Its conjugation action is the reflection
attached to the root and coroot of the `sl₂` pair.

These representatives supply the point-level Weyl group data used to transport simple-root
subgroups to arbitrary roots and to compare the normalizer of the represented torus with the Weyl
group of the root datum.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint`: the Weyl representative as a point
  of the toral closure.
* `TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralWeylPoint`: its matrix is the integral Weyl
  automorphism in the chosen basis.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint_conj_rootSubgroupPoints`: conjugation
  sends the `i` root subgroup to the `j` root subgroup, negating the parameter.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint_conj_weightTorusPoints`: its conjugation
  action on the represented split torus.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint_mem_normalizer_weightTorusPoints`: the
  Weyl representative belongs to the torus normalizer inside the carrier.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

open TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Fintype κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)

omit [Fintype κ] in
private theorem coe_kostantRootSubgroupParam {A : Type v} [CommRing A] (i : I)
    (t : Multiplicative A) :
    (kostantRootSubgroupParam e h ρ M hM i (hnil i) (CommAlgCat.of ℤ A) t :
        Module.End A (A ⊗[ℤ] M)) =
      baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M
        (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv)
        (Multiplicative.toAdd t) :=
  LinearMap.ext fun z =>
    kostantRootSubgroupParam_val_apply e h ρ M hM i (hnil i) (CommAlgCat.of ℤ A) t z

omit [Fintype κ] in
private theorem basisMatrix_kostantWeylProduct (i j : I) (A : Type v) [CommRing A] :
    Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom
        (kostantRootSubgroupParam e h ρ M hM i (hnil i) (CommAlgCat.of ℤ A)
            (Multiplicative.ofAdd 1) *
          kostantRootSubgroupParam e h ρ M hM j (hnil j) (CommAlgCat.of ℤ A)
            (Multiplicative.ofAdd (-1)) *
          kostantRootSubgroupParam e h ρ M hM i (hnil i) (CommAlgCat.of ℤ A)
            (Multiplicative.ofAdd 1)) =
      Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom
        (kostantWeylGL e h ρ M hM (hnil i) (hnil j) A) := by
  refine congrArg (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom)
    (Units.ext ?_)
  rw [Units.val_mul, Units.val_mul, coe_kostantRootSubgroupParam (i := i),
    coe_kostantRootSubgroupParam (i := j), toAdd_ofAdd, kostantWeylGL_val]
  exact (kostantWeylPoints_toLinearMap_eq
    e h ρ M hM (hnil i) (hnil j) (A := A)).symm

/-! ## The Weyl representative in the carrier -/

/-- The Weyl representative `xᵢ(1) xⱼ(-1) xᵢ(1)` as a point of the Kostant toral closure.

The intended indices `i` and `j` are opposite roots in an `sl₂` pair. The definition itself only
uses their represented root subgroups; the `sl₂` relations enter when describing conjugation. -/
noncomputable def kostantToralWeylPoint (i j : I) (A : Type v) [CommRing A] :
    kostantToralPointsSubgroup e h ρ M hM hnil b wt A :=
  kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A
      (Multiplicative.ofAdd (1 : A)) *
    kostantToralRootSubgroupPoints e h ρ M hM hnil b wt j A
      (Multiplicative.ofAdd (-1 : A)) *
    kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A
      (Multiplicative.ofAdd (1 : A))

/-- In the chosen basis, the carrier's Weyl representative is the matrix of the integral Weyl
automorphism of the admissible lattice. -/
@[simp]
theorem coe_kostantToralWeylPoint (i j : I) (A : Type v) [CommRing A] :
    (kostantToralWeylPoint e h ρ M hM hnil b wt i j A :
        Matrix.GeneralLinearGroup (Fin n) A) =
      Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMulEquiv
        (kostantWeylGL e h ρ M hM (hnil i) (hnil j) A) := by
  simpa only [kostantToralWeylPoint, Subgroup.coe_mul,
    coe_kostantToralRootSubgroupPoints, map_mul,
    basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A i (Multiplicative.ofAdd 1),
    basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A j (Multiplicative.ofAdd (-1)),
    MulEquiv.toMonoidHom_eq_coe] using
    basisMatrix_kostantWeylProduct e h ρ M hM hnil b i j A

/-! ## Normalization of the represented torus -/

variable {i j : I} {c : κ} {α : κ → ℤ}
variable (hT : IsSl2Triple (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (hα : ∀ q, ⁅h q, e i⁆ = (α q : ℚ) • e i)
variable (hαneg : ∀ q, ⁅h q, e j⁆ = -((α q : ℚ) • e j))

omit [Fintype κ] in
include hT in
private theorem basisMatrix_kostantWeylConjRoot (A : Type v) [CommRing A] (u : A) :
    Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom
        (kostantWeylGL e h ρ M hM (hnil i) (hnil j) A *
          kostantRootSubgroupParam e h ρ M hM i (hnil i) (CommAlgCat.of ℤ A)
            (Multiplicative.ofAdd u) *
          (kostantWeylGL e h ρ M hM (hnil i) (hnil j) A)⁻¹) =
      Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom
        (kostantRootSubgroupParam e h ρ M hM j (hnil j) (CommAlgCat.of ℤ A)
          (Multiplicative.ofAdd (-u))) := by
  refine congrArg (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom)
    (Units.ext ?_)
  rw [Units.val_mul, Units.val_mul, kostantWeylGL_val, kostantWeylGL_inv_val,
    coe_kostantRootSubgroupParam (i := i), coe_kostantRootSubgroupParam (i := j),
    toAdd_ofAdd]
  exact kostantWeylPoints_conj_baseChangeExp
    e h ρ M hM (hnil i) (hnil j) hT u

include hT in
/-- Conjugation by the carrier's Weyl representative sends the `i` root subgroup to the `j` root
subgroup, negating the parameter: `nᵢ xᵢ(u) nᵢ⁻¹ = xⱼ(-u)`. -/
theorem kostantToralWeylPoint_conj_rootSubgroupPoints (A : Type v) [CommRing A] (u : A) :
    kostantToralWeylPoint e h ρ M hM hnil b wt i j A *
        kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A
          (Multiplicative.ofAdd u) *
        (kostantToralWeylPoint e h ρ M hM hnil b wt i j A)⁻¹ =
      kostantToralRootSubgroupPoints e h ρ M hM hnil b wt j A
        (Multiplicative.ofAdd (-u)) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_kostantToralWeylPoint,
    coe_kostantToralRootSubgroupPoints, map_mul, map_inv,
    basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A i (Multiplicative.ofAdd u),
    basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A j (Multiplicative.ofAdd (-u)),
    MulEquiv.toMonoidHom_eq_coe] using
    basisMatrix_kostantWeylConjRoot e h ρ M hM hnil b hT A u

include hT hα hαneg in
/-- Conjugating a represented weight-torus point by the carrier's Weyl representative reflects
the torus point by the root `α` and its coroot coordinate `c`. -/
theorem kostantToralWeylPoint_conj_weightTorusPoints
    [DecidableEq κ]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (A : Type v) [CommRing A] (s : κ → Aˣ) :
    kostantToralWeylPoint e h ρ M hM hnil b wt i j A *
        kostantToralWeightTorusPoints e h ρ M hM hnil b wt A s *
        (kostantToralWeylPoint e h ρ M hM hnil b wt i j A)⁻¹ =
      kostantToralWeightTorusPoints e h ρ M hM hnil b wt A
        (weylReflectTorusPoint α c s) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_kostantToralWeylPoint, coe_kostantToralWeightTorusPoints,
    coe_kostantToralWeightTorusPoints]
  have hmatrix := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom)
    (kostantWeylGL_conj_kostantTorusPoints e h ρ M hM (hnil i) (hnil j)
      hT hα hαneg b wt hwt s)
  simpa only [map_mul, map_inv, MulEquiv.toMonoidHom_eq_coe,
    basisMatrix_kostantTorusPoints] using hmatrix

include hT hα hαneg in
/-- The Weyl representative is in the normalizer of the represented weight torus inside the
Kostant toral closure. -/
theorem kostantToralWeylPoint_mem_normalizer_weightTorusPoints
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (A : Type v) [CommRing A] :
    kostantToralWeylPoint e h ρ M hM hnil b wt i j A ∈
      Subgroup.normalizer
        (kostantToralWeightTorusPoints e h ρ M hM hnil b wt A).range := by
  classical
  let K := kostantToralPointsSubgroup e h ρ M hM hnil b wt A
  let T := (kostantTorusMatrix M b wt :
    (κ → Aˣ) →* Matrix.GeneralLinearGroup (Fin n) A).range
  have hTK : T ≤ K := by
    rintro _ ⟨s, rfl⟩
    exact kostantTorusMatrix_mem_toralPoints e h ρ M hM hnil b wt A s
  have hcarrier :
      (kostantToralWeightTorusPoints e h ρ M hM hnil b wt A).range =
        T.subgroupOf K := by
    let fK := (kostantTorusMatrix M b wt).codRestrict K fun x ↦ hTK ⟨x, rfl⟩
    have hf : kostantToralWeightTorusPoints e h ρ M hM hnil b wt A = fK := by
      apply MonoidHom.ext
      intro s
      apply Subtype.ext
      exact coe_kostantToralWeightTorusPoints e h ρ M hM hnil b wt A s
    rw [hf]
    exact (MonoidHom.subgroupOf_range_eq_of_le (kostantTorusMatrix M b wt) hTK).symm
  rw [hcarrier, ← Subgroup.subgroupOf_normalizer_eq hTK]
  rw [Subgroup.mem_subgroupOf]
  rw [coe_kostantToralWeylPoint]
  let f := Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom
  let T' := (kostantTorusPoints M b wt A).range
  have hTmap : T'.map f = T := by
    rw [MonoidHom.map_range]
    apply congrArg (fun g : (κ → Aˣ) →* Matrix.GeneralLinearGroup (Fin n) A => g.range)
    apply MonoidHom.ext
    intro s
    exact basisMatrix_kostantTorusPoints M b wt s
  rw [← hTmap]
  apply Subgroup.le_normalizer_map f
  exact Subgroup.mem_map_of_mem f <|
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr <|
      map_kostantTorusPoints_range_conj_kostantWeylGL
        e h ρ M hM (hnil i) (hnil j) hT hα hαneg b wt hwt

end TauCeti.UniversalEnvelopingAlgebra
