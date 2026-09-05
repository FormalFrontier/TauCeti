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
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint_conj_rootSubgroup`: conjugation
  exchanges the two root subgroups in the `sl₂` pair.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint_conj_weightTorus`: its conjugation
  action on the represented split torus.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralWeylPoint_mem_normalizer_weightTorus`: the Weyl
  representative belongs to the torus normalizer inside the carrier.

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
  rw [kostantToralWeylPoint]
  simp only [Subgroup.coe_mul, coe_kostantToralRootSubgroupPoints]
  rw [← basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A i
      (Multiplicative.ofAdd 1),
    ← basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A j
      (Multiplicative.ofAdd (-1)),
    ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  apply LinearMap.ext
  intro z
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    kostantRootSubgroupParam_val_apply, kostantRootSubgroupParam_val_apply,
    kostantRootSubgroupParam_val_apply, toAdd_ofAdd, toAdd_ofAdd, kostantWeylGL_val]
  exact LinearMap.congr_fun
    (kostantWeylPoints_toLinearMap_eq e h ρ M hM (hnil i) (hnil j) (A := A)).symm z

/-! ## Normalization of the represented torus -/

variable {i j : I} {c : κ} {α : κ → ℤ}
variable (hT : IsSl2Triple (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (hα : ∀ q, ⁅h q, e i⁆ = (α q : ℚ) • e i)
variable (hαneg : ∀ q, ⁅h q, e j⁆ = -((α q : ℚ) • e j))

include hT in
/-- Conjugation by the carrier's Weyl representative exchanges the two root subgroups of the
`sl₂` pair, negating the parameter: `nᵢ xᵢ(u) nᵢ⁻¹ = xⱼ(-u)`. -/
theorem kostantToralWeylPoint_conj_rootSubgroup (A : Type v) [CommRing A] (u : A) :
    kostantToralWeylPoint e h ρ M hM hnil b wt i j A *
        kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A
          (Multiplicative.ofAdd u) *
        (kostantToralWeylPoint e h ρ M hM hnil b wt i j A)⁻¹ =
      kostantToralRootSubgroupPoints e h ρ M hM hnil b wt j A
        (Multiplicative.ofAdd (-u)) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_kostantToralWeylPoint, coe_kostantToralRootSubgroupPoints,
    coe_kostantToralRootSubgroupPoints,
    ← basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A i
      (Multiplicative.ofAdd u),
    ← basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A j
      (Multiplicative.ofAdd (-u))]
  have hGL :
      kostantWeylGL e h ρ M hM (hnil i) (hnil j) A *
          kostantRootSubgroupParam e h ρ M hM i (hnil i) (CommAlgCat.of ℤ A)
            (Multiplicative.ofAdd u) *
          (kostantWeylGL e h ρ M hM (hnil i) (hnil j) A)⁻¹ =
        kostantRootSubgroupParam e h ρ M hM j (hnil j) (CommAlgCat.of ℤ A)
          (Multiplicative.ofAdd (-u)) := by
    apply Units.ext
    apply LinearMap.ext
    intro z
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      kostantWeylGL_val, kostantWeylGL_inv_val,
      kostantRootSubgroupParam_val_apply, kostantRootSubgroupParam_val_apply,
      toAdd_ofAdd, toAdd_ofAdd]
    exact LinearMap.congr_fun
      (kostantWeylPoints_conj_baseChangeExp e h ρ M hM (hnil i) (hnil j) hT u) z
  simpa only [map_mul, map_inv, MulEquiv.toMonoidHom_eq_coe] using
    congrArg (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom) hGL

include hT hα hαneg in
/-- Conjugating a represented weight-torus point by the carrier's Weyl representative reflects
the torus point by the root `α` and its coroot coordinate `c`. -/
theorem kostantToralWeylPoint_conj_weightTorus
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
theorem kostantToralWeylPoint_mem_normalizer_weightTorus
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    (A : Type v) [CommRing A] :
    kostantToralWeylPoint e h ρ M hM hnil b wt i j A ∈
      Subgroup.normalizer
        (kostantToralWeightTorusPoints e h ρ M hM hnil b wt A).range := by
  classical
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hαc : α c = 2 := rootWeight_apply_coroot_eq_two e h ρ hT (hα c)
  have hconj := kostantToralWeylPoint_conj_weightTorus
    e h ρ M hM hnil b wt hT hα hαneg hwt A
  have hconj' : ∀ s : κ → Aˣ,
      (MulAut.conj (kostantToralWeylPoint e h ρ M hM hnil b wt i j A))
          (kostantToralWeightTorusPoints e h ρ M hM hnil b wt A s) =
        kostantToralWeightTorusPoints e h ρ M hM hnil b wt A
          (weylReflectTorusPoint α c s) :=
    hconj
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, ⟨s, rfl⟩, rfl⟩
    exact ⟨weylReflectTorusPoint α c s, (hconj' s).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨kostantToralWeightTorusPoints e h ρ M hM hnil b wt A
        (weylReflectTorusPoint α c s),
      ⟨weylReflectTorusPoint α c s, rfl⟩, ?_⟩
    exact (hconj' (weylReflectTorusPoint α c s)).trans <|
      congrArg (kostantToralWeightTorusPoints e h ρ M hM hnil b wt A)
        (weylReflectTorusPoint_weylReflectTorusPoint α hαc s)

end TauCeti.UniversalEnvelopingAlgebra
