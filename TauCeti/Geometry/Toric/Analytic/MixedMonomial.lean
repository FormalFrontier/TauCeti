/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.Algebra.BigOperators.ZPow
public import TauCeti.Analysis.Calculus.ContDiffZPow

/-!
# Mixed monomial maps between mixed charts

A *mixed chart* is a product `ℂ ^ k × (ℂ ^ *) ^ l`, the model on which the affine analytic chart
of a regular `k`-dimensional cone in a rank-`(k + l)` lattice is built. The transition maps
between two such charts, and the maps induced by a morphism of fans, are *mixed monomial maps*:
each target coordinate is a product of integral powers of the source coordinates.

The exponents cannot be arbitrary. A source coordinate that is allowed to vanish may only be
raised to a natural power, and it may only contribute to a target coordinate that is itself
allowed to vanish: a monomial containing a boundary coordinate takes the value `0`, so it can
never be one of the invertible coordinates of the target. `MixedExponent` records exactly the
three admissible blocks and, by omitting a fourth field, makes the forbidden contribution
untypeable.

The ambient formula `mixedMonomialMap` is defined on all of `ℂ ^ k × ℂ ^ l`, using the junk value
`(0 : ℂ) ^ (n : ℤ) = 0` for `n < 0`. Every theorem about composing two of these maps is stated on
`mixedChartDomain`, the open locus where the torus coordinates are invertible: exponent arithmetic
needs `y ^ (m + n) = y ^ m * y ^ n`, which fails at `y = 0`, and the composite of two mixed
monomial maps really is a different function off that locus.

## Main declarations

* `TauCeti.Toric.MixedExponent`: the exponent data of a mixed monomial map.
* `TauCeti.Toric.mixedChartDomain`: the open locus where all torus coordinates are invertible.
* `TauCeti.Toric.mixedMonomialMap`: the ambient coordinate formula.
* `TauCeti.Toric.mixedMonomialMap_mapsTo`: a mixed monomial map preserves the mixed-chart locus.
* `TauCeti.Toric.contDiffAt_mixedMonomialMap` and
  `TauCeti.Toric.differentiableOn_mixedMonomialMap`: a mixed monomial map is holomorphic on the
  mixed-chart locus.
* `TauCeti.Toric.MixedExponent.comp` and `TauCeti.Toric.mixedMonomialMap_comp`: composition of
  exponent data is a product of block matrices, and it computes the composite map on the
  mixed-chart locus. `TauCeti.Toric.MixedExponent.id_comp`,
  `TauCeti.Toric.MixedExponent.comp_id` and `TauCeti.Toric.MixedExponent.comp_assoc` are the
  associated category laws.
* `TauCeti.Toric.MixedExponent.prod`, `TauCeti.Toric.mixedChartProdHomeomorph`, and
  `TauCeti.Toric.mixedMonomialMap_prod`: products of exponent data act componentwise on products
  of mixed charts.
* `TauCeti.Toric.hasDerivAt_mixedMonomialMap_fst_boundary`,
  `TauCeti.Toric.hasDerivAt_mixedMonomialMap_fst_torus`,
  `TauCeti.Toric.hasDerivAt_mixedMonomialMap_snd_boundary`, and
  `TauCeti.Toric.hasDerivAt_mixedMonomialMap_snd_torus`: the four blocks of the Jacobian in mixed
  coordinates.
* `TauCeti.Toric.mixedMonomialOpenPartialHomeomorph`: a two-sided inverse pair of exponent data
  gives a biholomorphism between the two mixed-chart loci, holomorphic in both directions by
  `TauCeti.Toric.contDiffOn_mixedMonomialOpenPartialHomeomorph` and
  `TauCeti.Toric.contDiffOn_mixedMonomialOpenPartialHomeomorph_symm`.
* `TauCeti.Toric.MixedExponent.ofTorusBlock` and
  `TauCeti.Toric.basisChangeOpenPartialHomeomorph`: the exponent data that keeps the boundary
  coordinates and acts on the torus coordinates by an integral matrix, and the biholomorphism it
  induces when that matrix is unimodular, holomorphic in both directions by
  `TauCeti.Toric.contDiffOn_basisChangeOpenPartialHomeomorph` and
  `TauCeti.Toric.contDiffOn_basisChangeOpenPartialHomeomorph_symm`. This is the shape of a change
  of the basis extending the primitive ray generators of a regular cone.

## References

The mathematics is §§1.1--1.3 and §3.1 of D. Cox, J. Little and H. Schenck, *Toric Varieties*,
and §§1.2--1.3 of W. Fulton, *Introduction to Toric Varieties*.
-/

public section

namespace TauCeti.Toric

open Finset

variable {k l k' l' k'' l'' : ℕ}

-- Source: the names and the three-block shape of `MixedExponent`, the coordinate formula
-- `mixedMonomialMap`, the locus `mixedChartDomain` and the block-matrix composition law
-- follow the target signatures in `AnalyticToricGeometry/Suggested.lean` of the
-- TauCetiProject/TauCetiRoadmap repository.
/-- Exponent data for a mixed monomial map `ℂ ^ k × (ℂ ^ *) ^ l → ℂ ^ k' × (ℂ ^ *) ^ l'`.

The three blocks are the only admissible ones. A boundary coordinate of the source, which may
vanish, carries a natural exponent and may only enter a boundary coordinate of the target; a torus
coordinate of the source, which is invertible, carries an integral exponent and may enter either
kind of target coordinate. There is deliberately no block from the boundary coordinates of the
source to the torus coordinates of the target: such a monomial would vanish somewhere. -/
@[ext]
structure MixedExponent (k l k' l' : ℕ) where
  /-- Exponents of the source boundary coordinates in the target boundary coordinates. -/
  boundaryBoundary : Matrix (Fin k') (Fin k) ℕ
  /-- Exponents of the source torus coordinates in the target boundary coordinates. -/
  boundaryTorus : Matrix (Fin k') (Fin l) ℤ
  /-- Exponents of the source torus coordinates in the target torus coordinates. -/
  torusTorus : Matrix (Fin l') (Fin l) ℤ

/-- The open locus of a mixed chart: the points whose torus coordinates are all invertible. -/
def mixedChartDomain (k l : ℕ) : Set ((Fin k → ℂ) × (Fin l → ℂ)) := {z | ∀ j, z.2 j ≠ 0}

@[simp]
theorem mem_mixedChartDomain {z : (Fin k → ℂ) × (Fin l → ℂ)} :
    z ∈ mixedChartDomain k l ↔ ∀ j, z.2 j ≠ 0 := Iff.rfl

/-- The mixed-chart domain is open in its ambient affine space. -/
theorem isOpen_mixedChartDomain : IsOpen (mixedChartDomain k l) := by
  have h : mixedChartDomain k l
      = ⋂ j, (fun z : (Fin k → ℂ) × (Fin l → ℂ) ↦ z.2 j) ⁻¹' {0}ᶜ := by
    ext z; simp
  rw [h]
  exact isOpen_iInter_of_finite fun j ↦
    isOpen_compl_singleton.preimage ((continuous_apply j).comp continuous_snd)

/-- The ambient coordinate formula of the mixed monomial map with exponent data `A`. Its
composition laws hold on `mixedChartDomain`, not at ambient points with a vanishing torus
coordinate. -/
noncomputable def mixedMonomialMap (A : MixedExponent k l k' l') :
    ((Fin k → ℂ) × (Fin l → ℂ)) → (Fin k' → ℂ) × (Fin l' → ℂ) := fun z ↦
  (fun a ↦ (∏ b, z.1 b ^ A.boundaryBoundary a b) * ∏ b, z.2 b ^ A.boundaryTorus a b,
    fun a ↦ ∏ b, z.2 b ^ A.torusTorus a b)

@[simp]
theorem mixedMonomialMap_fst_apply (A : MixedExponent k l k' l')
    (z : (Fin k → ℂ) × (Fin l → ℂ)) (a : Fin k') :
    (mixedMonomialMap A z).1 a =
      (∏ b, z.1 b ^ A.boundaryBoundary a b) * ∏ b, z.2 b ^ A.boundaryTorus a b := (rfl)

@[simp]
theorem mixedMonomialMap_snd_apply (A : MixedExponent k l k' l')
    (z : (Fin k → ℂ) × (Fin l → ℂ)) (a : Fin l') :
    (mixedMonomialMap A z).2 a = ∏ b, z.2 b ^ A.torusTorus a b := (rfl)

/-- A torus coordinate of the image of a point of the mixed-chart locus is invertible. -/
theorem mixedMonomialMap_snd_ne_zero (A : MixedExponent k l k' l')
    {z : (Fin k → ℂ) × (Fin l → ℂ)} (hz : z ∈ mixedChartDomain k l) (a : Fin l') :
    (mixedMonomialMap A z).2 a ≠ 0 := by
  rw [mixedMonomialMap_snd_apply]
  exact prod_ne_zero_iff.2 fun b _ ↦ zpow_ne_zero _ (hz b)

/-- A mixed monomial map sends the mixed-chart locus of its source into the mixed-chart locus of
its target. -/
theorem mixedMonomialMap_mapsTo (A : MixedExponent k l k' l') :
    Set.MapsTo (mixedMonomialMap A) (mixedChartDomain k l) (mixedChartDomain k' l') :=
  fun _ hz _ ↦ mixedMonomialMap_snd_ne_zero A hz _

/-- On the mixed-chart locus a boundary coordinate of the image vanishes exactly when one of the
source boundary coordinates occurring in it vanishes. -/
theorem mixedMonomialMap_fst_eq_zero_iff (A : MixedExponent k l k' l')
    {z : (Fin k → ℂ) × (Fin l → ℂ)} (hz : z ∈ mixedChartDomain k l) (a : Fin k') :
    (mixedMonomialMap A z).1 a = 0 ↔ ∃ b, z.1 b = 0 ∧ A.boundaryBoundary a b ≠ 0 := by
  rw [mixedMonomialMap_fst_apply, mul_eq_zero, or_iff_left
    (prod_ne_zero_iff.2 fun b _ ↦ zpow_ne_zero _ (hz b)), prod_eq_zero_iff]
  simp [pow_eq_zero_iff']

/-! ### Composition of exponent data -/

namespace MixedExponent

/-- The exponent data of the identity of a mixed chart. -/
protected def id (k l : ℕ) : MixedExponent k l k l where
  boundaryBoundary := 1
  boundaryTorus := 0
  torusTorus := 1

@[simp] theorem id_boundaryBoundary : (MixedExponent.id k l).boundaryBoundary = 1 := (rfl)
@[simp] theorem id_boundaryTorus : (MixedExponent.id k l).boundaryTorus = 0 := (rfl)
@[simp] theorem id_torusTorus : (MixedExponent.id k l).torusTorus = 1 := (rfl)

/-- Composition of exponent data. The exponents of the source torus coordinates in the target
boundary coordinates receive a contribution from each of the two blocks of `B` that land in a
boundary coordinate. -/
protected def comp (B : MixedExponent k' l' k'' l'') (A : MixedExponent k l k' l') :
    MixedExponent k l k'' l'' where
  boundaryBoundary := B.boundaryBoundary * A.boundaryBoundary
  boundaryTorus :=
    B.boundaryBoundary.map (Nat.cast : ℕ → ℤ) * A.boundaryTorus + B.boundaryTorus * A.torusTorus
  torusTorus := B.torusTorus * A.torusTorus

@[simp]
theorem comp_boundaryBoundary (B : MixedExponent k' l' k'' l'') (A : MixedExponent k l k' l') :
    (B.comp A).boundaryBoundary = B.boundaryBoundary * A.boundaryBoundary := (rfl)

@[simp]
theorem comp_boundaryTorus (B : MixedExponent k' l' k'' l'') (A : MixedExponent k l k' l') :
    (B.comp A).boundaryTorus =
      B.boundaryBoundary.map (Nat.cast : ℕ → ℤ) * A.boundaryTorus +
        B.boundaryTorus * A.torusTorus := (rfl)

@[simp]
theorem comp_torusTorus (B : MixedExponent k' l' k'' l'') (A : MixedExponent k l k' l') :
    (B.comp A).torusTorus = B.torusTorus * A.torusTorus := (rfl)

/-- The identity exponent data is a left unit for composition. -/
@[simp]
theorem id_comp (A : MixedExponent k l k' l') : (MixedExponent.id k' l').comp A = A :=
  MixedExponent.ext (by simp) (by simp [Matrix.map_one _ Nat.cast_zero Nat.cast_one]) (by simp)

/-- The identity exponent data is a right unit for composition. -/
@[simp]
theorem comp_id (A : MixedExponent k l k' l') : A.comp (MixedExponent.id k l) = A :=
  MixedExponent.ext (by simp) (by simp) (by simp)

/-- Composition of exponent data is associative. -/
theorem comp_assoc {k''' l''' : ℕ} (C : MixedExponent k'' l'' k''' l''')
    (B : MixedExponent k' l' k'' l'') (A : MixedExponent k l k' l') :
    (C.comp B).comp A = C.comp (B.comp A) :=
  MixedExponent.ext (Matrix.mul_assoc _ _ _)
    (by
      simp only [comp_boundaryTorus, comp_boundaryBoundary, comp_torusTorus]
      have hmap :
          (C.boundaryBoundary * B.boundaryBoundary).map (Nat.cast : ℕ → ℤ) =
            C.boundaryBoundary.map Nat.cast * B.boundaryBoundary.map Nat.cast := by
        simpa only [Nat.coe_castRingHom] using
          (Matrix.map_mul (L := C.boundaryBoundary) (M := B.boundaryBoundary)
            (f := Nat.castRingHom ℤ))
      rw [hmap]
      simp [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc])
    (Matrix.mul_assoc _ _ _)

/-- The product of mixed exponent data is the block diagonal exponent data. -/
def prod {k₁ l₁ k₁' l₁' k₂ l₂ k₂' l₂' : ℕ}
    (A : MixedExponent k₁ l₁ k₁' l₁') (B : MixedExponent k₂ l₂ k₂' l₂') :
    MixedExponent (k₁ + k₂) (l₁ + l₂) (k₁' + k₂') (l₁' + l₂') where
  boundaryBoundary :=
    (Matrix.fromBlocks A.boundaryBoundary 0 0 B.boundaryBoundary).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm
  boundaryTorus :=
    (Matrix.fromBlocks A.boundaryTorus 0 0 B.boundaryTorus).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm
  torusTorus :=
    (Matrix.fromBlocks A.torusTorus 0 0 B.torusTorus).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm

@[simp]
theorem prod_boundaryBoundary {k₁ l₁ k₁' l₁' k₂ l₂ k₂' l₂' : ℕ}
    (A : MixedExponent k₁ l₁ k₁' l₁') (B : MixedExponent k₂ l₂ k₂' l₂') :
    (A.prod B).boundaryBoundary =
      (Matrix.fromBlocks A.boundaryBoundary 0 0 B.boundaryBoundary).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := (rfl)

@[simp]
theorem prod_boundaryTorus {k₁ l₁ k₁' l₁' k₂ l₂ k₂' l₂' : ℕ}
    (A : MixedExponent k₁ l₁ k₁' l₁') (B : MixedExponent k₂ l₂ k₂' l₂') :
    (A.prod B).boundaryTorus =
      (Matrix.fromBlocks A.boundaryTorus 0 0 B.boundaryTorus).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := (rfl)

@[simp]
theorem prod_torusTorus {k₁ l₁ k₁' l₁' k₂ l₂ k₂' l₂' : ℕ}
    (A : MixedExponent k₁ l₁ k₁' l₁') (B : MixedExponent k₂ l₂ k₂' l₂') :
    (A.prod B).torusTorus =
      (Matrix.fromBlocks A.torusTorus 0 0 B.torusTorus).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := (rfl)

end MixedExponent

/-! ### Composition of mixed monomial maps -/

/-- The identity exponent data induces the identity map, at every ambient point. -/
@[simp]
theorem mixedMonomialMap_id : mixedMonomialMap (MixedExponent.id k l) = id := by
  have hone : ∀ {m : ℕ} (w : Fin m → ℂ) (a : Fin m),
      ∏ b, w b ^ ((1 : Matrix (Fin m) (Fin m) ℕ) a b) = w a := by
    intro m w a
    rw [prod_eq_single a (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
    simp
  have honeZ : ∀ {m : ℕ} (w : Fin m → ℂ) (a : Fin m),
      ∏ b, w b ^ ((1 : Matrix (Fin m) (Fin m) ℤ) a b) = w a := by
    intro m w a
    rw [prod_eq_single a (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
    simp
  funext z
  refine Prod.ext (funext fun a ↦ ?_) (funext fun a ↦ ?_)
  · simp [hone z.1 a]
  · simp [honeZ z.2 a]

/-- Composing two mixed monomial maps multiplies their exponent data, on the locus where the torus
coordinates are invertible. No such formula is claimed at ambient points with a vanishing torus
coordinate. -/
@[simp]
theorem mixedMonomialMap_comp (B : MixedExponent k' l' k'' l'') (A : MixedExponent k l k' l')
    {z : (Fin k → ℂ) × (Fin l → ℂ)} (hz : z ∈ mixedChartDomain k l) :
    mixedMonomialMap (B.comp A) z = mixedMonomialMap B (mixedMonomialMap A z) := by
  have hy : ∀ b, z.2 b ≠ 0 := hz
  refine Prod.ext (funext fun c ↦ ?_) (funext fun c ↦ ?_)
  · have hbb := prod_prod_pow univ univ z.1 A.boundaryBoundary (B.boundaryBoundary c)
    have hbt := prod_prod_zpow_pow univ univ (fun b _ ↦ hy b) A.boundaryTorus
      (B.boundaryBoundary c)
    have htt := prod_prod_zpow univ univ (fun b _ ↦ hy b) A.torusTorus (B.boundaryTorus c)
    simp only [mixedMonomialMap_fst_apply, mixedMonomialMap_snd_apply, mul_pow,
      prod_mul_distrib, MixedExponent.comp_boundaryBoundary, MixedExponent.comp_boundaryTorus,
      Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply]
    rw [hbb, hbt, htt, mul_assoc, ← prod_mul_distrib]
    exact congrArg _ (prod_congr rfl fun b _ ↦ zpow_add₀ (hy b) _ _)
  · have htt := prod_prod_zpow univ univ (fun b _ ↦ hy b) A.torusTorus (B.torusTorus c)
    simp only [mixedMonomialMap_snd_apply, MixedExponent.comp_torusTorus, Matrix.mul_apply]
    rw [htt]

/-! ### Products -/

/-- Splitting the boundary and torus coordinates identifies the mixed chart of the sum of two
dimensions with the product of the two mixed charts. -/
noncomputable def mixedChartProdHomeomorph {k₁ l₁ k₂ l₂ : ℕ} :
    ((Fin (k₁ + k₂) → ℂ) × (Fin (l₁ + l₂) → ℂ)) ≃ₜ
      (((Fin k₁ → ℂ) × (Fin l₁ → ℂ)) × ((Fin k₂ → ℂ) × (Fin l₂ → ℂ))) :=
  ((Fin.appendHomeomorph (X := ℂ) k₁ k₂).symm.prodCongr
    (Fin.appendHomeomorph (X := ℂ) l₁ l₂).symm).trans
      (Homeomorph.prodProdProdComm _ _ _ _)

@[simp]
theorem mixedChartProdHomeomorph_apply {k₁ l₁ k₂ l₂ : ℕ}
    (z : (Fin (k₁ + k₂) → ℂ) × (Fin (l₁ + l₂) → ℂ)) :
    mixedChartProdHomeomorph z =
      (((fun i ↦ z.1 (Fin.castAdd k₂ i)), fun i ↦ z.2 (Fin.castAdd l₂ i)),
        ((fun i ↦ z.1 (Fin.natAdd k₁ i)), fun i ↦ z.2 (Fin.natAdd l₁ i))) := (rfl)

@[simp]
theorem mixedChartProdHomeomorph_symm_apply {k₁ l₁ k₂ l₂ : ℕ}
    (z : ((Fin k₁ → ℂ) × (Fin l₁ → ℂ)) × ((Fin k₂ → ℂ) × (Fin l₂ → ℂ))) :
    mixedChartProdHomeomorph.symm z =
      (Fin.addCases z.1.1 z.2.1, Fin.addCases z.1.2 z.2.2) := (rfl)

/-- The canonical coordinate splitting identifies the mixed-chart domain of the summed dimensions
with the product of the two mixed-chart domains. -/
@[simp]
theorem mixedChartProdHomeomorph_preimage_prod {k₁ l₁ k₂ l₂ : ℕ} :
    mixedChartProdHomeomorph ⁻¹' (mixedChartDomain k₁ l₁ ×ˢ mixedChartDomain k₂ l₂) =
      mixedChartDomain (k₁ + k₂) (l₁ + l₂) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_prod, mem_mixedChartDomain,
    mixedChartProdHomeomorph_apply]
  constructor
  · rintro ⟨h₁, h₂⟩ j
    exact Fin.addCases h₁ h₂ j
  · intro h
    exact ⟨fun i ↦ h (Fin.castAdd l₂ i), fun i ↦ h (Fin.natAdd l₁ i)⟩

/-- The mixed monomial map of block diagonal product exponent data is the product of the two
mixed monomial maps, under the canonical splitting of mixed-chart coordinates. -/
theorem mixedMonomialMap_prod {k₁ l₁ k₁' l₁' k₂ l₂ k₂' l₂' : ℕ}
    (A : MixedExponent k₁ l₁ k₁' l₁') (B : MixedExponent k₂ l₂ k₂' l₂')
    (z : (Fin (k₁ + k₂) → ℂ) × (Fin (l₁ + l₂) → ℂ)) :
    mixedChartProdHomeomorph (mixedMonomialMap (A.prod B) z) =
      (mixedMonomialMap A (mixedChartProdHomeomorph z).1,
        mixedMonomialMap B (mixedChartProdHomeomorph z).2) := by
  ext i <;>
    simp [mixedMonomialMap, MixedExponent.prod, Fin.prod_univ_add, Matrix.fromBlocks]

/-! ### Holomorphy -/

variable {n : WithTop ℕ∞}

/-- A mixed monomial map is holomorphic at every point of the mixed-chart locus, to any order. -/
theorem contDiffAt_mixedMonomialMap (A : MixedExponent k l k' l')
    {z : (Fin k → ℂ) × (Fin l → ℂ)} (hz : z ∈ mixedChartDomain k l) :
    ContDiffAt ℂ n (mixedMonomialMap A) z := by
  have hx : ∀ b, ContDiffAt ℂ n (fun w : (Fin k → ℂ) × (Fin l → ℂ) ↦ w.1 b) z :=
    fun b ↦ contDiffAt_pi.mp contDiffAt_fst b
  have hy : ∀ b, ContDiffAt ℂ n (fun w : (Fin k → ℂ) × (Fin l → ℂ) ↦ w.2 b) z :=
    fun b ↦ contDiffAt_pi.mp contDiffAt_snd b
  refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun a ↦ ?_) (contDiffAt_pi.mpr fun a ↦ ?_)
  · exact (contDiffAt_prod fun b _ ↦ (hx b).pow _).mul
      (contDiffAt_prod fun b _ ↦ (hy b).zpow (Or.inl (hz b)))
  · exact contDiffAt_prod fun b _ ↦ (hy b).zpow (Or.inl (hz b))

/-- A mixed monomial map is holomorphic on the mixed-chart locus, to any order. -/
theorem contDiffOn_mixedMonomialMap (A : MixedExponent k l k' l') :
    ContDiffOn ℂ n (mixedMonomialMap A) (mixedChartDomain k l) :=
  fun _ hz ↦ (contDiffAt_mixedMonomialMap A hz).contDiffWithinAt

/-- A mixed monomial map is complex differentiable on the mixed-chart locus. -/
theorem differentiableOn_mixedMonomialMap (A : MixedExponent k l k' l') :
    DifferentiableOn ℂ (mixedMonomialMap A) (mixedChartDomain k l) :=
  fun _ hz ↦ ((contDiffAt_mixedMonomialMap (n := 1) A hz).differentiableAt
    one_ne_zero).differentiableWithinAt

/-! ### Jacobian entries -/

/-- The boundary-to-boundary block of the Jacobian of a mixed monomial map. The formula remains
valid when the boundary coordinate vanishes. -/
theorem hasDerivAt_mixedMonomialMap_fst_boundary (A : MixedExponent k l k' l')
    (z : (Fin k → ℂ) × (Fin l → ℂ)) (a : Fin k') (b : Fin k) :
    HasDerivAt
      (fun t ↦ (mixedMonomialMap A (Function.update z.1 b t, z.2)).1 a)
      ((A.boundaryBoundary a b : ℂ) * z.1 b ^ (A.boundaryBoundary a b - 1) *
        ((∏ c ∈ univ \ {b}, z.1 c ^ A.boundaryBoundary a c) *
          ∏ c, z.2 c ^ A.boundaryTorus a c)) (z.1 b) := by
  have hfun : (fun t ↦ (mixedMonomialMap A (Function.update z.1 b t, z.2)).1 a) =
      (fun t ↦ t ^ A.boundaryBoundary a b *
        ((∏ c ∈ univ \ {b}, z.1 c ^ A.boundaryBoundary a c) *
          ∏ c, z.2 c ^ A.boundaryTorus a c)) := by
    funext t
    simp only [mixedMonomialMap_fst_apply]
    rw [funext fun j ↦
        Function.apply_update (fun i (w : ℂ) ↦ w ^ A.boundaryBoundary a i) z.1 b t j,
      prod_update_of_mem (mem_univ b)]
    simp only [mul_assoc]
  rw [hfun]
  exact (hasDerivAt_pow (A.boundaryBoundary a b) (z.1 b)).mul_const
    ((∏ c ∈ univ \ {b}, z.1 c ^ A.boundaryBoundary a c) *
      ∏ c, z.2 c ^ A.boundaryTorus a c)

/-- The torus-to-boundary block of the Jacobian of a mixed monomial map, on the mixed-chart
domain. -/
theorem hasDerivAt_mixedMonomialMap_fst_torus (A : MixedExponent k l k' l')
    {z : (Fin k → ℂ) × (Fin l → ℂ)} (hz : z ∈ mixedChartDomain k l)
    (a : Fin k') (b : Fin l) :
    HasDerivAt
      (fun t ↦ (mixedMonomialMap A (z.1, Function.update z.2 b t)).1 a)
      ((A.boundaryTorus a b : ℂ) * z.2 b ^ (A.boundaryTorus a b - 1) *
        ((∏ c, z.1 c ^ A.boundaryBoundary a c) *
          ∏ c ∈ univ \ {b}, z.2 c ^ A.boundaryTorus a c)) (z.2 b) := by
  have hfun : (fun t ↦ (mixedMonomialMap A (z.1, Function.update z.2 b t)).1 a) =
      (fun t ↦ (∏ c, z.1 c ^ A.boundaryBoundary a c) *
        (t ^ A.boundaryTorus a b *
          ∏ c ∈ univ \ {b}, z.2 c ^ A.boundaryTorus a c)) := by
    funext t
    simp only [mixedMonomialMap_fst_apply]
    rw [funext fun j ↦
        Function.apply_update (fun i (w : ℂ) ↦ w ^ A.boundaryTorus a i) z.2 b t j,
      prod_update_of_mem (mem_univ b)]
  rw [hfun]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    ((hasDerivAt_zpow (A.boundaryTorus a b) (z.2 b) (Or.inl (hz b))).mul_const
      (∏ c ∈ univ \ {b}, z.2 c ^ A.boundaryTorus a c)).const_mul
        (∏ c, z.1 c ^ A.boundaryBoundary a c)

/-- The boundary-to-torus block of the Jacobian of a mixed monomial map is zero. -/
theorem hasDerivAt_mixedMonomialMap_snd_boundary (A : MixedExponent k l k' l')
    (z : (Fin k → ℂ) × (Fin l → ℂ)) (a : Fin l') (b : Fin k) :
    HasDerivAt (fun t ↦ (mixedMonomialMap A (Function.update z.1 b t, z.2)).2 a) 0
      (z.1 b) := by
  simpa only [mixedMonomialMap_snd_apply] using
    (hasDerivAt_const (x := z.1 b) (c := ∏ c, z.2 c ^ A.torusTorus a c))

/-- The torus-to-torus block of the Jacobian of a mixed monomial map, on the mixed-chart domain. -/
theorem hasDerivAt_mixedMonomialMap_snd_torus (A : MixedExponent k l k' l')
    {z : (Fin k → ℂ) × (Fin l → ℂ)} (hz : z ∈ mixedChartDomain k l)
    (a : Fin l') (b : Fin l) :
    HasDerivAt
      (fun t ↦ (mixedMonomialMap A (z.1, Function.update z.2 b t)).2 a)
      ((A.torusTorus a b : ℂ) * z.2 b ^ (A.torusTorus a b - 1) *
        ∏ c ∈ univ \ {b}, z.2 c ^ A.torusTorus a c) (z.2 b) := by
  have hfun : (fun t ↦ (mixedMonomialMap A (z.1, Function.update z.2 b t)).2 a) =
      (fun t ↦ t ^ A.torusTorus a b *
        ∏ c ∈ univ \ {b}, z.2 c ^ A.torusTorus a c) := by
    funext t
    simp only [mixedMonomialMap_snd_apply]
    rw [funext fun j ↦
        Function.apply_update (fun i (w : ℂ) ↦ w ^ A.torusTorus a i) z.2 b t j,
      prod_update_of_mem (mem_univ b)]
  rw [hfun]
  exact (hasDerivAt_zpow (A.torusTorus a b) (z.2 b) (Or.inl (hz b))).mul_const
    (∏ c ∈ univ \ {b}, z.2 c ^ A.torusTorus a c)

/-! ### Biholomorphisms between mixed charts -/

/-- A two-sided inverse pair of exponent data induces a homeomorphism between the two mixed-chart
loci. It is a biholomorphism by `contDiffOn_mixedMonomialOpenPartialHomeomorph` and
`contDiffOn_mixedMonomialOpenPartialHomeomorph_symm`. -/
noncomputable def mixedMonomialOpenPartialHomeomorph (A : MixedExponent k l k' l')
    (B : MixedExponent k' l' k l) (hBA : B.comp A = MixedExponent.id k l)
    (hAB : A.comp B = MixedExponent.id k' l') :
    OpenPartialHomeomorph ((Fin k → ℂ) × (Fin l → ℂ)) ((Fin k' → ℂ) × (Fin l' → ℂ)) where
  toFun := mixedMonomialMap A
  invFun := mixedMonomialMap B
  source := mixedChartDomain k l
  target := mixedChartDomain k' l'
  map_source' := mixedMonomialMap_mapsTo A
  map_target' := mixedMonomialMap_mapsTo B
  left_inv' z hz := by
    have h := mixedMonomialMap_comp B A hz
    rw [hBA, mixedMonomialMap_id] at h
    exact h.symm
  right_inv' w hw := by
    have h := mixedMonomialMap_comp A B hw
    rw [hAB, mixedMonomialMap_id] at h
    exact h.symm
  open_source := isOpen_mixedChartDomain
  open_target := isOpen_mixedChartDomain
  continuousOn_toFun := (differentiableOn_mixedMonomialMap A).continuousOn
  continuousOn_invFun := (differentiableOn_mixedMonomialMap B).continuousOn

section

variable (A : MixedExponent k l k' l') (B : MixedExponent k' l' k l)
  (hBA : B.comp A = MixedExponent.id k l) (hAB : A.comp B = MixedExponent.id k' l')

@[simp]
theorem mixedMonomialOpenPartialHomeomorph_coe :
    ⇑(mixedMonomialOpenPartialHomeomorph A B hBA hAB) = mixedMonomialMap A := (rfl)

@[simp]
theorem mixedMonomialOpenPartialHomeomorph_symm_coe :
    ⇑(mixedMonomialOpenPartialHomeomorph A B hBA hAB).symm = mixedMonomialMap B := (rfl)

@[simp]
theorem mixedMonomialOpenPartialHomeomorph_source :
    (mixedMonomialOpenPartialHomeomorph A B hBA hAB).source = mixedChartDomain k l := (rfl)

@[simp]
theorem mixedMonomialOpenPartialHomeomorph_target :
    (mixedMonomialOpenPartialHomeomorph A B hBA hAB).target = mixedChartDomain k' l' := (rfl)

/-- An inverse pair of exponent data induces a biholomorphism: the induced homeomorphism is
holomorphic, to any order. -/
theorem contDiffOn_mixedMonomialOpenPartialHomeomorph :
    ContDiffOn ℂ n (mixedMonomialOpenPartialHomeomorph A B hBA hAB)
      (mixedMonomialOpenPartialHomeomorph A B hBA hAB).source := by
  simpa only [mixedMonomialOpenPartialHomeomorph_coe, mixedMonomialOpenPartialHomeomorph_source]
    using contDiffOn_mixedMonomialMap A

/-- An inverse pair of exponent data induces a biholomorphism: the inverse of the induced
homeomorphism is holomorphic, to any order. -/
theorem contDiffOn_mixedMonomialOpenPartialHomeomorph_symm :
    ContDiffOn ℂ n (mixedMonomialOpenPartialHomeomorph A B hBA hAB).symm
      (mixedMonomialOpenPartialHomeomorph A B hBA hAB).target := by
  simpa only [mixedMonomialOpenPartialHomeomorph_symm_coe,
    mixedMonomialOpenPartialHomeomorph_target] using contDiffOn_mixedMonomialMap B

end

/-! ### Changing the basis extending the primitive ray generators -/

namespace MixedExponent

/-- The exponent data of a self-map of a mixed chart that keeps the boundary coordinates, twists
them by the integral matrix `C`, and acts on the torus coordinates by the integral matrix `D`.
Two bases of the lattice extending the primitive ray generators of a regular cone differ by
exactly such a block, with `D` unimodular. -/
def ofTorusBlock (C : Matrix (Fin k) (Fin l) ℤ) (D : Matrix (Fin l) (Fin l) ℤ) :
    MixedExponent k l k l where
  boundaryBoundary := 1
  boundaryTorus := C
  torusTorus := D

@[simp]
theorem ofTorusBlock_boundaryBoundary (C : Matrix (Fin k) (Fin l) ℤ)
    (D : Matrix (Fin l) (Fin l) ℤ) : (ofTorusBlock C D).boundaryBoundary = 1 := (rfl)

@[simp]
theorem ofTorusBlock_boundaryTorus (C : Matrix (Fin k) (Fin l) ℤ)
    (D : Matrix (Fin l) (Fin l) ℤ) : (ofTorusBlock C D).boundaryTorus = C := (rfl)

@[simp]
theorem ofTorusBlock_torusTorus (C : Matrix (Fin k) (Fin l) ℤ)
    (D : Matrix (Fin l) (Fin l) ℤ) : (ofTorusBlock C D).torusTorus = D := (rfl)

@[simp]
theorem ofTorusBlock_zero_one : ofTorusBlock (0 : Matrix (Fin k) (Fin l) ℤ) 1 =
    MixedExponent.id k l := (rfl)

/-- Composing the torus-block data `(C, D)` followed by `(C', D')` gives boundary twist
`C + C' * D` and torus block `D' * D`. -/
@[simp]
theorem ofTorusBlock_comp_ofTorusBlock (C C' : Matrix (Fin k) (Fin l) ℤ)
    (D D' : Matrix (Fin l) (Fin l) ℤ) :
    (ofTorusBlock C' D').comp (ofTorusBlock C D) = ofTorusBlock (C + C' * D) (D' * D) :=
  MixedExponent.ext (by simp) (by simp [Matrix.map_one _ Nat.cast_zero Nat.cast_one]) (by simp)

/-- A unimodular torus block gives an inverse pair of exponent data. -/
theorem ofTorusBlock_comp_eq_id_of_mul_eq_one (C : Matrix (Fin k) (Fin l) ℤ)
    {D D' : Matrix (Fin l) (Fin l) ℤ} (h : D' * D = 1) :
    (ofTorusBlock (-(C * D')) D').comp (ofTorusBlock C D) = MixedExponent.id k l := by
  simp [Matrix.mul_assoc, h]

end MixedExponent

/-- The biholomorphism of a mixed chart induced by a unimodular change of the basis extending the
primitive ray generators: the boundary coordinates are kept and twisted by `C`, and the torus
coordinates are transformed by the unimodular matrix `D`. -/
noncomputable def basisChangeOpenPartialHomeomorph (C : Matrix (Fin k) (Fin l) ℤ)
    (D : Matrix (Fin l) (Fin l) ℤ) (hD : IsUnit D.det) :
    OpenPartialHomeomorph ((Fin k → ℂ) × (Fin l → ℂ)) ((Fin k → ℂ) × (Fin l → ℂ)) :=
  mixedMonomialOpenPartialHomeomorph (MixedExponent.ofTorusBlock C D)
    (MixedExponent.ofTorusBlock (-(C * D⁻¹)) D⁻¹)
    (MixedExponent.ofTorusBlock_comp_eq_id_of_mul_eq_one C (Matrix.nonsing_inv_mul D hD))
    (by simp [Matrix.mul_nonsing_inv D hD])

section

variable (C : Matrix (Fin k) (Fin l) ℤ) (D : Matrix (Fin l) (Fin l) ℤ)
  (hD : IsUnit D.det)

@[simp]
theorem basisChangeOpenPartialHomeomorph_coe :
    ⇑(basisChangeOpenPartialHomeomorph C D hD) =
      mixedMonomialMap (MixedExponent.ofTorusBlock C D) := (rfl)

@[simp]
theorem basisChangeOpenPartialHomeomorph_symm_coe :
    ⇑(basisChangeOpenPartialHomeomorph C D hD).symm =
      mixedMonomialMap (MixedExponent.ofTorusBlock (-(C * D⁻¹)) D⁻¹) := (rfl)

@[simp]
theorem basisChangeOpenPartialHomeomorph_source :
    (basisChangeOpenPartialHomeomorph C D hD).source = mixedChartDomain k l := (rfl)

@[simp]
theorem basisChangeOpenPartialHomeomorph_target :
    (basisChangeOpenPartialHomeomorph C D hD).target = mixedChartDomain k l := (rfl)

/-- A unimodular change of the extending basis induces a biholomorphism: the induced homeomorphism
is holomorphic, to any order. -/
theorem contDiffOn_basisChangeOpenPartialHomeomorph :
    ContDiffOn ℂ n (basisChangeOpenPartialHomeomorph C D hD)
      (basisChangeOpenPartialHomeomorph C D hD).source := by
  simpa only [basisChangeOpenPartialHomeomorph_coe, basisChangeOpenPartialHomeomorph_source]
    using contDiffOn_mixedMonomialMap (MixedExponent.ofTorusBlock C D)

/-- A unimodular change of the extending basis induces a biholomorphism: the inverse of the induced
homeomorphism is holomorphic, to any order. -/
theorem contDiffOn_basisChangeOpenPartialHomeomorph_symm :
    ContDiffOn ℂ n (basisChangeOpenPartialHomeomorph C D hD).symm
      (basisChangeOpenPartialHomeomorph C D hD).target := by
  simpa only [basisChangeOpenPartialHomeomorph_symm_coe, basisChangeOpenPartialHomeomorph_target]
    using contDiffOn_mixedMonomialMap (MixedExponent.ofTorusBlock (-(C * D⁻¹)) D⁻¹)

end

end TauCeti.Toric
