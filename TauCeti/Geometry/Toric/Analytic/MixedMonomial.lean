/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

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
* `TauCeti.Toric.mixedMonomialMap_contDiffAt` and
  `TauCeti.Toric.mixedMonomialMap_differentiableOn`: a mixed monomial map is holomorphic on the
  mixed-chart locus.
* `TauCeti.Toric.MixedExponent.comp` and `TauCeti.Toric.mixedMonomialMap_comp`: composition of
  exponent data is a product of block matrices, and it computes the composite map on the
  mixed-chart locus. `TauCeti.Toric.MixedExponent.id_comp`,
  `TauCeti.Toric.MixedExponent.comp_id` and `TauCeti.Toric.MixedExponent.comp_assoc` are the
  associated category laws.
* `TauCeti.Toric.mixedMonomialOpenPartialHomeomorph`: a two-sided inverse pair of exponent data
  gives a biholomorphism between the two mixed-chart loci, holomorphic in both directions by
  `TauCeti.Toric.mixedMonomialOpenPartialHomeomorph_contDiffOn` and
  `TauCeti.Toric.mixedMonomialOpenPartialHomeomorph_symm_contDiffOn`.
* `TauCeti.Toric.MixedExponent.ofTorusBlock` and
  `TauCeti.Toric.basisChangeOpenPartialHomeomorph`: the exponent data that keeps the boundary
  coordinates and acts on the torus coordinates by an integral matrix, and the biholomorphism it
  induces when that matrix is unimodular. This is the shape of a change of the basis extending
  the primitive ray generators of a regular cone.

## References

The mathematics is §§1.1--1.3 and §3.1 of D. Cox, J. Little and H. Schenck, *Toric Varieties*,
and §§1.2--1.3 of W. Fulton, *Introduction to Toric Varieties*.
-/

public section

namespace TauCeti.Toric

open Finset

variable {k l k' l' k'' l'' : ℕ}

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

@[simp]
theorem id_comp (A : MixedExponent k l k' l') : (MixedExponent.id k' l').comp A = A :=
  MixedExponent.ext (by simp) (by simp [Matrix.map_one _ Nat.cast_zero Nat.cast_one]) (by simp)

@[simp]
theorem comp_id (A : MixedExponent k l k' l') : A.comp (MixedExponent.id k l) = A :=
  MixedExponent.ext (by simp) (by simp) (by simp)

/-- Casting the boundary block to `ℤ` is multiplicative. -/
private theorem map_natCast_mul {m p q : ℕ} (L : Matrix (Fin m) (Fin p) ℕ)
    (M : Matrix (Fin p) (Fin q) ℕ) :
    (L * M).map (Nat.cast : ℕ → ℤ) = L.map Nat.cast * M.map Nat.cast :=
  Matrix.map_mul (f := Nat.castRingHom ℤ)

theorem comp_assoc (C : MixedExponent k'' l'' k l) (B : MixedExponent k' l' k'' l'')
    (A : MixedExponent k l k' l') : (C.comp B).comp A = C.comp (B.comp A) :=
  MixedExponent.ext (Matrix.mul_assoc _ _ _)
    (by simp [map_natCast_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc])
    (Matrix.mul_assoc _ _ _)

end MixedExponent

/-! ### Composition of mixed monomial maps -/

/-- A product of integral powers of one invertible complex number collapses to a single power. -/
private theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) {y : ℂ} (hy : y ≠ 0)
    (e : ι → ℤ) : ∏ i ∈ s, y ^ e i = y ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [prod_cons, sum_cons, ih, zpow_add₀ hy]

/-- The exponent bookkeeping of a composite monomial in invertible coordinates. -/
private theorem prod_prod_zpow {m : ℕ} {y : Fin l → ℂ} (hy : ∀ b, y b ≠ 0)
    (e : Fin m → Fin l → ℤ) (g : Fin m → ℤ) :
    ∏ a, (∏ b, y b ^ e a b) ^ g a = ∏ b, y b ^ ∑ a, g a * e a b := by
  calc ∏ a, (∏ b, y b ^ e a b) ^ g a = ∏ b, ∏ a, y b ^ (g a * e a b) := by
        rw [Finset.prod_comm]
        exact prod_congr rfl fun a _ ↦ by
          rw [← Finset.prod_zpow]
          exact prod_congr rfl fun b _ ↦ by rw [← zpow_mul, mul_comm]
    _ = ∏ b, y b ^ ∑ a, g a * e a b :=
        prod_congr rfl fun b _ ↦ prod_zpow_eq_zpow_sum _ (hy b) _

/-- The exponent bookkeeping of a composite monomial in invertible coordinates raised to natural
powers. -/
private theorem prod_prod_zpow_pow {m : ℕ} {y : Fin l → ℂ} (hy : ∀ b, y b ≠ 0)
    (e : Fin m → Fin l → ℤ) (g : Fin m → ℕ) :
    ∏ a, (∏ b, y b ^ e a b) ^ g a = ∏ b, y b ^ ∑ a, (g a : ℤ) * e a b := by
  rw [← prod_prod_zpow hy e fun a ↦ (g a : ℤ)]
  exact prod_congr rfl fun a _ ↦ (zpow_natCast _ _).symm

/-- The exponent bookkeeping of a composite monomial in the boundary coordinates. -/
private theorem prod_prod_pow {m : ℕ} (x : Fin k → ℂ) (e : Fin m → Fin k → ℕ) (g : Fin m → ℕ) :
    ∏ a, (∏ b, x b ^ e a b) ^ g a = ∏ b, x b ^ ∑ a, g a * e a b := by
  calc ∏ a, (∏ b, x b ^ e a b) ^ g a = ∏ b, ∏ a, x b ^ (g a * e a b) := by
        rw [Finset.prod_comm]
        exact prod_congr rfl fun a _ ↦ by
          rw [← Finset.prod_pow]
          exact prod_congr rfl fun b _ ↦ by rw [← pow_mul, mul_comm]
    _ = ∏ b, x b ^ ∑ a, g a * e a b :=
        prod_congr rfl fun b _ ↦ prod_pow_eq_pow_sum _ _ _

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
theorem mixedMonomialMap_comp (B : MixedExponent k' l' k'' l'') (A : MixedExponent k l k' l')
    {z : (Fin k → ℂ) × (Fin l → ℂ)} (hz : z ∈ mixedChartDomain k l) :
    mixedMonomialMap (B.comp A) z = mixedMonomialMap B (mixedMonomialMap A z) := by
  have hy : ∀ b, z.2 b ≠ 0 := hz
  refine Prod.ext (funext fun c ↦ ?_) (funext fun c ↦ ?_)
  · have hbb := prod_prod_pow z.1 A.boundaryBoundary (B.boundaryBoundary c)
    have hbt := prod_prod_zpow_pow hy A.boundaryTorus (B.boundaryBoundary c)
    have htt := prod_prod_zpow hy A.torusTorus (B.boundaryTorus c)
    simp only [mixedMonomialMap_fst_apply, mixedMonomialMap_snd_apply, mul_pow,
      prod_mul_distrib, MixedExponent.comp_boundaryBoundary, MixedExponent.comp_boundaryTorus,
      Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply]
    rw [hbb, hbt, htt, mul_assoc, ← prod_mul_distrib]
    exact congrArg _ (prod_congr rfl fun b _ ↦ zpow_add₀ (hy b) _ _)
  · have htt := prod_prod_zpow hy A.torusTorus (B.torusTorus c)
    simp only [mixedMonomialMap_snd_apply, MixedExponent.comp_torusTorus, Matrix.mul_apply]
    rw [htt]

/-! ### Holomorphy -/

variable {n : WithTop ℕ∞}

private theorem contDiffAt_finsetProd {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s : Finset ι} {g : ι → E → ℂ} {x : E} (h : ∀ i ∈ s, ContDiffAt ℂ n (g i) x) :
    ContDiffAt ℂ n (fun z ↦ ∏ i ∈ s, g i z) x := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using contDiffAt_const
  | cons a s ha ih =>
      simp only [prod_cons]
      exact (h a (by simp)).mul (ih fun i hi ↦ h i (by simp [hi]))

private theorem contDiffAt_zpow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {x : E} (hf : ContDiffAt ℂ n f x) (hx : f x ≠ 0) (m : ℤ) :
    ContDiffAt ℂ n (fun z ↦ f z ^ m) x := by
  obtain ⟨i, rfl | rfl⟩ := m.eq_nat_or_neg
  · simpa [zpow_natCast] using hf.pow i
  · simpa [zpow_neg, zpow_natCast, Pi.inv_def] using (hf.pow i).inv (pow_ne_zero _ hx)

/-- A mixed monomial map is holomorphic at every point of the mixed-chart locus, to any order. -/
theorem mixedMonomialMap_contDiffAt (A : MixedExponent k l k' l')
    {z : (Fin k → ℂ) × (Fin l → ℂ)} (hz : z ∈ mixedChartDomain k l) :
    ContDiffAt ℂ n (mixedMonomialMap A) z := by
  have hx : ∀ b, ContDiffAt ℂ n (fun w : (Fin k → ℂ) × (Fin l → ℂ) ↦ w.1 b) z :=
    fun b ↦ contDiffAt_pi.mp contDiffAt_fst b
  have hy : ∀ b, ContDiffAt ℂ n (fun w : (Fin k → ℂ) × (Fin l → ℂ) ↦ w.2 b) z :=
    fun b ↦ contDiffAt_pi.mp contDiffAt_snd b
  refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun a ↦ ?_) (contDiffAt_pi.mpr fun a ↦ ?_)
  · exact (contDiffAt_finsetProd fun b _ ↦ (hx b).pow _).mul
      (contDiffAt_finsetProd fun b _ ↦ contDiffAt_zpow (hy b) (hz b) _)
  · exact contDiffAt_finsetProd fun b _ ↦ contDiffAt_zpow (hy b) (hz b) _

/-- A mixed monomial map is holomorphic on the mixed-chart locus, to any order. -/
theorem mixedMonomialMap_contDiffOn (A : MixedExponent k l k' l') :
    ContDiffOn ℂ n (mixedMonomialMap A) (mixedChartDomain k l) :=
  fun _ hz ↦ (mixedMonomialMap_contDiffAt A hz).contDiffWithinAt

theorem mixedMonomialMap_differentiableOn (A : MixedExponent k l k' l') :
    DifferentiableOn ℂ (mixedMonomialMap A) (mixedChartDomain k l) :=
  fun _ hz ↦ ((mixedMonomialMap_contDiffAt (n := 1) A hz).differentiableAt
    one_ne_zero).differentiableWithinAt

/-! ### Biholomorphisms between mixed charts -/

/-- A two-sided inverse pair of exponent data induces a homeomorphism between the two mixed-chart
loci. It is a biholomorphism by `mixedMonomialOpenPartialHomeomorph_contDiffOn` and
`mixedMonomialOpenPartialHomeomorph_symm_contDiffOn`. -/
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
  continuousOn_toFun := (mixedMonomialMap_differentiableOn A).continuousOn
  continuousOn_invFun := (mixedMonomialMap_differentiableOn B).continuousOn

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
theorem mixedMonomialOpenPartialHomeomorph_contDiffOn :
    ContDiffOn ℂ n (mixedMonomialOpenPartialHomeomorph A B hBA hAB)
      (mixedMonomialOpenPartialHomeomorph A B hBA hAB).source :=
  mixedMonomialMap_contDiffOn A

/-- An inverse pair of exponent data induces a biholomorphism: the inverse of the induced
homeomorphism is holomorphic, to any order. -/
theorem mixedMonomialOpenPartialHomeomorph_symm_contDiffOn :
    ContDiffOn ℂ n (mixedMonomialOpenPartialHomeomorph A B hBA hAB).symm
      (mixedMonomialOpenPartialHomeomorph A B hBA hAB).target :=
  mixedMonomialMap_contDiffOn B

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

theorem ofTorusBlock_comp_ofTorusBlock (C C' : Matrix (Fin k) (Fin l) ℤ)
    (D D' : Matrix (Fin l) (Fin l) ℤ) :
    (ofTorusBlock C' D').comp (ofTorusBlock C D) = ofTorusBlock (C + C' * D) (D' * D) :=
  MixedExponent.ext (by simp) (by simp [Matrix.map_one _ Nat.cast_zero Nat.cast_one]) (by simp)

/-- A unimodular torus block gives an inverse pair of exponent data. -/
theorem ofTorusBlock_comp_ofTorusBlock_of_mul_eq_one (C : Matrix (Fin k) (Fin l) ℤ)
    {D D' : Matrix (Fin l) (Fin l) ℤ} (h : D' * D = 1) :
    (ofTorusBlock (-(C * D')) D').comp (ofTorusBlock C D) = MixedExponent.id k l := by
  rw [ofTorusBlock_comp_ofTorusBlock, h, Matrix.neg_mul, Matrix.mul_assoc, h, Matrix.mul_one,
    add_neg_cancel, ofTorusBlock_zero_one]

end MixedExponent

/-- The biholomorphism of a mixed chart induced by a unimodular change of the basis extending the
primitive ray generators: the boundary coordinates are kept and twisted by `C`, and the torus
coordinates are transformed by the unimodular matrix `D`. -/
noncomputable def basisChangeOpenPartialHomeomorph (C : Matrix (Fin k) (Fin l) ℤ)
    {D D' : Matrix (Fin l) (Fin l) ℤ} (h : D * D' = 1) (h' : D' * D = 1) :
    OpenPartialHomeomorph ((Fin k → ℂ) × (Fin l → ℂ)) ((Fin k → ℂ) × (Fin l → ℂ)) :=
  mixedMonomialOpenPartialHomeomorph (MixedExponent.ofTorusBlock C D)
    (MixedExponent.ofTorusBlock (-(C * D')) D')
    (MixedExponent.ofTorusBlock_comp_ofTorusBlock_of_mul_eq_one C h')
    (by
      rw [MixedExponent.ofTorusBlock_comp_ofTorusBlock, h, neg_add_cancel,
        MixedExponent.ofTorusBlock_zero_one])

section

variable (C : Matrix (Fin k) (Fin l) ℤ) {D D' : Matrix (Fin l) (Fin l) ℤ} (h : D * D' = 1)
  (h' : D' * D = 1)

@[simp]
theorem basisChangeOpenPartialHomeomorph_coe :
    ⇑(basisChangeOpenPartialHomeomorph C h h') =
      mixedMonomialMap (MixedExponent.ofTorusBlock C D) := (rfl)

@[simp]
theorem basisChangeOpenPartialHomeomorph_symm_coe :
    ⇑(basisChangeOpenPartialHomeomorph C h h').symm =
      mixedMonomialMap (MixedExponent.ofTorusBlock (-(C * D')) D') := (rfl)

@[simp]
theorem basisChangeOpenPartialHomeomorph_source :
    (basisChangeOpenPartialHomeomorph C h h').source = mixedChartDomain k l := (rfl)

@[simp]
theorem basisChangeOpenPartialHomeomorph_target :
    (basisChangeOpenPartialHomeomorph C h h').target = mixedChartDomain k l := (rfl)

end

end TauCeti.Toric
