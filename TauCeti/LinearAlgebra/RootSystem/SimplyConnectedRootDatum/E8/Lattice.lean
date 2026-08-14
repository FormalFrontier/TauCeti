/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Basic
import TauCeti.LinearAlgebra.RootSystem.E8Coordinates

public section

/-!
# The listed `E₈` coroots are all the norm-two vectors

The two hundred and forty coroots of type `E₈` are enumerated in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Basic` as coordinate vectors in the
simple-coroot basis. This file proves that the enumeration is *complete*: a vector of
`Fin 8 → ℤ` whose `E₈` norm is two is one of the two hundred and forty listed coroots
(`TauCeti.DynkinType.exists_e8Coroot_eq`).

Completeness is what turns reflection into a permutation of the root indices, since the reflection
of a norm-two vector in another one is again of norm two, by an identity of bilinear algebra. It
therefore replaces the two hundred and forty by two hundred and forty table of reflected indices
that a direct construction would have to tabulate and check.

## The argument

The `E₈` norm `(v ᵥ* CartanMatrix.E₈) ⬝ᵥ v` is the Gram form of the simple-coroot basis, so the
norm-two vectors are the minimal vectors of the `E₈` lattice, read in that basis. They are counted
in the Euclidean model instead, where the lattice is described by congruences rather than by a Gram
matrix. To keep the coordinates integral the model is scaled by two: `IsDoubledE8` describes
`2 · Γ₈`, whose vectors of norm eight are of exactly two shapes, `(±2)` in two coordinates and
`(±1)` in all eight with an even number of minus signs. Those shapes are the 112 even minimal
vectors (the norm-two roots of type `D₈` scaled by two, supplied by
`TauCeti.DynkinType.typeDRootEquiv`) and the 128 odd minimal vectors with an even number of minus
signs.

The map `e8DoubledEmbed` sends the simple-coroot coordinates to the doubled Euclidean model by
multiplying with `TauCeti.DynkinType.e8DoubledSimpleRoot`, the shared integral table of
`TauCeti.LinearAlgebra.RootSystem.E8Coordinates`; it multiplies the norm by four, so it carries
norm-two vectors to norm-eight vectors of `2 · Γ₈`. It is injective, and the listed coroots are two
hundred and forty distinct norm-two vectors, so their images already exhaust the two hundred and
forty vectors of the enumeration, and no norm-two vector is left over. The classification is used
only through this counting step: neither the surjectivity of `e8DoubledEmbed` onto `2 · Γ₈` nor the
equality of the two lattices is needed, and neither is proved. The counting scaffold built on the
table is therefore private to this file; the completeness statement is its only public consequence.

## Main results

* `TauCeti.DynkinType.exists_e8Coroot_eq`: a norm-two vector of the simple-coroot lattice is one of
  the listed `E₈` coroots.

## References

The Euclidean model of the `E₈` lattice and its two hundred and forty minimal vectors are Bourbaki,
*Lie Groups and Lie Algebras, Chapters 4--6*, Plate VII, and Conway--Sloane, *Sphere Packings,
Lattices and Groups*, chapter 4, section 8. This supports the target "a named datum per valid type"
in Layer 6 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

namespace TauCeti

open _root_.Matrix

namespace DynkinType

/-! ## The doubled `E₈` lattice and its vectors of norm eight -/

/-- The doubled `E₈` lattice `2 · Γ₈` in Euclidean coordinates: a vector all of whose coordinates
are congruent modulo two and whose coordinate sum is divisible by four.

Doubling clears the half-integral coordinates of `Γ₈`, so this is a sublattice of `ℤ⁸`: an integral
vector of `Γ₈` doubles to an all-even vector with coordinate sum in `4ℤ`, and a half-integral one
doubles to an all-odd vector with the same property. Only the inclusion
`isDoubledE8_e8DoubledEmbed` is needed below, so this file never proves that the condition cuts out
exactly the doubled lattice. -/
private def IsDoubledE8 (x : Fin 8 → ℤ) : Prop :=
  (∀ j, (2 : ℤ) ∣ x j - x 0) ∧ (4 : ℤ) ∣ ∑ j, x j

/-- The vectors `(2 : ℤ) • y` where `y` is a norm-two vector of type `D₈`. -/
private noncomputable def e8DoubledEvenMinimalVector (k : Fin 112) : Fin 8 → ℤ :=
  (2 : ℤ) • (typeDRootEquiv 8 (by omega) k).1

/-- The index type for odd minimal vectors: a choice of signs with an even number of minus signs. -/
private abbrev E8DoubledOddIndex : Type :=
  {s : Fin 8 → Bool // Even (Finset.univ.filter fun j ↦ s j = true).card}

/-- The vectors with all coordinates `±1` and an even number of minus signs. -/
private def e8DoubledOddMinimalVector (s : E8DoubledOddIndex) : Fin 8 → ℤ :=
  fun j ↦ if s.1 j then 1 else -1

/-- The 240 minimal vectors in the doubled Euclidean model: the 112 even minimal vectors and the 128
odd minimal vectors. -/
private noncomputable def e8DoubledMinimalSet : Finset (Fin 8 → ℤ) :=
  (Finset.univ.image e8DoubledEvenMinimalVector) ∪ (Finset.univ.image e8DoubledOddMinimalVector)

private theorem card_e8DoubledMinimalSet_le : e8DoubledMinimalSet.card ≤ 240 := by
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 : (Finset.univ.image e8DoubledEvenMinimalVector).card ≤ 112 := by
    refine le_trans (Finset.card_image_le) (by simp)
  have h2 : (Finset.univ.image e8DoubledOddMinimalVector).card ≤ 128 := by
    refine le_trans (Finset.card_image_le) ?_
    rw [Finset.card_univ]
    decide +kernel
  omega

/-- A coordinate of a norm-eight vector is at most two in absolute value. -/
private lemma abs_le_two_of_dotProduct_self {x : Fin 8 → ℤ} (hx : x ⬝ᵥ x = 8) (j : Fin 8) :
    -2 ≤ x j ∧ x j ≤ 2 := by
  have hsq : x j * x j ≤ 8 := by
    rw [← hx, dotProduct]
    exact Finset.single_le_sum (fun i _ ↦ mul_self_nonneg (x i)) (Finset.mem_univ j)
  constructor <;> nlinarith [hsq]

/-- A vector of the doubled lattice of norm eight is in the candidate minimal set. -/
private theorem mem_e8DoubledMinimalSet_of_isDoubledE8 {x : Fin 8 → ℤ} (hlat : IsDoubledE8 x)
    (hnorm : x ⬝ᵥ x = 8) : x ∈ e8DoubledMinimalSet := by
  classical
  obtain ⟨hpar, hsum⟩ := hlat
  have hbound := abs_le_two_of_dotProduct_self hnorm
  rcases Int.even_or_odd (x 0) with h0 | h0
  · -- Every coordinate is even, so `x = 2 • y` with `y ⬝ᵥ y = 2`.
    have heven (j : Fin 8) : (2 : ℤ) ∣ x j := by
      obtain ⟨c, hc⟩ := h0
      obtain ⟨d, hd⟩ := hpar j
      exact ⟨c + d, by omega⟩
    choose y hy using fun j ↦ heven j
    have hx2y : x = (2 : ℤ) • y := funext fun j ↦ by
      simp only [Pi.smul_apply, smul_eq_mul, hy j]
    have hnorm_y : y ⬝ᵥ y = 2 := by
      have h : x ⬝ᵥ x = 4 * (y ⬝ᵥ y) := by
        rw [hx2y]
        simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
        ring
      omega
    obtain ⟨k, hk⟩ := (typeDRootEquiv 8 (by omega)).surjective ⟨y, hnorm_y⟩
    rw [e8DoubledMinimalSet, Finset.mem_union]
    left
    refine Finset.mem_image.mpr ⟨k, Finset.mem_univ k, ?_⟩
    dsimp [e8DoubledEvenMinimalVector]
    rw [hk, hx2y]
  · -- Every coordinate is odd, hence `±1`, and the sum condition makes the sign count even.
    have hvals : ∀ j, x j = 1 ∨ x j = -1 := fun j ↦ by
      obtain ⟨c, hc⟩ := h0
      obtain ⟨d, hd⟩ := hpar j
      have := hbound j
      omega
    set t : Finset (Fin 8) := Finset.univ.filter (fun j ↦ x j = 1) with ht
    have hcount : ∑ j, x j = 2 * (t.card : ℤ) - 8 := by
      have hpoint : ∀ j ∈ Finset.univ, x j = 2 * (if x j = 1 then (1 : ℤ) else 0) - 1 :=
        fun j _ ↦ by rcases hvals j with h | h <;> simp [h]
      rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
        ← ht]
      simp
    have hparity : Even t.card := by
      obtain ⟨c, hc⟩ := hsum
      rw [Nat.even_iff]
      omega
    rw [e8DoubledMinimalSet, Finset.mem_union]
    right
    refine Finset.mem_image.mpr ⟨⟨fun j ↦ x j = 1, ?_⟩, Finset.mem_univ _, ?_⟩
    · simpa [ht] using hparity
    · ext j
      dsimp [e8DoubledOddMinimalVector]
      rcases hvals j with h | h <;> simp [h]

/-! ## The doubled Euclidean model -/

/-- Simple-coroot coordinates read in the doubled Euclidean model: the combination of the doubled
simple roots of `TauCeti.LinearAlgebra.RootSystem.E8Coordinates` with the given coordinates. -/
private def e8DoubledEmbed (v : Fin 8 → ℤ) : Fin 8 → ℤ := v ᵥ* e8DoubledSimpleRoot

/-- Reading the simple-coroot coordinates in the doubled model multiplies the `E₈` norm by four. -/
private theorem e8DoubledEmbed_dotProduct_self (v : Fin 8 → ℤ) :
    e8DoubledEmbed v ⬝ᵥ e8DoubledEmbed v = 4 * ((v ᵥ* CartanMatrix.E₈) ⬝ᵥ v) := by
  rw [e8DoubledEmbed]
  nth_rewrite 2 [← Matrix.mulVec_transpose]
  rw [dotProduct_mulVec, Matrix.vecMul_vecMul, e8DoubledSimpleRoot_mul_transpose,
    Matrix.vecMul_smul, smul_dotProduct, smul_eq_mul]

/-- Reading the simple-coroot coordinates in the doubled model is injective. -/
private theorem e8DoubledEmbed_injective : Function.Injective e8DoubledEmbed := by
  intro v w h
  apply sub_eq_zero.mp
  refine Matrix.eq_zero_of_vecMul_eq_zero (M := CartanMatrix.E₈)
    (by rw [CartanMatrix.E₈_det]; norm_num) ?_
  have h0 : (v - w) ᵥ* e8DoubledSimpleRoot = 0 := by
    rw [Matrix.sub_vecMul]
    exact sub_eq_zero.mpr h
  have h1 : (v - w) ᵥ* (e8DoubledSimpleRoot * e8DoubledSimpleRootᵀ) = 0 := by
    rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul]
  rw [e8DoubledSimpleRoot_mul_transpose, Matrix.vecMul_smul] at h1
  exact (smul_eq_zero.mp h1).resolve_left (by norm_num)

/-- Simple-coroot coordinates land in the doubled `E₈` lattice. -/
private theorem isDoubledE8_e8DoubledEmbed (v : Fin 8 → ℤ) : IsDoubledE8 (e8DoubledEmbed v) := by
  constructor
  · intro j
    have hexpand : e8DoubledEmbed v j - e8DoubledEmbed v 0 =
        ∑ i, v i * (e8DoubledSimpleRoot i j - e8DoubledSimpleRoot i 0) := by
      simp only [e8DoubledEmbed, Matrix.vecMul, dotProduct, mul_sub, Finset.sum_sub_distrib]
    rw [hexpand]
    exact Finset.dvd_sum fun i _ ↦
      Dvd.dvd.mul_left (e8DoubledSimpleRoot_two_dvd_sub i j) _
  · have hexpand : ∑ j, e8DoubledEmbed v j = ∑ i, v i * ∑ j, e8DoubledSimpleRoot i j := by
      simp only [e8DoubledEmbed, Matrix.vecMul, dotProduct, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hexpand]
    exact Finset.dvd_sum fun i _ ↦
      Dvd.dvd.mul_left (e8DoubledSimpleRoot_four_dvd_sum i) _

/-! ## Completeness of the enumeration -/

/-- **The listed `E₈` coroots are all the norm-two vectors of the simple-coroot lattice.** The
enumeration of the two hundred and forty coroots is complete: nothing of norm two is missing from
it. -/
theorem exists_e8Coroot_eq {v : Fin 8 → ℤ} (hv : (v ᵥ* CartanMatrix.E₈) ⬝ᵥ v = 2) :
    ∃ k, e8Coroot k = v := by
  classical
  have hmin : ∀ w : Fin 8 → ℤ, (w ᵥ* CartanMatrix.E₈) ⬝ᵥ w = 2 →
      e8DoubledEmbed w ∈ e8DoubledMinimalSet := by
    intro w hw
    exact mem_e8DoubledMinimalSet_of_isDoubledE8 (isDoubledE8_e8DoubledEmbed w)
      (by rw [e8DoubledEmbed_dotProduct_self, hw]; norm_num)
  set T : Finset (Fin 8 → ℤ) := e8DoubledMinimalSet with hT
  set C : Finset (Fin 8 → ℤ) := Finset.univ.image fun k ↦ e8DoubledEmbed (e8Coroot k) with hC
  have hCT : C ⊆ T := by
    rw [hC]
    intro y hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
    exact hmin _ (by rw [← e8Root_apply]; exact e8Root_dotProduct_coroot k)
  have hinj : Function.Injective fun k ↦ e8DoubledEmbed (e8Coroot k) :=
    fun _ _ h ↦ e8Coroot.injective (e8DoubledEmbed_injective h)
  have hCcard : C.card = 240 := by
    rw [hC, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hTcard : T.card ≤ 240 := card_e8DoubledMinimalSet_le
  have hCT' : C = T := Finset.eq_of_subset_of_card_le hCT (by omega)
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hCT' ▸ hmin v hv)
  exact ⟨k, e8DoubledEmbed_injective hk⟩

end DynkinType

end TauCeti
