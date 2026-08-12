/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Basic

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
`(±1)` in all eight with an even number of minus signs. Those shapes are enumerated by
`e8DoubledMinimalVector`, whose index type has two hundred and forty elements.

The map `e8DoubledEmbed` sends the simple-coroot coordinates to the doubled Euclidean model by
multiplying with the doubled simple roots of Bourbaki's Plate VII; it multiplies the norm by four,
so it carries norm-two vectors to norm-eight vectors of `2 · Γ₈`. It is injective, and the listed
coroots are two hundred and forty distinct norm-two vectors, so their images already exhaust the
two hundred and forty vectors of the enumeration, and no norm-two vector is left over. The
classification is used only through this counting step: neither the surjectivity of
`e8DoubledEmbed` onto `2 · Γ₈` nor the equality of the two lattices is needed, and neither is
proved. That whole Euclidean scaffold is therefore private to this file; the completeness statement
is its only public consequence.

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

/-- The index type of the enumeration below: either an ordered pair of distinct coordinates
carrying a sign each, or a sign for every coordinate with an even number of minus signs. -/
private abbrev E8DoubledMinimalIndex : Type :=
  ({p : Fin 8 × Fin 8 // p.1 < p.2} × Bool × Bool) ⊕
    {s : Fin 8 → Bool // Even (Finset.univ.filter fun j ↦ s j = true).card}

/-- The two shapes of norm eight in the doubled lattice `2 · Γ₈`: the vectors `±2 eᵢ ± 2 eⱼ` for
`i < j`, and the vectors with all coordinates `±1` and an even number of minus signs. -/
private def e8DoubledMinimalVector : E8DoubledMinimalIndex → (Fin 8 → ℤ)
  | .inl (p, s, t) => fun j ↦
      if j = p.1.1 then (if s then 2 else -2) else if j = p.1.2 then (if t then 2 else -2) else 0
  | .inr s => fun j ↦ if s.1 j then 1 else -1

/-- The index type has two hundred and forty elements: `4 * 28` of the first shape and `128` of the
second. -/
private theorem card_e8DoubledMinimalIndex : Fintype.card E8DoubledMinimalIndex = 240 := by
  decide +kernel

/-- A coordinate of a norm-eight vector is at most two in absolute value. -/
private lemma abs_le_two_of_dotProduct_self {x : Fin 8 → ℤ} (hx : x ⬝ᵥ x = 8) (j : Fin 8) :
    -2 ≤ x j ∧ x j ≤ 2 := by
  have hsq : x j * x j ≤ 8 := by
    rw [← hx, dotProduct]
    exact Finset.single_le_sum (fun i _ ↦ mul_self_nonneg (x i)) (Finset.mem_univ j)
  constructor <;> nlinarith [hsq]

/-- A vector supported on two coordinates, with the value `±2` there, is listed. -/
private lemma exists_e8DoubledMinimalVector_eq_of_pair {x : Fin 8 → ℤ} {a b : Fin 8} (hab : a < b)
    (hvals : ∀ j, x j = -2 ∨ x j = 0 ∨ x j = 2)
    (hsupp : ∀ j, x j ≠ 0 ↔ (j = a ∨ j = b)) : ∃ i, e8DoubledMinimalVector i = x := by
  refine ⟨.inl (⟨(a, b), hab⟩, x a = 2, x b = 2), funext fun j ↦ ?_⟩
  by_cases hja : j = a
  · subst hja
    have ha : x j ≠ 0 := (hsupp j).mpr (Or.inl rfl)
    rcases hvals j with h | h | h
    · simp [e8DoubledMinimalVector, h]
    · exact absurd h ha
    · simp [e8DoubledMinimalVector, h]
  · by_cases hjb : j = b
    · subst hjb
      have hb : x j ≠ 0 := (hsupp j).mpr (Or.inr rfl)
      rcases hvals j with h | h | h
      · simp [e8DoubledMinimalVector, h, hja]
      · exact absurd h hb
      · simp [e8DoubledMinimalVector, h, hja]
    · have hzero : x j = 0 := not_not.mp ((hsupp j).not.mpr (by tauto))
      simp [e8DoubledMinimalVector, hja, hjb, hzero]

/-- **A vector of the doubled lattice of norm eight is one of the listed ones.** A vector
satisfying `IsDoubledE8` with `x ⬝ᵥ x = 8` is `±2 eᵢ ± 2 eⱼ` with `i < j`, or has all coordinates
`±1` with an even number of minus signs. Only this inclusion is proved: that the listed vectors lie
in `2 · Γ₈`, and that eight is the minimal norm there, are not needed below. -/
private theorem exists_e8DoubledMinimalVector_eq {x : Fin 8 → ℤ} (hlat : IsDoubledE8 x)
    (hnorm : x ⬝ᵥ x = 8) : ∃ i, e8DoubledMinimalVector i = x := by
  classical
  obtain ⟨hpar, hsum⟩ := hlat
  have hbound := abs_le_two_of_dotProduct_self hnorm
  rcases Int.even_or_odd (x 0) with h0 | h0
  · -- Every coordinate is even, hence `0` or `±2`, and exactly two of them are nonzero.
    have hvals : ∀ j, x j = -2 ∨ x j = 0 ∨ x j = 2 := fun j ↦ by
      obtain ⟨c, hc⟩ := h0
      obtain ⟨d, hd⟩ := hpar j
      have := hbound j
      omega
    set s : Finset (Fin 8) := Finset.univ.filter (fun j ↦ x j ≠ 0) with hs
    have hmem : ∀ j, j ∈ s ↔ x j ≠ 0 := by simp [hs]
    have hcard : s.card = 2 := by
      have hrestrict : ∑ j ∈ s, x j * x j = 8 := by
        rw [← hnorm, dotProduct]
        refine Finset.sum_subset (f := fun j ↦ x j * x j)
          (Finset.filter_subset (fun j ↦ x j ≠ 0) Finset.univ) fun j _ hj ↦ ?_
        rw [not_not.mp ((hmem j).not.mp hj), mul_zero]
      have hconst : ∀ j ∈ s, x j * x j = 4 := fun j hj ↦ by
        have := (hmem j).mp hj
        rcases hvals j with h | h | h <;> simp_all
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hrestrict
      omega
    obtain ⟨a, b, hab, hs2⟩ := Finset.card_eq_two.mp hcard
    have hsupp : ∀ j, x j ≠ 0 ↔ (j = a ∨ j = b) := by
      intro j
      rw [← hmem j, hs2]
      simp
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact exists_e8DoubledMinimalVector_eq_of_pair hlt hvals hsupp
    · exact exists_e8DoubledMinimalVector_eq_of_pair hlt hvals fun j ↦ (hsupp j).trans or_comm
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
    refine ⟨.inr ⟨fun j ↦ x j = 1, ?_⟩, funext fun j ↦ ?_⟩
    · simpa [ht] using hparity
    · rcases hvals j with h | h <;> simp [e8DoubledMinimalVector, h]

/-! ## The doubled Euclidean model -/

/-- The doubled Bourbaki simple roots of type `E₈`: row `i` is twice the `i`-th simple root of
Plate VII, in the Euclidean coordinates of the model, so that all entries are integers. Only two
properties of the table are used below, and both are checked: its Gram matrix is four times the
`E₈` Cartan matrix, and its rows lie in the doubled lattice. -/
private def e8DoubledSimpleRoot : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 1, -1, -1, -1, -1, -1, -1,  1;
      2,  2,  0,  0,  0,  0,  0,  0;
     -2,  2,  0,  0,  0,  0,  0,  0;
      0, -2,  2,  0,  0,  0,  0,  0;
      0,  0, -2,  2,  0,  0,  0,  0;
      0,  0,  0, -2,  2,  0,  0,  0;
      0,  0,  0,  0, -2,  2,  0,  0;
      0,  0,  0,  0,  0, -2,  2,  0]

/-- The doubled simple roots have the `E₈` Cartan matrix as their Gram matrix, up to the factor
four that doubling introduces. -/
private lemma e8DoubledSimpleRoot_mul_transpose :
    e8DoubledSimpleRoot * e8DoubledSimpleRootᵀ = (4 : ℤ) • CartanMatrix.E₈ := by decide

/-- Two entries in the same row of the doubled simple roots are congruent modulo two. -/
private lemma e8DoubledSimpleRoot_sub_emod :
    ∀ i j : Fin 8, (e8DoubledSimpleRoot i j - e8DoubledSimpleRoot i 0) % 2 = 0 := by decide

/-- Every doubled simple root has coordinate sum divisible by four. -/
private lemma e8DoubledSimpleRoot_sum_emod :
    ∀ i : Fin 8, (∑ j, e8DoubledSimpleRoot i j) % 4 = 0 := by decide

/-- Simple-coroot coordinates read in the doubled Euclidean model: the combination of the doubled
simple roots with the given coordinates. -/
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
      Dvd.dvd.mul_left (Int.dvd_of_emod_eq_zero (e8DoubledSimpleRoot_sub_emod i j)) _
  · have hexpand : ∑ j, e8DoubledEmbed v j = ∑ i, v i * ∑ j, e8DoubledSimpleRoot i j := by
      simp only [e8DoubledEmbed, Matrix.vecMul, dotProduct, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hexpand]
    exact Finset.dvd_sum fun i _ ↦
      Dvd.dvd.mul_left (Int.dvd_of_emod_eq_zero (e8DoubledSimpleRoot_sum_emod i)) _

/-! ## Completeness of the enumeration -/

/-- **The listed `E₈` coroots are all the norm-two vectors of the simple-coroot lattice.** The
enumeration of the two hundred and forty coroots is complete: nothing of norm two is missing from
it. -/
theorem exists_e8Coroot_eq {v : Fin 8 → ℤ} (hv : (v ᵥ* CartanMatrix.E₈) ⬝ᵥ v = 2) :
    ∃ k, e8Coroot k = v := by
  classical
  have hmin : ∀ w : Fin 8 → ℤ, (w ᵥ* CartanMatrix.E₈) ⬝ᵥ w = 2 →
      e8DoubledEmbed w ∈ Finset.univ.image e8DoubledMinimalVector := by
    intro w hw
    obtain ⟨i, hi⟩ := exists_e8DoubledMinimalVector_eq (isDoubledE8_e8DoubledEmbed w)
      (by rw [e8DoubledEmbed_dotProduct_self, hw]; norm_num)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  set T : Finset (Fin 8 → ℤ) := Finset.univ.image e8DoubledMinimalVector with hT
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
  have hTcard : T.card ≤ 240 := by
    rw [hT]
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_univ, card_e8DoubledMinimalIndex]
  have hCT' : C = T := Finset.eq_of_subset_of_card_le hCT (by omega)
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hCT' ▸ hmin v hv)
  exact ⟨k, e8DoubledEmbed_injective hk⟩

end DynkinType

end TauCeti
