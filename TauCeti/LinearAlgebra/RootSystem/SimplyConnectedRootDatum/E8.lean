/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
public import Mathlib.Data.Fin.Tuple.Embedding

public section

/-!
# The pinned simply connected root datum of type E8

This file enumerates the 240 roots of type `E8` and builds the pinned integral root datum they
carry. Coroots are expressed in the simple-coroot basis and roots in the fundamental-weight basis.
Both tables are indexed by the same `Fin 240`: the first eight entries of the root table are the
Bourbaki simple roots and the first eight entries of the coroot table are the corresponding simple
coroots. The remaining positive entries are ordered by height, and the last 120 entries are the
negatives of the first 120.

`E₈` is simply laced, so a single stored table of coroot coordinates determines the roots as well,
through `TauCeti.DynkinType.e8Root_eq_mulVec`. The reflections are handled the same way: only the
eight *simple* reflections are tabulated as permutations of the root indices, and reflection in an
arbitrary root is obtained by conjugating a simple reflection along a stored word in the simple
reflections, through Mathlib's `Module.preReflection_preReflection`. This keeps the stored data
linear rather than quadratic in the number of roots.

The datum is the root-data input for Layer 6 of the root-systems roadmap. It follows Bourbaki,
*Lie Groups and Lie Algebras, Chapters 4--6*, Plate VII.

## Main definitions

* `TauCeti.DynkinType.e8Root`, `TauCeti.DynkinType.e8Coroot`: the pinned 240-element tables.
* `TauCeti.DynkinType.e8SimplyConnectedRootDatum`: the pinned integral root datum of type `E₈`.
* `TauCeti.DynkinType.e8SimplyConnectedBase`: its Bourbaki-numbered base.

## Main results

* `TauCeti.DynkinType.hasCartanType_e8SimplyConnectedRootDatum`: the pinned datum realizes the
  standard Cartan matrix of `E8` against its pinned base.
* `TauCeti.DynkinType.corootSpan_e8SimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, which is the simply connected lattice condition.
-/

namespace TauCeti

open _root_.Matrix

namespace DynkinType

private def e8PositiveCorootChunk0 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 1, 1],
  ![0, 0, 0, 0, 0, 1, 1, 0]
]

private def e8PositiveCorootChunk1 : Fin 10 → (Fin 8 → ℤ) := ![
  ![0, 0, 0, 0, 1, 1, 0, 0],
  ![0, 0, 0, 1, 1, 0, 0, 0],
  ![0, 0, 1, 1, 0, 0, 0, 0],
  ![0, 1, 0, 1, 0, 0, 0, 0],
  ![1, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 1, 1],
  ![0, 0, 0, 0, 1, 1, 1, 0],
  ![0, 0, 0, 1, 1, 1, 0, 0],
  ![0, 0, 1, 1, 1, 0, 0, 0],
  ![0, 1, 0, 1, 1, 0, 0, 0]
]

private def e8PositiveCorootChunk2 : Fin 10 → (Fin 8 → ℤ) := ![
  ![0, 1, 1, 1, 0, 0, 0, 0],
  ![1, 0, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 1, 1, 1],
  ![0, 0, 0, 1, 1, 1, 1, 0],
  ![0, 0, 1, 1, 1, 1, 0, 0],
  ![0, 1, 0, 1, 1, 1, 0, 0],
  ![0, 1, 1, 1, 1, 0, 0, 0],
  ![1, 0, 1, 1, 1, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 1, 1, 1, 1, 1]
]

private def e8PositiveCorootChunk3 : Fin 10 → (Fin 8 → ℤ) := ![
  ![0, 0, 1, 1, 1, 1, 1, 0],
  ![0, 1, 0, 1, 1, 1, 1, 0],
  ![0, 1, 1, 1, 1, 1, 0, 0],
  ![0, 1, 1, 2, 1, 0, 0, 0],
  ![1, 0, 1, 1, 1, 1, 0, 0],
  ![1, 1, 1, 1, 1, 0, 0, 0],
  ![0, 0, 1, 1, 1, 1, 1, 1],
  ![0, 1, 0, 1, 1, 1, 1, 1],
  ![0, 1, 1, 1, 1, 1, 1, 0],
  ![0, 1, 1, 2, 1, 1, 0, 0]
]

private def e8PositiveCorootChunk4 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 0, 1, 1, 1, 1, 1, 0],
  ![1, 1, 1, 1, 1, 1, 0, 0],
  ![1, 1, 1, 2, 1, 0, 0, 0],
  ![0, 1, 1, 1, 1, 1, 1, 1],
  ![0, 1, 1, 2, 1, 1, 1, 0],
  ![0, 1, 1, 2, 2, 1, 0, 0],
  ![1, 0, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1, 1, 0],
  ![1, 1, 1, 2, 1, 1, 0, 0],
  ![1, 1, 2, 2, 1, 0, 0, 0]
]

private def e8PositiveCorootChunk5 : Fin 10 → (Fin 8 → ℤ) := ![
  ![0, 1, 1, 2, 1, 1, 1, 1],
  ![0, 1, 1, 2, 2, 1, 1, 0],
  ![1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 2, 1, 1, 1, 0],
  ![1, 1, 1, 2, 2, 1, 0, 0],
  ![1, 1, 2, 2, 1, 1, 0, 0],
  ![0, 1, 1, 2, 2, 1, 1, 1],
  ![0, 1, 1, 2, 2, 2, 1, 0],
  ![1, 1, 1, 2, 1, 1, 1, 1],
  ![1, 1, 1, 2, 2, 1, 1, 0]
]

private def e8PositiveCorootChunk6 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 1, 2, 2, 1, 1, 1, 0],
  ![1, 1, 2, 2, 2, 1, 0, 0],
  ![0, 1, 1, 2, 2, 2, 1, 1],
  ![1, 1, 1, 2, 2, 1, 1, 1],
  ![1, 1, 1, 2, 2, 2, 1, 0],
  ![1, 1, 2, 2, 1, 1, 1, 1],
  ![1, 1, 2, 2, 2, 1, 1, 0],
  ![1, 1, 2, 3, 2, 1, 0, 0],
  ![0, 1, 1, 2, 2, 2, 2, 1],
  ![1, 1, 1, 2, 2, 2, 1, 1]
]

private def e8PositiveCorootChunk7 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 1, 2, 2, 2, 1, 1, 1],
  ![1, 1, 2, 2, 2, 2, 1, 0],
  ![1, 1, 2, 3, 2, 1, 1, 0],
  ![1, 2, 2, 3, 2, 1, 0, 0],
  ![1, 1, 1, 2, 2, 2, 2, 1],
  ![1, 1, 2, 2, 2, 2, 1, 1],
  ![1, 1, 2, 3, 2, 1, 1, 1],
  ![1, 1, 2, 3, 2, 2, 1, 0],
  ![1, 2, 2, 3, 2, 1, 1, 0],
  ![1, 1, 2, 2, 2, 2, 2, 1]
]

private def e8PositiveCorootChunk8 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 1, 2, 3, 2, 2, 1, 1],
  ![1, 1, 2, 3, 3, 2, 1, 0],
  ![1, 2, 2, 3, 2, 1, 1, 1],
  ![1, 2, 2, 3, 2, 2, 1, 0],
  ![1, 1, 2, 3, 2, 2, 2, 1],
  ![1, 1, 2, 3, 3, 2, 1, 1],
  ![1, 2, 2, 3, 2, 2, 1, 1],
  ![1, 2, 2, 3, 3, 2, 1, 0],
  ![1, 1, 2, 3, 3, 2, 2, 1],
  ![1, 2, 2, 3, 2, 2, 2, 1]
]

private def e8PositiveCorootChunk9 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 2, 2, 3, 3, 2, 1, 1],
  ![1, 2, 2, 4, 3, 2, 1, 0],
  ![1, 1, 2, 3, 3, 3, 2, 1],
  ![1, 2, 2, 3, 3, 2, 2, 1],
  ![1, 2, 2, 4, 3, 2, 1, 1],
  ![1, 2, 3, 4, 3, 2, 1, 0],
  ![1, 2, 2, 3, 3, 3, 2, 1],
  ![1, 2, 2, 4, 3, 2, 2, 1],
  ![1, 2, 3, 4, 3, 2, 1, 1],
  ![2, 2, 3, 4, 3, 2, 1, 0]
]

private def e8PositiveCorootChunk10 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 2, 2, 4, 3, 3, 2, 1],
  ![1, 2, 3, 4, 3, 2, 2, 1],
  ![2, 2, 3, 4, 3, 2, 1, 1],
  ![1, 2, 2, 4, 4, 3, 2, 1],
  ![1, 2, 3, 4, 3, 3, 2, 1],
  ![2, 2, 3, 4, 3, 2, 2, 1],
  ![1, 2, 3, 4, 4, 3, 2, 1],
  ![2, 2, 3, 4, 3, 3, 2, 1],
  ![1, 2, 3, 5, 4, 3, 2, 1],
  ![2, 2, 3, 4, 4, 3, 2, 1]
]

private def e8PositiveCorootChunk11 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 3, 3, 5, 4, 3, 2, 1],
  ![2, 2, 3, 5, 4, 3, 2, 1],
  ![2, 2, 4, 5, 4, 3, 2, 1],
  ![2, 3, 3, 5, 4, 3, 2, 1],
  ![2, 3, 4, 5, 4, 3, 2, 1],
  ![2, 3, 4, 6, 4, 3, 2, 1],
  ![2, 3, 4, 6, 5, 3, 2, 1],
  ![2, 3, 4, 6, 5, 4, 2, 1],
  ![2, 3, 4, 6, 5, 4, 3, 1],
  ![2, 3, 4, 6, 5, 4, 3, 2]
]

private def e8CorootCode (x : Fin 8 → ℤ) : ℤ :=
  x 0 + 7 * x 1 + 49 * x 2 + 343 * x 3 + 2401 * x 4 + 16807 * x 5 +
    117649 * x 6 + 823543 * x 7

/-- The 120 positive `E8` coroots in the simple-coroot basis. The first eight entries are the
Bourbaki simple coroots and the rest are ordered by height. -/
def e8PositiveCoroot : Fin 120 ↪ (Fin 8 → ℤ) where
  toFun := Fin.append e8PositiveCorootChunk0 (Fin.append e8PositiveCorootChunk1
    (Fin.append e8PositiveCorootChunk2 (Fin.append e8PositiveCorootChunk3
    (Fin.append e8PositiveCorootChunk4 (Fin.append e8PositiveCorootChunk5
    (Fin.append e8PositiveCorootChunk6 (Fin.append e8PositiveCorootChunk7
    (Fin.append e8PositiveCorootChunk8 (Fin.append e8PositiveCorootChunk9
    (Fin.append e8PositiveCorootChunk10 e8PositiveCorootChunk11))))))))))
  inj' := by
    apply Function.Injective.of_comp (f := e8CorootCode)
    -- The 120 × 120 case check runs in the kernel, whose evaluation has no recursion limit.
    decide +kernel

/-- Every positive `E8` coroot has nonnegative simple-coroot coordinates. -/
theorem e8PositiveCoroot_nonneg (i : Fin 120) (j : Fin 8) :
    0 ≤ e8PositiveCoroot i j := by
  fin_cases i <;> fin_cases j <;> decide

private lemma e8PositiveCoroot_sum_pos (i : Fin 120) :
    0 < ∑ j, e8PositiveCoroot i j := by
  fin_cases i <;> decide

private lemma e8PositiveCoroot_ne_neg (i j : Fin 120) :
    e8PositiveCoroot i ≠ -e8PositiveCoroot j := by
  intro h
  have hsum := congrArg (fun x : Fin 8 → ℤ ↦ ∑ k, x k) h
  have hj : 0 < ∑ k, e8PositiveCoroot j k := e8PositiveCoroot_sum_pos j
  simp only [Pi.neg_apply, Finset.sum_neg_distrib] at hsum
  have hi : 0 < ∑ k, e8PositiveCoroot i k := e8PositiveCoroot_sum_pos i
  omega

/-- The negatives of the 120 positive `E8` coroots. -/
private def e8NegativeCoroot : Fin 120 ↪ (Fin 8 → ℤ) :=
  e8PositiveCoroot.trans (Equiv.neg (Fin 8 → ℤ)).toEmbedding

private lemma e8PositiveCoroot_range_disjoint :
    Disjoint (Set.range e8PositiveCoroot) (Set.range e8NegativeCoroot) := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  exact e8PositiveCoroot_ne_neg i j hj.symm

/-- The 240 `E8` coroots in the simple-coroot basis, with the positive coroots followed by their
negatives. -/
def e8Coroot : Fin 240 ↪ (Fin 8 → ℤ) :=
  Fin.Embedding.append e8PositiveCoroot_range_disjoint

/-- The 240 `E8` roots in the fundamental-weight basis. -/
def e8Root : Fin 240 ↪ (Fin 8 → ℤ) where
  toFun i := e8Coroot i ᵥ* CartanMatrix.E₈
  inj' := by
    intro i j hij
    apply e8Coroot.injective
    apply sub_eq_zero.mp
    apply Matrix.eq_zero_of_vecMul_eq_zero (by rw [CartanMatrix.E₈_det]; norm_num)
    rw [sub_vecMul]
    exact sub_eq_zero.mpr hij

/-- The `E8` roots are obtained from the coroot coordinates using the Cartan matrix. -/
theorem e8Root_apply (i : Fin 240) :
    e8Root i = e8Coroot i ᵥ* CartanMatrix.E₈ := (rfl)

/-- The coroot table is the concatenation of the positive coroots with their negatives. -/
private theorem e8Coroot_coe :
    ⇑e8Coroot = Fin.append (⇑e8PositiveCoroot) fun i ↦ -e8PositiveCoroot i :=
  Fin.Embedding.coe_append _

/-! ## The three blocks of root indices -/

/-- The `i`-th simple root of type `E₈` sits at root index `i`, the Bourbaki node `i + 1`. -/
def e8SimpleIndex (i : Fin 8) : Fin 240 := ⟨i, by omega⟩

/-- The `i`-th positive root of type `E₈` sits at root index `i`. -/
def e8PositiveIndex (i : Fin 120) : Fin 240 := ⟨i, by omega⟩

/-- The negative of the `i`-th positive root of type `E₈` sits at root index `i + 120`. -/
def e8NegativeIndex (i : Fin 120) : Fin 240 := ⟨i + 120, by omega⟩

@[simp] lemma e8SimpleIndex_val (i : Fin 8) : (e8SimpleIndex i : ℕ) = i := (rfl)

@[simp] lemma e8PositiveIndex_val (i : Fin 120) : (e8PositiveIndex i : ℕ) = i := (rfl)

@[simp] lemma e8NegativeIndex_val (i : Fin 120) : (e8NegativeIndex i : ℕ) = (i : ℕ) + 120 := (rfl)

lemma e8SimpleIndex_injective : Function.Injective e8SimpleIndex :=
  fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h)

/-- The first half of the coroot table is the positive coroot enumeration. -/
@[simp] theorem coroot_e8PositiveIndex (i : Fin 120) :
    e8Coroot (e8PositiveIndex i) = e8PositiveCoroot i := by
  rw [e8Coroot_coe]
  exact Fin.append_left _ _ i

/-- The negative half of the coroot table is the negation of the positive half. -/
@[simp] theorem coroot_e8NegativeIndex (i : Fin 120) :
    e8Coroot (e8NegativeIndex i) = -e8Coroot (e8PositiveIndex i) := by
  rw [coroot_e8PositiveIndex]
  change e8Coroot (Fin.addNat i 120) = _
  rw [← Fin.natAdd_eq_addNat, e8Coroot_coe, Fin.append_right]

/-- **The root coordinates are the Cartan-matrix image of the coroot coordinates.** Writing a
coroot as `β^∨ = ∑ i, cᵢ αᵢ^∨` in the simple coroots, the pairings of `β` against the simple
coroots are `⟨β, αⱼ^∨⟩ = ∑ i, cᵢ ⟨αᵢ, αⱼ^∨⟩`, which is the `j`-th entry of the Cartan-matrix image
of `c` because `CartanMatrix.E₈` is symmetric.

This is deliberately not a `simp` lemma: unfolding a root into the Cartan-matrix image of its
coroot is a change of representation, not a normal form. -/
theorem e8Root_eq_mulVec (i : Fin 240) : e8Root i = CartanMatrix.E₈ *ᵥ e8Coroot i := by
  rw [e8Root_apply]
  conv_lhs => rw [← CartanMatrix.E₈_transpose]
  exact Matrix.vecMul_transpose _ _

/-- The negative half of the root table is the negation of the positive half. -/
@[simp] theorem root_e8NegativeIndex (i : Fin 120) :
    e8Root (e8NegativeIndex i) = -e8Root (e8PositiveIndex i) := by
  rw [e8Root_eq_mulVec, e8Root_eq_mulVec, coroot_e8NegativeIndex, Matrix.mulVec_neg]

/-- Every listed `E8` root pairs to two with its corresponding coroot. -/
@[simp] theorem e8Root_dotProduct_coroot (i : Fin 240) : e8Root i ⬝ᵥ e8Coroot i = 2 := by
  fin_cases i <;> decide

/-- **The simple coroots are the standard basis.** This is what pins the cocharacter lattice as the
coroot lattice, so that the datum is the simply connected one. -/
@[simp] theorem coroot_e8SimpleIndex (i : Fin 8) : e8Coroot (e8SimpleIndex i) = Pi.single i 1 := by
  fin_cases i <;> decide

/-- **The simple roots are the rows of the Cartan matrix.** In the fundamental-weight basis the
`i`-th simple root of the pinned type `E₈` datum is the `i`-th row of `CartanMatrix.E₈`, which is
what pins the character lattice as the weight lattice. -/
@[simp] theorem root_e8SimpleIndex (i : Fin 8) : e8Root (e8SimpleIndex i) = CartanMatrix.E₈ i := by
  rw [e8Root_eq_mulVec, coroot_e8SimpleIndex, Matrix.mulVec_single_one]
  exact funext (CartanMatrix.E₈_isSymm.apply i)

/-- The last positive `E8` coroot has Bourbaki marks `(2, 3, 4, 6, 5, 4, 3, 2)`. -/
theorem e8Coroot_apply_last_positive :
    e8Coroot 119 = ![2, 3, 4, 6, 5, 4, 3, 2] := by decide

/-- Every coroot of type `E₈` has simple-coroot coordinates of one sign. -/
theorem e8Coroot_nonneg_or_nonpos (k : Fin 240) :
    (∀ j, 0 ≤ e8Coroot k j) ∨ (∀ j, e8Coroot k j ≤ 0) := by
  rcases lt_or_ge (k : ℕ) 120 with hk | hk
  · refine Or.inl fun j => ?_
    have hp : k = e8PositiveIndex ⟨k, hk⟩ := Fin.ext rfl
    rw [hp, coroot_e8PositiveIndex]
    exact e8PositiveCoroot_nonneg _ j
  · refine Or.inr fun j => ?_
    have hn : k = e8NegativeIndex ⟨(k : ℕ) - 120, by omega⟩ := Fin.ext (by simp; omega)
    rw [hn, coroot_e8NegativeIndex, coroot_e8PositiveIndex]
    simpa using e8PositiveCoroot_nonneg _ j

/-! ## The symmetric form and the reflection formula

Reflections are computed on coordinate vectors before they are transported to root indices. A
reflection is Mathlib's `Module.preReflection` for the linear functional attached to the reflecting
coroot by the form of `CartanMatrix.E₈`, so its involutivity and the conjugation rule
`s_{w α} = w s_α w⁻¹` are `Module.involutive_preReflection` and
`Module.preReflection_preReflection` rather than new computations.
-/

/-- The symmetric bilinear form attached to `CartanMatrix.E₈`, read on simple-coroot
coordinates. -/
private def e8Form (x y : Fin 8 → ℤ) : ℤ := (x ᵥ* CartanMatrix.E₈) ⬝ᵥ y

private lemma e8Form_coroot_left (i : Fin 240) (v : Fin 8 → ℤ) :
    e8Form (e8Coroot i) v = e8Root i ⬝ᵥ v := (rfl)

private lemma e8Form_eq_mulVec (x y : Fin 8 → ℤ) :
    e8Form x y = (CartanMatrix.E₈ *ᵥ x) ⬝ᵥ y := by
  rw [e8Form]
  conv_lhs => rw [← CartanMatrix.E₈_transpose]
  rw [Matrix.vecMul_transpose]

private lemma e8Form_comm (x y : Fin 8 → ℤ) : e8Form x y = e8Form y x := by
  rw [e8Form_eq_mulVec, e8Form, dotProduct_comm, Matrix.dotProduct_mulVec]

private lemma e8Form_add_right (x y z : Fin 8 → ℤ) :
    e8Form x (y + z) = e8Form x y + e8Form x z := by
  rw [e8Form, e8Form, e8Form, dotProduct_add]

private lemma e8Form_sub_right (x y z : Fin 8 → ℤ) :
    e8Form x (y - z) = e8Form x y - e8Form x z := by
  rw [e8Form, e8Form, e8Form, dotProduct_sub]

private lemma e8Form_zsmul_right (a : ℤ) (x y : Fin 8 → ℤ) :
    e8Form x (a • y) = a * e8Form x y := by
  rw [e8Form, e8Form, dotProduct_smul, smul_eq_mul]

private lemma e8Form_sub_left (x y z : Fin 8 → ℤ) :
    e8Form (x - y) z = e8Form x z - e8Form y z := by
  rw [e8Form_comm, e8Form_comm x z, e8Form_comm y z, e8Form_sub_right]

private lemma e8Form_zsmul_left (a : ℤ) (x y : Fin 8 → ℤ) :
    e8Form (a • x) y = a * e8Form x y := by
  rw [e8Form_comm, e8Form_comm x y, e8Form_zsmul_right]

private lemma e8Form_neg_left (x y : Fin 8 → ℤ) : e8Form (-x) y = -e8Form x y := by
  rw [e8Form, e8Form, Matrix.neg_vecMul, neg_dotProduct]

/-- The linear functional `e8Form c` attached to a coordinate vector `c` by the `E₈` form. On a
coroot it is the pairing against the corresponding root. -/
private def e8Dual (c : Fin 8 → ℤ) : Module.Dual ℤ (Fin 8 → ℤ) where
  toFun := e8Form c
  map_add' := e8Form_add_right c
  map_smul' a y := by simpa [smul_eq_mul] using e8Form_zsmul_right a c y

private lemma e8Dual_apply (c v : Fin 8 → ℤ) : e8Dual c v = e8Form c v := (rfl)

/-- Reflection in the root whose coroot coordinates are `c`, as a map of coordinate vectors. -/
private def e8Refl (c v : Fin 8 → ℤ) : Fin 8 → ℤ := Module.preReflection c (e8Dual c) v

private lemma e8Refl_apply (c v : Fin 8 → ℤ) : e8Refl c v = v - e8Form c v • c :=
  Module.preReflection_apply c (e8Dual c) v

private lemma e8Refl_neg_left (c v : Fin 8 → ℤ) : e8Refl (-c) v = e8Refl c v := by
  rw [e8Refl_apply, e8Refl_apply, e8Form_neg_left, neg_smul, smul_neg, neg_neg]

/-- Reflecting the functional attached to `x` in the functional attached to `c` gives the
functional attached to the reflected vector. This is where the symmetry of the form enters, and it
is what makes `Module.preReflection_preReflection` applicable. -/
private lemma preReflection_e8Dual (c x : Fin 8 → ℤ) :
    Module.preReflection (e8Dual c) (Module.Dual.eval ℤ (Fin 8 → ℤ) c) (e8Dual x) =
      e8Dual (e8Refl c x) := by
  refine LinearMap.ext fun v => ?_
  rw [Module.preReflection_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.Dual.eval_apply, smul_eq_mul]
  simp only [e8Dual_apply]
  rw [e8Refl_apply, e8Form_sub_left, e8Form_zsmul_left, e8Form_comm x c]

private lemma e8Refl_involutive (c : Fin 8 → ℤ) (hc : e8Form c c = 2) :
    Function.Involutive (e8Refl c) :=
  Module.involutive_preReflection (f := e8Dual c) hc

/-- **Conjugating a reflection by a reflection reflects in the image root.** This is what lets a
single simple reflection generate the reflection in every root of its Weyl orbit. -/
private lemma e8Refl_e8Refl (c : Fin 8 → ℤ) (hc : e8Form c c = 2) (x v : Fin 8 → ℤ) :
    e8Refl (e8Refl c x) v = e8Refl c (e8Refl x (e8Refl c v)) := by
  have h := Module.preReflection_preReflection (x := c) (y := x) (f := e8Dual c) (e8Dual x) hc
  rw [preReflection_e8Dual] at h
  exact LinearMap.congr_fun h v

private lemma e8Form_coroot_self (i : Fin 240) : e8Form (e8Coroot i) (e8Coroot i) = 2 :=
  (e8Form_coroot_left i _).trans (e8Root_dotProduct_coroot i)

/-! ## Reflections as maps of root indices -/

/-- A map of root indices realizes reflection in the root indexed by `i`. -/
private def IsReflIndex (i : Fin 240) (f : Fin 240 → Fin 240) : Prop :=
  ∀ j, e8Coroot (f j) = e8Refl (e8Coroot i) (e8Coroot j)

private lemma IsReflIndex.involutive {i : Fin 240} {f : Fin 240 → Fin 240} (h : IsReflIndex i f) :
    Function.Involutive f := fun j => e8Coroot.injective <| by
  rw [h (f j), h j, e8Refl_involutive _ (e8Form_coroot_self i)]

/-- **Conjugating by a reflection.** If `g` reflects in the root indexed by `a` and `f` reflects in
the root indexed by `m`, then `g ∘ f ∘ g` reflects in the root indexed by `g m`. -/
private lemma IsReflIndex.conj {a m : Fin 240} {g f : Fin 240 → Fin 240}
    (hg : IsReflIndex a g) (hf : IsReflIndex m f) :
    IsReflIndex (g m) fun k => g (f (g k)) := fun k => by
  rw [hg (f (g k)), hf (g k), hg k, hg m,
    e8Refl_e8Refl _ (e8Form_coroot_self a) (e8Coroot m) (e8Coroot k)]

/-! ## The eight simple reflections

The table below is the permutation of the 240 root indices induced by reflection in each simple
root. Every one of its `8 × 240` defining identities is checked in the kernel by
`TauCeti.DynkinType.e8SimpleReflectionIndex_coroot`, so no entry is taken on trust.
-/

private def e8SimpleReflectionIndex : Fin 8 → Fin 240 → Fin 240 := ![
  ![120, 1, 14, 3, 4, 5, 6, 7, 8, 9, 10, 11, 21, 13, 2, 15, 16, 17, 27, 19, 28, 12, 22, 23, 34, 25,
   35, 18, 20, 29, 40, 31, 41, 42, 24, 26, 46, 37, 47, 48, 30, 32, 33, 52, 53, 54, 36, 38, 39, 49,
   58, 59, 43, 44, 45, 55, 63, 64, 50, 51, 60, 61, 69, 56, 57, 65, 66, 67, 74, 62, 70, 71, 72, 73,
   68, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 99, 96, 97,
   102, 95, 100, 105, 98, 103, 107, 101, 109, 104, 111, 106, 113, 108, 112, 110, 114, 115, 116,
   117, 118, 119, 0, 121, 134, 123, 124, 125, 126, 127, 128, 129, 130, 131, 141, 133, 122, 135,
   136, 137, 147, 139, 148, 132, 142, 143, 154, 145, 155, 138, 140, 149, 160, 151, 161, 162, 144,
   146, 166, 157, 167, 168, 150, 152, 153, 172, 173, 174, 156, 158, 159, 169, 178, 179, 163, 164,
   165, 175, 183, 184, 170, 171, 180, 181, 189, 176, 177, 185, 186, 187, 194, 182, 190, 191, 192,
   193, 188, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211,
   212, 213, 214, 219, 216, 217, 222, 215, 220, 225, 218, 223, 227, 221, 229, 224, 231, 226, 233,
   228, 232, 230, 234, 235, 236, 237, 238, 239],
  ![0, 121, 2, 13, 4, 5, 6, 7, 8, 9, 10, 19, 20, 3, 14, 15, 16, 25, 26, 11, 12, 28, 22, 31, 32, 17,
   18, 35, 21, 37, 38, 23, 24, 33, 41, 27, 43, 29, 30, 39, 47, 34, 42, 36, 44, 45, 52, 40, 48, 49,
   50, 51, 46, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 73, 68, 69, 70, 71, 78, 67,
   74, 75, 82, 83, 72, 79, 86, 87, 76, 77, 89, 90, 80, 81, 93, 84, 85, 91, 96, 88, 94, 95, 92, 97,
   98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 110, 109, 108, 113, 114, 111, 112, 115, 116,
   117, 118, 119, 120, 1, 122, 133, 124, 125, 126, 127, 128, 129, 130, 139, 140, 123, 134, 135,
   136, 145, 146, 131, 132, 148, 142, 151, 152, 137, 138, 155, 141, 157, 158, 143, 144, 153, 161,
   147, 163, 149, 150, 159, 167, 154, 162, 156, 164, 165, 172, 160, 168, 169, 170, 171, 166, 173,
   174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 193, 188, 189, 190, 191, 198,
   187, 194, 195, 202, 203, 192, 199, 206, 207, 196, 197, 209, 210, 200, 201, 213, 204, 205, 211,
   216, 208, 214, 215, 212, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 230, 229, 228,
   233, 234, 231, 232, 235, 236, 237, 238, 239],
  ![14, 1, 122, 12, 4, 5, 6, 7, 8, 9, 10, 18, 3, 20, 0, 15, 16, 24, 11, 26, 13, 21, 22, 30, 17, 32,
   19, 27, 28, 36, 23, 38, 25, 33, 34, 35, 29, 43, 31, 39, 40, 41, 49, 37, 44, 45, 46, 47, 55, 42,
   50, 51, 52, 60, 61, 48, 56, 57, 65, 66, 53, 54, 62, 70, 71, 58, 59, 67, 68, 75, 63, 64, 72, 73,
   79, 69, 76, 77, 78, 74, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 95, 92, 93, 98, 91, 96,
   101, 94, 99, 104, 97, 102, 106, 100, 105, 103, 107, 108, 109, 110, 112, 111, 114, 113, 115,
   116, 117, 118, 119, 134, 121, 2, 132, 124, 125, 126, 127, 128, 129, 130, 138, 123, 140, 120,
   135, 136, 144, 131, 146, 133, 141, 142, 150, 137, 152, 139, 147, 148, 156, 143, 158, 145, 153,
   154, 155, 149, 163, 151, 159, 160, 161, 169, 157, 164, 165, 166, 167, 175, 162, 170, 171, 172,
   180, 181, 168, 176, 177, 185, 186, 173, 174, 182, 190, 191, 178, 179, 187, 188, 195, 183, 184,
   192, 193, 199, 189, 196, 197, 198, 194, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210,
   215, 212, 213, 218, 211, 216, 221, 214, 219, 224, 217, 222, 226, 220, 225, 223, 227, 228, 229,
   230, 232, 231, 234, 233, 235, 236, 237, 238, 239],
  ![0, 13, 12, 123, 11, 5, 6, 7, 8, 9, 17, 4, 2, 1, 21, 15, 23, 10, 18, 19, 20, 14, 29, 16, 24, 25,
   33, 27, 28, 22, 30, 31, 39, 26, 34, 42, 36, 37, 44, 32, 40, 48, 35, 50, 38, 45, 46, 53, 41, 49,
   43, 51, 58, 47, 54, 55, 56, 57, 52, 59, 60, 67, 62, 63, 64, 65, 72, 61, 68, 69, 76, 77, 66, 73,
   74, 80, 70, 71, 78, 84, 75, 81, 82, 83, 79, 85, 86, 91, 88, 89, 94, 87, 92, 97, 90, 95, 100,
   93, 98, 99, 96, 101, 102, 103, 104, 105, 108, 107, 106, 111, 110, 109, 112, 113, 115, 114, 116,
   117, 118, 119, 120, 133, 132, 3, 131, 125, 126, 127, 128, 129, 137, 124, 122, 121, 141, 135,
   143, 130, 138, 139, 140, 134, 149, 136, 144, 145, 153, 147, 148, 142, 150, 151, 159, 146, 154,
   162, 156, 157, 164, 152, 160, 168, 155, 170, 158, 165, 166, 173, 161, 169, 163, 171, 178, 167,
   174, 175, 176, 177, 172, 179, 180, 187, 182, 183, 184, 185, 192, 181, 188, 189, 196, 197, 186,
   193, 194, 200, 190, 191, 198, 204, 195, 201, 202, 203, 199, 205, 206, 211, 208, 209, 214, 207,
   212, 217, 210, 215, 220, 213, 218, 219, 216, 221, 222, 223, 224, 225, 228, 227, 226, 231, 230,
   229, 232, 233, 235, 234, 236, 237, 238, 239],
  ![0, 1, 2, 11, 124, 10, 6, 7, 8, 16, 5, 3, 18, 19, 14, 22, 9, 17, 12, 13, 26, 27, 15, 23, 24, 25,
   20, 21, 35, 29, 30, 31, 32, 33, 34, 28, 36, 37, 38, 45, 40, 41, 42, 43, 51, 39, 46, 47, 54, 49,
   56, 44, 52, 59, 48, 61, 50, 57, 63, 53, 66, 55, 62, 58, 64, 70, 60, 67, 68, 69, 65, 71, 72, 73,
   74, 75, 76, 81, 78, 79, 85, 77, 82, 87, 88, 80, 90, 83, 84, 93, 86, 91, 92, 89, 94, 95, 96, 97,
   98, 99, 103, 101, 102, 100, 106, 105, 104, 109, 108, 107, 110, 111, 112, 113, 114, 116, 115,
   117, 118, 119, 120, 121, 122, 131, 4, 130, 126, 127, 128, 136, 125, 123, 138, 139, 134, 142,
   129, 137, 132, 133, 146, 147, 135, 143, 144, 145, 140, 141, 155, 149, 150, 151, 152, 153, 154,
   148, 156, 157, 158, 165, 160, 161, 162, 163, 171, 159, 166, 167, 174, 169, 176, 164, 172, 179,
   168, 181, 170, 177, 183, 173, 186, 175, 182, 178, 184, 190, 180, 187, 188, 189, 185, 191, 192,
   193, 194, 195, 196, 201, 198, 199, 205, 197, 202, 207, 208, 200, 210, 203, 204, 213, 206, 211,
   212, 209, 214, 215, 216, 217, 218, 219, 223, 221, 222, 220, 226, 225, 224, 229, 228, 227, 230,
   231, 232, 233, 234, 236, 235, 237, 238, 239],
  ![0, 1, 2, 3, 10, 125, 9, 7, 15, 6, 4, 17, 12, 13, 14, 8, 16, 11, 24, 25, 20, 21, 22, 23, 18, 19,
   32, 34, 28, 29, 30, 31, 26, 39, 27, 41, 36, 37, 38, 33, 40, 35, 48, 43, 44, 45, 46, 47, 42, 55,
   50, 57, 52, 53, 54, 49, 62, 51, 58, 64, 60, 61, 56, 69, 59, 65, 71, 67, 68, 63, 75, 66, 77, 73,
   74, 70, 80, 72, 83, 79, 76, 81, 86, 78, 84, 85, 82, 87, 92, 89, 90, 91, 88, 96, 94, 95, 93,
   100, 98, 99, 97, 104, 102, 103, 101, 107, 106, 105, 108, 109, 110, 111, 112, 113, 114, 115,
   117, 116, 118, 119, 120, 121, 122, 123, 130, 5, 129, 127, 135, 126, 124, 137, 132, 133, 134,
   128, 136, 131, 144, 145, 140, 141, 142, 143, 138, 139, 152, 154, 148, 149, 150, 151, 146, 159,
   147, 161, 156, 157, 158, 153, 160, 155, 168, 163, 164, 165, 166, 167, 162, 175, 170, 177, 172,
   173, 174, 169, 182, 171, 178, 184, 180, 181, 176, 189, 179, 185, 191, 187, 188, 183, 195, 186,
   197, 193, 194, 190, 200, 192, 203, 199, 196, 201, 206, 198, 204, 205, 202, 207, 212, 209, 210,
   211, 208, 216, 214, 215, 213, 220, 218, 219, 217, 224, 222, 223, 221, 227, 226, 225, 228, 229,
   230, 231, 232, 233, 234, 235, 237, 236, 238, 239],
  ![0, 1, 2, 3, 4, 9, 126, 8, 7, 5, 16, 11, 12, 13, 14, 15, 10, 23, 18, 19, 20, 21, 22, 17, 30, 31,
   26, 27, 28, 29, 24, 25, 38, 33, 40, 35, 36, 37, 32, 44, 34, 47, 42, 43, 39, 51, 46, 41, 53, 49,
   50, 45, 52, 48, 59, 60, 56, 57, 58, 54, 55, 66, 68, 63, 64, 65, 61, 72, 62, 74, 70, 71, 67, 78,
   69, 79, 76, 77, 73, 75, 84, 81, 82, 83, 80, 88, 89, 87, 85, 86, 93, 91, 92, 90, 97, 95, 96, 94,
   101, 99, 100, 98, 105, 103, 104, 102, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
   118, 117, 119, 120, 121, 122, 123, 124, 129, 6, 128, 127, 125, 136, 131, 132, 133, 134, 135,
   130, 143, 138, 139, 140, 141, 142, 137, 150, 151, 146, 147, 148, 149, 144, 145, 158, 153, 160,
   155, 156, 157, 152, 164, 154, 167, 162, 163, 159, 171, 166, 161, 173, 169, 170, 165, 172, 168,
   179, 180, 176, 177, 178, 174, 175, 186, 188, 183, 184, 185, 181, 192, 182, 194, 190, 191, 187,
   198, 189, 199, 196, 197, 193, 195, 204, 201, 202, 203, 200, 208, 209, 207, 205, 206, 213, 211,
   212, 210, 217, 215, 216, 214, 221, 219, 220, 218, 225, 223, 224, 222, 226, 227, 228, 229, 230,
   231, 232, 233, 234, 235, 236, 238, 237, 239],
  ![0, 1, 2, 3, 4, 5, 8, 127, 6, 15, 10, 11, 12, 13, 14, 9, 22, 17, 18, 19, 20, 21, 16, 29, 24, 25,
   26, 27, 28, 23, 36, 37, 32, 33, 34, 35, 30, 31, 43, 39, 46, 41, 42, 38, 50, 45, 40, 52, 48, 49,
   44, 56, 47, 58, 54, 55, 51, 62, 53, 63, 65, 61, 57, 59, 69, 60, 70, 67, 68, 64, 66, 75, 76, 73,
   74, 71, 72, 80, 82, 79, 77, 85, 78, 86, 84, 81, 83, 90, 88, 89, 87, 94, 92, 93, 91, 98, 96, 97,
   95, 102, 100, 101, 99, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
   117, 119, 118, 120, 121, 122, 123, 124, 125, 128, 7, 126, 135, 130, 131, 132, 133, 134, 129,
   142, 137, 138, 139, 140, 141, 136, 149, 144, 145, 146, 147, 148, 143, 156, 157, 152, 153, 154,
   155, 150, 151, 163, 159, 166, 161, 162, 158, 170, 165, 160, 172, 168, 169, 164, 176, 167, 178,
   174, 175, 171, 182, 173, 183, 185, 181, 177, 179, 189, 180, 190, 187, 188, 184, 186, 195, 196,
   193, 194, 191, 192, 200, 202, 199, 197, 205, 198, 206, 204, 201, 203, 210, 208, 209, 207, 214,
   212, 213, 211, 218, 216, 217, 215, 222, 220, 221, 219, 223, 224, 225, 226, 227, 228, 229, 230,
   231, 232, 233, 234, 235, 236, 237, 239, 238]
]

/-- The tabulated simple reflections are the reflections in the simple roots. Every one of these
`8 × 240` identities is checked in the kernel. -/
private lemma e8SimpleReflectionIndex_coroot (s : Fin 8) (j : Fin 240) :
    e8Coroot (e8SimpleReflectionIndex s j) = e8Coroot j -
      e8Form (e8Coroot (e8SimpleIndex s)) (e8Coroot j) • e8Coroot (e8SimpleIndex s) := by
  decide +kernel +revert

private lemma isReflIndex_e8SimpleReflectionIndex (s : Fin 8) :
    IsReflIndex (e8SimpleIndex s) (e8SimpleReflectionIndex s) := fun j => by
  rw [e8Refl_apply]
  exact e8SimpleReflectionIndex_coroot s j

/-! ## Reflection in an arbitrary root

The Weyl group of `E₈` is transitive on the 240 roots, so every root is `w αᵢ` for a simple root
`αᵢ` and a word `w` in the simple reflections. The two tables below record such a witness for each
positive root, and `TauCeti.DynkinType.IsReflIndex.conj` turns it into the reflection.
-/

/-- The image of a root index under the word `w` of simple reflections, applied right to left. -/
private def e8WordMap (w : List (Fin 8)) (k : Fin 240) : Fin 240 :=
  w.foldr e8SimpleReflectionIndex k

/-- The image of a root index under the inverse of `TauCeti.DynkinType.e8WordMap w`. -/
private def e8WordMapInv (w : List (Fin 8)) (k : Fin 240) : Fin 240 :=
  w.foldl (fun x s => e8SimpleReflectionIndex s x) k

private lemma isReflIndex_conj_word (w : List (Fin 8)) {m : Fin 240} {f : Fin 240 → Fin 240}
    (hf : IsReflIndex m f) :
    IsReflIndex (e8WordMap w m) fun k => e8WordMap w (f (e8WordMapInv w k)) := by
  induction w with
  | nil => exact hf
  | cons s w ih => exact (isReflIndex_e8SimpleReflectionIndex s).conj ih

/-- For each positive root, the simple root its Weyl-group witness starts from. -/
private def e8ReflectionSource : Fin 120 → Fin 8 := ![
  0, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1, 1, 0, 4, 3, 2, 1, 1, 0, 0, 3, 2, 1,
  1, 1, 0, 0, 2, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0,
  0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- For each positive root, a word in the simple reflections carrying
`TauCeti.DynkinType.e8ReflectionSource` to it. The words are shortest ones, found by a breadth-first
search of the Weyl orbit; `TauCeti.DynkinType.e8WordMap_e8ReflectionWord` checks each of them. -/
private def e8ReflectionWord : Fin 120 → List (Fin 8) := ![
  [], [], [], [], [], [], [], [], [7], [6], [5], [4], [3], [3], [2], [7, 6], [6, 5], [5, 4],
  [4, 3], [4, 3], [2, 3], [3, 2], [7, 6, 5], [6, 5, 4], [5, 4, 3], [5, 4, 3], [4, 2, 3],
  [4, 3, 2], [1, 3, 2], [7, 6, 5, 4], [6, 5, 4, 3], [6, 5, 4, 3], [5, 4, 2, 3], [3, 4, 2, 3],
  [5, 4, 3, 2], [4, 1, 3, 2], [7, 6, 5, 4, 3], [7, 6, 5, 4, 3], [6, 5, 4, 2, 3], [5, 3, 4, 2, 3],
  [6, 5, 4, 3, 2], [5, 4, 1, 3, 2], [3, 4, 1, 3, 2], [7, 6, 5, 4, 2, 3], [6, 5, 3, 4, 2, 3],
  [4, 5, 3, 4, 2, 3], [7, 6, 5, 4, 3, 2], [6, 5, 4, 1, 3, 2], [5, 3, 4, 1, 3, 2],
  [2, 3, 4, 1, 3, 2], [7, 6, 5, 3, 4, 2, 3], [6, 4, 5, 3, 4, 2, 3], [7, 6, 5, 4, 1, 3, 2],
  [6, 5, 3, 4, 1, 3, 2], [4, 5, 3, 4, 1, 3, 2], [5, 2, 3, 4, 1, 3, 2], [7, 6, 4, 5, 3, 4, 2, 3],
  [5, 6, 4, 5, 3, 4, 2, 3], [7, 6, 5, 3, 4, 1, 3, 2], [6, 4, 5, 3, 4, 1, 3, 2],
  [6, 5, 2, 3, 4, 1, 3, 2], [4, 5, 2, 3, 4, 1, 3, 2], [7, 5, 6, 4, 5, 3, 4, 2, 3],
  [7, 6, 4, 5, 3, 4, 1, 3, 2], [5, 6, 4, 5, 3, 4, 1, 3, 2], [7, 6, 5, 2, 3, 4, 1, 3, 2],
  [6, 4, 5, 2, 3, 4, 1, 3, 2], [3, 4, 5, 2, 3, 4, 1, 3, 2], [6, 7, 5, 6, 4, 5, 3, 4, 2, 3],
  [7, 5, 6, 4, 5, 3, 4, 1, 3, 2], [7, 6, 4, 5, 2, 3, 4, 1, 3, 2], [5, 6, 4, 5, 2, 3, 4, 1, 3, 2],
  [6, 3, 4, 5, 2, 3, 4, 1, 3, 2], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [6, 7, 5, 6, 4, 5, 3, 4, 1, 3, 2], [7, 5, 6, 4, 5, 2, 3, 4, 1, 3, 2],
  [7, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2], [5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2], [6, 7, 5, 6, 4, 5, 2, 3, 4, 1, 3, 2],
  [7, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2], [4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [7, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2], [5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [6, 7, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2], [7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [7, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2], [4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [6, 7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2], [6, 7, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [7, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2], [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [5, 6, 7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2], [6, 7, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [7, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2], [2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [5, 6, 7, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [6, 7, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [7, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [5, 6, 7, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [6, 7, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [4, 5, 6, 7, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [5, 6, 7, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [4, 5, 6, 7, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [1, 3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [2, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [4, 3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
  [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]]

/-- Each stored word carries its stored simple root to the positive root it is recorded for. -/
private lemma e8WordMap_e8ReflectionWord (i : Fin 120) :
    e8WordMap (e8ReflectionWord i) (e8SimpleIndex (e8ReflectionSource i)) = e8PositiveIndex i := by
  decide +kernel +revert

/-- Reflection in the `i`-th positive root, as a map of root indices. -/
private def e8ReflectionIndexAux (i : Fin 120) (k : Fin 240) : Fin 240 :=
  e8WordMap (e8ReflectionWord i)
    (e8SimpleReflectionIndex (e8ReflectionSource i) (e8WordMapInv (e8ReflectionWord i) k))

/-- Reflection in the root indexed by `i`, as a map of root indices. Only the residue of `i` modulo
`120` is used, a positive root and its negative reflecting alike. -/
private def e8ReflectionIndex (i : Fin 240) : Fin 240 → Fin 240 :=
  e8ReflectionIndexAux ⟨(i : ℕ) % 120, Nat.mod_lt _ (by omega)⟩

private lemma isReflIndex_e8ReflectionIndexAux (i : Fin 120) :
    IsReflIndex (e8PositiveIndex i) (e8ReflectionIndexAux i) := by
  rw [← e8WordMap_e8ReflectionWord i]
  exact isReflIndex_conj_word _ (isReflIndex_e8SimpleReflectionIndex _)

private lemma isReflIndex_e8ReflectionIndex (i : Fin 240) :
    IsReflIndex i (e8ReflectionIndex i) := by
  rcases lt_or_ge (i : ℕ) 120 with hi | hi
  · have hmod : (⟨(i : ℕ) % 120, Nat.mod_lt _ (by omega)⟩ : Fin 120) = ⟨i, hi⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hi)
    have h := isReflIndex_e8ReflectionIndexAux ⟨(i : ℕ), hi⟩
    rw [show e8PositiveIndex ⟨(i : ℕ), hi⟩ = i from Fin.ext rfl] at h
    rw [e8ReflectionIndex, hmod]
    exact h
  · have hlt : (i : ℕ) - 120 < 120 := by omega
    have hmod : (⟨(i : ℕ) % 120, Nat.mod_lt _ (by omega)⟩ : Fin 120) = ⟨(i : ℕ) - 120, hlt⟩ :=
      Fin.ext (show (i : ℕ) % 120 = (i : ℕ) - 120 by omega)
    have hneg : e8NegativeIndex ⟨(i : ℕ) - 120, hlt⟩ = i :=
      Fin.ext (show (i : ℕ) - 120 + 120 = (i : ℕ) by omega)
    have hcoroot : e8Coroot (e8PositiveIndex ⟨(i : ℕ) - 120, hlt⟩) = -e8Coroot i := by
      conv_rhs => rw [← hneg]
      rw [coroot_e8NegativeIndex, neg_neg]
    intro j
    rw [e8ReflectionIndex, hmod, isReflIndex_e8ReflectionIndexAux _ j, hcoroot, e8Refl_neg_left]

private lemma e8ReflectionIndex_coroot (i j : Fin 240) :
    e8Coroot j - (e8Root i ⬝ᵥ e8Coroot j) • e8Coroot i = e8Coroot (e8ReflectionIndex i j) := by
  rw [isReflIndex_e8ReflectionIndex i j, e8Refl_apply, e8Form_coroot_left]

/-- The pairing of the pinned tables is symmetric. This is the simply-laced feature of `E₈`: the
pairing is the symmetric bilinear form attached to `CartanMatrix.E₈`, read on the shared
simple-root coordinates of a root and its coroot. -/
theorem e8Root_dotProduct_e8Coroot_comm (i j : Fin 240) :
    e8Root i ⬝ᵥ e8Coroot j = e8Root j ⬝ᵥ e8Coroot i :=
  e8Form_comm (e8Coroot i) (e8Coroot j)

/-- The root reflections are the Cartan-matrix image of the coroot reflections, so they need no
second table. -/
private lemma e8ReflectionIndex_root (i j : Fin 240) :
    e8Root j - (e8Root j ⬝ᵥ e8Coroot i) • e8Root i = e8Root (e8ReflectionIndex i j) := by
  have h := congrArg CartanMatrix.E₈.mulVecLin (e8ReflectionIndex_coroot i j)
  rw [map_sub, map_zsmul] at h
  simpa only [Matrix.mulVecLin_apply, ← e8Root_eq_mulVec, e8Root_dotProduct_e8Coroot_comm j i]
    using h

/-- Reflection in an `E₈` root as a permutation of the pinned root indices. -/
private def e8ReflectionPerm (i : Fin 240) : Equiv.Perm (Fin 240) :=
  Function.Involutive.toPerm _ (isReflIndex_e8ReflectionIndex i).involutive

/-! ## The pinned datum -/

/-- The pinned simply connected root datum of type `E₈`.

Both lattices are `Fin 8 → ℤ`: the character lattice in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. Root indices `0` through `7` are the Bourbaki
simple roots; see `TauCeti.DynkinType.root_e8SimpleIndex`. -/
def e8SimplyConnectedRootDatum : RootDatum (Fin 240) (Fin 8 → ℤ) (Fin 8 → ℤ) where
  toLinearMap := (dotProductEquiv ℤ (Fin 8)).toLinearMap
  root := e8Root
  coroot := e8Coroot
  root_coroot_two i := e8Root_dotProduct_coroot i
  reflectionPerm := e8ReflectionPerm
  reflectionPerm_root i j := e8ReflectionIndex_root i j
  reflectionPerm_coroot i j := e8ReflectionIndex_coroot i j

/-- The root embedding of the pinned `E₈` datum is the explicit table `e8Root`. -/
@[simp] lemma e8SimplyConnectedRootDatum_root : e8SimplyConnectedRootDatum.root = e8Root := (rfl)

/-- The coroot embedding of the pinned `E₈` datum is the explicit table `e8Coroot`. -/
@[simp] lemma e8SimplyConnectedRootDatum_coroot :
    e8SimplyConnectedRootDatum.coroot = e8Coroot := (rfl)

/-- The perfect pairing of the pinned `E₈` datum is the dot product of coordinate vectors, the
fundamental-weight and simple-coroot bases being dual to one another. -/
@[simp] lemma e8SimplyConnectedRootDatum_toLinearMap (x y : Fin 8 → ℤ) :
    e8SimplyConnectedRootDatum.toLinearMap x y = x ⬝ᵥ y := (rfl)

/-- Pairing a pinned `E₈` root with a coroot computes as their coordinate dot product. -/
@[simp] lemma e8SimplyConnectedRootDatum_pairing (i j : Fin 240) :
    e8SimplyConnectedRootDatum.pairing i j = e8Root i ⬝ᵥ e8Coroot j := (rfl)

/-- **The coroots of the pinned type `E₈` datum span the cocharacter lattice.** This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. For `E₈` the
roots span the same lattice, the weight lattice and the root lattice coinciding because
`CartanMatrix.E₈` has determinant one. -/
theorem corootSpan_e8SimplyConnectedRootDatum_eq_top :
    e8SimplyConnectedRootDatum.corootSpan ℤ = ⊤ :=
  corootSpan_eq_top_of_coroot_eq_single coroot_e8SimpleIndex

/-! ## The pinned base -/

private lemma e8Coroot_eq_sum (k : Fin 240) :
    ∑ i, e8Coroot k i • e8Coroot (e8SimpleIndex i) = e8Coroot k := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

private lemma e8Root_eq_sum (k : Fin 240) :
    ∑ i, e8Coroot k i • e8Root (e8SimpleIndex i) = e8Root k := by
  have h := congrArg CartanMatrix.E₈.mulVecLin (e8Coroot_eq_sum k)
  rw [map_sum] at h
  simpa only [map_zsmul, Matrix.mulVecLin_apply, ← e8Root_eq_mulVec] using h

private lemma linearIndependent_root_e8SimpleIndex :
    LinearIndependent ℤ fun i : Fin 8 => e8Root (e8SimpleIndex i) := by
  have hcomp : (fun i : Fin 8 => e8Root (e8SimpleIndex i)) = fun i => CartanMatrix.E₈ i :=
    funext root_e8SimpleIndex
  rw [hcomp]
  exact Matrix.linearIndependent_rows_of_det_ne_zero (by rw [CartanMatrix.E₈_det]; norm_num)

private lemma linearIndependent_coroot_e8SimpleIndex :
    LinearIndependent ℤ fun i : Fin 8 => e8Coroot (e8SimpleIndex i) := by
  simpa only [coroot_e8SimpleIndex] using Pi.linearIndependent_single_one (Fin 8) ℤ

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `E₈`. Its support
is the set of the first eight root indices, carrying the simple roots in Bourbaki order. -/
def e8SimplyConnectedBase : e8SimplyConnectedRootDatum.Base where
  support := simpleSupport e8SimpleIndex_injective
  linearIndepOn_root :=
    linearIndepOn_simpleSupport _ _ linearIndependent_root_e8SimpleIndex
  linearIndepOn_coroot :=
    linearIndepOn_simpleSupport _ _ linearIndependent_coroot_e8SimpleIndex
  root_mem_or_neg_mem k := by
    rw [e8SimplyConnectedRootDatum_root, image_simpleSupport, ← e8Root_eq_sum k]
    exact sum_smul_mem_or_neg_mem_closure _ _ (e8Coroot_nonneg_or_nonpos k)
  coroot_mem_or_neg_mem k := by
    rw [e8SimplyConnectedRootDatum_coroot, image_simpleSupport, ← e8Coroot_eq_sum k]
    exact sum_smul_mem_or_neg_mem_closure _ _ (e8Coroot_nonneg_or_nonpos k)

/-- Membership in the pinned base support is exactly membership among the first eight root
indices. -/
@[simp] theorem mem_e8SimplyConnectedBase_support {k : Fin 240} :
    k ∈ e8SimplyConnectedBase.support ↔ (k : ℕ) < 8 := by
  rw [show e8SimplyConnectedBase.support = simpleSupport e8SimpleIndex_injective from rfl,
    mem_simpleSupport]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ i.isLt, fun hk => ⟨⟨k, hk⟩, Fin.ext rfl⟩⟩

/-- **The Cartan integers at the first eight root indices are Mathlib's Bourbaki-numbered `E₈`
matrix.** This pins the node order independently of the existential relabelling in
`TauCeti.HasCartanType`. -/
theorem pairing_e8SimpleIndex (i j : Fin 8) :
    e8SimplyConnectedRootDatum.pairing (e8SimpleIndex i) (e8SimpleIndex j) =
      CartanMatrix.E₈ i j := by
  rw [e8SimplyConnectedRootDatum_pairing, root_e8SimpleIndex, coroot_e8SimpleIndex,
    dotProduct_single, mul_one]

/-- **The pinned datum of type `E₈` has Cartan type `E8`.** Its Bourbaki-numbered base realizes the
standard Cartan matrix `CartanMatrix.E₈`, with the node numbering of `TauCeti.DynkinType`. -/
theorem hasCartanType_e8SimplyConnectedRootDatum :
    HasCartanType e8SimplyConnectedRootDatum e8SimplyConnectedBase E8 :=
  hasCartanType_of_pairing_eq e8SimpleIndex_injective rfl fun i j =>
    (pairing_e8SimpleIndex i j).trans (by simp)

end DynkinType

end TauCeti
