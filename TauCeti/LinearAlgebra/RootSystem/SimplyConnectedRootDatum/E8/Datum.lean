/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Lattice
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.RootSystem.Base

public section

/-!
# The simply connected root datum of type `E₈`

This file builds the pinned integral root datum of type `E₈` on the character and cocharacter
lattices `Fin 8 → ℤ`, out of the enumeration of the two hundred and forty roots in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8`. The character lattice is written in
the fundamental-weight basis and the cocharacter lattice in the simple-coroot basis, so that the
`i`-th simple root is the `i`-th row of the Bourbaki-numbered Cartan matrix `CartanMatrix.E₈` and
the `i`-th simple coroot is the `i`-th standard basis vector.

## The reflection permutations

The one piece of a root datum that an enumeration does not carry is the permutation of the root
indices induced by each reflection. It is obtained here without tabulating it. Reflection in a
norm-two vector preserves the `E₈` Gram form of the simple-coroot basis, so it maps norm-two
vectors to norm-two vectors, and it is involutive; the enumeration exhausts the norm-two vectors
(`TauCeti.DynkinType.exists_e8Coroot_eq`), so it transports along
`TauCeti.DynkinType.e8CorootEquiv` to an involutive permutation of `Fin 240`. The identities the
root datum requires then hold by bilinear algebra rather than by two hundred and forty by two
hundred and forty coordinate comparisons.

## The lattices

Only the coroots are asked to span their lattice, in
`TauCeti.DynkinType.corootSpan_e8SimplyConnectedRootDatum_eq_top`, which is the condition the
pinned Chevalley--Demazure construction consumes. In the sibling files that condition is the
asymmetric half of the pinning, the roots spanning the root lattice at the index recorded by the
Cartan determinant inside the weight lattice. Type `E₈` is one of the three types — with `F₄` and
`G₂` — whose Cartan determinant is `1`, so here the root and the weight lattice agree and the
simply connected form is also the adjoint one; the datum is nevertheless stated through the same
coroot-side condition as its siblings, which is what the per-type dispatcher will collect.

## Main definitions

* `TauCeti.DynkinType.e8ReflectionPerm`: reflection in a root, as a permutation of root indices.
* `TauCeti.DynkinType.e8SimplyConnectedRootDatum`: the pinned root datum of type `E₈`.
* `TauCeti.DynkinType.e8SimplyConnectedBase`: the base formed by the first eight root indices.

## Main results

* `TauCeti.DynkinType.hasCartanType_e8SimplyConnectedRootDatum`: the pinned base has Cartan type
  `E8`.
* `TauCeti.DynkinType.corootSpan_e8SimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate VII, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. This is the `E₈` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. Its assembly follows
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6`.
-/

namespace TauCeti

open _root_.Matrix

namespace DynkinType

/-! ## The `E₈` Gram form -/

/-- The Gram form of the simple-coroot basis is symmetric, type `E₈` being simply laced. -/
private lemma e8_vecMul_dotProduct_comm (v w : Fin 8 → ℤ) :
    (v ᵥ* CartanMatrix.E₈) ⬝ᵥ w = (w ᵥ* CartanMatrix.E₈) ⬝ᵥ v := by
  rw [← dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, CartanMatrix.E₈_isSymm]

/-- The `E₈` roots are the images of the coroots under the Cartan matrix, read on the left or,
equivalently, on the right. -/
theorem e8Root_eq_mulVec (j : Fin 240) : e8Root j = CartanMatrix.E₈ *ᵥ e8Coroot j := by
  rw [e8Root_apply, ← mulVec_transpose, CartanMatrix.E₈_isSymm]

/-- Pairing a root with a coroot is the Gram form of their simple-coroot coordinates. -/
theorem e8Root_dotProduct_e8Coroot (i j : Fin 240) :
    e8Root i ⬝ᵥ e8Coroot j = (e8Coroot i ᵥ* CartanMatrix.E₈) ⬝ᵥ e8Coroot j := by
  rw [e8Root_apply]

/-! ## Reflection as a permutation of the root indices -/

/-- The listed `E₈` coroots enumerate the norm-two vectors of the simple-coroot lattice, without
repetition. -/
noncomputable def e8CorootEquiv : Fin 240 ≃ {v : Fin 8 → ℤ // (v ᵥ* CartanMatrix.E₈) ⬝ᵥ v = 2} :=
  Equiv.ofBijective (fun k ↦ ⟨e8Coroot k, e8Coroot_vecMul_dotProduct_self k⟩)
    ⟨fun _ _ h ↦ e8Coroot.injective (congrArg Subtype.val h),
      fun v ↦ (exists_e8Coroot_eq v.2).imp fun _ hk ↦ Subtype.ext hk⟩

@[simp] theorem e8CorootEquiv_coe (k : Fin 240) : (e8CorootEquiv k : Fin 8 → ℤ) = e8Coroot k :=
  (rfl)

/-- Reflection of a norm-two vector in another one, in the simple-coroot coordinates. The Gram form
is preserved by such a reflection, so the value is again of norm two. -/
private lemma e8_reflect_dotProduct_self {u v : Fin 8 → ℤ}
    (hu : (u ᵥ* CartanMatrix.E₈) ⬝ᵥ u = 2) (hv : (v ᵥ* CartanMatrix.E₈) ⬝ᵥ v = 2) :
    ((v - ((v ᵥ* CartanMatrix.E₈) ⬝ᵥ u) • u) ᵥ* CartanMatrix.E₈) ⬝ᵥ
      (v - ((v ᵥ* CartanMatrix.E₈) ⬝ᵥ u) • u) = 2 := by
  simp only [sub_vecMul, smul_vecMul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hu, hv, e8_vecMul_dotProduct_comm u v]
  ring

private def e8Reflect (u v : {v : Fin 8 → ℤ // (v ᵥ* CartanMatrix.E₈) ⬝ᵥ v = 2}) :
    {v : Fin 8 → ℤ // (v ᵥ* CartanMatrix.E₈) ⬝ᵥ v = 2} :=
  ⟨v.1 - ((v.1 ᵥ* CartanMatrix.E₈) ⬝ᵥ u.1) • u.1, e8_reflect_dotProduct_self u.2 v.2⟩

private lemma e8Reflect_coe (u v : {v : Fin 8 → ℤ // (v ᵥ* CartanMatrix.E₈) ⬝ᵥ v = 2}) :
    (e8Reflect u v : Fin 8 → ℤ) = v.1 - ((v.1 ᵥ* CartanMatrix.E₈) ⬝ᵥ u.1) • u.1 := (rfl)

private lemma e8Reflect_involutive (u : {v : Fin 8 → ℤ // (v ᵥ* CartanMatrix.E₈) ⬝ᵥ v = 2}) :
    Function.Involutive (e8Reflect u) := by
  intro v
  have hcoeff : ((v.1 - ((v.1 ᵥ* CartanMatrix.E₈) ⬝ᵥ u.1) • u.1) ᵥ* CartanMatrix.E₈) ⬝ᵥ u.1 =
      -((v.1 ᵥ* CartanMatrix.E₈) ⬝ᵥ u.1) := by
    rw [sub_vecMul, smul_vecMul, sub_dotProduct, smul_dotProduct, smul_eq_mul, u.2]
    ring
  refine Subtype.ext ?_
  rw [e8Reflect_coe, e8Reflect_coe, hcoeff, neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- Reflection in an `E₈` root as a permutation of the pinned root indices. It is transported from
reflection of norm-two vectors along the enumeration `TauCeti.DynkinType.e8CorootEquiv`, so no
table of reflected indices is stored. -/
noncomputable def e8ReflectionPerm (i : Fin 240) : Equiv.Perm (Fin 240) :=
  e8CorootEquiv.permCongr.symm
    (Function.Involutive.toPerm _ (e8Reflect_involutive (e8CorootEquiv i)))

/-- Reflection in the `i`-th root sends the `j`-th coroot to the reflected coordinate vector. -/
theorem e8Coroot_e8ReflectionPerm (i j : Fin 240) :
    e8Coroot (e8ReflectionPerm i j) =
      e8Coroot j - ((e8Coroot j ᵥ* CartanMatrix.E₈) ⬝ᵥ e8Coroot i) • e8Coroot i := by
  have h : e8CorootEquiv (e8ReflectionPerm i j) =
      e8Reflect (e8CorootEquiv i) (e8CorootEquiv j) := by
    rw [e8ReflectionPerm, Equiv.permCongr_symm, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
    rfl
  have hval := congrArg Subtype.val h
  rwa [e8CorootEquiv_coe, e8Reflect_coe, e8CorootEquiv_coe, e8CorootEquiv_coe] at hval

/-- The reflection permutations are compatible with the coroot table, in the form the root datum
requires. -/
theorem e8ReflectionPerm_coroot (i j : Fin 240) :
    e8Coroot j - (e8Root i ⬝ᵥ e8Coroot j) • e8Coroot i = e8Coroot (e8ReflectionPerm i j) := by
  rw [e8Coroot_e8ReflectionPerm, e8Root_dotProduct_e8Coroot,
    e8_vecMul_dotProduct_comm (e8Coroot i) (e8Coroot j)]

/-- The reflection permutations are compatible with the root table, in the form the root datum
requires. -/
theorem e8ReflectionPerm_root (i j : Fin 240) :
    e8Root j - (e8Root j ⬝ᵥ e8Coroot i) • e8Root i = e8Root (e8ReflectionPerm i j) := by
  have h := congrArg (fun x : Fin 8 → ℤ ↦ x ᵥ* CartanMatrix.E₈) (e8Coroot_e8ReflectionPerm i j)
  simp only [sub_vecMul, smul_vecMul, ← e8Root_apply] at h
  rw [h, e8Root_dotProduct_e8Coroot]

/-! ## The pinned datum -/

/-- The pinned simply connected root datum of type `E₈`.

Both lattices are `Fin 8 → ℤ`: the character lattice in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. Root indices `0` through `7` are the Bourbaki
simple roots; see `TauCeti.DynkinType.e8Root_simple`. -/
noncomputable def e8SimplyConnectedRootDatum : RootDatum (Fin 240) (Fin 8 → ℤ) (Fin 8 → ℤ) where
  toLinearMap := (dotProductEquiv ℤ (Fin 8)).toLinearMap
  root := e8Root
  coroot := e8Coroot
  root_coroot_two i := e8Root_dotProduct_coroot i
  reflectionPerm := e8ReflectionPerm
  reflectionPerm_root i j := e8ReflectionPerm_root i j
  reflectionPerm_coroot i j := e8ReflectionPerm_coroot i j

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

/-! ## The pinned base -/

/-- The index of the `i`-th Bourbaki simple root in the pinned `E₈` enumeration. -/
def e8SimpleIndex (i : Fin 8) : Fin 240 := Fin.castAdd 232 i

@[simp] lemma e8SimpleIndex_val (i : Fin 8) : (e8SimpleIndex i : ℕ) = i := (rfl)

lemma e8SimpleIndex_injective : Function.Injective e8SimpleIndex :=
  Fin.castAdd_injective _ _

/-- The simple roots of the pinned `E₈` datum are the rows of the Bourbaki Cartan matrix. -/
@[simp] theorem root_e8SimpleIndex (i : Fin 8) :
    e8Root (e8SimpleIndex i) = CartanMatrix.E₈.row i := e8Root_simple i

/-- The simple coroots of the pinned `E₈` datum are the standard basis vectors. -/
@[simp] theorem coroot_e8SimpleIndex (i : Fin 8) :
    e8Coroot (e8SimpleIndex i) = Pi.single i 1 := e8Coroot_simple i

/-- **The coroots of the pinned type `E₈` datum span the cocharacter lattice.** This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. -/
theorem corootSpan_e8SimplyConnectedRootDatum_eq_top :
    e8SimplyConnectedRootDatum.corootSpan ℤ = ⊤ :=
  corootSpan_eq_top_of_coroot_eq_single coroot_e8SimpleIndex

/-- The support of the pinned base of type `E₈`: the first eight root indices. -/
private abbrev e8SimpleSupport : Finset (Fin 240) := simpleSupport e8SimpleIndex_injective

/-- Every `E₈` coroot has simple-coroot coordinates that are all nonnegative or all nonpositive,
the positive half of the table being nonnegative and the negative half its negation. -/
private lemma e8Coroot_nonneg_or_nonpos (j : Fin 240) :
    (∀ k, 0 ≤ e8Coroot j k) ∨ (∀ k, e8Coroot j k ≤ 0) := by
  induction j using Fin.addCases (m := 120) (n := 120) with
  | left j =>
    refine Or.inl fun k ↦ ?_
    rw [e8Coroot_castAdd]
    exact e8PositiveCoroot_nonneg _ k
  | right j =>
    refine Or.inr fun k ↦ ?_
    rw [Fin.natAdd_eq_addNat, e8Coroot_addNat, Pi.neg_apply, neg_nonpos]
    exact e8PositiveCoroot_nonneg _ k

/-- In the cocharacter lattice a coroot is the combination of the simple coroots recorded by its
own coordinates, the simple coroots being the standard basis. -/
private lemma sum_smul_coroot_e8SimpleIndex (j : Fin 240) :
    ∑ k : Fin 8, e8Coroot j k • e8Coroot (e8SimpleIndex k) = e8Coroot j := by
  have hk (k : Fin 8) :
      e8Coroot j k • e8Coroot (e8SimpleIndex k) = Pi.single k (e8Coroot j k) := by
    rw [coroot_e8SimpleIndex, ← Pi.single_smul', smul_eq_mul, mul_one]
  simpa only [hk] using LinearMap.sum_single_apply _ (e8Coroot j)

/-- In the character lattice a root is the combination of the simple roots recorded by the same
coordinates, the two tables differing by the Cartan-matrix map. -/
private lemma sum_smul_root_e8SimpleIndex (j : Fin 240) :
    ∑ k : Fin 8, e8Coroot j k • e8Root (e8SimpleIndex k) = e8Root j := by
  have h := congrArg CartanMatrix.E₈.mulVecLin (sum_smul_coroot_e8SimpleIndex j)
  rw [map_sum] at h
  simpa only [map_zsmul, mulVecLin_apply, ← e8Root_eq_mulVec] using h

private lemma linearIndependent_root_e8SimpleIndex :
    LinearIndependent ℤ fun i : Fin 8 ↦ e8Root (e8SimpleIndex i) := by
  have h : (fun i : Fin 8 ↦ e8Root (e8SimpleIndex i)) = fun i ↦ CartanMatrix.E₈ i :=
    funext root_e8SimpleIndex
  rw [h]
  exact linearIndependent_rows_of_det_ne_zero (by rw [CartanMatrix.E₈_det]; norm_num)

private lemma linearIndependent_coroot_e8SimpleIndex :
    LinearIndependent ℤ fun i : Fin 8 ↦ e8Coroot (e8SimpleIndex i) := by
  simpa only [coroot_e8SimpleIndex] using Pi.linearIndependent_single_one (Fin 8) ℤ

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `E₈`. Its support
is the set of the first eight root indices, carrying the simple roots in Bourbaki order. -/
noncomputable def e8SimplyConnectedBase : e8SimplyConnectedRootDatum.Base where
  support := e8SimpleSupport
  linearIndepOn_root :=
    linearIndepOn_simpleSupport _ _ linearIndependent_root_e8SimpleIndex
  linearIndepOn_coroot :=
    linearIndepOn_simpleSupport _ _ linearIndependent_coroot_e8SimpleIndex
  root_mem_or_neg_mem k := by
    simp only [e8SimplyConnectedRootDatum_root]
    rw [image_simpleSupport, ← sum_smul_root_e8SimpleIndex k]
    exact sum_smul_mem_or_neg_mem_closure _ _ (e8Coroot_nonneg_or_nonpos k)
  coroot_mem_or_neg_mem k := by
    simp only [e8SimplyConnectedRootDatum_coroot]
    rw [image_simpleSupport, ← sum_smul_coroot_e8SimpleIndex k]
    exact sum_smul_mem_or_neg_mem_closure _ _ (e8Coroot_nonneg_or_nonpos k)

/-- The support of the pinned base of type `E₈` is the image of the simple index map, the field
it is built from. -/
private lemma e8SimplyConnectedBase_support :
    e8SimplyConnectedBase.support = simpleSupport e8SimpleIndex_injective := (rfl)

/-- Membership in the pinned base support is exactly membership among the first eight root
indices. -/
@[simp] theorem mem_e8SimplyConnectedBase_support {k : Fin 240} :
    k ∈ e8SimplyConnectedBase.support ↔ (k : ℕ) < 8 := by
  rw [e8SimplyConnectedBase_support, mem_simpleSupport]
  constructor
  · rintro ⟨i, rfl⟩
    rw [e8SimpleIndex_val]
    exact i.isLt
  · exact fun hk ↦ ⟨⟨k, hk⟩, Fin.ext (by rw [e8SimpleIndex_val])⟩

/-- **The Cartan integers at the first eight root indices are Mathlib's Bourbaki-numbered `E₈`
matrix.** This pins the node order independently of the existential relabelling in
`TauCeti.HasCartanType`. -/
theorem pairing_e8SimpleIndex (i j : Fin 8) :
    e8SimplyConnectedRootDatum.pairing (e8SimpleIndex i) (e8SimpleIndex j) =
      CartanMatrix.E₈ i j := by
  rw [e8SimplyConnectedRootDatum_pairing, root_e8SimpleIndex, coroot_e8SimpleIndex,
    dotProduct_single, mul_one]
  rfl

/-- **The pinned datum of type `E₈` has Cartan type `E8`.** Its Bourbaki-numbered base realizes the
standard Cartan matrix `CartanMatrix.E₈`, with the node numbering of `TauCeti.DynkinType`. -/
theorem hasCartanType_e8SimplyConnectedRootDatum :
    HasCartanType e8SimplyConnectedRootDatum e8SimplyConnectedBase E8 :=
  hasCartanType_of_pairing_eq e8SimpleIndex_injective rfl fun i j ↦
    (pairing_e8SimpleIndex i j).trans (by simp)

end DynkinType

end TauCeti
