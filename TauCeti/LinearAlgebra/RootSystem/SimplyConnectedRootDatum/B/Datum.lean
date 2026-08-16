/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Model

public section

/-!
# The simply connected root datum of type `Bₙ`

This file assembles the coordinate model of
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Model` into the pinned integral root
datum of type `Bₙ`, uniformly in the rank `n`, on the character and cocharacter lattices
`Fin n → ℤ`. The character lattice is written in the fundamental-weight basis and the cocharacter
lattice in the simple-coroot basis, so the `i`-th simple root is the `i`-th row of the
Bourbaki-numbered Cartan matrix `CartanMatrix.B n` and the `i`-th simple coroot is the `i`-th
standard basis vector.

## The enumeration

The roots are indexed by `Fin (2 * n ^ 2)`, which is `TauCeti.DynkinType.numRoots (.B n)`. The
model names a root by a signed basis vector `u` together with a cyclic offset `d`, so the raw index
type is `Fin (2 * n) × Fin n`; the enumeration rotates the first coordinate and reverses the second
so that the Bourbaki simple roots come first. All but the last simple root are long and the last
one is short, so they cannot occupy a single block of a product enumeration: the rotation puts
`α₀, …, α_{n-2}` at indices `0, …, n - 2` and sends the short `α_{n-1}` elsewhere, and a single
transposition then brings that one to index `n - 1`.

Only the coroots are asked to span their lattice, and only that half is recorded, in
`TauCeti.DynkinType.corootSpan_typeBSimplyConnectedRootDatum_eq_top`. The roots span the root
lattice, which for `0 < n` sits inside the weight lattice with index `2` (Bourbaki, Plate II); at
`n = 0` both lattices are trivial and the two coincide. So the datum is a `RootDatum` carrying no
`RootPairing.IsRootSystem` instance. That asymmetry is what "simply connected" means here.

## Main definitions

* `TauCeti.DynkinType.typeBSimplyConnectedRootDatum`: the pinned root datum of type `Bₙ`.
* `TauCeti.DynkinType.typeBSimpleIndex`: the first `n` root indices, the Bourbaki-numbered simple
  roots.
* `TauCeti.DynkinType.typeBSimplyConnectedBase`: the base they form.

Nothing here is `@[expose]`d: the datum, its enumeration and its base are used through the lemmas
below, not by unfolding.

## Main results

* `TauCeti.DynkinType.root_typeBSimpleIndex` and `TauCeti.DynkinType.coroot_typeBSimpleIndex`: the
  `i`-th simple root is the `i`-th row of `CartanMatrix.B n` and the `i`-th simple coroot is
  `Pi.single i 1`, which is what pins the two lattices as the weight and coroot lattices.
* `TauCeti.DynkinType.hasCartanType_typeBSimplyConnectedRootDatum`: the pinned base has Cartan
  type `B n`.
* `TauCeti.DynkinType.corootSpan_typeBSimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate II, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. This is the `Bₙ` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

namespace TauCeti.DynkinType

open Function Set Submodule TypeB

variable {n : ℕ}

/-! ## Reading off the coordinates of an explicit signed basis vector -/

private lemma typeB_sgn_mk_lt {a : ℕ} (h2 : a < 2 * n) (h : a < n) :
    sgn (⟨a, h2⟩ : Fin (2 * n)) = 1 := by
  rw [sgn_def, ite_eq_left h]

private lemma typeB_sgn_mk_ge {a : ℕ} (h2 : a < 2 * n) (h : n ≤ a) :
    sgn (⟨a, h2⟩ : Fin (2 * n)) = -1 := by
  rw [sgn_def, ite_eq_right (show ¬(a < n) by omega)]

private lemma typeB_axis_mk_lt {a : ℕ} (h2 : a < 2 * n) (h : a < n) :
    axis (⟨a, h2⟩ : Fin (2 * n)) = a := by
  rw [axis_def, ite_eq_left h]

private lemma typeB_axis_mk_ge {a : ℕ} (h2 : a < 2 * n) (h : n ≤ a) :
    axis (⟨a, h2⟩ : Fin (2 * n)) = a - n :=
  by rw [axis_def, ite_eq_right (show ¬(a < n) by omega)]

private lemma typeB_signedWeight_mk_lt {a : ℕ} (h2 : a < 2 * n) (h : a < n) :
    signedWeight (⟨a, h2⟩ : Fin (2 * n)) = weight n a := by
  rw [signedWeight_def, typeB_sgn_mk_lt h2 h, typeB_axis_mk_lt h2 h, one_smul]

private lemma typeB_signedWeight_mk_ge {a : ℕ} (h2 : a < 2 * n) (h : n ≤ a) :
    signedWeight (⟨a, h2⟩ : Fin (2 * n)) = -weight n (a - n) := by
  rw [signedWeight_def, typeB_sgn_mk_ge h2 h, typeB_axis_mk_ge h2 h, neg_one_smul]

private lemma coe_shift_mk {a b : ℕ} (ha : a < 2 * n) (hb : b < n) :
    ((shift (⟨a, ha⟩ : Fin (2 * n)) ⟨b, hb⟩ : Fin (2 * n)) : ℕ) =
      if a + b < 2 * n then a + b else a + b - 2 * n := by
  rw [coe_shift]

private lemma shift_mk {a b c : ℕ} (ha : a < 2 * n) (hb : b < n) (hc : c < 2 * n)
    (h : (if a + b < 2 * n then a + b else a + b - 2 * n) = c) :
    shift (⟨a, ha⟩ : Fin (2 * n)) ⟨b, hb⟩ = ⟨c, hc⟩ :=
  Fin.ext (by rw [coe_shift_mk]; exact h)

private lemma typeB_signedCoweight_mk_lt {a : ℕ} (h2 : a < 2 * n) (h : a < n) :
    signedCoweight (⟨a, h2⟩ : Fin (2 * n)) = coweight n a := by
  rw [signedCoweight_def, typeB_sgn_mk_lt h2 h, typeB_axis_mk_lt h2 h, one_smul]

/-! ## The reflection permutation on the raw index type -/

/-- The reflection in the root indexed by `z`, acting on the raw index type. -/
private def typeBReflIdx (z w : Fin (2 * n) × Fin n) : Fin (2 * n) × Fin n :=
  index (reflMap z.1 (shift z.1 z.2) w.1) (reflMap z.1 (shift z.1 z.2) (shift w.1 w.2))

private lemma typeBReflIdx_involutive (z : Fin (2 * n) × Fin n) : Involutive (typeBReflIdx z) := by
  intro w
  have hpq : IsPair z.1 (shift z.1 z.2) := isPair_shift _ _
  have hw : IsPair w.1 (shift w.1 w.2) := isPair_shift _ _
  have hRw := isPair_reflMap hpq hw
  have hinv := reflMap_involutive hpq
  simp only [typeBReflIdx]
  rcases shift_index hRw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2, h1, hinv, hinv, index_shift]
  · rw [h2, h1, hinv, hinv, ← index_comm hw, index_shift]

private lemma rootIdx_typeBReflIdx (z w : Fin (2 * n) × Fin n) :
    rootIdx w - (rootIdx w ⬝ᵥ corootIdx z) • rootIdx z = rootIdx (typeBReflIdx z w) := by
  have hpq : IsPair z.1 (shift z.1 z.2) := isPair_shift _ _
  have hw : IsPair w.1 (shift w.1 w.2) := isPair_shift _ _
  have hRw := isPair_reflMap hpq hw
  rw [typeBReflIdx, rootIdx_index hRw, rootIdx_def, rootIdx_def, corootIdx_def]
  rcases eq_or_ne w.1 (shift w.1 w.2) with heq | hne
  · rw [← heq, rootOfPair_self, rootOfPair_self, signedWeight_reflMap hpq]
  · have hne' : reflMap z.1 (shift z.1 z.2) w.1 ≠
        reflMap z.1 (shift z.1 z.2) (shift w.1 w.2) :=
      fun hc => hne ((reflMap_involutive hpq).injective hc)
    rw [rootOfPair_of_ne hne, rootOfPair_of_ne hne', signedWeight_reflMap hpq,
      signedWeight_reflMap hpq,
      add_dotProduct, add_smul]
    abel

private lemma corootIdx_typeBReflIdx (z w : Fin (2 * n) × Fin n) :
    corootIdx w - (rootIdx z ⬝ᵥ corootIdx w) • corootIdx z = corootIdx (typeBReflIdx z w) := by
  have hpq : IsPair z.1 (shift z.1 z.2) := isPair_shift _ _
  have hw : IsPair w.1 (shift w.1 w.2) := isPair_shift _ _
  have hRw := isPair_reflMap hpq hw
  set p := z.1 with hp
  set q := shift z.1 z.2 with hq
  set u := w.1 with hu
  set v := shift w.1 w.2 with hv
  rw [typeBReflIdx, corootIdx_index hRw, corootIdx_def, corootIdx_def, rootIdx_def,
    ← hp, ← hq, ← hu, ← hv]
  refine smul_right_injective _ (by norm_num : (2 : ℤ) ≠ 0) ?_
  have hc : (2 : ℤ) * (rootOfPair p q ⬝ᵥ corootOfPair u v) =
      rootOfPair p q ⬝ᵥ signedCoweight u + rootOfPair p q ⬝ᵥ signedCoweight v := by
    rw [← dotProduct_add, ← corootOfPair_add_self u v, dotProduct_add]
    ring
  calc (2 : ℤ) • (corootOfPair u v -
        (rootOfPair p q ⬝ᵥ corootOfPair u v) • corootOfPair p q)
      = (2 : ℤ) • corootOfPair u v -
          ((2 : ℤ) * (rootOfPair p q ⬝ᵥ corootOfPair u v)) • corootOfPair p q := by
        simp only [smul_sub, smul_smul]
    _ = signedCoweight u + signedCoweight v -
          (rootOfPair p q ⬝ᵥ signedCoweight u + rootOfPair p q ⬝ᵥ signedCoweight v) •
            corootOfPair p q := by
        rw [two_smul_corootOfPair, hc]
    _ = (signedCoweight u - (rootOfPair p q ⬝ᵥ signedCoweight u) • corootOfPair p q) +
          (signedCoweight v - (rootOfPair p q ⬝ᵥ signedCoweight v) • corootOfPair p q) := by
        simp only [add_smul]
        abel
    _ = signedCoweight (reflMap p q u) + signedCoweight (reflMap p q v) := by
        rw [signedCoweight_reflMap hpq, signedCoweight_reflMap hpq]
    _ = (2 : ℤ) • corootOfPair (reflMap p q u) (reflMap p q v) :=
      (two_smul_corootOfPair _ _).symm

private lemma rootIdx_injective : Injective (rootIdx : Fin (2 * n) × Fin n → Fin n → ℤ) := by
  intro z z' h
  refine index_eq_of_pair_mem_iff fun m => ?_
  rw [← rootIdx_dotProduct_signedCoweight_eq_two_iff,
    ← rootIdx_dotProduct_signedCoweight_eq_two_iff, h]

private lemma corootIdx_injective : Injective (corootIdx : Fin (2 * n) × Fin n → Fin n → ℤ) := by
  intro z z' h
  refine index_eq_of_pair_mem_iff fun m => ?_
  rw [← two_mul_signedWeight_dotProduct_corootIdx_iff,
    ← two_mul_signedWeight_dotProduct_corootIdx_iff, h]

/-! ## The enumeration of the roots -/

private lemma typeB_lt_two_mul_sq {i : ℕ} (hi : i < n) : i < 2 * n ^ 2 :=
  lt_of_lt_of_le hi (le_trans (Nat.le_self_pow (by norm_num) n)
    (Nat.le_mul_of_pos_left (n ^ 2) (by norm_num)))

/-- The rotation of the signed basis vectors by `n - 1` steps. Composed with the reversal of the
offsets it moves the long simple roots to the front of the enumeration. -/
private def typeBRot (n : ℕ) : Equiv.Perm (Fin (2 * n)) where
  toFun u := ⟨if (u : ℕ) + (n - 1) < 2 * n then (u : ℕ) + (n - 1) else (u : ℕ) + (n - 1) - 2 * n,
    by have := u.isLt; split <;> omega⟩
  invFun u := ⟨if (u : ℕ) + (n + 1) < 2 * n then (u : ℕ) + (n + 1) else (u : ℕ) + (n + 1) - 2 * n,
    by have := u.isLt; split <;> omega⟩
  left_inv u := by
    have := u.isLt
    refine Fin.ext ?_
    dsimp only
    split_ifs <;> omega
  right_inv u := by
    have := u.isLt
    refine Fin.ext ?_
    dsimp only
    split_ifs <;> omega

private lemma typeB_two_mul_sq (n : ℕ) : n * (2 * n) = 2 * n ^ 2 := by ring

/-- The enumeration of the roots before the final transposition: the offset indexes the block and
the rotated signed basis vector indexes the position inside it. -/
private def typeBEnum₀ (n : ℕ) : Fin (2 * n) × Fin n ≃ Fin (2 * n ^ 2) :=
  (((typeBRot n).prodCongr Fin.revPerm).trans (Equiv.prodComm _ _)).trans
    (finProdFinEquiv.trans (finCongr (typeB_two_mul_sq n)))

private lemma coe_typeBEnum₀ {a b : ℕ} (ha : a < 2 * n) (hb : b < n) :
    ((typeBEnum₀ n (⟨a, ha⟩, ⟨b, hb⟩) : Fin (2 * n ^ 2)) : ℕ) =
      (if a + (n - 1) < 2 * n then a + (n - 1) else a + (n - 1) - 2 * n) +
        2 * n * (n - (b + 1)) := (rfl)

/-- The raw index of the short simple root `α_{n-1} = e_{n-1}`. -/
private def typeBShortPair (n : ℕ) (h : 0 < n) : Fin (2 * n) × Fin n :=
  (⟨n - 1, by omega⟩, ⟨0, h⟩)

/-- The transposition bringing the short simple root to index `n - 1`. -/
private def typeBSwapLast (n : ℕ) : Equiv.Perm (Fin (2 * n ^ 2)) :=
  if h : 0 < n then
    Equiv.swap (⟨n - 1, typeB_lt_two_mul_sq (by omega)⟩ : Fin (2 * n ^ 2))
      (typeBEnum₀ n (typeBShortPair n h))
  else Equiv.refl _

/-- The pinned enumeration of the roots of type `Bₙ` by `Fin (2 * n ^ 2)`, arranged so that the
Bourbaki simple roots occupy the first `n` indices. -/
private def typeBEnum (n : ℕ) : Fin (2 * n) × Fin n ≃ Fin (2 * n ^ 2) :=
  (typeBEnum₀ n).trans (typeBSwapLast n)

/-- The raw index of the `i`-th Bourbaki simple root: the short root `e_{n-1}` at the last node,
and the pair `{-e_{i+1}, e_i}` otherwise. -/
private def typeBSimplePair (i : Fin n) : Fin (2 * n) × Fin n :=
  if h : (i : ℕ) + 1 = n then typeBShortPair n (by have := i.isLt; omega)
  else (⟨n + (i : ℕ) + 1, by have := i.isLt; omega⟩, ⟨n - 1, by have := i.isLt; omega⟩)

/-- The `i`-th simple root of type `Bₙ` sits at root index `i`, the Bourbaki node `i + 1`. -/
def typeBSimpleIndex (n : ℕ) (i : Fin n) : Fin (2 * n ^ 2) :=
  ⟨i, typeB_lt_two_mul_sq i.isLt⟩

@[simp] lemma typeBSimpleIndex_val (i : Fin n) : (typeBSimpleIndex n i : ℕ) = i := (rfl)

lemma typeBSimpleIndex_injective : Injective (typeBSimpleIndex n) := fun i j h =>
  Fin.ext (by simpa using congrArg Fin.val h)

private lemma typeBEnum_typeBSimplePair (i : Fin n) :
    typeBEnum n (typeBSimplePair i) = typeBSimpleIndex n i := by
  have hi := i.isLt
  have hpos : 0 < n := by omega
  have hswap : typeBSwapLast n =
      Equiv.swap (⟨n - 1, typeB_lt_two_mul_sq (show n - 1 < n by omega)⟩ : Fin (2 * n ^ 2))
        (typeBEnum₀ n (typeBShortPair n hpos)) := by
    rw [typeBSwapLast, dite_eq_left hpos]
  by_cases hlast : (i : ℕ) + 1 = n
  · have hsp : typeBSimplePair i = typeBShortPair n hpos := by
      rw [typeBSimplePair, dite_eq_left hlast]
    rw [typeBEnum, Equiv.trans_apply, hsp, hswap, Equiv.swap_apply_right]
    exact Fin.ext (show n - 1 = (i : ℕ) from by omega)
  · have hval : ((typeBEnum₀ n (typeBSimplePair i) : Fin (2 * n ^ 2)) : ℕ) = (i : ℕ) := by
      rw [typeBSimplePair, dite_eq_right hlast, coe_typeBEnum₀,
        show n - (n - 1 + 1) = 0 by omega, Nat.mul_zero, Nat.add_zero]
      split_ifs <;> omega
    have hne1 : typeBEnum₀ n (typeBSimplePair i) ≠
        (⟨n - 1, typeB_lt_two_mul_sq (show n - 1 < n by omega)⟩ : Fin (2 * n ^ 2)) := by
      intro hc
      have h4 : (i : ℕ) = n - 1 := by rw [← hval]; exact congrArg Fin.val hc
      omega
    have hne2 : typeBEnum₀ n (typeBSimplePair i) ≠ typeBEnum₀ n (typeBShortPair n hpos) := by
      intro hc
      have heq := (typeBEnum₀ n).injective hc
      rw [typeBSimplePair, dite_eq_right hlast, typeBShortPair] at heq
      have h3 := congrArg Prod.fst heq
      have h4 : n + (i : ℕ) + 1 = n - 1 := congrArg Fin.val h3
      omega
    rw [typeBEnum, Equiv.trans_apply, hswap, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    exact Fin.ext (by rw [hval, typeBSimpleIndex_val])

private lemma typeBEnum_symm_typeBSimpleIndex (i : Fin n) :
    (typeBEnum n).symm (typeBSimpleIndex n i) = typeBSimplePair i := by
  rw [← typeBEnum_typeBSimplePair i, Equiv.symm_apply_apply]

/-! ## The root datum -/

/-- The standard dot-product pairing on the character and cocharacter coordinate lattices is
perfect; this local instance supplies the perfect pairing required to construct the root datum. -/
private instance : (dotProductBilin ℤ ℤ :
    (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) →ₗ[ℤ] ℤ).IsPerfPair := by
  -- `dotProductEquiv` has `dotProductBilin` as its underlying linear map by definition.
  change (dotProductEquiv ℤ (Fin n)).toLinearMap.IsPerfPair
  infer_instance

/-- The reflection in the root at index `k`, transported to the enumerated index type. -/
private def typeBReflPerm (n : ℕ) (k : Fin (2 * n ^ 2)) : Equiv.Perm (Fin (2 * n ^ 2)) :=
  ((typeBEnum n).symm.trans
    (Involutive.toPerm _ (typeBReflIdx_involutive ((typeBEnum n).symm k)))).trans (typeBEnum n)

private lemma typeBReflPerm_apply (k l : Fin (2 * n ^ 2)) :
    (typeBEnum n).symm (typeBReflPerm n k l) =
      typeBReflIdx ((typeBEnum n).symm k) ((typeBEnum n).symm l) := by
  simp [typeBReflPerm]

private lemma typeBReflPerm_root (k l : Fin (2 * n ^ 2)) :
    rootIdx ((typeBEnum n).symm l) -
        (rootIdx ((typeBEnum n).symm l) ⬝ᵥ corootIdx ((typeBEnum n).symm k)) •
          rootIdx ((typeBEnum n).symm k) =
      rootIdx ((typeBEnum n).symm (typeBReflPerm n k l)) := by
  rw [typeBReflPerm_apply]
  exact rootIdx_typeBReflIdx _ _

private lemma typeBReflPerm_coroot (k l : Fin (2 * n ^ 2)) :
    corootIdx ((typeBEnum n).symm l) -
        (rootIdx ((typeBEnum n).symm k) ⬝ᵥ corootIdx ((typeBEnum n).symm l)) •
          corootIdx ((typeBEnum n).symm k) =
      corootIdx ((typeBEnum n).symm (typeBReflPerm n k l)) := by
  rw [typeBReflPerm_apply]
  exact corootIdx_typeBReflIdx _ _

private lemma rootIdx_dotProduct_corootIdx (z : Fin (2 * n) × Fin n) :
    rootIdx z ⬝ᵥ corootIdx z = 2 := by
  rw [rootIdx_def, corootIdx_def]
  exact rootOfPair_dotProduct_corootOfPair (isPair_shift z.1 z.2)

/-- The pinned simply connected root datum of type `Bₙ`.

Both lattices are `Fin n → ℤ`: the character lattice in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. The `2 * n ^ 2` roots are the classical
`± e_a ± e_b` and `± e_a`, enumerated with the simple roots first; see
`TauCeti.DynkinType.root_typeBSimpleIndex`. -/
def typeBSimplyConnectedRootDatum (n : ℕ) :
    RootDatum (Fin (2 * n ^ 2)) (Fin n → ℤ) (Fin n → ℤ) where
  toLinearMap := dotProductBilin ℤ ℤ
  root := ⟨fun k => rootIdx ((typeBEnum n).symm k),
    rootIdx_injective.comp (typeBEnum n).symm.injective⟩
  coroot := ⟨fun k => corootIdx ((typeBEnum n).symm k),
    corootIdx_injective.comp (typeBEnum n).symm.injective⟩
  root_coroot_two k := rootIdx_dotProduct_corootIdx ((typeBEnum n).symm k)
  reflectionPerm := typeBReflPerm n
  reflectionPerm_root := typeBReflPerm_root
  reflectionPerm_coroot := typeBReflPerm_coroot

/-- The pinned pairing is the classical dot product, in both the fundamental-weight and the
simple-coroot coordinates. -/
@[simp] theorem toLinearMap_typeBSimplyConnectedRootDatum (x y : Fin n → ℤ) :
    (typeBSimplyConnectedRootDatum n).toLinearMap x y = x ⬝ᵥ y := (rfl)

private lemma root_typeBSimplyConnectedRootDatum (k : Fin (2 * n ^ 2)) :
    (typeBSimplyConnectedRootDatum n).root k = rootIdx ((typeBEnum n).symm k) := (rfl)

private lemma coroot_typeBSimplyConnectedRootDatum (k : Fin (2 * n ^ 2)) :
    (typeBSimplyConnectedRootDatum n).coroot k = corootIdx ((typeBEnum n).symm k) := (rfl)

private lemma pairing_typeBSimplyConnectedRootDatum (k l : Fin (2 * n ^ 2)) :
    (typeBSimplyConnectedRootDatum n).pairing k l =
      (typeBSimplyConnectedRootDatum n).root k ⬝ᵥ (typeBSimplyConnectedRootDatum n).coroot l :=
  (rfl)

/-- The roots of the pinned type `Bₙ` datum are exactly the roots constructed from admissible
unordered pairs of signed basis vectors. -/
theorem mem_range_root_typeBSimplyConnectedRootDatum_iff {x : Fin n → ℤ} :
    x ∈ range (typeBSimplyConnectedRootDatum n).root ↔
      ∃ u v : Fin (2 * n), IsPair u v ∧ x = rootOfPair u v := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨((typeBEnum n).symm k).1, shift ((typeBEnum n).symm k).1
      ((typeBEnum n).symm k).2, isPair_shift _ _, ?_⟩
    rw [root_typeBSimplyConnectedRootDatum, rootIdx_def]
  · rintro ⟨u, v, huv, rfl⟩
    refine ⟨typeBEnum n (index u v), ?_⟩
    rw [root_typeBSimplyConnectedRootDatum, Equiv.symm_apply_apply, rootIdx_index huv]

/-- The coroots of the pinned type `Bₙ` datum are exactly the coroots constructed from admissible
unordered pairs of signed basis vectors. -/
theorem mem_range_coroot_typeBSimplyConnectedRootDatum_iff {x : Fin n → ℤ} :
    x ∈ range (typeBSimplyConnectedRootDatum n).coroot ↔
      ∃ u v : Fin (2 * n), IsPair u v ∧ x = corootOfPair u v := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨((typeBEnum n).symm k).1, shift ((typeBEnum n).symm k).1
      ((typeBEnum n).symm k).2, isPair_shift _ _, ?_⟩
    rw [coroot_typeBSimplyConnectedRootDatum, corootIdx_def]
  · rintro ⟨u, v, huv, rfl⟩
    refine ⟨typeBEnum n (index u v), ?_⟩
    rw [coroot_typeBSimplyConnectedRootDatum, Equiv.symm_apply_apply, corootIdx_index huv]

/-! ## The simple roots and coroots -/

/-- The character coordinates of the `i`-th simple root, in the uniform form
`weight n i - weight n (i + 1)`, the second summand vanishing at the last node. -/
private lemma rootIdx_typeBSimplePair (i : Fin n) :
    rootIdx (typeBSimplePair i) = weight n (i : ℕ) - weight n ((i : ℕ) + 1) := by
  have hi := i.isLt
  by_cases hlast : (i : ℕ) + 1 = n
  · have hshort : shift (⟨n - 1, by omega⟩ : Fin (2 * n)) (⟨0, by omega⟩ : Fin n) =
        ⟨n - 1, by omega⟩ := shift_eq_self rfl
    rw [rootIdx_def, typeBSimplePair, dite_eq_left hlast, typeBShortPair]
    rw [hshort, rootOfPair_self, typeB_signedWeight_mk_lt _ (show n - 1 < n by omega),
      weight_eq_zero_of_le (le_of_eq hlast.symm), sub_zero]
    congr 1
    omega
  · have hlt : (i : ℕ) + 1 < n := by omega
    have hv : shift (⟨n + (i : ℕ) + 1, by omega⟩ : Fin (2 * n)) (⟨n - 1, by omega⟩ : Fin n) =
        ⟨(i : ℕ), by omega⟩ :=
      shift_mk _ _ _ (by split_ifs <;> omega)
    have hne : (⟨n + (i : ℕ) + 1, by omega⟩ : Fin (2 * n)) ≠ ⟨(i : ℕ), by omega⟩ := by
      simp only [ne_eq, Fin.mk.injEq]
      omega
    rw [rootIdx_def, typeBSimplePair, dite_eq_right hlast]
    rw [hv, rootOfPair_of_ne hne, typeB_signedWeight_mk_ge _ (show n ≤ n + (i : ℕ) + 1 by omega),
      typeB_signedWeight_mk_lt _ (show (i : ℕ) < n by omega),
      show n + (i : ℕ) + 1 - n = (i : ℕ) + 1 by omega]
    abel

/-- **The simple roots are the rows of the Cartan matrix.** In the fundamental-weight basis the
`i`-th simple root of the pinned type `Bₙ` datum is the `i`-th row of `CartanMatrix.B n`, which is
what pins the character lattice as the weight lattice. -/
@[simp] theorem root_typeBSimpleIndex (i : Fin n) :
    (typeBSimplyConnectedRootDatum n).root (typeBSimpleIndex n i) =
      fun k => CartanMatrix.B n i k := by
  have hi := i.isLt
  rw [root_typeBSimplyConnectedRootDatum, typeBEnum_symm_typeBSimpleIndex,
    rootIdx_typeBSimplePair]
  funext k
  have hk := k.isLt
  simp only [weight_apply, Pi.sub_apply, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- **The simple coroots are the standard basis.** This is what pins the cocharacter lattice as the
coroot lattice, so that the datum is the simply connected one. -/
@[simp] theorem coroot_typeBSimpleIndex (i : Fin n) :
    (typeBSimplyConnectedRootDatum n).coroot (typeBSimpleIndex n i) = Pi.single i 1 := by
  have hi := i.isLt
  rw [coroot_typeBSimplyConnectedRootDatum, typeBEnum_symm_typeBSimpleIndex, corootIdx_def]
  by_cases hlast : (i : ℕ) + 1 = n
  · have hshort : shift (⟨n - 1, by omega⟩ : Fin (2 * n)) (⟨0, by omega⟩ : Fin n) =
        ⟨n - 1, by omega⟩ := shift_eq_self rfl
    rw [typeBSimplePair, dite_eq_left hlast, typeBShortPair, hshort, corootOfPair_self,
      typeB_signedCoweight_mk_lt _ (show n - 1 < n by omega)]
    funext k
    have hk := k.isLt
    simp only [coweight_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  · have hlt : (i : ℕ) + 1 < n := by omega
    have hv : shift (⟨n + (i : ℕ) + 1, by omega⟩ : Fin (2 * n)) (⟨n - 1, by omega⟩ : Fin n) =
        ⟨(i : ℕ), by omega⟩ :=
      shift_mk _ _ _ (by split_ifs <;> omega)
    rw [typeBSimplePair, dite_eq_right hlast, hv]
    funext k
    have hk := k.isLt
    simp only [corootOfPair_apply, Pi.single_apply, Fin.ext_iff,
      typeB_sgn_mk_ge (n := n) (a := n + (i : ℕ) + 1) (by omega)
        (show n ≤ n + (i : ℕ) + 1 by omega),
      typeB_sgn_mk_lt (n := n) (a := (i : ℕ)) (by omega) (show (i : ℕ) < n by omega),
      typeB_axis_mk_ge (n := n) (a := n + (i : ℕ) + 1) (by omega)
        (show n ≤ n + (i : ℕ) + 1 by omega),
      typeB_axis_mk_lt (n := n) (a := (i : ℕ)) (by omega) (show (i : ℕ) < n by omega)]
    rw [ite_eq_right (show ¬((-1 : ℤ) = 1) by norm_num)]
    split_ifs <;> omega

/-! ## The pinned base -/

/-- The covector dual to the simple roots, up to the factor `2`: the simple-coroot coordinates of
`2 (e₀ + ⋯ + e_j)`. -/
private def typeBDualVec (n j : ℕ) : Fin n → ℤ := ∑ b ∈ Finset.range (j + 1), coweight n b

private lemma weight_dotProduct_typeBDualVec {a j : ℕ} (ha : a < n) :
    weight n a ⬝ᵥ typeBDualVec n j = if a ≤ j then 2 else 0 := by
  rw [typeBDualVec, dotProduct_sum,
    Finset.sum_congr rfl fun b _ => weight_dotProduct_coweight (n := n) (b := b) ha,
    Finset.sum_ite_eq (Finset.range (j + 1)) a fun _ => (2 : ℤ)]
  simp only [Finset.mem_range]
  split_ifs <;> omega

private lemma typeBSimpleRoot_dotProduct_typeBDualVec (i j : Fin n) :
    (weight n (i : ℕ) - weight n ((i : ℕ) + 1)) ⬝ᵥ typeBDualVec n (j : ℕ) =
      if i = j then 2 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  rw [sub_dotProduct, weight_dotProduct_typeBDualVec hi]
  by_cases hlast : (i : ℕ) + 1 = n
  · rw [weight_eq_zero_of_le (le_of_eq hlast.symm), zero_dotProduct]
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  · rw [weight_dotProduct_typeBDualVec (show (i : ℕ) + 1 < n by omega)]
    simp only [Fin.ext_iff]
    split_ifs <;> omega

private lemma linearIndependent_typeBSimpleRoot (n : ℕ) :
    LinearIndependent ℤ fun i : Fin n => weight n (i : ℕ) - weight n ((i : ℕ) + 1) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (· ⬝ᵥ typeBDualVec n (j : ℕ)) hg
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct,
    typeBSimpleRoot_dotProduct_typeBDualVec, mul_ite, mul_zero] at h
  rw [Finset.sum_ite_eq' Finset.univ j fun i => g i * 2] at h
  simp only [Finset.mem_univ, ite_true] at h
  omega

/-- The support of the pinned base of type `Bₙ`: the first `n` root indices. -/
private abbrev typeBSimpleSupport (n : ℕ) : Finset (Fin (2 * n ^ 2)) :=
  simpleSupport (typeBSimpleIndex_injective (n := n))

private lemma mem_typeBSimpleSupport {k : Fin (2 * n ^ 2)} :
    k ∈ typeBSimpleSupport n ↔ (k : ℕ) < n :=
  mem_simpleSupport_iff_lt (typeBSimpleIndex_injective (n := n)) (fun _ ↦ typeBSimpleIndex_val _)

private lemma coe_typeBSimpleSupport :
    (typeBSimpleSupport n : Set (Fin (2 * n ^ 2))) = range (typeBSimpleIndex n) :=
  coe_simpleSupport _

private lemma comp_root_typeBSimpleIndex :
    (typeBSimplyConnectedRootDatum n).root ∘ typeBSimpleIndex n =
      fun i : Fin n => weight n (i : ℕ) - weight n ((i : ℕ) + 1) := by
  funext i
  simp only [comp_apply, root_typeBSimplyConnectedRootDatum, typeBEnum_symm_typeBSimpleIndex,
    rootIdx_typeBSimplePair]

private lemma image_root_typeBSimpleSupport :
    (typeBSimplyConnectedRootDatum n).root '' (typeBSimpleSupport n : Set (Fin (2 * n ^ 2))) =
      range fun i : Fin n => weight n (i : ℕ) - weight n ((i : ℕ) + 1) := by
  rw [coe_typeBSimpleSupport, ← range_comp, comp_root_typeBSimpleIndex]

private lemma image_coroot_typeBSimpleSupport :
    (typeBSimplyConnectedRootDatum n).coroot '' (typeBSimpleSupport n : Set (Fin (2 * n ^ 2))) =
      range fun i : Fin n => (Pi.single i 1 : Fin n → ℤ) := by
  rw [coe_typeBSimpleSupport, ← range_comp]
  exact congrArg range (funext fun i => coroot_typeBSimpleIndex i)

private lemma typeB_weight_mem_closure {a : ℕ} (ha : a ≤ n) :
    weight n a ∈ AddSubmonoid.closure
      (range fun i : Fin n => weight n (i : ℕ) - weight n ((i : ℕ) + 1)) := by
  have h := sub_mem_closure_of_le (n := n) (weight n) le_rfl ha
  rwa [weight_eq_zero_of_le le_rfl, sub_zero] at h

private lemma typeB_signedWeight_add_signedWeight_mem_closure (u v : Fin (2 * n)) (hu : sgn u = 1)
    (hv : sgn v = 1) :
    signedWeight u + signedWeight v ∈ AddSubmonoid.closure
      (range fun i : Fin n => weight n (i : ℕ) - weight n ((i : ℕ) + 1)) := by
  rw [signedWeight_def, signedWeight_def, hu, hv, one_smul, one_smul]
  exact AddSubmonoid.add_mem _ (typeB_weight_mem_closure (le_of_lt (axis_lt u)))
    (typeB_weight_mem_closure (le_of_lt (axis_lt v)))

private lemma typeB_signedWeight_sub_signedWeight_mem_closure (u v : Fin (2 * n)) (hu : sgn u = 1)
    (hv : sgn v = -1)
    (hle : axis u ≤ axis v) :
    signedWeight u + signedWeight v ∈ AddSubmonoid.closure
      (range fun i : Fin n => weight n (i : ℕ) - weight n ((i : ℕ) + 1)) := by
  rw [signedWeight_def, signedWeight_def, hu, hv, one_smul, neg_one_smul, ← sub_eq_add_neg]
  exact sub_mem_closure_of_le (n := n) (weight n) (le_of_lt (axis_lt v)) hle

private lemma typeB_mem_closure_single {w : Fin n → ℤ} (hw : ∀ j, 0 ≤ w j) :
    w ∈ AddSubmonoid.closure (range fun i : Fin n => (Pi.single i 1 : Fin n → ℤ)) := by
  rw [← (Pi.basisFun ℤ (Fin n)).sum_repr w]
  simpa only [Pi.basisFun_apply, Pi.basisFun_repr] using
    sum_smul_mem_closure (fun i : Fin n => (Pi.single i 1 : Fin n → ℤ)) w hw

private lemma corootOfPair_apply_last {u v : Fin (2 * n)} {j : Fin n}
    (hj : (j : ℕ) + 1 = n) :
    corootOfPair u v j = if sgn u = sgn v then sgn u else 0 := by
  rw [corootOfPair_apply, ite_eq_left hj]

private lemma corootOfPair_apply_of_ne {u v : Fin (2 * n)} {j : Fin n}
    (hj : (j : ℕ) + 1 ≠ n) :
    corootOfPair u v j = sgn u * (if axis u ≤ (j : ℕ) then 1 else 0) +
      sgn v * (if axis v ≤ (j : ℕ) then 1 else 0) := by
  rw [corootOfPair_apply, ite_eq_right hj]

private lemma typeB_corootOfPair_nonneg_of_sgn_eq_one {u v : Fin (2 * n)} (hsu : sgn u = 1)
    (hsv : sgn v = 1) (j : Fin n) : 0 ≤ corootOfPair u v j := by
  by_cases hj : (j : ℕ) + 1 = n
  · rw [corootOfPair_apply_last hj, hsu, hsv, ite_eq_left rfl]
    omega
  · rw [corootOfPair_apply_of_ne hj, hsu, hsv]
    split_ifs <;> omega

private lemma typeB_corootOfPair_nonpos_of_sgn_eq_neg_one {u v : Fin (2 * n)}
    (hsu : sgn u = -1) (hsv : sgn v = -1) (j : Fin n) : corootOfPair u v j ≤ 0 := by
  by_cases hj : (j : ℕ) + 1 = n
  · rw [corootOfPair_apply_last hj, hsu, hsv, ite_eq_left rfl]
    omega
  · rw [corootOfPair_apply_of_ne hj, hsu, hsv]
    split_ifs <;> omega

private lemma typeB_corootOfPair_nonneg_of_sgn_eq_one_of_sgn_eq_neg_one_of_axis_le
    {u v : Fin (2 * n)} (hsu : sgn u = 1) (hsv : sgn v = -1)
    (hle : axis u ≤ axis v) (j : Fin n) : 0 ≤ corootOfPair u v j := by
  by_cases hj : (j : ℕ) + 1 = n
  · rw [corootOfPair_apply_last hj, hsu, hsv, ite_eq_right (show ¬((1 : ℤ) = -1) by norm_num)]
  · rw [corootOfPair_apply_of_ne hj, hsu, hsv]
    split_ifs <;> omega

private lemma typeB_corootOfPair_nonpos_of_sgn_eq_one_of_sgn_eq_neg_one_of_axis_le
    {u v : Fin (2 * n)} (hsu : sgn u = 1) (hsv : sgn v = -1)
    (hle : axis v ≤ axis u) (j : Fin n) : corootOfPair u v j ≤ 0 := by
  by_cases hj : (j : ℕ) + 1 = n
  · rw [corootOfPair_apply_last hj, hsu, hsv, ite_eq_right (show ¬((1 : ℤ) = -1) by norm_num)]
  · rw [corootOfPair_apply_of_ne hj, hsu, hsv]
    split_ifs <;> omega

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `Bₙ`. Its support
is the set of the first `n` root indices, carrying the simple roots in Bourbaki order. -/
def typeBSimplyConnectedBase (n : ℕ) : (typeBSimplyConnectedRootDatum n).Base where
  support := typeBSimpleSupport n
  linearIndepOn_root :=
    linearIndepOn_simpleSupport _ _ <| by
      rw [comp_root_typeBSimpleIndex]
      exact linearIndependent_typeBSimpleRoot n
  linearIndepOn_coroot :=
    linearIndepOn_simpleSupport _ _ <| by
      have hcomp : (typeBSimplyConnectedRootDatum n).coroot ∘ typeBSimpleIndex n =
          ⇑(Pi.basisFun ℤ (Fin n)) := by
        funext i
        rw [comp_apply, coroot_typeBSimpleIndex]
        simp
      rw [hcomp]
      exact (Pi.basisFun ℤ (Fin n)).linearIndependent
  root_mem_or_neg_mem k := by
    rw [image_root_typeBSimpleSupport]
    obtain ⟨u, v, hroot⟩ : ∃ u v : Fin (2 * n),
        (typeBSimplyConnectedRootDatum n).root k = rootOfPair u v :=
      ⟨_, _, by rw [root_typeBSimplyConnectedRootDatum, rootIdx_def]⟩
    rcases eq_or_ne u v with heq | hne
    · rw [hroot, ← heq, rootOfPair_self]
      rcases sgn_eq_one_or_neg_one u with hs | hs
      · refine Or.inl ?_
        rw [signedWeight_def, hs, one_smul]
        exact typeB_weight_mem_closure (le_of_lt (axis_lt u))
      · refine Or.inr ?_
        rw [signedWeight_def, hs, neg_one_smul, neg_neg]
        exact typeB_weight_mem_closure (le_of_lt (axis_lt u))
    · rw [hroot, rootOfPair_of_ne hne]
      rcases sgn_eq_one_or_neg_one u with hsu | hsu <;>
        rcases sgn_eq_one_or_neg_one v with hsv | hsv
      · exact Or.inl (typeB_signedWeight_add_signedWeight_mem_closure u v hsu hsv)
      · rcases le_total (axis u) (axis v) with hle | hle
        · exact Or.inl (typeB_signedWeight_sub_signedWeight_mem_closure u v hsu hsv hle)
        · refine Or.inr ?_
          rw [neg_add, ← signedWeight_opp, ← signedWeight_opp, add_comm]
          exact typeB_signedWeight_sub_signedWeight_mem_closure (opp v) (opp u)
            (by simp [sgn_opp, hsv])
            (by simp [sgn_opp, hsu]) (by rwa [axis_opp, axis_opp])
      · rcases le_total (axis v) (axis u) with hle | hle
        · rw [add_comm]
          exact Or.inl (typeB_signedWeight_sub_signedWeight_mem_closure v u hsv hsu hle)
        · refine Or.inr ?_
          rw [neg_add, ← signedWeight_opp, ← signedWeight_opp]
          exact typeB_signedWeight_sub_signedWeight_mem_closure (opp u) (opp v)
            (by simp [sgn_opp, hsu])
            (by simp [sgn_opp, hsv]) (by rwa [axis_opp, axis_opp])
      · refine Or.inr ?_
        rw [neg_add, ← signedWeight_opp, ← signedWeight_opp]
        exact typeB_signedWeight_add_signedWeight_mem_closure (opp u) (opp v)
          (by simp [sgn_opp, hsu])
          (by simp [sgn_opp, hsv])
  coroot_mem_or_neg_mem k := by
    rw [image_coroot_typeBSimpleSupport]
    obtain ⟨u, v, hcor⟩ : ∃ u v : Fin (2 * n),
        (typeBSimplyConnectedRootDatum n).coroot k = corootOfPair u v :=
      ⟨_, _, by rw [coroot_typeBSimplyConnectedRootDatum, corootIdx_def]⟩
    rw [hcor]
    rcases sgn_eq_one_or_neg_one u with hsu | hsu <;>
      rcases sgn_eq_one_or_neg_one v with hsv | hsv
    · exact Or.inl
        (typeB_mem_closure_single (typeB_corootOfPair_nonneg_of_sgn_eq_one hsu hsv))
    · rcases le_total (axis u) (axis v) with hle | hle
      · exact Or.inl (typeB_mem_closure_single
          (typeB_corootOfPair_nonneg_of_sgn_eq_one_of_sgn_eq_neg_one_of_axis_le hsu hsv hle))
      · exact Or.inr (typeB_mem_closure_single fun j =>
          neg_nonneg.mpr
            (typeB_corootOfPair_nonpos_of_sgn_eq_one_of_sgn_eq_neg_one_of_axis_le hsu hsv hle j))
    · rw [corootOfPair_comm]
      rcases le_total (axis v) (axis u) with hle | hle
      · exact Or.inl (typeB_mem_closure_single
          (typeB_corootOfPair_nonneg_of_sgn_eq_one_of_sgn_eq_neg_one_of_axis_le hsv hsu hle))
      · exact Or.inr (typeB_mem_closure_single fun j =>
          neg_nonneg.mpr
            (typeB_corootOfPair_nonpos_of_sgn_eq_one_of_sgn_eq_neg_one_of_axis_le hsv hsu hle j))
    · exact Or.inr (typeB_mem_closure_single fun j =>
        neg_nonneg.mpr (typeB_corootOfPair_nonpos_of_sgn_eq_neg_one hsu hsv j))

/-- Membership in the pinned base support is exactly membership among the first `n` root
indices. -/
@[simp] theorem mem_typeBSimplyConnectedBase_support {k : Fin (2 * n ^ 2)} :
    k ∈ (typeBSimplyConnectedBase n).support ↔ (k : ℕ) < n :=
  mem_typeBSimpleSupport

/-- The pairing of two Bourbaki-indexed simple roots and coroots is the corresponding entry of
the type-`B` Cartan matrix. -/
@[simp] lemma pairing_typeBSimpleIndex (i j : Fin n) :
    (typeBSimplyConnectedRootDatum n).pairing (typeBSimpleIndex n i) (typeBSimpleIndex n j) =
      CartanMatrix.B n i j := by
  rw [pairing_typeBSimplyConnectedRootDatum, root_typeBSimpleIndex, coroot_typeBSimpleIndex,
    dotProduct_single, mul_one]

/-- **The pinned datum of type `Bₙ` has Cartan type `B n`.** Its Bourbaki-numbered base realizes
the standard Cartan matrix `CartanMatrix.B n`, with the node numbering of
`TauCeti.DynkinType`. -/
theorem hasCartanType_typeBSimplyConnectedRootDatum (n : ℕ) :
    HasCartanType (typeBSimplyConnectedRootDatum n) (typeBSimplyConnectedBase n) (.B n) :=
  hasCartanType_of_pairing_eq (typeBSimpleIndex_injective (n := n)) rfl fun i j =>
    (pairing_typeBSimpleIndex i j).trans (by simp)

/-- **The coroots of the pinned type `Bₙ` datum span the cocharacter lattice.** This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. Its
counterpart for the roots is deliberately absent: they span the root lattice, which for `0 < n`
sits inside the weight lattice with index `2` (Bourbaki, Plate II), the degenerate rank `n = 0`
being the only case where the two lattices agree. -/
theorem corootSpan_typeBSimplyConnectedRootDatum_eq_top (n : ℕ) :
    (typeBSimplyConnectedRootDatum n).corootSpan ℤ = ⊤ :=
  corootSpan_eq_top_of_coroot_eq_single (coroot_typeBSimpleIndex (n := n))

end TauCeti.DynkinType
