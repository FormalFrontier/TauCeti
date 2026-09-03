/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Basic
public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
import TauCeti.LinearAlgebra.RootSystem.Swap

public section

/-!
# The simply connected root datum of type `Aₙ`

This file constructs, uniformly in the rank `n`, the pinned integral root datum of type `Aₙ` on the
character and cocharacter lattices `Fin n → ℤ`. The character lattice is written in the
fundamental-weight basis and the cocharacter lattice in the simple-coroot basis, so the `i`-th
simple root is the `i`-th row of the Bourbaki-numbered Cartan matrix `CartanMatrix.A n` and the
`i`-th simple coroot is the `i`-th standard basis vector.

## The coordinates

Write `e₀, …, e_n` for the standard basis of the classical model `ℤ ^ (n + 1)`, in which the roots
of type `Aₙ` are the `n * (n + 1)` vectors `e_a - e_b` with `a ≠ b` and the simple roots are
`αᵢ = eᵢ - eᵢ₊₁`. Everything below is the image of that model in the two pinned lattices: a vector
of the character lattice is recorded by its pairings against the simple coroots, and a vector of the
cocharacter lattice by its coordinates in the simple coroots. Although `e_a` itself does not lie in
the coroot lattice, choose a coordinate potential for it so that differences represent coroots:

```text
typeAWeight n a   = (⟨e_a, αₖ^∨⟩)ₖ           = ([a = k] - [a = k + 1])ₖ,
typeACoweight n a = (chosen potential at αₖ^∨)ₖ   = ([a ≤ k])ₖ.
```

For `a ≤ b`, the difference of the chosen potentials has the simple-coroot coordinates of
`e_a - e_b = ∑ a ≤ k < b, αₖ^∨`. The root `e_a - e_b` and its coroot are the corresponding
differences, and the whole construction is a finite calculation with these two families;
`typeAWeight_dotProduct_typeACoweight` is the one identity it rests on.

The roots are indexed by `Fin (n * (n + 1))`, the ordered pairs `(a, b)` of distinct elements of
`Fin (n + 1)` being enumerated by the difference `b - a ≠ 0` first and the source `a` second. The
first `n` indices are therefore the simple roots `α₀, …, α_{n-1}` in Bourbaki order, as
`root_typeASimpleIndex` records.

Only the coroots are asked to span their lattice, and only that half is recorded, in
`corootSpan_typeASimplyConnectedRootDatum_eq_top`. The roots span the root lattice, which sits
inside the weight lattice with index `n + 1` (Bourbaki, Plate I), so the datum is a `RootDatum`
carrying no `RootPairing.IsRootSystem` instance. That asymmetry is what "simply connected" means
here.

## The graph automorphism

The `Aₙ` diagram is a chain, so reversing it is a symmetry, and the last part of this file realizes
that symmetry on the pinned datum itself rather than only on the Cartan matrix. On the classical
model the realization is `e_a ↦ -e_{rev a}`, whose effect on a root is

```text
e_a - e_b ↦ e_{rev b} - e_{rev a},
```

and on both pinned lattices, whose coordinates are indexed by the simple nodes, it is the reversal
of coordinates. So a single linear automorphism of `Fin n → ℤ` serves as both the character and the
cocharacter map, and `TauCeti.DynkinType.typeAGraphAut` bundles it with the induced permutation of
the `n * (n + 1)` root indices as an element of `RootPairing.Aut`. It restricts to the reversal
`Fin.revPerm` on the Bourbaki-numbered simple roots, which is `TauCeti.graphPermA n`, the
permutation that
`TauCeti/LinearAlgebra/RootSystem/DiagramPermutations.lean` pins for the `²Aₙ` family; that module
is deliberately not imported here, since only the `Fin`-level reversal is used.

The sign in `e_a ↦ -e_{rev a}` is forced: `e_a ↦ e_{rev a}` sends `αᵢ = e_i - e_{i+1}` to
`e_{rev i} - e_{rev (i + 1)} = -α_{rev i}`, a negative root, so it does not preserve the base. The
composite with the opposition `-1` is the automorphism below. This is unrelated to
`TauCeti.opposition`, which is built from the longest Weyl element and needs the root-system
hypotheses this simply connected datum does not carry.

## Main definitions

* `TauCeti.DynkinType.typeASimplyConnectedRootDatum`: the pinned root datum of type `Aₙ`.
* `TauCeti.DynkinType.typeASimpleIndex`: the first `n` root indices, the Bourbaki-numbered simple
  roots.
* `TauCeti.DynkinType.typeASimplyConnectedBase`: the base they form.
* `TauCeti.DynkinType.typeAGraphAut`: the graph automorphism of the pinned datum.

## Main results

* `TauCeti.DynkinType.root_typeASimpleIndex` and
  `TauCeti.DynkinType.coroot_typeASimpleIndex`: the `i`-th simple root is the `i`-th row of
  `CartanMatrix.A n` and the `i`-th simple coroot is `Pi.single i 1`, which is what pins the two
  lattices as the weight and coroot lattices.
* `TauCeti.DynkinType.hasCartanType_typeASimplyConnectedRootDatum`: the pinned base has Cartan type
  `A n`.
* `TauCeti.DynkinType.corootSpan_typeASimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.
* `TauCeti.DynkinType.ncard_posRoots_typeASimplyConnectedRootDatum`: the number of positive roots
  is `(n + 1).choose 2`, for any base.
* `TauCeti.DynkinType.weightMap_typeAGraphAut_apply` and
  `TauCeti.DynkinType.coweightMap_typeAGraphAut_apply`: the graph automorphism reverses the
  coordinates of both lattices.
* `TauCeti.DynkinType.indexEquiv_typeAGraphAut_typeASimpleIndex`: on the Bourbaki-numbered simple
  roots it is the chain reversal.
* `TauCeti.DynkinType.typeAGraphAut_sq` and `TauCeti.DynkinType.typeAGraphAut_ne_one`: it is an
  involution, and is nontrivial as soon as the chain has two nodes.
* `TauCeti.DynkinType.support_map_typeASimplyConnectedBase_typeAGraphAut`: it preserves the pinned
  base.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate I, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. This is the `Aₙ` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The positive-root count is the
corresponding clause of the `Aₙ` worked example in the "Worked examples (acceptance criteria)"
section of that README; it agrees with the count in Bourbaki, Plate I.

The graph automorphism is the root-datum input to the isomorphism theorem for pinned groups in
Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, whose consumer is the graph-twisted
Steinberg map of milestone L1 of `TauCetiRoadmap/CFSGStatement/README.md`. The description of the
type-`A` diagram automorphism as `X ↦ -J Xᵀ J` on `sl_{n+1}`, of which the map below is the
root-datum shadow, is in R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

namespace TauCeti

open Function Set Submodule

namespace DynkinType

variable {n : ℕ}

/-! ## The two coordinate families -/

/-- The character-lattice coordinates of the classical basis vector `e_a` of type `Aₙ`: its
pairings `⟨e_a, αₖ^∨⟩ = [a = k] - [a = k + 1]` against the simple coroots. -/
private def typeAWeight (n a : ℕ) : Fin n → ℤ :=
  fun k => (if a = (k : ℕ) then 1 else 0) - (if a = (k : ℕ) + 1 then 1 else 0)

/-- A chosen simple-coroot-coordinate potential for the classical basis vector `e_a` of type `Aₙ`.
Although `e_a` itself does not lie in the coroot lattice, the differences of these potentials give
the coordinates of `e_a - e_b`; the `k`-th potential is `[a ≤ k]`. -/
private def typeACoweight (n a : ℕ) : Fin n → ℤ :=
  fun k => if a ≤ (k : ℕ) then 1 else 0

/-- The fundamental pairing identity of type `Aₙ`: in the classical model `⟨e_a, e_c^∨⟩` would be
`[a = c]`, and the two pinned lattices see that up to the single correction `[a = n]`, which
cancels in the differences that are the roots and coroots. -/
private lemma typeAWeight_dotProduct_typeACoweight {a c : ℕ} (ha : a ≤ n) (hc : c ≤ n) :
    typeAWeight n a ⬝ᵥ typeACoweight n c
      = (if a = c then 1 else 0) - (if a = n then 1 else 0) := by
  have key : ∀ b : ℕ, ∑ k : Fin n, (if b = (k : ℕ) then (1 : ℤ) else 0) *
      (if c ≤ (k : ℕ) then 1 else 0) = if h : b < n then (if c ≤ b then (1 : ℤ) else 0) else 0 :=
    fun b => by
      simp only [ite_mul, one_mul, zero_mul]
      simpa only [Nat.add_zero, Nat.sub_zero, Nat.zero_le, and_true] using
        sum_ite_val_add (fun k : Fin n => if c ≤ (k : ℕ) then (1 : ℤ) else 0) b 0
  have key' : ∀ b : ℕ, ∑ k : Fin n, (if b = (k : ℕ) + 1 then (1 : ℤ) else 0) *
      (if c ≤ (k : ℕ) then 1 else 0)
        = if h : b - 1 < n ∧ 1 ≤ b then (if c ≤ b - 1 then (1 : ℤ) else 0) else 0 :=
    fun b => by
      simp only [ite_mul, one_mul, zero_mul]
      exact sum_ite_val_add (fun k : Fin n => if c ≤ (k : ℕ) then (1 : ℤ) else 0) b 1
  simp only [dotProduct, typeAWeight, typeACoweight, sub_mul, Finset.sum_sub_distrib,
    key a, key' a]
  split_ifs <;> omega

/-! ## The roots and coroots indexed by ordered pairs -/

/-- The ordered pairs of distinct elements of `Fin (n + 1)`, indexing the roots `e_a - e_b` of type
`Aₙ` before they are enumerated by `Fin (n * (n + 1))`. -/
private abbrev TypeAIndex (n : ℕ) := {p : Fin (n + 1) × Fin (n + 1) // p.1 ≠ p.2}

/-- The root `e_a - e_b` in fundamental-weight coordinates. -/
private def typeAPairRoot (p : TypeAIndex n) : Fin n → ℤ :=
  typeAWeight n (p.val.1 : ℕ) - typeAWeight n (p.val.2 : ℕ)

/-- The coroot `(e_a - e_b)^∨ = e_a - e_b` in simple-coroot coordinates. -/
private def typeAPairCoroot (p : TypeAIndex n) : Fin n → ℤ :=
  typeACoweight n (p.val.1 : ℕ) - typeACoweight n (p.val.2 : ℕ)

private lemma typeAPairing (p q : TypeAIndex n) :
    typeAPairRoot p ⬝ᵥ typeAPairCoroot q =
      (if p.val.1 = q.val.1 then 1 else 0) - (if p.val.1 = q.val.2 then 1 else 0)
        - ((if p.val.2 = q.val.1 then 1 else 0) - (if p.val.2 = q.val.2 then (1 : ℤ) else 0)) := by
  have hle : ∀ x : Fin (n + 1), (x : ℕ) ≤ n := fun x => Nat.lt_succ_iff.mp x.isLt
  simp only [typeAPairRoot, typeAPairCoroot, sub_dotProduct, dotProduct_sub,
    typeAWeight_dotProduct_typeACoweight (hle _) (hle _), Fin.val_inj]
  ring

private lemma typeAPairRoot_self (p : TypeAIndex n) : typeAPairRoot p ⬝ᵥ typeAPairCoroot p = 2 := by
  rw [typeAPairing]
  have h := p.2
  split_ifs <;> simp_all

private lemma typeAPairRoot_injective : Injective (typeAPairRoot (n := n)) := by
  intro p q hpq
  have h2 : typeAPairRoot q ⬝ᵥ typeAPairCoroot p = 2 := by rw [← hpq]; exact typeAPairRoot_self p
  rw [typeAPairing] at h2
  have hp := p.2
  have hq := q.2
  refine Subtype.ext (Prod.ext ?_ ?_) <;> (split_ifs at h2 <;> simp_all)

private lemma typeAPairCoroot_injective : Injective (typeAPairCoroot (n := n)) := by
  intro p q hpq
  have h2 : typeAPairRoot p ⬝ᵥ typeAPairCoroot q = 2 := by rw [← hpq]; exact typeAPairRoot_self p
  rw [typeAPairing] at h2
  have hp := p.2
  have hq := q.2
  refine Subtype.ext (Prod.ext ?_ ?_) <;> (split_ifs at h2 <;> simp_all)

/-- Reflection in the root indexed by `p`, as the transposition of the two entries of `p` acting on
ordered pairs. -/
private def typeAPairReflection (p : TypeAIndex n) : TypeAIndex n ≃ TypeAIndex n :=
  Equiv.subtypeEquiv ((Equiv.swap p.val.1 p.val.2).prodCongr (Equiv.swap p.val.1 p.val.2))
    (fun q => by simp)

private lemma typeAWeight_swap (a b c : Fin (n + 1)) :
    typeAWeight n ((Equiv.swap a b c : Fin (n + 1)) : ℕ) =
      typeAWeight n (c : ℕ) - ((if c = a then 1 else 0) - (if c = b then (1 : ℤ) else 0)) •
        (typeAWeight n (a : ℕ) - typeAWeight n (b : ℕ)) :=
  apply_swap_eq (fun x : Fin (n + 1) => typeAWeight n (x : ℕ)) a b c

private lemma typeACoweight_swap (a b c : Fin (n + 1)) :
    typeACoweight n ((Equiv.swap a b c : Fin (n + 1)) : ℕ) =
      typeACoweight n (c : ℕ) - ((if c = a then 1 else 0) - (if c = b then (1 : ℤ) else 0)) •
        (typeACoweight n (a : ℕ) - typeACoweight n (b : ℕ)) :=
  apply_swap_eq (fun x : Fin (n + 1) => typeACoweight n (x : ℕ)) a b c

private lemma typeAPairReflection_root (p q : TypeAIndex n) :
    typeAPairRoot q - (typeAPairRoot q ⬝ᵥ typeAPairCoroot p) • typeAPairRoot p =
      typeAPairRoot (typeAPairReflection p q) := by
  have hR : typeAPairRoot (typeAPairReflection p q) =
      typeAWeight n ((Equiv.swap p.val.1 p.val.2 q.val.1 : Fin (n + 1)) : ℕ) -
        typeAWeight n ((Equiv.swap p.val.1 p.val.2 q.val.2 : Fin (n + 1)) : ℕ) := rfl
  rw [typeAPairing, hR, typeAWeight_swap, typeAWeight_swap]
  simp only [typeAPairRoot]
  module

private lemma ite_eq_comm (a b : Fin (n + 1)) :
    (if a = b then (1 : ℤ) else 0) = if b = a then 1 else 0 := by
  split_ifs <;> simp_all

private lemma typeAPairReflection_coroot (p q : TypeAIndex n) :
    typeAPairCoroot q - (typeAPairRoot p ⬝ᵥ typeAPairCoroot q) • typeAPairCoroot p =
      typeAPairCoroot (typeAPairReflection p q) := by
  have hR : typeAPairCoroot (typeAPairReflection p q) =
      typeACoweight n ((Equiv.swap p.val.1 p.val.2 q.val.1 : Fin (n + 1)) : ℕ) -
        typeACoweight n ((Equiv.swap p.val.1 p.val.2 q.val.2 : Fin (n + 1)) : ℕ) := rfl
  rw [typeAPairing, hR, typeACoweight_swap, typeACoweight_swap, ite_eq_comm p.val.1 q.val.1,
    ite_eq_comm p.val.1 q.val.2, ite_eq_comm p.val.2 q.val.1, ite_eq_comm p.val.2 q.val.2]
  simp only [typeAPairCoroot]
  module

/-! ## The Bourbaki enumeration of the roots -/

private lemma one_le_val_sub (p : TypeAIndex n) : 1 ≤ ((p.val.2 - p.val.1 : Fin (n + 1)) : ℕ) := by
  have h : (p.val.2 - p.val.1 : Fin (n + 1)) ≠ 0 := fun h => p.2 (sub_eq_zero.mp h).symm
  have : ((p.val.2 - p.val.1 : Fin (n + 1)) : ℕ) ≠ 0 := by
    simpa [Fin.val_eq_zero_iff] using h
  omega

/-- The nonzero difference `b - a` of an ordered pair of distinct elements, shifted down to an
index of `Fin n`. -/
private def typeADiff (p : TypeAIndex n) : Fin n :=
  ⟨((p.val.2 - p.val.1 : Fin (n + 1)) : ℕ) - 1, by
    have h1 := one_le_val_sub p
    have h2 : ((p.val.2 - p.val.1 : Fin (n + 1)) : ℕ) < n + 1 := Fin.isLt _
    omega⟩

private lemma typeADiff_val (p : TypeAIndex n) :
    (typeADiff p : ℕ) = ((p.val.2 - p.val.1 : Fin (n + 1)) : ℕ) - 1 := rfl

/-- The shift of a `Fin n` index to the nonzero elements of `Fin (n + 1)`, inverse to
`TauCeti.DynkinType.typeADiff`. -/
private def typeASucc (i : Fin n) : Fin (n + 1) := ⟨(i : ℕ) + 1, by omega⟩

private lemma typeASucc_val (i : Fin n) : (typeASucc i : ℕ) = (i : ℕ) + 1 := rfl

private lemma typeASucc_ne_zero (i : Fin n) : typeASucc i ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  rw [typeASucc_val] at h'
  simp at h'

/-- The enumeration of the ordered pairs of distinct elements of `Fin (n + 1)` by the difference
`b - a ≠ 0` first and the source `a` second. Composed with `finProdFinEquiv` it puts the simple
roots at the first `n` indices. -/
private def typeAPairEquiv (n : ℕ) : TypeAIndex n ≃ Fin n × Fin (n + 1) where
  toFun p := (typeADiff p, p.val.1)
  invFun q := ⟨(q.2, q.2 + typeASucc q.1), by
    intro h
    refine typeASucc_ne_zero q.1 ?_
    have h0 : q.2 + 0 = q.2 + typeASucc q.1 := by simpa using h
    exact (add_left_cancel h0).symm⟩
  left_inv p := by
    have h1 := one_le_val_sub p
    have hx : typeASucc (typeADiff p) = p.val.2 - p.val.1 :=
      Fin.ext (by rw [typeASucc_val, typeADiff_val]; omega)
    refine Subtype.ext (Prod.ext rfl ?_)
    -- Unfold the subtype equivalence to compare its second `Fin (n + 1)` coordinate.
    change p.val.1 + typeASucc (typeADiff p) = p.val.2
    rw [hx]
    abel
  right_inv q := by
    refine Prod.ext (Fin.ext ?_) rfl
    -- Unfold the first coordinate of the product equivalence to compare its natural values.
    change ((q.2 + typeASucc q.1 - q.2 : Fin (n + 1)) : ℕ) - 1 = (q.1 : ℕ)
    rw [add_sub_cancel_left, typeASucc_val]
    omega

/-- The pinned enumeration of the roots of type `Aₙ` by `Fin (n * (n + 1))`. -/
private def typeAIndexEquiv (n : ℕ) : TypeAIndex n ≃ Fin (n * (n + 1)) :=
  (typeAPairEquiv n).trans finProdFinEquiv

/-- Reflection in the root indexed by `k`, transported to the pinned enumeration. -/
private def typeAReflectionPerm (n : ℕ) (k : Fin (n * (n + 1))) :
    Fin (n * (n + 1)) ≃ Fin (n * (n + 1)) :=
  ((typeAIndexEquiv n).symm.trans
    (typeAPairReflection ((typeAIndexEquiv n).symm k))).trans (typeAIndexEquiv n)

private lemma typeAReflectionPerm_apply (k l : Fin (n * (n + 1))) :
    (typeAIndexEquiv n).symm (typeAReflectionPerm n k l) =
      typeAPairReflection ((typeAIndexEquiv n).symm k) ((typeAIndexEquiv n).symm l) := by
  simp [typeAReflectionPerm]

private lemma typeAReflectionPerm_root (k l : Fin (n * (n + 1))) :
    typeAPairRoot ((typeAIndexEquiv n).symm l) -
        (typeAPairRoot ((typeAIndexEquiv n).symm l) ⬝ᵥ
          typeAPairCoroot ((typeAIndexEquiv n).symm k)) •
          typeAPairRoot ((typeAIndexEquiv n).symm k) =
      typeAPairRoot ((typeAIndexEquiv n).symm (typeAReflectionPerm n k l)) := by
  rw [typeAReflectionPerm_apply]
  exact typeAPairReflection_root _ _

private lemma typeAReflectionPerm_coroot (k l : Fin (n * (n + 1))) :
    typeAPairCoroot ((typeAIndexEquiv n).symm l) -
        (typeAPairRoot ((typeAIndexEquiv n).symm k) ⬝ᵥ
          typeAPairCoroot ((typeAIndexEquiv n).symm l)) •
          typeAPairCoroot ((typeAIndexEquiv n).symm k) =
      typeAPairCoroot ((typeAIndexEquiv n).symm (typeAReflectionPerm n k l)) := by
  rw [typeAReflectionPerm_apply]
  exact typeAPairReflection_coroot _ _

/-- The pinned simply connected root datum of type `Aₙ`.

Both lattices are `Fin n → ℤ`: the character lattice in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. The `n * (n + 1)` roots are the classical
`e_a - e_b` with `a ≠ b`, enumerated with the simple roots first; see
`TauCeti.DynkinType.root_typeASimpleIndex`. -/
def typeASimplyConnectedRootDatum (n : ℕ) :
    RootDatum (Fin (n * (n + 1))) (Fin n → ℤ) (Fin n → ℤ) where
  toLinearMap := dotProductBilin ℤ ℤ
  root := ⟨fun k => typeAPairRoot ((typeAIndexEquiv n).symm k),
    typeAPairRoot_injective.comp (typeAIndexEquiv n).symm.injective⟩
  coroot := ⟨fun k => typeAPairCoroot ((typeAIndexEquiv n).symm k),
    typeAPairCoroot_injective.comp (typeAIndexEquiv n).symm.injective⟩
  root_coroot_two k := typeAPairRoot_self ((typeAIndexEquiv n).symm k)
  reflectionPerm := typeAReflectionPerm n
  reflectionPerm_root := typeAReflectionPerm_root
  reflectionPerm_coroot := typeAReflectionPerm_coroot

/-- The pinned pairing of type `Aₙ` is the dot product of the two lattices. -/
@[simp] theorem toLinearMap_typeASimplyConnectedRootDatum (x y : Fin n → ℤ) :
    (typeASimplyConnectedRootDatum n).toLinearMap x y = x ⬝ᵥ y := (rfl)

private lemma root_typeASimplyConnectedRootDatum (k : Fin (n * (n + 1))) :
    (typeASimplyConnectedRootDatum n).root k = typeAPairRoot ((typeAIndexEquiv n).symm k) :=
  rfl

private lemma coroot_typeASimplyConnectedRootDatum (k : Fin (n * (n + 1))) :
    (typeASimplyConnectedRootDatum n).coroot k = typeAPairCoroot ((typeAIndexEquiv n).symm k) :=
  rfl

private lemma pairing_typeASimplyConnectedRootDatum (k l : Fin (n * (n + 1))) :
    (typeASimplyConnectedRootDatum n).pairing k l =
      (typeASimplyConnectedRootDatum n).root k ⬝ᵥ (typeASimplyConnectedRootDatum n).coroot l :=
  rfl

/-- The root--coroot pairing of the pinned type `A` datum is symmetric. -/
theorem pairing_typeASimplyConnectedRootDatum_comm (k l : Fin (n * (n + 1))) :
    (typeASimplyConnectedRootDatum n).pairing k l =
      (typeASimplyConnectedRootDatum n).pairing l k := by
  rw [pairing_typeASimplyConnectedRootDatum, pairing_typeASimplyConnectedRootDatum,
    root_typeASimplyConnectedRootDatum, root_typeASimplyConnectedRootDatum,
    coroot_typeASimplyConnectedRootDatum, coroot_typeASimplyConnectedRootDatum,
    typeAPairing, typeAPairing]
  rw [ite_eq_comm ((typeAIndexEquiv n).symm l).val.1 ((typeAIndexEquiv n).symm k).val.1,
    ite_eq_comm ((typeAIndexEquiv n).symm l).val.1 ((typeAIndexEquiv n).symm k).val.2,
    ite_eq_comm ((typeAIndexEquiv n).symm l).val.2 ((typeAIndexEquiv n).symm k).val.1,
    ite_eq_comm ((typeAIndexEquiv n).symm l).val.2 ((typeAIndexEquiv n).symm k).val.2]
  ring

/-- The `i`-th simple root of type `Aₙ` sits at root index `i`, the Bourbaki node `i + 1`. -/
def typeASimpleIndex (n : ℕ) (i : Fin n) : Fin (n * (n + 1)) :=
  Fin.castLE (Nat.le_mul_of_pos_right n n.succ_pos) i

@[simp] lemma typeASimpleIndex_val (i : Fin n) : (typeASimpleIndex n i : ℕ) = i := by
  simp [typeASimpleIndex]

lemma typeASimpleIndex_injective : Injective (typeASimpleIndex n) :=
  Fin.castLE_injective (Nat.le_mul_of_pos_right n n.succ_pos)

private lemma typeAIndexEquiv_symm_typeASimpleIndex (i : Fin n) :
    (typeAIndexEquiv n).symm (typeASimpleIndex n i) =
      ⟨(⟨i, by omega⟩, ⟨(i : ℕ) + 1, by omega⟩), by simp [Fin.ext_iff]⟩ := by
  have hlt : (i : ℕ) < n + 1 := by omega
  have hlt' : (i : ℕ) + 1 < n + 1 := by omega
  refine Subtype.ext (Prod.ext ?_ ?_) <;>
    · apply Fin.ext
      simp [typeAIndexEquiv, typeAPairEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
        typeASimpleIndex, typeASucc_val, Nat.div_eq_of_lt hlt,
        Nat.mod_eq_of_lt hlt, Fin.add_def, Nat.mod_eq_of_lt hlt']

private lemma root_typeASimpleIndex_eq (i : Fin n) :
    (typeASimplyConnectedRootDatum n).root (typeASimpleIndex n i) =
      typeAWeight n (i : ℕ) - typeAWeight n ((i : ℕ) + 1) := by
  rw [root_typeASimplyConnectedRootDatum, typeAIndexEquiv_symm_typeASimpleIndex]
  rfl

private lemma coroot_typeASimpleIndex_eq (i : Fin n) :
    (typeASimplyConnectedRootDatum n).coroot (typeASimpleIndex n i) =
      typeACoweight n (i : ℕ) - typeACoweight n ((i : ℕ) + 1) := by
  rw [coroot_typeASimplyConnectedRootDatum, typeAIndexEquiv_symm_typeASimpleIndex]
  rfl

/-- **The simple roots are the rows of the Cartan matrix.** In the fundamental-weight basis the
`i`-th simple root of the pinned type `Aₙ` datum is the `i`-th row of `CartanMatrix.A n`, which is
what pins the character lattice as the weight lattice. -/
@[simp] theorem root_typeASimpleIndex (i : Fin n) :
    (typeASimplyConnectedRootDatum n).root (typeASimpleIndex n i) =
      fun k => CartanMatrix.A n i k := by
  rw [root_typeASimpleIndex_eq]
  funext k
  simp only [typeAWeight, Pi.sub_apply, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma typeACoweight_sub_succ (i : Fin n) :
    typeACoweight n (i : ℕ) - typeACoweight n ((i : ℕ) + 1) = Pi.single i 1 := by
  funext k
  simp only [typeACoweight, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- **The simple coroots are the standard basis.** This is what pins the cocharacter lattice as the
coroot lattice, so that the datum is the simply connected one. -/
@[simp] theorem coroot_typeASimpleIndex (i : Fin n) :
    (typeASimplyConnectedRootDatum n).coroot (typeASimpleIndex n i) = Pi.single i 1 := by
  rw [coroot_typeASimpleIndex_eq, typeACoweight_sub_succ]

/-! ## The pinned base -/

/-- **A sequence with vanishing second difference is linear.** In an additive cancellative
commutative monoid, if `S 0 = 0` and `S (k + 1) + S (k + 1) = S k + S (k + 2)` for every `k < n`,
then `S j = j • S 1` for every `j ≤ n + 1`. -/
private lemma eq_nsmul_of_second_difference_zero {M : Type*} [AddCancelCommMonoid M] {S : ℕ → M}
    {n : ℕ} (hS0 : S 0 = 0) (hrec : ∀ k < n, S (k + 1) + S (k + 1) = S k + S (k + 2)) :
    ∀ j ≤ n + 1, S j = j • S 1 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => intro _; simpa using hS0
    | 1 => intro _; simp
    | (m + 2) =>
      intro hm
      have h0 := ih m (by omega) (by omega)
      have h1 := ih (m + 1) (by omega) (by omega)
      have h2 := hrec m (by omega)
      -- the recurrence reads `(m + 1) • S 1 + (m + 1) • S 1 = m • S 1 + S (m + 2)`, and both
      -- sides carry the summand `m • S 1`
      rw [h0, h1] at h2
      refine add_left_cancel (a := m • S 1) ?_
      rw [← h2, ← add_smul, ← add_smul]
      congr 1
      omega

/-- The simple roots of type `Aₙ` are linearly independent. A relation among the rows of
`CartanMatrix.A n` forces its coefficients to grow linearly, and the missing row past the last node
then makes the common ratio `(n + 1)`-torsion, hence zero. -/
private lemma linearIndependent_typeASimpleRoot (n : ℕ) :
    LinearIndependent ℤ fun i : Fin n => typeAWeight n (i : ℕ) - typeAWeight n ((i : ℕ) + 1) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let S : ℕ → ℤ := fun c => ∑ j : Fin n, (if (j : ℕ) + 1 = c then g j else 0)
  have hSval : ∀ j : Fin n, S ((j : ℕ) + 1) = g j := by
    intro j
    simpa only [S, Nat.add_right_cancel_iff, Fin.val_inj] using Fintype.sum_ite_eq' j g
  have hSzero : ∀ c : ℕ, n < c → S c = 0 := by
    intro c hc
    refine Finset.sum_eq_zero fun j _ => ite_eq_right ?_
    have := j.isLt
    omega
  have hS0 : S 0 = 0 := Finset.sum_eq_zero fun j _ => ite_eq_right (by omega)
  have hshift : ∀ c : ℕ, ∑ j : Fin n, (if (j : ℕ) = c then g j else 0) = S (c + 1) :=
    fun c => Finset.sum_congr rfl fun j _ => by by_cases h : (j : ℕ) = c <;> simp [h]
  have hrec : ∀ k : Fin n, S ((k : ℕ) + 1) + S ((k : ℕ) + 1) = S (k : ℕ) + S ((k : ℕ) + 2) := by
    intro k
    have h := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, typeAWeight, smul_eq_mul,
      Pi.zero_apply, mul_sub, mul_ite, mul_one, mul_zero] at h
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h
    rw [hshift, hshift] at h
    have e1 : ∑ j : Fin n, (if (j : ℕ) + 1 = (k : ℕ) then g j else 0) = S (k : ℕ) := rfl
    have e2 : ∑ j : Fin n, (if (j : ℕ) + 1 = (k : ℕ) + 1 then g j else 0) = S ((k : ℕ) + 1) := rfl
    rw [e1, e2] at h
    linarith [h]
  have key : ∀ j : ℕ, j ≤ n + 1 → S j = j * S 1 := fun j hj => by
    simpa [nsmul_eq_mul] using
      eq_nsmul_of_second_difference_zero hS0 (fun k hk => hrec ⟨k, hk⟩) j hj
  have hS1 : S 1 = 0 := by
    have h := key (n + 1) le_rfl
    rw [hSzero (n + 1) (by omega)] at h
    have hz : ((n : ℤ) + 1) * S 1 = 0 := by push_cast at h ⊢; linarith
    rcases mul_eq_zero.mp hz with h' | h'
    · exact absurd h' (by positivity)
    · exact h'
  intro i
  rw [← hSval i, key ((i : ℕ) + 1) (by have := i.isLt; omega), hS1, mul_zero]

private lemma linearIndependent_typeASimpleCoroot (n : ℕ) :
    LinearIndependent ℤ fun i : Fin n => typeACoweight n (i : ℕ) -
      typeACoweight n ((i : ℕ) + 1) := by
  simpa only [typeACoweight_sub_succ] using Pi.linearIndependent_single_one (Fin n) ℤ

/-- The support of the pinned base of type `Aₙ`: the first `n` root indices. -/
private abbrev typeASimpleSupport (n : ℕ) : Finset (Fin (n * (n + 1))) :=
  simpleSupport (typeASimpleIndex_injective (n := n))

private lemma mem_typeASimpleSupport {k : Fin (n * (n + 1))} :
    k ∈ typeASimpleSupport n ↔ (k : ℕ) < n :=
  mem_simpleSupport_iff_lt (typeASimpleIndex_injective (n := n)) (fun _ ↦ typeASimpleIndex_val _)

private lemma image_root_typeASimpleSupport :
    (typeASimplyConnectedRootDatum n).root '' (typeASimpleSupport n : Set (Fin (n * (n + 1)))) =
      range fun i : Fin n => typeAWeight n (i : ℕ) - typeAWeight n ((i : ℕ) + 1) := by
  rw [typeASimpleSupport, image_simpleSupport]
  exact congrArg range (funext fun i => root_typeASimpleIndex_eq i)

private lemma image_coroot_typeASimpleSupport :
    (typeASimplyConnectedRootDatum n).coroot '' (typeASimpleSupport n : Set (Fin (n * (n + 1)))) =
      range fun i : Fin n => typeACoweight n (i : ℕ) - typeACoweight n ((i : ℕ) + 1) := by
  rw [typeASimpleSupport, image_simpleSupport]
  exact congrArg range (funext fun i => coroot_typeASimpleIndex_eq i)

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `Aₙ`. Its support
is the set of the first `n` root indices, carrying the simple roots in Bourbaki order. -/
def typeASimplyConnectedBase (n : ℕ) : (typeASimplyConnectedRootDatum n).Base where
  support := typeASimpleSupport n
  linearIndepOn_root :=
    linearIndepOn_simpleSupport _ _ <| by
      have hcomp : (typeASimplyConnectedRootDatum n).root ∘ typeASimpleIndex n =
          fun i : Fin n => typeAWeight n (i : ℕ) - typeAWeight n ((i : ℕ) + 1) :=
        funext fun i => root_typeASimpleIndex_eq i
      rw [hcomp]
      exact linearIndependent_typeASimpleRoot n
  linearIndepOn_coroot :=
    linearIndepOn_simpleSupport _ _ <| by
      have hcomp : (typeASimplyConnectedRootDatum n).coroot ∘ typeASimpleIndex n =
          fun i : Fin n => typeACoweight n (i : ℕ) - typeACoweight n ((i : ℕ) + 1) :=
        funext fun i => coroot_typeASimpleIndex_eq i
      rw [hcomp]
      exact linearIndependent_typeASimpleCoroot n
  root_mem_or_neg_mem k := by
    have hroot : (typeASimplyConnectedRootDatum n).root k =
        typeAWeight n (((typeAIndexEquiv n).symm k).val.1 : ℕ) -
          typeAWeight n (((typeAIndexEquiv n).symm k).val.2 : ℕ) := rfl
    rw [image_root_typeASimpleSupport, hroot]
    rcases le_total ((((typeAIndexEquiv n).symm k).val.1 : Fin (n + 1)) : ℕ)
        ((((typeAIndexEquiv n).symm k).val.2 : Fin (n + 1)) : ℕ) with h | h
    · exact Or.inl (sub_mem_closure_of_le (typeAWeight n)
        (Nat.lt_succ_iff.mp (((typeAIndexEquiv n).symm k).val.2).isLt) h)
    · refine Or.inr ?_
      rw [neg_sub]
      exact sub_mem_closure_of_le (typeAWeight n)
        (Nat.lt_succ_iff.mp (((typeAIndexEquiv n).symm k).val.1).isLt) h
  coroot_mem_or_neg_mem k := by
    have hcoroot : (typeASimplyConnectedRootDatum n).coroot k =
        typeACoweight n (((typeAIndexEquiv n).symm k).val.1 : ℕ) -
          typeACoweight n (((typeAIndexEquiv n).symm k).val.2 : ℕ) := rfl
    rw [image_coroot_typeASimpleSupport, hcoroot]
    rcases le_total ((((typeAIndexEquiv n).symm k).val.1 : Fin (n + 1)) : ℕ)
        ((((typeAIndexEquiv n).symm k).val.2 : Fin (n + 1)) : ℕ) with h | h
    · exact Or.inl (sub_mem_closure_of_le (typeACoweight n)
        (Nat.lt_succ_iff.mp (((typeAIndexEquiv n).symm k).val.2).isLt) h)
    · refine Or.inr ?_
      rw [neg_sub]
      exact sub_mem_closure_of_le (typeACoweight n)
        (Nat.lt_succ_iff.mp (((typeAIndexEquiv n).symm k).val.1).isLt) h

/-- Membership in the pinned base support is exactly membership among the first `n` root indices. -/
@[simp] theorem mem_typeASimplyConnectedBase_support {k : Fin (n * (n + 1))} :
    k ∈ (typeASimplyConnectedBase n).support ↔ (k : ℕ) < n :=
  mem_typeASimpleSupport

private lemma pairing_typeASimpleIndex (i j : Fin n) :
    (typeASimplyConnectedRootDatum n).pairing (typeASimpleIndex n i) (typeASimpleIndex n j) =
      CartanMatrix.A n i j := by
  rw [pairing_typeASimplyConnectedRootDatum, root_typeASimpleIndex, coroot_typeASimpleIndex,
    dotProduct_single, mul_one]

/-- **The pinned datum of type `Aₙ` has Cartan type `A n`.** Its Bourbaki-numbered base realizes the
standard Cartan matrix `CartanMatrix.A n`, with the node numbering of `TauCeti.DynkinType`. -/
theorem hasCartanType_typeASimplyConnectedRootDatum (n : ℕ) :
    HasCartanType (typeASimplyConnectedRootDatum n) (typeASimplyConnectedBase n) (.A n) :=
  hasCartanType_of_pairing_eq (typeASimpleIndex_injective (n := n)) rfl fun i j =>
    (pairing_typeASimpleIndex i j).trans (by simp)

/-- **The coroots of the pinned type `Aₙ` datum span the cocharacter lattice.** This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. Its
counterpart for the roots is deliberately absent: they span the root lattice, which sits inside the
weight lattice with index `n + 1` (Bourbaki, Plate I). -/
theorem corootSpan_typeASimplyConnectedRootDatum_eq_top (n : ℕ) :
    (typeASimplyConnectedRootDatum n).corootSpan ℤ = ⊤ :=
  corootSpan_eq_top_of_coroot_eq_single (coroot_typeASimpleIndex (n := n))

/-- **The pinned root datum of type `Aₙ` has `(n + 1).choose 2` positive roots.** Exactly half of
its `n * (n + 1)` roots are positive, for any base. -/
@[simp]
theorem ncard_posRoots_typeASimplyConnectedRootDatum (n : ℕ)
    (b : (typeASimplyConnectedRootDatum n).Base) :
    (posRoots (typeASimplyConnectedRootDatum n) b).ncard = (n + 1).choose 2 := by
  rw [ncard_posRoots_eq_natCard_div_two]
  simp [Nat.choose_two_right, Nat.mul_comm]

/-! ## The graph automorphism -/

/-- The graph automorphism of type `Aₙ` read on the classical ordered pairs: it exchanges the two
entries and reverses each, `(a, b) ↦ (rev b, rev a)`. This is the effect of `e_a ↦ -e_{rev a}` on
the root `e_a - e_b`. -/
private def typeAGraphPairMap (p : TypeAIndex n) : TypeAIndex n :=
  ⟨(p.val.2.rev, p.val.1.rev), fun h => p.2 (Fin.rev_injective h).symm⟩

private lemma typeAGraphPairMap_involutive : Involutive (typeAGraphPairMap (n := n)) :=
  fun _ => Subtype.ext (Prod.ext (Fin.rev_rev _) (Fin.rev_rev _))

private lemma val_rev_succ (a : Fin (n + 1)) : ((a.rev : Fin (n + 1)) : ℕ) = n - (a : ℕ) := by
  rw [Fin.val_rev]
  omega

/-- Reversing the classical index negates the character coordinates read at the reversed node. The
sign is the `-1` in `e_a ↦ -e_{rev a}`. -/
private lemma typeAWeight_rev {a : ℕ} (ha : a ≤ n) (k : Fin n) :
    typeAWeight n (n - a) k = -typeAWeight n a k.rev := by
  have hk : ((k.rev : Fin n) : ℕ) = n - 1 - (k : ℕ) := by rw [Fin.val_rev]; omega
  have hkn := k.isLt
  simp only [typeAWeight, hk]
  split_ifs <;> omega

/-- Reversing the classical index reflects the chosen cocharacter potential at the reversed node.
The additive constant is harmless: only differences of potentials are coroots. -/
private lemma typeACoweight_rev {a : ℕ} (ha : a ≤ n) (k : Fin n) :
    typeACoweight n (n - a) k = 1 - typeACoweight n a k.rev := by
  have hk : ((k.rev : Fin n) : ℕ) = n - 1 - (k : ℕ) := by rw [Fin.val_rev]; omega
  have hkn := k.isLt
  simp only [typeACoweight, hk]
  split_ifs <;> omega

private lemma typeAPairRoot_typeAGraphPairMap (p : TypeAIndex n) (k : Fin n) :
    typeAPairRoot (typeAGraphPairMap p) k = typeAPairRoot p k.rev := by
  have hle : ∀ x : Fin (n + 1), (x : ℕ) ≤ n := fun x => Nat.lt_succ_iff.mp x.isLt
  simp only [typeAPairRoot, typeAGraphPairMap, Pi.sub_apply, val_rev_succ,
    typeAWeight_rev (hle _) k]
  ring

private lemma typeAPairCoroot_typeAGraphPairMap (p : TypeAIndex n) (k : Fin n) :
    typeAPairCoroot (typeAGraphPairMap p) k = typeAPairCoroot p k.rev := by
  have hle : ∀ x : Fin (n + 1), (x : ℕ) ≤ n := fun x => Nat.lt_succ_iff.mp x.isLt
  simp only [typeAPairCoroot, typeAGraphPairMap, Pi.sub_apply, val_rev_succ,
    typeACoweight_rev (hle _) k]
  ring

/-- The permutation of the pinned root indices induced by the graph automorphism. -/
private def typeAGraphIndexPerm (n : ℕ) : Equiv.Perm (Fin (n * (n + 1))) :=
  ((typeAIndexEquiv n).symm.trans (typeAGraphPairMap_involutive (n := n)).toPerm).trans
    (typeAIndexEquiv n)

private lemma typeAIndexEquiv_symm_typeAGraphIndexPerm (k : Fin (n * (n + 1))) :
    (typeAIndexEquiv n).symm (typeAGraphIndexPerm n k) =
      typeAGraphPairMap ((typeAIndexEquiv n).symm k) := by
  simp [typeAGraphIndexPerm, Involutive.coe_toPerm]

private lemma typeAGraphIndexPerm_involutive : Involutive (typeAGraphIndexPerm n) := fun k =>
  (typeAIndexEquiv n).symm.injective <| by
    rw [typeAIndexEquiv_symm_typeAGraphIndexPerm, typeAIndexEquiv_symm_typeAGraphIndexPerm,
      typeAGraphPairMap_involutive]

private lemma typeAGraphIndexPerm_symm :
    (typeAGraphIndexPerm n).symm = typeAGraphIndexPerm n :=
  Equiv.ext fun k => by
    rw [Equiv.symm_apply_eq]
    exact (typeAGraphIndexPerm_involutive k).symm

/-- Reversing the coordinates of `Fin n → ℤ`, the common character- and cocharacter-lattice map of
the type `Aₙ` graph automorphism. -/
private def typeARevEquiv (n : ℕ) : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) :=
  LinearEquiv.funCongrLeft ℤ ℤ (Fin.revPerm : Equiv.Perm (Fin n))

private lemma typeARevEquiv_eq (x : Fin n → ℤ) : typeARevEquiv n x = fun k => x k.rev := (rfl)

/-- **The graph automorphism of the pinned simply connected root datum of type `Aₙ`.** It reverses
the coordinates of the character and cocharacter lattices, which on the classical model is
`e_a ↦ -e_{rev a}`, and permutes the roots accordingly. It is the root-datum shadow of the
diagram automorphism of `sl_{n + 1}`, and the `Fin`-level datum a pinned group automorphism of the
`²Aₙ` family is built from. -/
def typeAGraphAut (n : ℕ) : RootPairing.Aut (typeASimplyConnectedRootDatum n) where
  weightMap := (typeARevEquiv n).toLinearMap
  coweightMap := (typeARevEquiv n).toLinearMap
  indexEquiv := typeAGraphIndexPerm n
  weight_coweight_transpose := by
    -- Both sides evaluate to a dot product against a reversed vector; reindexing the sum by the
    -- reversal, an involution, exchanges the two.
    have key : ∀ u v : Fin n → ℤ, (fun k => u k.rev) ⬝ᵥ v = u ⬝ᵥ fun k => v k.rev := fun u v =>
      Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin n)) _ _ fun k => by simp
    refine LinearMap.ext fun y => LinearMap.ext fun x => ?_
    simpa [typeARevEquiv_eq] using key x y
  root_weightMap := by
    funext k j
    simpa [typeARevEquiv_eq, root_typeASimplyConnectedRootDatum,
      typeAIndexEquiv_symm_typeAGraphIndexPerm] using
      (typeAPairRoot_typeAGraphPairMap ((typeAIndexEquiv n).symm k) j).symm
  coroot_coweightMap := by
    funext k j
    simpa [typeARevEquiv_eq, coroot_typeASimplyConnectedRootDatum, typeAGraphIndexPerm_symm,
      typeAIndexEquiv_symm_typeAGraphIndexPerm] using
      (typeAPairCoroot_typeAGraphPairMap ((typeAIndexEquiv n).symm k) j).symm
  bijective_weightMap := (typeARevEquiv n).bijective
  bijective_coweightMap := (typeARevEquiv n).bijective

private lemma indexEquiv_typeAGraphAut :
    (typeAGraphAut n).indexEquiv = typeAGraphIndexPerm n := (rfl)

/-- The graph automorphism reverses the fundamental-weight coordinates of a character. -/
@[simp] theorem weightMap_typeAGraphAut_apply (x : Fin n → ℤ) (k : Fin n) :
    (typeAGraphAut n).toHom.weightMap x k = x k.rev := by
  unfold typeAGraphAut
  exact congrFun (typeARevEquiv_eq x) k

/-- The graph automorphism reverses the simple-coroot coordinates of a cocharacter. -/
@[simp] theorem coweightMap_typeAGraphAut_apply (x : Fin n → ℤ) (k : Fin n) :
    (typeAGraphAut n).toHom.coweightMap x k = x k.rev := by
  unfold typeAGraphAut
  exact congrFun (typeARevEquiv_eq x) k

/-- **The graph automorphism reverses the Bourbaki-numbered chain.** On the first `n` root indices,
the simple roots in Bourbaki order, the induced permutation is `Fin.revPerm`, which is
`TauCeti.graphPermA n`. -/
@[simp] theorem indexEquiv_typeAGraphAut_typeASimpleIndex (i : Fin n) :
    (typeAGraphAut n).indexEquiv (typeASimpleIndex n i) = typeASimpleIndex n i.rev := by
  refine (typeAIndexEquiv n).symm.injective ?_
  have hi : (i : ℕ) < n := i.isLt
  rw [indexEquiv_typeAGraphAut,
    typeAIndexEquiv_symm_typeAGraphIndexPerm, typeAIndexEquiv_symm_typeASimpleIndex,
    typeAIndexEquiv_symm_typeASimpleIndex]
  refine Subtype.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;>
    simp only [typeAGraphPairMap, Fin.val_rev] <;> omega

/-- **The type `Aₙ` graph automorphism is an involution.** It is the automorphism attached to the
order-two symmetry of the `Aₙ` diagram, so a Steinberg endomorphism of the `²Aₙ` family built from
it composes with the field Frobenius to something whose square is an ordinary Frobenius. -/
@[simp] theorem typeAGraphAut_sq (n : ℕ) : typeAGraphAut n ^ 2 = 1 := by
  rw [sq]
  ext x k
  · simp
  · simp
  · simp only [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.toHom_comp,
      RootPairing.Hom.comp, Equiv.trans_apply, RootPairing.Equiv.toHom_one,
      RootPairing.Hom.indexEquiv_one, Equiv.refl_apply, indexEquiv_typeAGraphAut]
    rw [typeAGraphIndexPerm_involutive]

/-- **The type `Aₙ` graph automorphism is nontrivial once the chain has two nodes.** The bound is
the one carried by `TauCeti.graphPermA_ne_one`: on fewer nodes the reversal of `Fin n` is the
identity, and there is nothing to prove nontrivial. -/
theorem typeAGraphAut_ne_one {n : ℕ} (hn : 2 ≤ n) : typeAGraphAut n ≠ 1 := by
  intro h
  have hz : (0 : ℕ) < n := by omega
  have h0 := congrArg (fun g : RootPairing.Aut (typeASimplyConnectedRootDatum n) =>
    g.indexEquiv (typeASimpleIndex n ⟨0, hz⟩)) h
  simp only [indexEquiv_typeAGraphAut_typeASimpleIndex, RootPairing.Equiv.toHom_one,
    RootPairing.Hom.indexEquiv_one, Equiv.refl_apply] at h0
  have h1 : ((⟨0, hz⟩ : Fin n).rev : Fin n) = ⟨0, hz⟩ := typeASimpleIndex_injective h0
  have h2 : ((⟨0, hz⟩ : Fin n).rev : Fin n).val = 0 := congrArg Fin.val h1
  simp only [Fin.val_rev] at h2
  omega

/-- **The graph automorphism preserves the pinned base.** Its permutation of root indices maps the
first `n` indices onto themselves, so the automorphism is a symmetry of the pinning and not merely
of the root system. -/
@[simp] theorem support_map_typeASimplyConnectedBase_typeAGraphAut (n : ℕ) :
    Finset.image (typeAGraphAut n).indexEquiv (typeASimplyConnectedBase n).support =
      (typeASimplyConnectedBase n).support := by
  classical
  have hmem : ∀ k : Fin (n * (n + 1)), (k : ℕ) < n →
      (((typeAGraphAut n).indexEquiv k : Fin (n * (n + 1))) : ℕ) < n := by
    intro k hk
    have hk' : k = typeASimpleIndex n ⟨k, hk⟩ := Fin.ext (by simp)
    rw [hk', indexEquiv_typeAGraphAut_typeASimpleIndex, typeASimpleIndex_val]
    exact (⟨(k : ℕ), hk⟩ : Fin n).rev.isLt
  have hsymm : (typeAGraphAut n).indexEquiv.symm = (typeAGraphAut n).indexEquiv :=
    typeAGraphIndexPerm_symm
  refine Finset.ext fun k => ?_
  rw [Finset.mem_image]
  refine ⟨?_, fun hk => ⟨(typeAGraphAut n).indexEquiv.symm k, ?_, Equiv.apply_symm_apply _ _⟩⟩
  · rintro ⟨l, hl, rfl⟩
    exact mem_typeASimplyConnectedBase_support.mpr
      (hmem l (mem_typeASimplyConnectedBase_support.mp hl))
  · rw [mem_typeASimplyConnectedBase_support, hsymm]
    exact hmem k (mem_typeASimplyConnectedBase_support.mp hk)

end DynkinType

end TauCeti
