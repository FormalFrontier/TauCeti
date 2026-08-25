/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Reflection

public section

/-!
# The classical model of type `Cₙ` in the pinned coordinates

This file sets up the coordinates in which
`TauCeti.DynkinType.typeCSimplyConnectedRootDatum` is built, and proves everything about the roots
of type `Cₙ` that can be said before they are indexed: the two coordinate families, the signed
classical basis vectors `± e_a` out of which every root is a sum of two, and the action of a
reflection on those signed basis vectors.

Write `e₀, …, e_{n-1}` for the standard basis of the classical model `ℤ ^ n`, in which the roots of
type `Cₙ` are the short roots `± e_a ± e_b` with `a ≠ b` and the long roots `± 2 e_a`, with simple
roots `αᵢ = eᵢ - eᵢ₊₁` for `i < n - 1` and `α_{n-1} = 2 e_{n-1}`. The corresponding simple coroots
are `αᵢ^∨ = eᵢ - eᵢ₊₁` and `α_{n-1}^∨ = e_{n-1}`, and they are a basis of the classical lattice,
which is what makes `Cₙ` the classical family whose whole construction stays inside the classical
basis vectors: both

```text
weight n a   = (⟨e_a, αₖ^∨⟩)ₖ         = ([a = k] - [a = k + 1])ₖ,
coweight n a = (coefficient of αₖ^∨)ₖ = ([a ≤ k])ₖ
```

are integral, the second because `e_a = ∑ a ≤ k, αₖ^∨`. Everything here is a finite calculation with
these two families, resting on the single identity
`TauCeti.DynkinType.TypeC.weight_dotProduct_coweight`, which says that the pinned pairing sees the
classical pairing `⟨e_a, e_c⟩ = [a = c]` exactly.

The reflection in the root `p + q` acts on signed basis vectors by the involution exchanging `p`
with `-q` and `-p` with `q`; that is `TauCeti.DynkinType.TypeC.signedReflection`, and its
uniformity in the shape of the root is what makes the two reflection axioms one five-case
calculation rather than one case per pair of shapes. The long roots are the case `p = q`, where the
coroot is the halved `p` rather than `p + q`, and that is the only asymmetry between the two
calculations.

## The domain of the pair operations

A pair `(p, q)` of signed basis vectors names a root only when `q ≠ signedNeg p`. On the excluded
diagonal `q = -p` the sum `p + q` is zero, which is no root, and there is no reflection in it, so
outside that hypothesis `TauCeti.DynkinType.TypeC.pairRoot`,
`TauCeti.DynkinType.TypeC.pairCoroot` and `TauCeti.DynkinType.TypeC.signedReflection` are total
functions carrying auxiliary data with no root-theoretic meaning. Every substantive lemma below
accordingly assumes `q ≠ signedNeg p`, and the root indices of the datum are built so that the
hypothesis always holds.

## Main definitions

* `TauCeti.DynkinType.TypeC.weight` and `TauCeti.DynkinType.TypeC.coweight`: the character- and
  cocharacter-lattice coordinates of a classical basis vector.
* `TauCeti.DynkinType.TypeC.pairRoot` and `TauCeti.DynkinType.TypeC.pairCoroot`: the root `p + q`
  and its coroot, in those coordinates, for `q ≠ signedNeg p`.
* `TauCeti.DynkinType.TypeC.signedReflection`: the reflection in `p + q`, on signed basis vectors,
  for `q ≠ signedNeg p`.

## Main results

* `TauCeti.DynkinType.TypeC.signedWeight_signedReflection` and
  `TauCeti.DynkinType.TypeC.signedCoweight_signedReflection`: the reflection acts as the reflection
  formula says it does.
* `TauCeti.DynkinType.TypeC.pairRoot_reflection` and
  `TauCeti.DynkinType.TypeC.pairCoroot_reflection`: the transported form of those two identities,
  which is what the root datum's reflection axioms consume.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate III, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. This supports the `Cₙ` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

namespace TauCeti

open Function Set

namespace DynkinType

/- The classical model of the root system of type `Cₙ`, in the coordinates pinned by the
fundamental weights and the simple coroots. -/
namespace TypeC

variable {n : ℕ}

/-! ## The two coordinate families -/

/-- The character-lattice coordinates of the classical basis vector `e_a` of type `Cₙ`: its
pairings `⟨e_a, αₖ^∨⟩ = [a = k] - [a = k + 1]` against the simple coroots. -/
def weight (n a : ℕ) : Fin n → ℤ :=
  fun k => (if a = (k : ℕ) then 1 else 0) - (if a = (k : ℕ) + 1 then 1 else 0)

@[simp] lemma weight_apply (n a : ℕ) (k : Fin n) :
    weight n a k = (if a = (k : ℕ) then 1 else 0) - (if a = (k : ℕ) + 1 then 1 else 0) :=
  by rw [weight]

/-- The cocharacter-lattice coordinates of the classical basis vector `e_a` of type `Cₙ`, read off
`e_a = ∑ a ≤ k, αₖ^∨`: the `k`-th coordinate is `[a ≤ k]`. -/
def coweight (n a : ℕ) : Fin n → ℤ :=
  fun k => if a ≤ (k : ℕ) then 1 else 0

@[simp] lemma coweight_apply (n a : ℕ) (k : Fin n) :
    coweight n a k = if a ≤ (k : ℕ) then 1 else 0 :=
  by rw [coweight]

lemma coweight_eq_zero_of_le {a : ℕ} (ha : n ≤ a) : coweight n a = 0 := by
  funext k
  have := k.isLt
  exact ite_eq_right (by omega)

/-- The fundamental pairing identity of type `Cₙ`: the two pinned lattices see the classical
pairing `⟨e_a, e_c⟩ = [a = c]` exactly, with no correction term, because the simple coroots of `Cₙ`
are a basis of the classical lattice. -/
lemma weight_dotProduct_coweight {a c : ℕ} (ha : a < n) :
    weight n a ⬝ᵥ coweight n c = if a = c then 1 else 0 := by
  have key : ∀ b : ℕ, ∑ k : Fin n, (if b = (k : ℕ) then (1 : ℤ) else 0) *
      (if c ≤ (k : ℕ) then 1 else 0) = if h : b < n then (if c ≤ b then (1 : ℤ) else 0) else 0 := by
    intro b
    simp only [ite_mul, one_mul, zero_mul]
    simpa only [Nat.add_zero, Nat.sub_zero, Nat.zero_le, and_true] using
      sum_ite_val_add (fun k : Fin n => if c ≤ (k : ℕ) then (1 : ℤ) else 0) b 0
  have key' : ∀ b : ℕ, ∑ k : Fin n, (if b = (k : ℕ) + 1 then (1 : ℤ) else 0) *
      (if c ≤ (k : ℕ) then 1 else 0)
        = if h : b - 1 < n ∧ 1 ≤ b then (if c ≤ b - 1 then (1 : ℤ) else 0) else 0 := by
    intro b
    simp only [ite_mul, one_mul, zero_mul]
    exact sum_ite_val_add (fun k : Fin n => if c ≤ (k : ℕ) then (1 : ℤ) else 0) b 1
  simp only [dotProduct, weight, coweight, sub_mul, Finset.sum_sub_distrib,
    key a, key' a]
  split_ifs <;> omega

/-! ## Signed basis vectors -/

/-- A signed classical basis vector `± e_a`, the atom out of which every root of type `Cₙ` is built
as a sum of two. -/
abbrev Signed (n : ℕ) := Fin n × Bool

/-- The opposite `∓ e_a` of a signed basis vector. -/
def signedNeg (x : Signed n) : Signed n := (x.1, !x.2)

@[simp] lemma signedNeg_mk (a : Fin n) (s : Bool) :
    signedNeg ((a, s) : Signed n) = (a, !s) := by
  rw [signedNeg]

@[simp] lemma signedNeg_signedNeg (x : Signed n) : signedNeg (signedNeg x) = x := by
  simp [signedNeg]

lemma signedNeg_ne (x : Signed n) : signedNeg x ≠ x := by
  simp [signedNeg, Prod.ext_iff]

lemma ne_signedNeg_of_ne_signedNeg {x y : Signed n} (h : y ≠ signedNeg x) :
    x ≠ signedNeg y := by
  intro hx
  exact h (by rw [hx, signedNeg_signedNeg])

/-- The character-lattice coordinates of a signed basis vector. -/
def signedWeight (x : Signed n) : Fin n → ℤ :=
  if x.2 then -weight n (x.1 : ℕ) else weight n (x.1 : ℕ)

/-- The cocharacter-lattice coordinates of a signed basis vector. -/
def signedCoweight (x : Signed n) : Fin n → ℤ :=
  if x.2 then -coweight n (x.1 : ℕ) else coweight n (x.1 : ℕ)

@[simp] lemma signedWeight_false (a : Fin n) :
    signedWeight ((a, false) : Signed n) = weight n (a : ℕ) := by
  simp [signedWeight]

@[simp] lemma signedWeight_true (a : Fin n) :
    signedWeight ((a, true) : Signed n) = -weight n (a : ℕ) := by
  simp [signedWeight]

@[simp] lemma signedCoweight_false (a : Fin n) :
    signedCoweight ((a, false) : Signed n) = coweight n (a : ℕ) := by
  simp [signedCoweight]

@[simp] lemma signedCoweight_true (a : Fin n) :
    signedCoweight ((a, true) : Signed n) = -coweight n (a : ℕ) := by
  simp [signedCoweight]

@[simp] lemma signedWeight_signedNeg (x : Signed n) :
    signedWeight (signedNeg x) = -signedWeight x := by
  obtain ⟨a, s⟩ := x
  cases s <;> simp [signedWeight, signedNeg]

@[simp] lemma signedCoweight_signedNeg (x : Signed n) :
    signedCoweight (signedNeg x) = -signedCoweight x := by
  obtain ⟨a, s⟩ := x
  cases s <;> simp [signedCoweight, signedNeg]

/-- The pinned pairing of two signed basis vectors: `1` on the diagonal, `-1` on opposites, and `0`
otherwise. -/
lemma signedWeight_dotProduct_signedCoweight (x y : Signed n) :
    signedWeight x ⬝ᵥ signedCoweight y =
      if x = y then 1 else if x = signedNeg y then -1 else 0 := by
  obtain ⟨a, s⟩ := x
  obtain ⟨b, t⟩ := y
  have h := weight_dotProduct_coweight (n := n) (a := (a : ℕ)) (c := (b : ℕ)) a.isLt
  have hab : (a = b) ↔ ((a : ℕ) = (b : ℕ)) := by simp [Fin.ext_iff]
  cases s <;> cases t <;>
    simp only [signedWeight, signedCoweight, signedNeg, Bool.false_eq_true, ite_false, ite_true,
      Bool.not_false, Bool.not_true, neg_dotProduct, dotProduct_neg, neg_neg, h, Prod.mk.injEq,
      hab] <;>
    split_ifs <;> simp_all

lemma signedWeight_dotProduct_self (x : Signed n) :
    signedWeight x ⬝ᵥ signedCoweight x = 1 := by
  rw [signedWeight_dotProduct_signedCoweight, ite_eq_left rfl]

lemma signedWeight_dotProduct_nonpos {x y : Signed n} (h : x ≠ y) :
    signedWeight x ⬝ᵥ signedCoweight y ≤ 0 := by
  rw [signedWeight_dotProduct_signedCoweight, ite_eq_right h]
  split_ifs <;> omega

lemma signedWeight_dotProduct_nonneg {x y : Signed n} (h : x ≠ signedNeg y) :
    0 ≤ signedWeight x ⬝ᵥ signedCoweight y := by
  rw [signedWeight_dotProduct_signedCoweight]
  split_ifs <;> omega

lemma signedWeight_dotProduct_eq_zero {x y : Signed n} (h : x ≠ y)
    (h' : x ≠ signedNeg y) : signedWeight x ⬝ᵥ signedCoweight y = 0 := by
  rw [signedWeight_dotProduct_signedCoweight, ite_eq_right h, ite_eq_right h']

lemma eq_of_signedWeight_dotProduct_eq_one {x y : Signed n}
    (h : signedWeight x ⬝ᵥ signedCoweight y = 1) : x = y := by
  by_contra hxy
  have := signedWeight_dotProduct_nonpos hxy
  omega

lemma signedWeight_injective : Injective (signedWeight (n := n)) := by
  intro x y h
  refine eq_of_signedWeight_dotProduct_eq_one ?_
  rw [h]
  exact signedWeight_dotProduct_self y

/-! ## Roots and coroots of a pair of signed basis vectors -/

/-- The root `p + q` attached to a pair of signed basis vectors, in fundamental-weight coordinates.

This is a root only under `y ≠ signedNeg x`; on the excluded diagonal `y = -x` the value is `0`,
which is no root. -/
def pairRoot (x y : Signed n) : Fin n → ℤ := signedWeight x + signedWeight y

lemma pairRoot_def (x y : Signed n) : pairRoot x y = signedWeight x + signedWeight y := by
  rw [pairRoot]

/-- The coroot of the root `p + q`, in simple-coroot coordinates. It is `p + q` again for the short
roots `p ≠ q`, and the halved `p` for the long roots `p = q`.

This is the coroot of a root only under `y ≠ signedNeg x`; on the excluded diagonal `y = -x` there
is no root `x + y` and the value here is auxiliary data. -/
def pairCoroot (x y : Signed n) : Fin n → ℤ :=
  if x = y then signedCoweight x else signedCoweight x + signedCoweight y

@[simp] lemma pairCoroot_self (x : Signed n) : pairCoroot x x = signedCoweight x :=
  ite_eq_left rfl

@[simp] lemma pairCoroot_of_ne {x y : Signed n} (h : x ≠ y) :
    pairCoroot x y = signedCoweight x + signedCoweight y :=
  ite_eq_right h

lemma pairRoot_comm (x y : Signed n) : pairRoot x y = pairRoot y x :=
  add_comm _ _

lemma pairCoroot_comm (x y : Signed n) : pairCoroot x y = pairCoroot y x := by
  rcases eq_or_ne x y with rfl | h
  · rfl
  · rw [pairCoroot, pairCoroot, ite_eq_right h, ite_eq_right h.symm, add_comm]

lemma pairRoot_dotProduct_pairCoroot_self {p q : Signed n} (h : q ≠ signedNeg p) :
    pairRoot p q ⬝ᵥ pairCoroot p q = 2 := by
  rcases eq_or_ne p q with rfl | hpq
  · rw [pairCoroot, ite_eq_left rfl, pairRoot, add_dotProduct, signedWeight_dotProduct_self]
    norm_num
  · rw [pairCoroot, ite_eq_right hpq, pairRoot, add_dotProduct, dotProduct_add, dotProduct_add,
      signedWeight_dotProduct_self, signedWeight_dotProduct_self,
      signedWeight_dotProduct_eq_zero hpq (ne_signedNeg_of_ne_signedNeg h),
      signedWeight_dotProduct_eq_zero hpq.symm h]
    ring

/-- Cartan integers between roots in the classical type `C` model have absolute value at most
two. -/
lemma abs_pairRoot_dotProduct_pairCoroot_le_two {x y p q : Signed n}
    (hpq : q ≠ signedNeg p) :
    |pairRoot x y ⬝ᵥ pairCoroot p q| ≤ 2 := by
  have atom_le_one (z : Signed n) : |signedWeight z ⬝ᵥ pairCoroot p q| ≤ 1 := by
    rcases eq_or_ne p q with rfl | hpq_ne
    · rw [pairCoroot_self, signedWeight_dotProduct_signedCoweight, abs_le]
      constructor <;> split_ifs <;> omega
    · rw [pairCoroot_of_ne hpq_ne, dotProduct_add,
        signedWeight_dotProduct_signedCoweight,
        signedWeight_dotProduct_signedCoweight, abs_le]
      have hp_ne_neg_q : p ≠ signedNeg q := ne_signedNeg_of_ne_signedNeg hpq
      have hnegp_ne_negq : signedNeg p ≠ signedNeg q := by
        intro h
        exact hpq_ne (by simpa using congrArg signedNeg h)
      constructor <;> split_ifs <;> simp_all
  rw [pairRoot, add_dotProduct]
  have hx := atom_le_one x
  have hy := atom_le_one y
  calc
    |signedWeight x ⬝ᵥ pairCoroot p q + signedWeight y ⬝ᵥ pairCoroot p q| ≤
        |signedWeight x ⬝ᵥ pairCoroot p q| + |signedWeight y ⬝ᵥ pairCoroot p q| :=
      abs_add_le _ _
    _ ≤ 2 := by omega

/-- A signed basis vector pairs to at least `1` with the coroot of `p + q` exactly when it is `p` or
`q`. This is the recognition principle behind injectivity of the roots and coroots. -/
lemma one_le_dotProduct_pairCoroot_iff {p q : Signed n} (h : q ≠ signedNeg p)
    (z : Signed n) :
    1 ≤ signedWeight z ⬝ᵥ pairCoroot p q ↔ (z = p ∨ z = q) := by
  have hpq := ne_signedNeg_of_ne_signedNeg h
  constructor
  · intro hz
    by_contra hc
    have hzp : z ≠ p := fun h' => hc (Or.inl h')
    have hzq : z ≠ q := fun h' => hc (Or.inr h')
    rcases eq_or_ne p q with rfl | hne
    · rw [pairCoroot, ite_eq_left rfl] at hz
      have := signedWeight_dotProduct_nonpos hzp
      omega
    · rw [pairCoroot, ite_eq_right hne, dotProduct_add] at hz
      have := signedWeight_dotProduct_nonpos hzp
      have := signedWeight_dotProduct_nonpos hzq
      omega
  · intro hz
    rcases eq_or_ne p q with rfl | hne
    · rw [pairCoroot, ite_eq_left rfl]
      have hzp : z = p := by rcases hz with h' | h' <;> exact h'
      rw [hzp, signedWeight_dotProduct_self]
    · rw [pairCoroot, ite_eq_right hne, dotProduct_add]
      rcases hz with hz | hz <;> rw [hz]
      · have h1 := signedWeight_dotProduct_self p
        have h2 := signedWeight_dotProduct_nonneg (x := p) (y := q) hpq
        omega
      · have h1 := signedWeight_dotProduct_self q
        have h2 := signedWeight_dotProduct_nonneg (x := q) (y := p) h
        omega

/-- The root half of `TauCeti.DynkinType.TypeC.one_le_dotProduct_pairCoroot_iff`. -/
lemma one_le_pairRoot_dotProduct_iff {p q : Signed n} (h : q ≠ signedNeg p)
    (z : Signed n) :
    1 ≤ pairRoot p q ⬝ᵥ signedCoweight z ↔ (z = p ∨ z = q) := by
  have hpq := ne_signedNeg_of_ne_signedNeg h
  rw [pairRoot, add_dotProduct]
  constructor
  · intro hz
    by_contra hc
    have hzp : z ≠ p := fun h' => hc (Or.inl h')
    have hzq : z ≠ q := fun h' => hc (Or.inr h')
    have := signedWeight_dotProduct_nonpos (Ne.symm hzp)
    have := signedWeight_dotProduct_nonpos (Ne.symm hzq)
    omega
  · intro hz
    rcases hz with hz | hz <;> rw [hz]
    · have h1 := signedWeight_dotProduct_self p
      have h2 := signedWeight_dotProduct_nonneg (x := q) (y := p) h
      omega
    · have h1 := signedWeight_dotProduct_self q
      have h2 := signedWeight_dotProduct_nonneg (x := p) (y := q) hpq
      omega

/-! ## The reflection on signed basis vectors -/

/-- Reflection in the root `p + q`, acting on signed basis vectors: it exchanges `p` with `-q` and
`-p` with `q`, and fixes everything else. On a long root `p = q` the two exchanges coincide and this
is the sign change at the index of `p`.

This is the reflection in a root only under `q ≠ signedNeg p`, the hypothesis of every lemma below;
on the excluded diagonal `q = -p` there is no root `p + q` to reflect in and the value here is
auxiliary data. -/
def signedReflection (p q z : Signed n) : Signed n :=
  if z = p then signedNeg q
  else if z = signedNeg q then p
  else if z = signedNeg p then q
  else if z = q then signedNeg p
  else z

@[simp] lemma signedReflection_left (p q : Signed n) :
    signedReflection p q p = signedNeg q := by
  rw [signedReflection, ite_eq_left rfl]

@[simp] lemma signedReflection_signedNeg_right {p q : Signed n} (h : q ≠ signedNeg p) :
    signedReflection p q (signedNeg q) = p := by
  rw [signedReflection, ite_eq_right fun hc => h (by rw [← hc, signedNeg_signedNeg]),
    ite_eq_left rfl]

@[simp] lemma signedReflection_signedNeg_left {p q : Signed n} (h : q ≠ signedNeg p) :
    signedReflection p q (signedNeg p) = q := by
  rcases eq_or_ne p q with rfl | hne
  · rw [signedReflection, ite_eq_right (signedNeg_ne p), ite_eq_left rfl]
  · rw [signedReflection, ite_eq_right (signedNeg_ne p),
      ite_eq_right fun hc => hne (by simpa only [signedNeg_signedNeg] using congrArg signedNeg hc),
      ite_eq_left rfl]

@[simp] lemma signedReflection_right {p q : Signed n} (h : q ≠ signedNeg p) :
    signedReflection p q q = signedNeg p := by
  rcases eq_or_ne p q with rfl | hne
  · rw [signedReflection, ite_eq_left rfl]
  · rw [signedReflection, ite_eq_right hne.symm, ite_eq_right (Ne.symm (signedNeg_ne q)),
      ite_eq_right h, ite_eq_left rfl]

@[simp] lemma signedReflection_of_ne {p q z : Signed n} (h1 : z ≠ p) (h2 : z ≠ q)
    (h3 : z ≠ signedNeg p) (h4 : z ≠ signedNeg q) : signedReflection p q z = z := by
  rw [signedReflection, ite_eq_right h1, ite_eq_right h4, ite_eq_right h3, ite_eq_right h2]

/-! ### The pairings of a root and its coroot against a signed basis vector -/

lemma dotProduct_pairCoroot_left {p q : Signed n} (h : q ≠ signedNeg p) :
    signedWeight p ⬝ᵥ pairCoroot p q = 1 := by
  rcases eq_or_ne p q with rfl | hne
  · rw [pairCoroot, ite_eq_left rfl, signedWeight_dotProduct_self]
  · rw [pairCoroot, ite_eq_right hne, dotProduct_add, signedWeight_dotProduct_self,
      signedWeight_dotProduct_eq_zero hne (ne_signedNeg_of_ne_signedNeg h), add_zero]

lemma dotProduct_pairCoroot_right {p q : Signed n} (h : q ≠ signedNeg p) :
    signedWeight q ⬝ᵥ pairCoroot p q = 1 := by
  rcases eq_or_ne p q with rfl | hne
  · rw [pairCoroot, ite_eq_left rfl, signedWeight_dotProduct_self]
  · rw [pairCoroot, ite_eq_right hne, dotProduct_add, signedWeight_dotProduct_self,
      signedWeight_dotProduct_eq_zero hne.symm h, zero_add]

lemma dotProduct_pairCoroot_of_ne {p q z : Signed n} (h1 : z ≠ p) (h2 : z ≠ q)
    (h3 : z ≠ signedNeg p) (h4 : z ≠ signedNeg q) : signedWeight z ⬝ᵥ pairCoroot p q = 0 := by
  rcases eq_or_ne p q with rfl | hne
  · rw [pairCoroot, ite_eq_left rfl, signedWeight_dotProduct_eq_zero h1 h3]
  · rw [pairCoroot, ite_eq_right hne, dotProduct_add, signedWeight_dotProduct_eq_zero h1 h3,
      signedWeight_dotProduct_eq_zero h2 h4, add_zero]

lemma pairRoot_dotProduct_of_ne {p q z : Signed n} (h1 : z ≠ p) (h2 : z ≠ q)
    (h3 : z ≠ signedNeg p) (h4 : z ≠ signedNeg q) : pairRoot p q ⬝ᵥ signedCoweight z = 0 := by
  rw [pairRoot, add_dotProduct,
    signedWeight_dotProduct_eq_zero (Ne.symm h1)
      (fun hc => h3 (by rw [hc, signedNeg_signedNeg])),
    signedWeight_dotProduct_eq_zero (Ne.symm h2)
      (fun hc => h4 (by rw [hc, signedNeg_signedNeg])), add_zero]

/-- **The reflection in a root acts on signed basis vectors.** This is the whole content of the
reflection axiom for the roots, and it is uniform in the shapes of both roots involved: the same
five-case calculation covers the short and the long reflecting root. -/
lemma signedWeight_signedReflection {p q : Signed n} (h : q ≠ signedNeg p)
    (z : Signed n) :
    signedWeight (signedReflection p q z) =
      signedWeight z - (signedWeight z ⬝ᵥ pairCoroot p q) • pairRoot p q := by
  rcases eq_or_ne z p with rfl | h1
  · rw [signedReflection_left, dotProduct_pairCoroot_left h, signedWeight_signedNeg, pairRoot]
    module
  · rcases eq_or_ne z q with rfl | h2
    · rw [signedReflection_right h, dotProduct_pairCoroot_right h, signedWeight_signedNeg, pairRoot]
      module
    · rcases eq_or_ne z (signedNeg p) with rfl | h3
      · rw [signedReflection_signedNeg_left h, signedWeight_signedNeg, neg_dotProduct,
          dotProduct_pairCoroot_left h, pairRoot]
        module
      · rcases eq_or_ne z (signedNeg q) with rfl | h4
        · rw [signedReflection_signedNeg_right h, signedWeight_signedNeg, neg_dotProduct,
            dotProduct_pairCoroot_right h, pairRoot]
          module
        · rw [signedReflection_of_ne h1 h2 h3 h4, dotProduct_pairCoroot_of_ne h1 h2 h3 h4]
          module

/-- The coroot half of `TauCeti.DynkinType.TypeC.signedWeight_signedReflection`. The long
reflecting root is a genuine second case here, its coroot being the halved one. -/
lemma signedCoweight_signedReflection {p q : Signed n} (h : q ≠ signedNeg p)
    (z : Signed n) :
    signedCoweight (signedReflection p q z) =
      signedCoweight z - (pairRoot p q ⬝ᵥ signedCoweight z) • pairCoroot p q := by
  rcases eq_or_ne p q with rfl | hne
  · -- the long reflecting root `2 p`, with coroot `p`
    have hcoeff : pairRoot p p ⬝ᵥ signedCoweight p = 2 := by
      rw [pairRoot, add_dotProduct, signedWeight_dotProduct_self]
      norm_num
    rcases eq_or_ne z p with rfl | h1
    · rw [signedReflection_left, hcoeff, signedCoweight_signedNeg, pairCoroot, ite_eq_left rfl]
      module
    · rcases eq_or_ne z (signedNeg p) with rfl | h3
      · rw [signedReflection_signedNeg_left h, signedCoweight_signedNeg, dotProduct_neg, hcoeff,
          pairCoroot, ite_eq_left rfl]
        module
      · rw [signedReflection_of_ne h1 h1 h3 h3, pairRoot_dotProduct_of_ne h1 h1 h3 h3]
        module
  · -- a short reflecting root, whose coroot is itself
    have hleft : pairRoot p q ⬝ᵥ signedCoweight p = 1 := by
      rw [pairRoot, add_dotProduct, signedWeight_dotProduct_self,
        signedWeight_dotProduct_eq_zero hne.symm h, add_zero]
    have hright : pairRoot p q ⬝ᵥ signedCoweight q = 1 := by
      rw [pairRoot, add_dotProduct, signedWeight_dotProduct_self,
        signedWeight_dotProduct_eq_zero hne (ne_signedNeg_of_ne_signedNeg h), zero_add]
    rcases eq_or_ne z p with rfl | h1
    · rw [signedReflection_left, hleft, signedCoweight_signedNeg, pairCoroot, ite_eq_right hne]
      module
    · rcases eq_or_ne z q with rfl | h2
      · rw [signedReflection_right h, hright, signedCoweight_signedNeg, pairCoroot,
          ite_eq_right hne]
        module
      · rcases eq_or_ne z (signedNeg p) with rfl | h3
        · rw [signedReflection_signedNeg_left h, signedCoweight_signedNeg, dotProduct_neg, hleft,
            pairCoroot, ite_eq_right hne]
          module
        · rcases eq_or_ne z (signedNeg q) with rfl | h4
          · rw [signedReflection_signedNeg_right h, signedCoweight_signedNeg, dotProduct_neg,
              hright, pairCoroot, ite_eq_right hne]
            module
          · rw [signedReflection_of_ne h1 h2 h3 h4, pairRoot_dotProduct_of_ne h1 h2 h3 h4]
            module

lemma signedReflection_injective {p q : Signed n} (h : q ≠ signedNeg p) :
    Injective (signedReflection p q) := by
  intro z w hzw
  -- In these coordinates `Module.preReflection` in the root `p + q` is definitionally the map
  -- `v ↦ v - (v ⬝ᵥ pairCoroot p q) • pairRoot p q`; Mathlib provides no named bridge, so the
  -- `change` below is what turns the goal left by its injectivity into the reflection formula.
  refine signedWeight_injective ((Module.involutive_preReflection (x := pairRoot p q)
    (f := (dotProductBilin ℤ ℤ).flip (pairCoroot p q))
    (pairRoot_dotProduct_pairCoroot_self h)).injective ?_)
  change signedWeight z - (signedWeight z ⬝ᵥ pairCoroot p q) • pairRoot p q
      = signedWeight w - (signedWeight w ⬝ᵥ pairCoroot p q) • pairRoot p q
  rw [← signedWeight_signedReflection h z, ← signedWeight_signedReflection h w, hzw]

lemma signedReflection_signedNeg {p q : Signed n} (h : q ≠ signedNeg p)
    (z : Signed n) :
    signedReflection p q (signedNeg z) = signedNeg (signedReflection p q z) := by
  refine signedWeight_injective ?_
  rw [signedWeight_signedReflection h (signedNeg z),
    signedWeight_signedNeg (signedReflection p q z), signedWeight_signedReflection h z,
    signedWeight_signedNeg z, neg_dotProduct, neg_smul]
  module

/-- Reflection in the root `p + q` transports the root of a pair to the root of the reflected
pair. -/
lemma pairRoot_reflection {p q : Signed n} (h : q ≠ signedNeg p) (x y : Signed n) :
    pairRoot x y - (pairRoot x y ⬝ᵥ pairCoroot p q) • pairRoot p q
      = pairRoot (signedReflection p q x) (signedReflection p q y) := by
  -- The targeted reflection lemmas are stated for the two summands, so expose just the outer
  -- `pairRoot` applications here while retaining the reflecting root as an API-level term.
  change signedWeight x + signedWeight y -
      ((signedWeight x + signedWeight y) ⬝ᵥ pairCoroot p q) • pairRoot p q
    = signedWeight (signedReflection p q x) + signedWeight (signedReflection p q y)
  rw [signedWeight_signedReflection h x, signedWeight_signedReflection h y, add_dotProduct]
  module

/-- The coroot half of `TauCeti.DynkinType.TypeC.pairRoot_reflection`. -/
lemma pairCoroot_reflection {p q : Signed n} (h : q ≠ signedNeg p) (x y : Signed n) :
    pairCoroot x y - (pairRoot p q ⬝ᵥ pairCoroot x y) • pairCoroot p q
      = pairCoroot (signedReflection p q x) (signedReflection p q y) := by
  by_cases hxy : x = y
  · subst hxy
    rw [pairCoroot_self, pairCoroot_self, signedCoweight_signedReflection h x]
  · rw [pairCoroot_of_ne hxy, pairCoroot_of_ne fun hc => hxy (signedReflection_injective h hc),
      signedCoweight_signedReflection h x, signedCoweight_signedReflection h y, dotProduct_add]
    module

end TypeC

end DynkinType

end TauCeti
