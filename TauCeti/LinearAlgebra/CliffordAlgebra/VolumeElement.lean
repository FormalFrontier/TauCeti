/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Data.List.OfFn
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
-- Private: `Nat.choose_succ_succ` and `Nat.choose_one_right` are used only inside the proof of
-- `CliffordAlgebra.volumeElement_mul_self`.
import Mathlib.Data.Nat.Choose.Basic

/-!
# The volume element of a Clifford algebra

The **volume element** (or pseudoscalar) of a quadratic space is the ordered Clifford product
`ι Q v₁ * ⋯ * ι Q vₙ` of an orthogonal basis. This file builds it, for an arbitrary list of
vectors, and proves the two facts that make it useful: how it commutes past a vector, and what its
square is.

Both come from the single relation `ι Q a * ι Q b = -(ι Q b * ι Q a)` for orthogonal `a` and `b`.
Pushing a vector `ι Q m` from one side of a product of `n` mutually orthogonal vectors to the other
costs a sign `(-1) ^ n` when `m` is orthogonal to every factor
(`CliffordAlgebra.volumeElement_mul_ι_of_forall_isOrtho`). When `m` is instead *one of* the factors,
one of the `n` transpositions is a vector past itself, which is free, so the cost is
`(-1) ^ (n - 1)`
(`CliffordAlgebra.volumeElement_mul_ι_of_mem`). That sign does not depend on `m`, and the condition
is linear in `m`, so it propagates from the factors to their span
(`CliffordAlgebra.volumeElement_mul_ι_of_mem_span`).

This is the even/odd dichotomy of the Clifford algebra as seen from the volume element. If the
factors span `M` and there are **oddly** many of them, the volume element commutes with every
generator, hence is **central** (`CliffordAlgebra.volumeElement_mem_center`); if there are evenly
many, it **anticommutes** with every generator
(`CliffordAlgebra.volumeElement_mul_ι_of_even_length`). It is the odd case that puts a second
element in the centre of the Clifford algebra of an odd-dimensional quadratic space, so that the
centre is a rank-two algebra rather than the scalars — the algebraic reason the structure theorem
of `TauCeti/RepresentationTheory/Spin/Structure.lean` splits an odd-dimensional Clifford algebra
into two matrix blocks while an even-dimensional one is a single block.

The square is a scalar,
`ω * ω = (-1) ^ (n.choose 2) * Q v₁ ⋯ Q vₙ` (`CliffordAlgebra.volumeElement_mul_self`), the sign
counting the `n.choose 2` transpositions needed to interleave two copies of the product. In
particular the volume element of a list of anisotropic vectors is a unit
(`CliffordAlgebra.isUnit_volumeElement`).

Nothing here needs `2` to be invertible, a field, or any finiteness: the hypotheses are exactly
pairwise orthogonality of the list, and, where the span is used, that the list spans `M`.

## Main definitions

* `CliffordAlgebra.volumeElement`: the ordered Clifford product of a list of vectors.

## Main results

* `CliffordAlgebra.volumeElement_mul_ι_of_forall_isOrtho`: a vector orthogonal to every factor
  moves across the product at the cost of `(-1) ^ n`.
* `CliffordAlgebra.volumeElement_mul_ι_of_mem_span`: a vector in the span of a pairwise orthogonal
  list moves across the product at the cost of `(-1) ^ (n - 1)`.
* `CliffordAlgebra.volumeElement_mem_center`: the volume element of a pairwise orthogonal spanning
  list of odd length is central.
* `CliffordAlgebra.volumeElement_mul_ι_of_even_length`: of even length, it anticommutes with every
  generator instead.
* `CliffordAlgebra.volumeElement_mul_self`: the square of the volume element of a pairwise
  orthogonal list is the scalar `(-1) ^ (n.choose 2) * ∏ᵢ Q vᵢ`.
* `CliffordAlgebra.isUnit_volumeElement`: it is a unit as soon as that scalar is.
* `CliffordAlgebra.volumeElement_ofFn_mem_center`: the volume element of an orthogonal basis
  indexed by `Fin n` with `n` odd is central.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 1, "The odd-dimensional case": the centre of a Clifford algebra is the scalars in even
  dimension and a rank-two algebra in odd dimension, whose two central idempotents split the odd
  Clifford algebra into two matrix blocks.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §3.
-/

public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The **volume element** of a list of vectors: the Clifford product
`ι Q v₁ * ⋯ * ι Q vₙ` taken in the order of the list, the empty product being `1`.

The name is chosen for the case the results below are about, that of a pairwise orthogonal list;
for a general list the ordered product is still the object the orthogonality hypotheses are
attached to, and no hypothesis is built into the definition. -/
def volumeElement (Q : QuadraticForm R M) (l : List M) : CliffordAlgebra Q :=
  (l.map (ι Q)).prod

variable {Q : QuadraticForm R M}

/-- The volume element is by definition the product of the images of the list under `ι Q`. -/
theorem volumeElement_eq_prod_map (Q : QuadraticForm R M) (l : List M) :
    volumeElement Q l = (l.map (ι Q)).prod := (rfl)

@[simp]
theorem volumeElement_nil : volumeElement Q ([] : List M) = 1 := (rfl)

@[simp]
theorem volumeElement_cons (a : M) (l : List M) :
    volumeElement Q (a :: l) = ι Q a * volumeElement Q l := by
  rw [volumeElement_eq_prod_map, volumeElement_eq_prod_map, List.map_cons, List.prod_cons]

theorem volumeElement_append (l₁ l₂ : List M) :
    volumeElement Q (l₁ ++ l₂) = volumeElement Q l₁ * volumeElement Q l₂ := by
  rw [volumeElement_eq_prod_map, volumeElement_eq_prod_map, volumeElement_eq_prod_map,
    List.map_append, List.prod_append]

/-! ### Moving a vector across the volume element -/

/-- Cancelling a repeated sign: `(-1) ^ (n + m) * (-1) ^ n = (-1) ^ m`, the bookkeeping that the
two-sided computation of `volumeElement_mul_ι_of_append_cons` runs on. -/
private theorem neg_one_pow_add_mul_neg_one_pow (n m : ℕ) :
    ((-1 : R) ^ (n + m)) * (-1) ^ n = (-1) ^ m := by
  rw [← pow_add]
  have : n + m + n = m + 2 * n := by omega
  rw [this, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- **A vector orthogonal to every factor crosses the volume element at the cost of `(-1) ^ n`**,
`n` the number of factors: each transposition with a factor contributes one sign. -/
theorem volumeElement_mul_ι_of_forall_isOrtho {l : List M} {m : M}
    (h : ∀ x ∈ l, Q.IsOrtho x m) :
    volumeElement Q l * ι Q m = ((-1 : R) ^ l.length) • (ι Q m * volumeElement Q l) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : Q.IsOrtho a m := h a List.mem_cons_self
    have hl : ∀ x ∈ l, Q.IsOrtho x m := fun x hx => h x (List.mem_cons_of_mem _ hx)
    calc volumeElement Q (a :: l) * ι Q m
        = ι Q a * (volumeElement Q l * ι Q m) := by rw [volumeElement_cons, mul_assoc]
      _ = ((-1 : R) ^ l.length) • (ι Q a * ι Q m * volumeElement Q l) := by
          rw [ih hl, mul_smul_comm, mul_assoc]
      _ = ((-1 : R) ^ l.length) • -(ι Q m * volumeElement Q (a :: l)) := by
          rw [ι_mul_ι_comm_of_isOrtho ha, neg_mul, volumeElement_cons, mul_assoc]
      _ = ((-1 : R) ^ (a :: l).length) • (ι Q m * volumeElement Q (a :: l)) := by
          rw [smul_neg, List.length_cons, pow_succ, mul_neg_one, neg_smul]

/-- The mirror image of `volumeElement_mul_ι_of_forall_isOrtho`: the same sign moves the vector
back, the sign being its own inverse. -/
theorem ι_mul_volumeElement_of_forall_isOrtho {l : List M} {m : M}
    (h : ∀ x ∈ l, Q.IsOrtho x m) :
    ι Q m * volumeElement Q l = ((-1 : R) ^ l.length) • (volumeElement Q l * ι Q m) := by
  rw [volumeElement_mul_ι_of_forall_isOrtho h, smul_smul, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_smul]

/-- **A factor of the volume element crosses it at the cost of `(-1) ^ (n - 1)`**: of the `n`
transpositions, the one exchanging the vector with the copy of itself inside the product is free.

The list is presented split at the chosen occurrence of the vector, so that the two halves can be
crossed separately. -/
theorem volumeElement_mul_ι_of_append_cons {l₁ l₂ : List M} {a : M}
    (h₁ : ∀ x ∈ l₁, Q.IsOrtho x a) (h₂ : ∀ x ∈ l₂, Q.IsOrtho x a) :
    volumeElement Q (l₁ ++ a :: l₂) * ι Q a
      = ((-1 : R) ^ (l₁.length + l₂.length)) • (ι Q a * volumeElement Q (l₁ ++ a :: l₂)) := by
  have hmid : volumeElement Q (l₁ ++ a :: l₂)
      = volumeElement Q l₁ * (ι Q a * volumeElement Q l₂) := by
    rw [volumeElement_append, volumeElement_cons]
  calc volumeElement Q (l₁ ++ a :: l₂) * ι Q a
      = volumeElement Q l₁ * (ι Q a * (volumeElement Q l₂ * ι Q a)) := by
        rw [hmid, mul_assoc, mul_assoc]
    _ = ((-1 : R) ^ l₂.length)
          • (volumeElement Q l₁ * (ι Q a * (ι Q a * volumeElement Q l₂))) := by
        rw [volumeElement_mul_ι_of_forall_isOrtho h₂, mul_smul_comm, mul_smul_comm]
    _ = ((-1 : R) ^ (l₁.length + l₂.length)) • ((((-1 : R) ^ l₁.length)
          • (volumeElement Q l₁ * ι Q a)) * (ι Q a * volumeElement Q l₂)) := by
        rw [smul_mul_assoc, smul_smul, neg_one_pow_add_mul_neg_one_pow, mul_assoc]
    _ = ((-1 : R) ^ (l₁.length + l₂.length)) • (ι Q a * volumeElement Q (l₁ ++ a :: l₂)) := by
        rw [← ι_mul_volumeElement_of_forall_isOrtho h₁, hmid, mul_assoc]

/-- **A factor of a pairwise orthogonal volume element crosses it at the cost of `(-1) ^ (n - 1)`.**
-/
theorem volumeElement_mul_ι_of_mem {l : List M} (hl : l.Pairwise Q.IsOrtho) {a : M} (ha : a ∈ l) :
    volumeElement Q l * ι Q a
      = ((-1 : R) ^ (l.length - 1)) • (ι Q a * volumeElement Q l) := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ha
  rw [List.pairwise_append, List.pairwise_cons] at hl
  obtain ⟨-, ⟨h₂, -⟩, h₁⟩ := hl
  have hlen : (l₁ ++ a :: l₂).length - 1 = l₁.length + l₂.length := by
    simp only [List.length_append, List.length_cons]
    omega
  rw [hlen]
  exact volumeElement_mul_ι_of_append_cons (fun x hx => h₁ x hx a List.mem_cons_self)
    (fun x hx => (h₂ x hx).symm)

/-- **The crossing sign propagates from the factors to their span.** The sign `(-1) ^ (n - 1)` does
not depend on the vector, and both sides of the crossing identity are linear in it, so the identity
holds on the whole span of the list — in particular on all of `M` when the list spans. -/
theorem volumeElement_mul_ι_of_mem_span {l : List M} (hl : l.Pairwise Q.IsOrtho) {m : M}
    (hm : m ∈ Submodule.span R {x : M | x ∈ l}) :
    volumeElement Q l * ι Q m
      = ((-1 : R) ^ (l.length - 1)) • (ι Q m * volumeElement Q l) := by
  have hle : Submodule.span R {x : M | x ∈ l}
      ≤ LinearMap.eqLocus ((LinearMap.mulLeft R (volumeElement Q l)).comp (ι Q))
        ((((-1 : R) ^ (l.length - 1)) • LinearMap.mulRight R (volumeElement Q l)).comp (ι Q)) := by
    rw [Submodule.span_le]
    intro x hx
    simpa using volumeElement_mul_ι_of_mem hl hx
  simpa using hle hm

/-! ### The even/odd dichotomy -/

/-- **The volume element of an odd number of pairwise orthogonal vectors spanning `M` is central.**

Crossing a generator costs `(-1) ^ (n - 1)`, and `n - 1` is even, so the volume element commutes
with every generator; the generators generate the algebra, so it commutes with everything. This is
the extra central element that makes the centre of an odd-dimensional Clifford algebra bigger than
the scalars. -/
theorem volumeElement_mem_center {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Odd l.length) (hspan : Submodule.span R {x : M | x ∈ l} = ⊤) :
    volumeElement Q l ∈ Subalgebra.center R (CliffordAlgebra Q) := by
  have hpar : Even (l.length - 1) := Nat.Odd.sub_odd hlen odd_one
  have key : ∀ m : M, volumeElement Q l * ι Q m = ι Q m * volumeElement Q l := by
    intro m
    have h := volumeElement_mul_ι_of_mem_span hl (m := m) (hspan ▸ Submodule.mem_top)
    rwa [hpar.neg_one_pow, one_smul] at h
  rw [Subalgebra.mem_center_iff]
  intro y
  induction y using CliffordAlgebra.induction with
  | algebraMap r => exact Algebra.commutes r _
  | ι m => exact (key m).symm
  | mul x y hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | add x y hx hy => rw [add_mul, hx, hy, mul_add]

/-- **The volume element of a nonempty even number of pairwise orthogonal vectors spanning `M`
anticommutes with every generator**, the crossing sign `(-1) ^ (n - 1)` now being `-1`. So in even
rank the volume element is central only in the degenerate situation where every generator is its
own negative. -/
theorem volumeElement_mul_ι_of_even_length {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Even l.length) (hne : l ≠ [])
    (hspan : Submodule.span R {x : M | x ∈ l} = ⊤) (m : M) :
    volumeElement Q l * ι Q m = -(ι Q m * volumeElement Q l) := by
  have hpos : 1 ≤ l.length := List.length_pos_iff.2 hne
  have hpar : Odd (l.length - 1) := Nat.Even.sub_odd hpos hlen odd_one
  have h := volumeElement_mul_ι_of_mem_span hl (m := m) (hspan ▸ Submodule.mem_top)
  rwa [hpar.neg_one_pow, neg_one_smul] at h

/-! ### The square of the volume element -/

/-- **The square of the volume element of a pairwise orthogonal list is a scalar**,
`(-1) ^ (n.choose 2) * Q v₁ ⋯ Q vₙ`: interleaving the two copies of the product takes
`n.choose 2` transpositions, and each pair of equal adjacent factors collapses to `Q vᵢ`. -/
theorem volumeElement_mul_self {l : List M} (hl : l.Pairwise Q.IsOrtho) :
    volumeElement Q l * volumeElement Q l
      = algebraMap R (CliffordAlgebra Q) (((-1 : R) ^ l.length.choose 2) * (l.map Q).prod) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨ha, hl'⟩ := hl
    have hsym : ∀ x ∈ l, Q.IsOrtho x a := fun x hx => (ha x hx).symm
    have hchoose : (a :: l).length.choose 2 = l.length + l.length.choose 2 := by
      rw [List.length_cons, Nat.choose_succ_succ, Nat.choose_one_right]
    calc volumeElement Q (a :: l) * volumeElement Q (a :: l)
        = ι Q a * (volumeElement Q l * ι Q a) * volumeElement Q l := by
          rw [volumeElement_cons, mul_assoc, mul_assoc, mul_assoc]
      _ = ((-1 : R) ^ l.length)
            • (ι Q a * ι Q a * (volumeElement Q l * volumeElement Q l)) := by
          rw [volumeElement_mul_ι_of_forall_isOrtho hsym, mul_smul_comm, smul_mul_assoc,
            mul_assoc, mul_assoc, mul_assoc]
      _ = algebraMap R (CliffordAlgebra Q)
            (((-1 : R) ^ (a :: l).length.choose 2) * ((a :: l).map Q).prod) := by
          rw [ι_sq_scalar, ih hl', ← map_mul, Algebra.smul_def, ← map_mul]
          congr 1
          rw [hchoose, List.map_cons, List.prod_cons, pow_add]
          ring

/-- **The volume element is a unit as soon as the product of the values `Q vᵢ` is**, its square
being that product up to sign. In particular the volume element of an orthogonal basis of a
quadratic space over a field is a unit exactly when no basis vector is isotropic. -/
theorem isUnit_volumeElement {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (h : IsUnit ((l.map Q).prod)) : IsUnit (volumeElement Q l) := by
  obtain ⟨u, hu⟩ : IsUnit (((-1 : R) ^ l.length.choose 2) * (l.map Q).prod) :=
    (isUnit_one.neg.pow _).mul h
  have hsq : volumeElement Q l * volumeElement Q l = algebraMap R (CliffordAlgebra Q) (u : R) := by
    rw [hu, volumeElement_mul_self hl]
  refine isUnit_iff_exists.2
    ⟨algebraMap R (CliffordAlgebra Q) ((u⁻¹ : Rˣ) : R) * volumeElement Q l, ?_, ?_⟩
  · rw [← mul_assoc, ← Algebra.commutes, mul_assoc, hsq, ← map_mul, Units.inv_mul, map_one]
  · rw [mul_assoc, hsq, ← map_mul, Units.inv_mul, map_one]

/-! ### Orthogonal bases -/

/-- **The volume element of an orthogonal basis of odd rank is central.** This is the form in which
the odd-rank half of the dichotomy is used: the centre of the Clifford algebra of an
odd-dimensional quadratic space contains the pseudoscalar as well as the scalars. -/
theorem volumeElement_ofFn_mem_center {n : ℕ} (b : Module.Basis (Fin n) R M)
    (hb : ∀ i j : Fin n, i ≠ j → Q.IsOrtho (b i) (b j)) (hn : Odd n) :
    volumeElement Q (List.ofFn b) ∈ Subalgebra.center R (CliffordAlgebra Q) := by
  refine volumeElement_mem_center ?_ ?_ ?_
  · exact List.pairwise_ofFn.2 fun _ _ hij => hb _ _ hij.ne
  · rwa [List.length_ofFn]
  · have : {x : M | x ∈ List.ofFn b} = Set.range b := by
      ext x
      simp [List.mem_ofFn']
    rw [this, b.span_eq]

end CliffordAlgebra
