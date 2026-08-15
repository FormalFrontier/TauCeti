/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Artin Braid Groups

The Artin braid group on `n` strands, $B_n$, is the group defined by generators
$\sigma_0, \sigma_1, \dots, \sigma_{n-2}$ (indexed by `Fin (n - 1)`) and relations:
- $\sigma_i \sigma_j = \sigma_j \sigma_i$ whenever $|i - j| \ge 2$ (far commutation),
- $\sigma_i \sigma_{i+1} \sigma_i = \sigma_{i+1} \sigma_i \sigma_{i+1}$ (adjacent braid relation).

This provides the algebraic foundation for the braid presentation of knots and links, as
requested by Layer 4 ("knot theory, done properly") of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`).

## Main definitions

* `TauCeti.KnotTheory.ArtinRelation n`: inductive predicate specifying the Artin relations in
  `FreeGroup (Fin (n - 1))`.
* `TauCeti.KnotTheory.artinRelations n`: defining Artin braid relations in
  `FreeGroup (Fin (n - 1))`.
* `TauCeti.KnotTheory.BraidGroup n`: Artin braid group $B_n$ on $n$ strands, defined as
  `PresentedGroup (artinRelations n)`.
* `TauCeti.KnotTheory.BraidGroup.sigma i`: generator $\sigma_i$ in `BraidGroup n`.
* `TauCeti.KnotTheory.BraidGroup.BraidWord n`: braid word, i.e. list of generator-sign pairs
  `Fin (n - 1) × Bool`.
* `TauCeti.KnotTheory.BraidGroup.evalWord`: evaluation of a `BraidWord n` as an element of
  `BraidGroup n`.
* `TauCeti.KnotTheory.BraidGroup.exponentSum`: total writhe / exponent sum homomorphism
  `BraidGroup n →* Multiplicative ℤ`.
* `TauCeti.KnotTheory.BraidGroup.permHom`: canonical permutation homomorphism
  `BraidGroup n →* Equiv.Perm (Fin n)`.
* `TauCeti.KnotTheory.BraidGroup.PureBraidGroup n`: subgroup of pure braids (`permHom.ker`).
* `TauCeti.KnotTheory.BraidGroup.castSuccHom`: natural strand-inclusion homomorphism
  `BraidGroup n →* BraidGroup (n + 1)`.

## Main results

* `TauCeti.KnotTheory.BraidGroup.comm`: generator commutation
  $\sigma_i \sigma_j = \sigma_j \sigma_i$ when $i.1 + 2 \le j.1$.
* `TauCeti.KnotTheory.BraidGroup.braid_rel`: braid relation
  $\sigma_i \sigma_j \sigma_i = \sigma_j \sigma_i \sigma_j$ when $j.1 = i.1 + 1$.
* `TauCeti.KnotTheory.BraidGroup.exponentSum_sigma`:
  `exponentSum (sigma i) = Multiplicative.ofAdd 1`.
* `TauCeti.KnotTheory.BraidGroup.permHom_sigma`: `permHom (sigma i)` is the transposition swapping
  $i$ and $i+1$.
-/

public section

namespace TauCeti.KnotTheory

open PresentedGroup Equiv Perm

/-- Commutator $a b a^{-1} b^{-1} = 1$ is equivalent to $a b = b a$. -/
theorem mul_inv_mul_inv_eq_one_iff {G : Type*} [Group G] {a b : G} :
    a * b * a⁻¹ * b⁻¹ = 1 ↔ a * b = b * a := by
  rw [mul_inv_eq_one]
  constructor <;> intro h
  · calc a * b = a * b * a⁻¹ * a := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = b * a := by rw [h]
  · calc a * b * a⁻¹ = b * a * a⁻¹ := by rw [h]
      _ = b := by rw [mul_assoc, mul_inv_cancel, mul_one]

/-- Two transpositions with disjoint supports commute. -/
theorem swap_comm_of_disjoint {α : Type*} [DecidableEq α] {a b c d : α}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  ext x
  simp only [Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> first | rfl | { subst_vars; contradiction }

/-- The braid relation holds for adjacent transpositions $(a, b)$ and $(b, c)$. -/
theorem swap_braid_rel {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Equiv.swap a b * Equiv.swap b c * Equiv.swap a b =
      Equiv.swap b c * Equiv.swap a b * Equiv.swap b c := by
  ext x
  simp only [Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> first | rfl | { subst_vars; contradiction }

/-- The defining relations for the Artin braid group on `n` strands in `FreeGroup (Fin (n - 1))`.
- `comm`: $\sigma_i \sigma_j \sigma_i^{-1} \sigma_j^{-1} = 1$ when $i.1 + 2 \le j.1$,
- `braid`: $\sigma_i \sigma_j \sigma_i (\sigma_j \sigma_i \sigma_j)^{-1} = 1$ when $j.1 = i.1 + 1$.
-/
inductive ArtinRelation (n : ℕ) : FreeGroup (Fin (n - 1)) → Prop
  | comm (i j : Fin (n - 1)) (h : i.1 + 2 ≤ j.1) :
      ArtinRelation n (FreeGroup.of i * FreeGroup.of j *
        (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹)
  | braid (i j : Fin (n - 1)) (h : i.1 + 1 = j.1) :
      ArtinRelation n (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
        (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹)

/-- The set of defining relations for the Artin braid group $B_n$. -/
def artinRelations (n : ℕ) : Set (FreeGroup (Fin (n - 1))) :=
  { r | ArtinRelation n r }

/-- The Artin braid group $B_n$ on `n` strands, presented by generators `Fin (n - 1)`
and relations `artinRelations n`. -/
def BraidGroup (n : ℕ) : Type _ :=
  PresentedGroup (artinRelations n)

namespace BraidGroup

variable {n : ℕ}

/-- `BraidGroup n` is a group under composition. -/
instance instGroup : Group (BraidGroup n) :=
  inferInstanceAs (Group (PresentedGroup (artinRelations n)))

/-- `BraidGroup n` is inhabited by the identity braid. -/
instance instInhabited : Inhabited (BraidGroup n) :=
  ⟨1⟩

/-- The standard generator $\sigma_i$ ($0 \le i < n - 1$) of the braid group $B_n$. -/
def sigma (i : Fin (n - 1)) : BraidGroup n :=
  PresentedGroup.of i

/-- Far generators commute: $\sigma_i \sigma_j = \sigma_j \sigma_i$ when $i.1 + 2 \le j.1$. -/
theorem comm (i j : Fin (n - 1)) (h : i.1 + 2 ≤ j.1) :
    sigma i * sigma j = sigma j * sigma i := by
  have hrel : FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹ ∈
      artinRelations n :=
    ArtinRelation.comm i j h
  have h1 := PresentedGroup.one_of_mem hrel
  dsimp [sigma, PresentedGroup.of, PresentedGroup.mk] at h1 ⊢
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  exact mul_inv_mul_inv_eq_one_iff.mp h1

/-- Adjacent generators satisfy the Artin braid relation:
$\sigma_i \sigma_j \sigma_i = \sigma_j \sigma_i \sigma_j$ when $j.1 = i.1 + 1$. -/
theorem braid_rel (i j : Fin (n - 1)) (h : i.1 + 1 = j.1) :
    sigma i * sigma j * sigma i = sigma j * sigma i * sigma j := by
  have hrel : FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
      (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹ ∈ artinRelations n :=
    ArtinRelation.braid i j h
  have h1 := PresentedGroup.one_of_mem hrel
  dsimp [sigma, PresentedGroup.of, PresentedGroup.mk] at h1 ⊢
  rw [map_mul, map_mul, map_mul, map_inv, map_mul, map_mul] at h1
  exact mul_inv_eq_one.mp h1

/-- A combinatorial **braid word** on `n` strands: a list of pairs `(i, b)` where `i` is the
generator index and `b = true` represents $\sigma_i$ while `b = false` represents $\sigma_i^{-1}$.
-/
abbrev BraidWord (n : ℕ) : Type _ := List (Fin (n - 1) × Bool)

/-- Evaluate a single generator crossing `(i, b)` into `BraidGroup n`. -/
def evalLetter (l : Fin (n - 1) × Bool) : BraidGroup n :=
  if l.2 then sigma l.1 else (sigma l.1)⁻¹

/-- A positive braid letter evaluates to the corresponding generator. -/
@[simp]
theorem evalLetter_true (i : Fin (n - 1)) : evalLetter (i, true) = sigma i := by
  simp [evalLetter]

/-- A negative braid letter evaluates to the inverse of the corresponding generator. -/
@[simp]
theorem evalLetter_false (i : Fin (n - 1)) : evalLetter (i, false) = (sigma i)⁻¹ := by
  simp [evalLetter]

/-- Evaluate a `BraidWord n` into `BraidGroup n` as the product of its letters. -/
def evalWord (w : BraidWord n) : BraidGroup n :=
  (w.map evalLetter).prod

@[simp]
theorem evalWord_nil : evalWord (n := n) [] = 1 := by
  dsimp [evalWord]
  rfl

@[simp]
theorem evalWord_cons (l : Fin (n - 1) × Bool) (w : BraidWord n) :
    evalWord (l :: w) = evalLetter l * evalWord w := by
  dsimp [evalWord]
  rw [List.map_cons, List.prod_cons]

@[simp]
theorem evalWord_append (w1 w2 : BraidWord n) :
    evalWord (w1 ++ w2) = evalWord w1 * evalWord w2 := by
  dsimp [evalWord]
  rw [List.map_append, List.prod_append]

/-- Reversing a braid word and flipping its signs evaluates to the inverse braid. -/
@[simp]
theorem evalWord_invRev (w : BraidWord n) :
    evalWord (FreeGroup.invRev w) = (evalWord w)⁻¹ := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [FreeGroup.invRev_cons, evalWord_append, evalWord_cons, ih]
    rcases l with ⟨i, b⟩
    cases b <;> simp [FreeGroup.invRev, evalLetter]

/-- The map from generators to `Multiplicative ℤ` sending each $\sigma_i$ to `1`. -/
private def exponentSumGen (n : ℕ) : Fin (n - 1) → Multiplicative ℤ :=
  fun _ ↦ Multiplicative.ofAdd 1

private theorem exponentSum_rel (r : FreeGroup (Fin (n - 1))) (hr : r ∈ artinRelations n) :
    FreeGroup.lift (exponentSumGen n) r = 1 := by
  rcases hr with ⟨i, j, h⟩ | ⟨i, j, h⟩
  · simp [exponentSumGen, FreeGroup.lift_apply_of]
  · simp [exponentSumGen, FreeGroup.lift_apply_of]

/-- The total writhe / exponent sum homomorphism `BraidGroup n →* Multiplicative ℤ`, sending
each generator $\sigma_i$ to $1$. -/
def exponentSum (n : ℕ) : BraidGroup n →* Multiplicative ℤ :=
  PresentedGroup.toGroup (exponentSum_rel (n := n))

/-- Evaluating `exponentSum` on a generator $\sigma_i$ gives $1$. -/
@[simp]
theorem exponentSum_sigma (i : Fin (n - 1)) :
    exponentSum n (sigma i) = Multiplicative.ofAdd 1 := by
  exact PresentedGroup.toGroup.of _

/-- Helper permutation sending generator `i : Fin (n - 1)` to the transposition $(i, i+1)$ in
`Equiv.Perm (Fin n)`. -/
private def permGen (n : ℕ) (i : Fin (n - 1)) : Equiv.Perm (Fin n) :=
  have hi : i.1 < n := by have hlt := i.is_lt; omega
  have hi_succ : i.1 + 1 < n := by have hlt := i.is_lt; omega
  Equiv.swap ⟨i.1, hi⟩ ⟨i.1 + 1, hi_succ⟩

private theorem permHom_rel (n : ℕ) (r : FreeGroup (Fin (n - 1)))
    (hr : r ∈ artinRelations n) :
    FreeGroup.lift (permGen n) r = 1 := by
  rcases hr with ⟨i, j, h⟩ | ⟨i, j, h⟩
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, permGen]
    rw [mul_inv_mul_inv_eq_one_iff]
    have hi : i.1 < n := by have hlt := i.is_lt; omega
    have hi_succ : i.1 + 1 < n := by have hlt := i.is_lt; omega
    have hj : j.1 < n := by have hlt := j.is_lt; omega
    have hj_succ : j.1 + 1 < n := by have hlt := j.is_lt; omega
    have hac : (⟨i.1, hi⟩ : Fin n) ≠ ⟨j.1, hj⟩ := by
      intro h_eq; injection h_eq with hv; omega
    have had : (⟨i.1, hi⟩ : Fin n) ≠ ⟨j.1 + 1, hj_succ⟩ := by
      intro h_eq; injection h_eq with hv; omega
    have hbc : (⟨i.1 + 1, hi_succ⟩ : Fin n) ≠ ⟨j.1, hj⟩ := by
      intro h_eq; injection h_eq with hv; omega
    have hbd : (⟨i.1 + 1, hi_succ⟩ : Fin n) ≠ ⟨j.1 + 1, hj_succ⟩ := by
      intro h_eq; injection h_eq with hv; omega
    exact swap_comm_of_disjoint hac had hbc hbd
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, permGen]
    rw [mul_inv_eq_one]
    have hi : i.1 < n := by have hlt := i.is_lt; omega
    have hi_succ : i.1 + 1 < n := by have hlt := i.is_lt; omega
    have hj_succ : j.1 + 1 < n := by have hlt := j.is_lt; omega
    have hab : (⟨i.1, hi⟩ : Fin n) ≠ ⟨i.1 + 1, hi_succ⟩ := by
      intro h_eq; injection h_eq with hv; omega
    have hbc : (⟨i.1 + 1, hi_succ⟩ : Fin n) ≠ ⟨j.1 + 1, hj_succ⟩ := by
      intro h_eq; injection h_eq with hv; omega
    have hac : (⟨i.1, hi⟩ : Fin n) ≠ ⟨j.1 + 1, hj_succ⟩ := by
      intro h_eq; injection h_eq with hv; omega
    have hj_eq : ⟨j.1, by have hlt := j.is_lt; omega⟩ = (⟨i.1 + 1, hi_succ⟩ : Fin n) := by
      ext; exact h.symm
    rw [hj_eq]
    exact swap_braid_rel hab hbc hac

/-- The canonical permutation homomorphism `BraidGroup n →* Equiv.Perm (Fin n)`, sending generator
$\sigma_i$ to the transposition swapping strand $i$ and strand $i+1$. -/
def permHom (n : ℕ) : BraidGroup n →* Equiv.Perm (Fin n) :=
  PresentedGroup.toGroup (permHom_rel n)

/-- Evaluating `permHom` on a generator $\sigma_i$ yields the transposition $(i, i+1)$. -/
@[simp]
theorem permHom_sigma (i : Fin (n - 1)) :
    permHom n (sigma i) =
      Equiv.swap ⟨i.1, by have hlt := i.is_lt; omega⟩
        ⟨i.1 + 1, by have hlt := i.is_lt; omega⟩ := by
  exact PresentedGroup.toGroup.of _

/-- The **pure braid group** $P_n \le B_n$, defined as the kernel of the permutation
homomorphism `permHom n`. -/
def PureBraidGroup (n : ℕ) : Subgroup (BraidGroup n) :=
  (permHom n).ker

/-- A braid is pure if and only if its permutation is the identity. -/
@[simp]
theorem mem_pureBraidGroup_iff (b : BraidGroup n) :
    b ∈ PureBraidGroup n ↔ permHom n b = 1 :=
  Iff.rfl

/-- The natural generator-embedding from $B_n$ to $B_{n+1}$ sending $\sigma_i$ to $\sigma_i$. -/
private def castSuccGen (n : ℕ) : Fin (n - 1) → BraidGroup (n + 1) :=
  fun i ↦ sigma ⟨i.1, by have hlt := i.is_lt; omega⟩

private theorem castSucc_rel (n : ℕ) (r : FreeGroup (Fin (n - 1)))
    (hr : r ∈ artinRelations n) :
    FreeGroup.lift (castSuccGen n) r = 1 := by
  rcases hr with ⟨i, j, h⟩ | ⟨i, j, h⟩
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, castSuccGen]
    rw [mul_inv_mul_inv_eq_one_iff]
    have hi : i.1 < n := by have hlt := i.is_lt; omega
    have hj : j.1 < n := by have hlt := j.is_lt; omega
    exact comm ⟨i.1, hi⟩ ⟨j.1, hj⟩ h
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, castSuccGen]
    rw [mul_inv_eq_one]
    have hi : i.1 < n := by have hlt := i.is_lt; omega
    have hj : j.1 < n := by have hlt := j.is_lt; omega
    exact braid_rel ⟨i.1, hi⟩ ⟨j.1, hj⟩ h

/-- The natural strand-inclusion group homomorphism $B_n \to* B_{n+1}$. -/
def castSuccHom (n : ℕ) : BraidGroup n →* BraidGroup (n + 1) :=
  PresentedGroup.toGroup (castSucc_rel n)

@[simp]
theorem castSuccHom_sigma (i : Fin (n - 1)) :
    castSuccHom n (sigma i) = sigma ⟨i.1, by have hlt := i.is_lt; omega⟩ := by
  exact PresentedGroup.toGroup.of _

end BraidGroup

end TauCeti.KnotTheory
