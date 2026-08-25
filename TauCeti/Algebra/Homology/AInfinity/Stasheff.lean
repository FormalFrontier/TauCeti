/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Reflection
public import TauCeti.LinearAlgebra.Graded.Insertion
public import TauCeti.LinearAlgebra.Graded.Shift

/-!
# The Stasheff identities and the suspension sign

An `A∞` algebra has operations `mₙ : A^{⊗ n} ⟶ A` of degree `2 - n` subject to the Stasheff
identities: for every `n`,

```text
∑_{n = r + s + t, s ≥ 1} (-1) ^ (r + s * t) m_{r + 1 + t} (1^{⊗ r} ⊗ m_s ⊗ 1^{⊗ t}) = 0.  (SIₙ)
```

The primary encoding of these identities is the suspended one: writing `sA` for the shift of `A`
and `bₙ` for the operations associated to `mₙ`, every `bₙ` has degree one and the identities lose
their structural coefficient,

```text
∑_{n = r + s + t, s ≥ 1} b_{r + 1 + t} (1^{⊗ r} ⊗ b_s ⊗ 1^{⊗ t}) = 0.
```

This file constructs both sums and proves that they agree up to one global sign, so that either
vanishes exactly when the other does.  Following the cited Getzler--Jones/Keller convention, the
definition adopts the sign prescribed by the Koszul rule for the suspension square: because `s`
has degree `-1`, its tensor power contributes
`(-1) ^ (∑ i, (n - 1 - i) * d i)`.  The tensor power itself is not formalized here.  Its exponent
is `MultilinearMap.suspExp`, and `TauCeti.AInfinity.barTerm_eq_smul` proves that the two
corresponding Stasheff terms differ by this same sign for every decomposition `n = p + s + t`.

Both sides also carry the Koszul coefficient of the inserted operation crossing the prefix
inputs, `(-1) ^ ((2 - s) * (d 0 + ⋯ + d (r - 1)))` before suspension and
`(-1) ^ ((d 0 - 1) + ⋯ + (d (r - 1) - 1))` after; these are the coefficients of
`MultilinearMap.koszulSign`, as `TauCeti.AInfinity.negOnePow_sum_range_eq_koszulSign` records. As in
`TauCeti/LinearAlgebra/Graded/Insertion.lean`, the degrees of the inputs are supplied as an
explicit parameter rather than read off a direct-sum decomposition; on the intended component the
sign is a scalar, and `TauCeti.AInfinity.replaceBlock_mem_replaceDeg` proves that the supplied
degrees are the actual ones once every operation is homogeneous of degree `2 - k`.

The arities one to four are written out on the nose using the supplied degree family `d`; these
formulas themselves make no homogeneity assumption. Homogeneity enters only in
`evalNat_mem_blockDeg` and `replaceBlock_mem_replaceDeg`. The degeneration to a differential
graded algebra is also checked.

Inputs are indexed by `ℕ` rather than by `Fin n` throughout; only the first `n` entries of an input
family are read, and this keeps the reindexing of the Stasheff sums free of transports between
propositionally equal arities.

## Main definitions

* `TauCeti.negOnePow`: the scalar `(-1) ^ e` of the ground ring.
* `MultilinearMap.suspExp`: the exponent prescribed for suspending a tuple.
* `MultilinearMap.suspend`: the suspended operation `b_k` attached to `m_k`.
* `TauCeti.AInfinity.stasheffTerm` and `TauCeti.AInfinity.barTerm`: the `(p, s, t)` term of the
  unsuspended and of the suspended Stasheff identity.
* `TauCeti.AInfinity.stasheffSum` and `TauCeti.AInfinity.barSum`: the two sides of `(SIₙ)`.

## Main results

* `TauCeti.AInfinity.suspExp_replaceDeg`: the sign identity behind the whole comparison; the two
  exponents differ by the suspension sign of the whole arity, up to an even number.
* `TauCeti.AInfinity.barTerm_eq_smul` and `TauCeti.AInfinity.barSum_eq_smul`: a suspended term,
  and hence the suspended sum, is the unsuspended one scaled by that sign.
* `TauCeti.AInfinity.barSum_eq_zero_iff`: the sign-free suspended identity holds exactly when the
  unsuspended identity with the coefficient `(-1) ^ (r + s * t)` does.
* `TauCeti.AInfinity.stasheffSum_one`, `TauCeti.AInfinity.stasheffSum_two`,
  `TauCeti.AInfinity.stasheffSum_three` and `TauCeti.AInfinity.stasheffSum_four`: the four
  identities written out using the supplied degree family.
* `TauCeti.AInfinity.stasheffSum_two_eq_zero_iff`,
  `TauCeti.AInfinity.stasheffSum_three_eq_zero_iff_of_ternary_eq_zero` and
  `TauCeti.AInfinity.stasheffSum_four_eq_zero_of_ternary_quaternary_eq_zero`: the differential
  graded degeneration.

This advances `TauCetiRoadmap/DGAInfinity/README.md`, Layer 0, item "signed graded multilinear and
tensor-coalgebra infrastructure", specifically "Implement the suspension/unsuspension equivalence
fixed above.  Prove the general Stasheff component formula and the arity `1`--`4` equations
verbatim." The sign prescribed by the suspension square is adopted in
`TauCeti/LinearAlgebra/Graded/Shift.lean`; its tensor power is not yet formalized. This file proves
the resulting Stasheff comparison and identities. What the roadmap's acceptance test still owes
is the identification of `(SIₙ)` with
the arity-`n` component of `b ∘ b = 0` on the bar coalgebra of
`TauCeti/LinearAlgebra/TensorCoalgebra/`, which needs the graded, signed coderivations of that
coalgebra.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2,
  for the suspension and brace signs.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6, for the
  degree `2 - n`, the coefficient `(-1) ^ (r + s * t)` and the degree `-1` suspension.
-/

public section

open scoped BigOperators
open _root_.MultilinearMap
open TauCeti.MultilinearMap

universe uR uA

namespace TauCeti

namespace AInfinity

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-! ### Operations on inputs indexed by the naturals -/

section Inputs

/-- Evaluate an arity-`k` operation on the first `k` entries of a family of inputs indexed by the
naturals.  Indexing inputs by `ℕ` rather than by `Fin k` keeps the index arithmetic of the
Stasheff sums below free of transports between propositionally equal arities. -/
@[expose]
def evalNat {k : ℕ} (f : MultilinearMap R (fun _ : Fin k ↦ A) A) (x : ℕ → A) : A :=
  f fun i ↦ x i.1

theorem evalNat_apply {k : ℕ} (f : MultilinearMap R (fun _ : Fin k ↦ A) A) (x : ℕ → A) :
    evalNat f x = f (fun i ↦ x i.1) := rfl

@[simp]
theorem evalNat_smul {k : ℕ} (c : R) (f : MultilinearMap R (fun _ : Fin k ↦ A) A) (x : ℕ → A) :
    evalNat (c • f) x = c • evalNat f x := by
  simp [evalNat]

@[simp]
theorem evalNat_one (f : MultilinearMap R (fun _ : Fin 1 ↦ A) A) (x : ℕ → A) :
    evalNat f x = f ![x 0] := by
  exact congrArg f (FinVec.etaExpand_eq _).symm

@[simp]
theorem evalNat_two (f : MultilinearMap R (fun _ : Fin 2 ↦ A) A) (x : ℕ → A) :
    evalNat f x = f ![x 0, x 1] := by
  exact congrArg f (FinVec.etaExpand_eq _).symm

@[simp]
theorem evalNat_three (f : MultilinearMap R (fun _ : Fin 3 ↦ A) A) (x : ℕ → A) :
    evalNat f x = f ![x 0, x 1, x 2] := by
  exact congrArg f (FinVec.etaExpand_eq _).symm

@[simp]
theorem evalNat_four (f : MultilinearMap R (fun _ : Fin 4 ↦ A) A) (x : ℕ → A) :
    evalNat f x = f ![x 0, x 1, x 2, x 3] := by
  exact congrArg f (FinVec.etaExpand_eq _).symm

/-- Replace the block of `s` entries at position `p` of a family indexed by the naturals by the
single entry `v`.  This is the input tuple of the outer operation of a Stasheff term. -/
@[expose]
def replaceBlock {α : Type*} (x : ℕ → α) (p s : ℕ) (v : α) : ℕ → α := fun i ↦
  if i < p then x i else if i = p then v else x (i + s - 1)

@[simp]
theorem replaceBlock_of_lt {α : Type*} (x : ℕ → α) (p s : ℕ) (v : α) {i : ℕ} (h : i < p) :
    replaceBlock x p s v i = x i := by simp [replaceBlock, h]

@[simp]
theorem replaceBlock_self {α : Type*} (x : ℕ → α) (p s : ℕ) (v : α) :
    replaceBlock x p s v p = v := by simp [replaceBlock]

@[simp]
theorem replaceBlock_of_gt {α : Type*} (x : ℕ → α) (p s : ℕ) (v : α) {i : ℕ} (h : p < i) :
    replaceBlock x p s v i = x (i + s - 1) := by
  simp only [replaceBlock]
  split_ifs with h₁ h₂
  · exact absurd h₁ (by omega)
  · exact absurd h₂ (by omega)
  · rfl

/-- Evaluating an operation on a tuple whose replaced entry is scaled scales the value: the
replaced entry sits in a single slot, in which the operation is linear. -/
theorem evalNat_replaceBlock_smul {u : ℕ} (f : MultilinearMap R (fun _ : Fin u ↦ A) A)
    (x : ℕ → A) {p : ℕ} (s : ℕ) (hp : p < u) (c : R) (v : A) :
    evalNat f (replaceBlock x p s (c • v)) = c • evalNat f (replaceBlock x p s v) := by
  have hupd : ∀ w : A, (fun i : Fin u ↦ replaceBlock x p s w i.1) =
      Function.update (fun i : Fin u ↦ replaceBlock x p s v i.1) ⟨p, hp⟩ w := by
    intro w
    funext i
    rcases eq_or_ne (i : ℕ) p with h | h
    · have hi : i = (⟨p, hp⟩ : Fin u) := Fin.ext h
      subst hi
      simp
    · rw [Function.update_of_ne (by simpa [Fin.ext_iff] using h)]
      rcases lt_or_gt_of_ne h with h' | h'
      · rw [replaceBlock_of_lt _ _ _ _ h', replaceBlock_of_lt _ _ _ _ h']
      · rw [replaceBlock_of_gt _ _ _ _ h', replaceBlock_of_gt _ _ _ _ h']
  rw [evalNat, evalNat, hupd (c • v), MultilinearMap.map_update_smul, ← hupd v]

end Inputs

/-! ### Evaluation of suspended operations -/

@[simp]
theorem evalNat_suspend {k : ℕ} (d : ℕ → ℤ) (f : MultilinearMap R (fun _ : Fin k ↦ A) A)
    (x : ℕ → A) :
    evalNat (suspend d f) x = negOnePow R (suspExp k d) • evalNat f x := by
  rw [suspend, evalNat_smul]

/-! ### The degrees of a substituted tuple -/

section Degrees

/-- The degree of the value of an arity-`s` operation of degree `2 - s` on the block of inputs of
degrees `d` at position `p`. -/
@[expose]
def blockDeg (d : ℕ → ℤ) (p s : ℕ) : ℤ := (∑ j ∈ Finset.range s, d (p + j)) + 2 - s

/-- The defining expression for the degree of a collapsed block. -/
theorem blockDeg_def (d : ℕ → ℤ) (p s : ℕ) :
    blockDeg d p s = (∑ j ∈ Finset.range s, d (p + j)) + 2 - s := rfl

/-- The degrees of the inputs of the outer operation of a Stasheff term: the block of `s` degrees
at position `p` is replaced by the degree of the value of the inner operation on it. -/
@[expose]
def replaceDeg (d : ℕ → ℤ) (p s : ℕ) : ℕ → ℤ := replaceBlock d p s (blockDeg d p s)

theorem replaceDeg_of_lt (d : ℕ → ℤ) (p s : ℕ) {i : ℕ} (h : i < p) :
    replaceDeg d p s i = d i := by rw [replaceDeg, replaceBlock_of_lt _ _ _ _ h]

@[simp]
theorem replaceDeg_self (d : ℕ → ℤ) (p s : ℕ) :
    replaceDeg d p s p = blockDeg d p s := by rw [replaceDeg, replaceBlock_self]

theorem replaceDeg_of_gt (d : ℕ → ℤ) (p s : ℕ) {i : ℕ} (h : p < i) :
    replaceDeg d p s i = d (i + s - 1) := by rw [replaceDeg, replaceBlock_of_gt _ _ _ _ h]

/-- **The suspension sign identity.**  Writing an arity of `p + s + t` as a prefix of length `p`,
an inner block of length `s` and a suffix of length `t`, the exponent collected on the suspended
side of a Stasheff term -- the Koszul sign of the degree-one operation `b_s` crossing the
suspended prefix, plus the two suspension signs of `b_s` and of the outer `b_{p+1+t}` -- differs
from the exponent collected on the unsuspended side -- the structural coefficient `(-1) ^ (p + st)`
and the Koszul sign of `m_s` crossing the prefix -- by the suspension sign of the whole arity,
up to an even number.

This is the computation which turns the sign-free suspended Stasheff identity into the identity
with the coefficient `(-1) ^ (r + s * t)`. -/
theorem suspExp_replaceDeg (d : ℕ → ℤ) (p s t : ℕ) :
    suspExp (p + 1 + t) (replaceDeg d p s) =
      ((p : ℤ) + s * t + (2 - s) * ∑ i ∈ Finset.range p, d i)
        + suspExp (p + s + t) d + 2 * ((t : ℤ) - p - s * t)
        - (∑ i ∈ Finset.range p, (d i - 1)) - suspExp s (fun j ↦ d (p + j)) := by
  have hA : suspExp (p + 1 + t) (replaceDeg d p s)
      = ((∑ i ∈ Finset.range p, ((p : ℤ) + t - i) * d i) + (t : ℤ) * blockDeg d p s)
        + ∑ j ∈ Finset.range t, ((t : ℤ) - 1 - j) * d (p + s + j) := by
    rw [suspExp_add (p + 1) t, Finset.sum_range_succ]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [replaceDeg_of_lt _ _ _ (Finset.mem_range.1 hi)]
      push_cast
      ring
    · rw [replaceDeg_self]
      push_cast
      ring
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [replaceDeg_of_gt _ _ _ (by omega),
        show p + 1 + j + s - 1 = p + s + j by omega]
  have hB : suspExp (p + s + t) d
      = ((∑ i ∈ Finset.range p, ((p : ℤ) + s + t - 1 - i) * d i)
          + ∑ j ∈ Finset.range s, ((t : ℤ) + s - 1 - j) * d (p + j))
        + ∑ j ∈ Finset.range t, ((t : ℤ) - 1 - j) * d (p + s + j) := by
    rw [show p + s + t = p + (s + t) by omega, suspExp_add, Finset.sum_range_add, ← add_assoc]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      push_cast
      ring
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      push_cast
      ring
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [show p + (s + j) = p + s + j by omega]
      push_cast
      ring
  have hI : (∑ i ∈ Finset.range p, (d i - 1)) + ∑ i ∈ Finset.range p, ((p : ℤ) + t - i) * d i
      = ((2 - (s : ℤ)) * ∑ i ∈ Finset.range p, d i
          + ∑ i ∈ Finset.range p, ((p : ℤ) + s + t - 1 - i) * d i) - p := by
    rw [eq_sub_iff_add_eq, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      show ((p : ℤ)) = ∑ _i ∈ Finset.range p, (1 : ℤ) by simp, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hII : suspExp s (fun j ↦ d (p + j)) + (t : ℤ) * blockDeg d p s
      = (∑ j ∈ Finset.range s, ((t : ℤ) + s - 1 - j) * d (p + j)) + (t : ℤ) * (2 - s) := by
    have hsum : (∑ j ∈ Finset.range s, ((t : ℤ) + s - 1 - j) * d (p + j))
        = (∑ j ∈ Finset.range s, ((s : ℤ) - 1 - j) * d (p + j))
          + (t : ℤ) * ∑ j ∈ Finset.range s, d (p + j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hsum, suspExp, blockDeg]
    ring
  rw [hA, hB]
  linear_combination hI + hII

end Degrees

/-! ### The Stasheff identities -/

section Stasheff

variable (m : ∀ k : ℕ, MultilinearMap R (fun _ : Fin k ↦ A) A) (d : ℕ → ℤ) (x : ℕ → A)

/-- The `(p, s, t)` term of the unsuspended Stasheff identity in arity `p + s + t`: the arity-`s`
operation is substituted into the `p`-th slot of the arity-`p + 1 + t` operation.  Its sign is the
structural Stasheff coefficient `(-1) ^ (p + s * t)` together with the Koszul coefficient
`(-1) ^ ((2 - s) * (d 0 + ⋯ + d (p - 1)))` of the degree-`2 - s` operation `m_s` crossing the `p`
prefix inputs. -/
@[expose]
def stasheffTerm (p s t : ℕ) : A :=
  negOnePow R ((p : ℤ) + s * t + (2 - s) * ∑ i ∈ Finset.range p, d i) •
    evalNat (m (p + 1 + t)) (replaceBlock x p s (evalNat (m s) fun j ↦ x (p + j)))

/-- The defining expression for an unsuspended Stasheff term. -/
theorem stasheffTerm_def (p s t : ℕ) : stasheffTerm m d x p s t =
    negOnePow R ((p : ℤ) + s * t + (2 - s) * ∑ i ∈ Finset.range p, d i) •
      evalNat (m (p + 1 + t))
        (replaceBlock x p s (evalNat (m s) fun j ↦ x (p + j))) := rfl

/-- The `(p, s, t)` term of the suspended Stasheff identity: the same substitution performed with
the suspended operations, with no structural coefficient and with the Koszul coefficient of the
degree-one operation `b_s` crossing the `p` suspended prefix inputs, whose degrees are `d i - 1`.
-/
@[expose]
def barTerm (p s t : ℕ) : A :=
  negOnePow R (∑ i ∈ Finset.range p, (d i - 1)) •
    evalNat (suspend (replaceDeg d p s) (m (p + 1 + t)))
      (replaceBlock x p s (evalNat (suspend (fun j ↦ d (p + j)) (m s)) fun j ↦ x (p + j)))

/-- The defining expression for a suspended Stasheff term. -/
theorem barTerm_def (p s t : ℕ) : barTerm m d x p s t =
    negOnePow R (∑ i ∈ Finset.range p, (d i - 1)) •
      evalNat (suspend (replaceDeg d p s) (m (p + 1 + t)))
        (replaceBlock x p s
          (evalNat (suspend (fun j ↦ d (p + j)) (m s)) fun j ↦ x (p + j))) := rfl

/-- The left-hand side `(SI_n)` of the arity-`n` Stasheff identity: the sum of
`TauCeti.AInfinity.stasheffTerm` over the decompositions `n = p + s + t` with `1 ≤ s`. -/
@[expose]
def stasheffSum (n : ℕ) : A :=
  ∑ p ∈ Finset.range (n + 1), ∑ s ∈ Finset.Icc 1 (n - p), stasheffTerm m d x p s (n - p - s)

/-- The defining double sum for the unsuspended Stasheff identity. -/
theorem stasheffSum_def (n : ℕ) : stasheffSum m d x n =
    ∑ p ∈ Finset.range (n + 1),
      ∑ s ∈ Finset.Icc 1 (n - p), stasheffTerm m d x p s (n - p - s) := rfl

/-- The left-hand side of the arity-`n` Stasheff identity in the suspended encoding: the sum of
`TauCeti.AInfinity.barTerm` over the same decompositions `n = p + s + t`, with no structural
coefficient.  Its identification with the arity-`n` component of `b ∘ b` on the bar coalgebra
belongs to the tensor-coalgebra layer and is not proved here. -/
@[expose]
def barSum (n : ℕ) : A :=
  ∑ p ∈ Finset.range (n + 1), ∑ s ∈ Finset.Icc 1 (n - p), barTerm m d x p s (n - p - s)

/-- The defining double sum for the suspended Stasheff identity. -/
theorem barSum_def (n : ℕ) : barSum m d x n =
    ∑ p ∈ Finset.range (n + 1),
      ∑ s ∈ Finset.Icc 1 (n - p), barTerm m d x p s (n - p - s) := rfl

/-- **The suspended and unsuspended Stasheff terms agree up to the suspension sign of the whole
arity.**  The sign does not depend on the decomposition, which is why the two identities are
equivalent. -/
theorem barTerm_eq_smul (p s t : ℕ) :
    barTerm m d x p s t =
      negOnePow R (suspExp (p + s + t) d) • stasheffTerm m d x p s t := by
  have hexp : (∑ i ∈ Finset.range p, (d i - 1)) + suspExp (p + 1 + t) (replaceDeg d p s)
        + suspExp s (fun j ↦ d (p + j))
      = suspExp (p + s + t) d +
          ((p : ℤ) + s * t + (2 - s) * ∑ i ∈ Finset.range p, d i)
        + 2 * ((t : ℤ) - p - s * t) := by
    rw [suspExp_replaceDeg]
    ring
  rw [barTerm, stasheffTerm, evalNat_suspend, evalNat_suspend,
    evalNat_replaceBlock_smul _ _ _ (by omega), smul_smul, smul_smul, smul_smul]
  congr 1
  rw [← negOnePow_add, ← negOnePow_add, hexp, negOnePow_add, negOnePow_two_mul, mul_one,
    negOnePow_add]

/-- **The suspended and unsuspended Stasheff identities agree up to a global sign.** -/
theorem barSum_eq_smul (n : ℕ) :
    barSum m d x n = negOnePow R (suspExp n d) • stasheffSum m d x n := by
  rw [barSum, stasheffSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.mem_range] at hp
  rw [Finset.mem_Icc] at hs
  rw [barTerm_eq_smul, show p + s + (n - p - s) = n by omega]

/-- **The sign-free suspended Stasheff identity holds exactly when the unsuspended one does.** -/
theorem barSum_eq_zero_iff (n : ℕ) :
    barSum m d x n = 0 ↔ stasheffSum m d x n = 0 := by
  rw [barSum_eq_smul, negOnePow_smul_eq_zero_iff]

end Stasheff

/-! ### The identities in arities one to four -/

section LowArity

variable (m : ∀ k : ℕ, MultilinearMap R (fun _ : Fin k ↦ A) A) (d : ℕ → ℤ) (x : ℕ → A)

/-- The arity-one identity is `m₁ m₁ = 0`. -/
theorem stasheffSum_one : stasheffSum m d x 1 = m 1 ![m 1 ![x 0]] := by
  simp only [stasheffSum_def, Nat.reduceAdd, stasheffTerm_def, Finset.sum_range_succ,
    Finset.range_one, Finset.sum_singleton, tsub_zero, Finset.Icc_self, CharP.cast_eq_zero,
    zero_add, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero, Nat.sub_zero, Nat.cast_one,
    tsub_self, negOnePow_zero, Nat.add_one_sub_one, Nat.add_zero, evalNat_one, replaceBlock_self,
    one_smul, Order.lt_one_iff, Finset.Icc_eq_empty_of_lt, zero_tsub]

/-- The arity-two identity, evaluated: `m₁ m₂ - m₂ (m₁ ⊗ 1) - m₂ (1 ⊗ m₁)`, where the Koszul rule
turns the last term into `(-1) ^ (d 0)` times `m₂ (a, m₁ b)`. -/
theorem stasheffSum_two : stasheffSum m d x 2
    = m 1 ![m 2 ![x 0, x 1]] - m 2 ![m 1 ![x 0], x 1]
      - negOnePow R (d 0) • m 2 ![x 0, m 1 ![x 1]] := by
  have h2 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  simp only [stasheffSum_def, Nat.reduceAdd, stasheffTerm_def, negOnePow_add,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, tsub_zero, h2,
    CharP.cast_eq_zero, negOnePow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero,
    mul_one, Nat.sub_zero, zero_add, Finset.mem_singleton, OfNat.one_ne_ofNat, not_false_eq_true,
    Finset.sum_insert, Nat.cast_one, Nat.add_one_sub_one, negOnePow_one, evalNat_one, evalNat_two,
    replaceBlock_self, Order.lt_one_iff, replaceBlock_of_gt, neg_smul, one_smul, Nat.cast_ofNat,
    tsub_self, Nat.reduceSub, Nat.add_zero, Finset.Icc_self, neg_mul, Finset.sum_neg_distrib,
    Int.reduceSub, add_zero, replaceBlock_of_lt, Finset.Icc_eq_empty_of_lt, zero_tsub]
  abel

/-- The arity-three identity, evaluated using the supplied degrees `d 0, d 1, d 2` (without a
homogeneity hypothesis):
`m₁ m₃ + m₂ (m₂ ⊗ 1) - m₂ (1 ⊗ m₂) + m₃ (m₁ ⊗ 1 ⊗ 1 + 1 ⊗ m₁ ⊗ 1 + 1 ⊗ 1 ⊗ m₁)`. -/
theorem stasheffSum_three : stasheffSum m d x 3
    = m 1 ![m 3 ![x 0, x 1, x 2]]
      + m 2 ![m 2 ![x 0, x 1], x 2] - m 2 ![x 0, m 2 ![x 1, x 2]]
      + m 3 ![m 1 ![x 0], x 1, x 2]
      + negOnePow R (d 0) • m 3 ![x 0, m 1 ![x 1], x 2]
      + negOnePow R (d 0 + d 1) • m 3 ![x 0, x 1, m 1 ![x 2]] := by
  have h3 : (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} := by decide
  have h2 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  have e2 : negOnePow R 2 = 1 := negOnePow_even ⟨1, by norm_num⟩
  simp only [stasheffSum_def, Nat.reduceAdd, stasheffTerm_def, negOnePow_add,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, tsub_zero, h3,
    CharP.cast_eq_zero, negOnePow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero,
    mul_one, Nat.sub_zero, zero_add, Finset.mem_insert, OfNat.one_ne_ofNat,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
    Nat.add_one_sub_one, Nat.cast_ofNat, e2, evalNat_one, evalNat_three, replaceBlock_self,
    Order.lt_one_iff, replaceBlock_of_gt, Order.lt_two_iff, zero_le, one_smul, Nat.reduceEqDiff,
    Nat.reduceSub, evalNat_two, tsub_self, Nat.add_zero, h2, negOnePow_one, neg_mul, neg_smul,
    Finset.sum_neg_distrib, Int.reduceSub, add_zero, replaceBlock_of_lt, Std.le_refl, sub_self,
    zero_mul, neg_add_rev, neg_neg, Finset.Icc_self, Finset.Icc_eq_empty_of_lt, zero_tsub,
    add_left_inj]
  abel

/-- The arity-four identity, evaluated using the supplied degrees `d 0, d 1, d 2, d 3` (without a
homogeneity hypothesis):
`m₁ m₄ - m₂ (m₃ ⊗ 1) - m₂ (1 ⊗ m₃) + m₃ (m₂ ⊗ 1 ⊗ 1) - m₃ (1 ⊗ m₂ ⊗ 1) + m₃ (1 ⊗ 1 ⊗ m₂)
- m₄ (m₁ ⊗ 1 ⊗ 1 ⊗ 1 + 1 ⊗ m₁ ⊗ 1 ⊗ 1 + 1 ⊗ 1 ⊗ m₁ ⊗ 1 + 1 ⊗ 1 ⊗ 1 ⊗ m₁)`. -/
theorem stasheffSum_four : stasheffSum m d x 4
    = m 1 ![m 4 ![x 0, x 1, x 2, x 3]]
      - m 2 ![m 3 ![x 0, x 1, x 2], x 3]
      - negOnePow R (d 0) • m 2 ![x 0, m 3 ![x 1, x 2, x 3]]
      + m 3 ![m 2 ![x 0, x 1], x 2, x 3] - m 3 ![x 0, m 2 ![x 1, x 2], x 3]
        + m 3 ![x 0, x 1, m 2 ![x 2, x 3]]
      - m 4 ![m 1 ![x 0], x 1, x 2, x 3]
      - negOnePow R (d 0) • m 4 ![x 0, m 1 ![x 1], x 2, x 3]
      - negOnePow R (d 0 + d 1) • m 4 ![x 0, x 1, m 1 ![x 2], x 3]
      - negOnePow R (d 0 + d 1 + d 2) • m 4 ![x 0, x 1, x 2, m 1 ![x 3]] := by
  have h4 : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  have h3 : (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} := by decide
  have h2 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  have e2 : negOnePow R 2 = 1 := negOnePow_even ⟨1, by norm_num⟩
  have e3 : negOnePow R 3 = -1 := negOnePow_odd ⟨1, by norm_num⟩
  have e4 : negOnePow R 4 = 1 := negOnePow_even ⟨2, by norm_num⟩
  simp only [stasheffSum_def, Nat.reduceAdd, stasheffTerm_def, negOnePow_add,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, tsub_zero, h4,
    CharP.cast_eq_zero, negOnePow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero,
    mul_one, Nat.sub_zero, zero_add, Finset.mem_insert, OfNat.one_ne_ofNat,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert, Nat.cast_one,
    Nat.add_one_sub_one, Nat.cast_ofNat, e3, evalNat_one, evalNat_four, replaceBlock_self,
    Order.lt_one_iff, replaceBlock_of_gt, Order.lt_two_iff, zero_le, Nat.ofNat_pos, neg_smul,
    one_smul, Nat.reduceEqDiff, Nat.reduceSub, Int.reduceMul, e4, evalNat_two, evalNat_three,
    tsub_self, Nat.add_zero, h3, negOnePow_one, neg_mul, Finset.sum_neg_distrib, e2,
    Int.reduceSub, add_zero, replaceBlock_of_lt, Std.le_refl, Nat.one_lt_ofNat, sub_self,
    zero_mul, negOnePow_neg, neg_add_rev, h2, Nat.lt_add_one, Finset.Icc_self,
    Finset.Icc_eq_empty_of_lt, zero_tsub]
  abel

/-- The arity-two identity is the Leibniz rule for `m₁` and `m₂`, with the Koszul sign
`(-1) ^ (d 0)` on the second term. -/
theorem stasheffSum_two_eq_zero_iff : stasheffSum m d x 2 = 0 ↔
    m 1 ![m 2 ![x 0, x 1]]
      = m 2 ![m 1 ![x 0], x 1] + negOnePow R (d 0) • m 2 ![x 0, m 1 ![x 1]] := by
  rw [stasheffSum_two, sub_sub, sub_eq_zero]

/-- When the ternary operation vanishes, the arity-three identity is associativity of `m₂`. -/
theorem stasheffSum_three_eq_zero_iff_of_ternary_eq_zero (h₃ : m 3 = 0) :
    stasheffSum m d x 3 = 0 ↔ m 2 ![m 2 ![x 0, x 1], x 2] = m 2 ![x 0, m 2 ![x 1, x 2]] := by
  have hz1 : m 1 ![(0 : A)] = 0 := (m 1).map_coord_zero 0 rfl
  rw [stasheffSum_three, h₃]
  simp only [_root_.zero_apply, hz1, smul_zero, add_zero, zero_add]
  rw [sub_eq_zero]

/-- When the ternary and quaternary operations vanish, the arity-four identity is vacuous. -/
theorem stasheffSum_four_eq_zero_of_ternary_quaternary_eq_zero (h₃ : m 3 = 0) (h₄ : m 4 = 0) :
    stasheffSum m d x 4 = 0 := by
  have hz1 : m 1 ![(0 : A)] = 0 := (m 1).map_coord_zero 0 rfl
  have hz2 : ∀ y : A, m 2 ![0, y] = 0 := fun y ↦ (m 2).map_coord_zero 0 rfl
  have hz2' : ∀ y : A, m 2 ![y, 0] = 0 := fun y ↦ (m 2).map_coord_zero 1 rfl
  rw [stasheffSum_four, h₃, h₄]
  simp only [_root_.zero_apply, hz1, hz2, sub_self, hz2', smul_zero, add_zero]

end LowArity

/-! ### Comparison with the Koszul coefficient and with homogeneous inputs -/

section Comparison

/-- A power of negative one whose exponent uses a prefix sum is the corresponding Koszul
coefficient. This specializes to both the unsuspended degree `2 - s` and suspended degree `1`. -/
theorem negOnePow_sum_range_eq_koszulSign (q : ℤ) (d : ℕ → ℤ) (p : ℕ) :
    negOnePow R (q * ∑ i ∈ Finset.range p, d i) =
      _root_.MultilinearMap.koszulSign (R := R) q (fun i : Fin p ↦ d i) := by
  rw [_root_.MultilinearMap.koszulSign_eq_negOnePow, Fin.sum_univ_eq_sum_range]
  rfl

variable {σ : Type*} [SetLike σ A] (𝒜 : ℤ → σ)

/-- `TauCeti.AInfinity.blockDeg` is the degree of the value of an operation of degree `2 - s` on a
block of homogeneous inputs. -/
theorem evalNat_mem_blockDeg {s : ℕ} (f : MultilinearMap R (fun _ : Fin s ↦ A) A)
    {d : ℕ → ℤ} {x : ℕ → A}
    (hf : MultilinearMap.IsHomogeneous f (fun _ ↦ 𝒜) 𝒜 (2 - s))
    (hx : ∀ i, x i ∈ 𝒜 (d i)) (p : ℕ) :
    evalNat f (fun j ↦ x (p + j)) ∈ 𝒜 (blockDeg d p s) := by
  rw [blockDeg, ← Fin.sum_univ_eq_sum_range (fun j ↦ d (p + j)) s,
    show ∀ a : ℤ, a + 2 - s = a + (2 - s) from fun a ↦ by ring]
  exact hf.map_mem _ _ fun j ↦ hx _

/-- **The supplied degrees of a Stasheff term are the actual ones.** If an arity-`s` operation is
homogeneous of degree `2 - s` and the inputs are homogeneous of degrees `d`, then `replaceDeg`
records the degrees of the inputs of the outer operation after inserting its value. -/
theorem replaceBlock_mem_replaceDeg {s : ℕ}
    (f : MultilinearMap R (fun _ : Fin s ↦ A) A) {d : ℕ → ℤ} {x : ℕ → A}
    (hf : MultilinearMap.IsHomogeneous f (fun _ ↦ 𝒜) 𝒜 (2 - s))
    (hx : ∀ i, x i ∈ 𝒜 (d i)) (p i : ℕ) :
    replaceBlock x p s (evalNat f fun j ↦ x (p + j)) i ∈ 𝒜 (replaceDeg d p s i) := by
  rw [replaceDeg, replaceBlock, replaceBlock]
  split_ifs with h₁ h₂
  · exact hx i
  · exact evalNat_mem_blockDeg 𝒜 f hf hx p
  · exact hx _

end Comparison

end AInfinity

end TauCeti
