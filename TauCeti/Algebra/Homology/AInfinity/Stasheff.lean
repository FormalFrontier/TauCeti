/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
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
is `MultilinearMap.suspExp`, and `TauCeti.AInfinity.suspendedStasheffTerm_eq_smul` proves that the
two corresponding Stasheff terms differ by this same sign for every decomposition `n = p + s + t`.

Both sides also carry the Koszul coefficient of the inserted operation crossing the prefix
inputs, `(-1) ^ ((2 - s) * (d 0 + ⋯ + d (r - 1)))` before suspension and
`(-1) ^ ((d 0 - 1) + ⋯ + (d (r - 1) - 1))` after; these are the coefficients of
`MultilinearMap.koszulSign`. As in
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

* `TauCeti.AInfinity.blockDeg` and `TauCeti.AInfinity.replaceDeg`: record the degree resulting from
  collapsing an input block.
* `TauCeti.AInfinity.stasheffTerm` and `TauCeti.AInfinity.suspendedStasheffTerm`: the `(p, s, t)`
  term of the unsuspended and suspended Stasheff identities.
* `TauCeti.AInfinity.stasheffSum` and `TauCeti.AInfinity.suspendedStasheffSum`: the two sides of
  `(SIₙ)`.

## Main results

* `TauCeti.AInfinity.suspExp_replaceDeg`: the sign identity behind the whole comparison; the two
  exponents differ by the suspension sign of the whole arity, up to an even number.
* `TauCeti.AInfinity.suspendedStasheffTerm_eq_smul` and
  `TauCeti.AInfinity.suspendedStasheffSum_eq_smul`: a suspended term, and hence the suspended sum,
  is the unsuspended one scaled by that sign.
* `TauCeti.AInfinity.suspendedStasheffSum_eq_zero_iff`: the suspended identity free of the
  structural coefficient `(-1) ^ (r + s * t)` holds exactly when the unsuspended identity does.
* `TauCeti.AInfinity.stasheffSum_one`, `TauCeti.AInfinity.stasheffSum_two`,
  `TauCeti.AInfinity.stasheffSum_three` and `TauCeti.AInfinity.stasheffSum_four`: the four
  identities written out using the supplied degree family.
* `TauCeti.AInfinity.stasheffSum_two_eq_zero_iff`,
  `TauCeti.AInfinity.stasheffSum_three_eq_zero_iff_of_m_three_eq_zero` and
  `TauCeti.AInfinity.stasheffSum_four_eq_zero_of_m_three_eq_zero_of_m_four_eq_zero`: the
  differential graded degeneration.

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

universe uR uA uN

namespace TauCeti

/-- Evaluating an operation on a tuple whose replaced entry is scaled scales the value: the
replaced entry sits in a single slot, in which the operation is linear. -/
private theorem evalNat_replaceBlock_smul {u : ℕ} {N : Type uN}
    {R : Type uR} {A : Type uA} [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R (fun _ : Fin u ↦ A) N)
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
  rw [evalNat_def, evalNat_def, hupd (c • v), MultilinearMap.map_update_smul, ← hupd v]

end TauCeti

namespace Finset

private theorem Icc_one_two : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide

private theorem Icc_one_three : (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} := by decide

private theorem Icc_one_four : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide

private theorem sum_Icc_one_two {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ Finset.Icc 1 2, f i = f 1 + f 2 := by
  simp [Icc_one_two]

private theorem sum_Icc_one_three {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ Finset.Icc 1 3, f i = f 1 + f 2 + f 3 := by
  simp [Icc_one_three, add_assoc]

private theorem sum_Icc_one_four {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ Finset.Icc 1 4, f i = f 1 + f 2 + f 3 + f 4 := by
  simp [Icc_one_four, add_assoc]

end Finset

namespace TauCeti

namespace AInfinity

open TauCeti
open _root_.MultilinearMap

variable {R : Type uR} {A : Type uA}

/-! ### Evaluation of suspended operations -/

section Evaluation

variable [CommRing R] [AddCommMonoid A] [Module R A]

@[simp]
theorem evalNat_suspend {k : ℕ} {N : Type uN} [AddCommMonoid N] [Module R N]
    (d : ℕ → ℤ) (f : MultilinearMap R (fun _ : Fin k ↦ A) N)
    (x : ℕ → A) :
    evalNat (suspend d f) x = negOnePowCast R (suspExp k d) • evalNat f x := by
  rw [suspend_eq_smul, evalNat_smul]

end Evaluation

/-! ### The degrees of a substituted tuple -/

section Degrees

/-- The degree of the value of an arity-`s` operation of degree `2 - s` on the block of inputs of
degrees `d` at position `p`. -/
def blockDeg (d : ℕ → ℤ) (p s : ℕ) : ℤ := (∑ j ∈ Finset.range s, d (p + j)) + 2 - s

/-- The defining expression for the degree of a collapsed block. -/
theorem blockDeg_def (d : ℕ → ℤ) (p s : ℕ) :
    blockDeg d p s = (∑ j ∈ Finset.range s, d (p + j)) + 2 - s := (rfl)

/-- The degrees of the inputs of the outer operation of a Stasheff term: the block of `s` degrees
at position `p` is replaced by the degree of the value of the inner operation on it. -/
def replaceDeg (d : ℕ → ℤ) (p s : ℕ) : ℕ → ℤ := replaceBlock d p s (blockDeg d p s)

@[simp]
theorem replaceDeg_of_lt (d : ℕ → ℤ) (p s : ℕ) {i : ℕ} (h : i < p) :
    replaceDeg d p s i = d i := by rw [replaceDeg, replaceBlock_of_lt _ _ _ _ h]

@[simp]
theorem replaceDeg_self (d : ℕ → ℤ) (p s : ℕ) :
    replaceDeg d p s p = blockDeg d p s := by rw [replaceDeg, replaceBlock_self]

@[simp]
theorem replaceDeg_of_gt (d : ℕ → ℤ) (p s : ℕ) {i : ℕ} (h : p < i) :
    replaceDeg d p s i = d (i + s - 1) := by rw [replaceDeg, replaceBlock_of_gt _ _ _ _ h]

/-- **The suspension sign identity.**  Writing an arity of `p + s + t` as a prefix of length `p`,
an inner block of length `s` and a suffix of length `t`, the exponent collected on the suspended
side of a Stasheff term -- the Koszul sign of the degree-one operation `b_s` crossing the
suspended prefix, plus the two suspension signs of `b_s` and of the outer `b_{p+1+t}` -- differs
from the exponent collected on the unsuspended side -- the structural coefficient `(-1) ^ (p + st)`
and the Koszul sign of `m_s` crossing the prefix -- by the suspension sign of the whole arity,
up to an even number.

This is the computation which turns the suspended identity without the structural coefficient
into the identity with the coefficient `(-1) ^ (r + s * t)`. -/
theorem suspExp_replaceDeg (d : ℕ → ℤ) (p s t : ℕ) :
    suspExp (p + 1 + t) (replaceDeg d p s) =
      ((p : ℤ) + s * t + (2 - s) * ∑ i ∈ Finset.range p, d i)
        + suspExp (p + s + t) d + 2 * ((t : ℤ) - p - s * t)
        - (∑ i ∈ Finset.range p, (d i - 1)) - suspExp s (fun j ↦ d (p + j)) := by
  -- Expand the suspension exponent after the inner block has been collapsed.
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
      have hindex : p + 1 + j + s - 1 = p + s + j := by omega
      rw [replaceDeg_of_gt _ _ _ (by omega), hindex]
  -- Split the exponent of the original tuple into prefix, inner block, and suffix.
  have hB := suspExp_add3 p s t d
  -- Compare the prefix contribution on the two sides of the sign identity.
  have hI : (∑ i ∈ Finset.range p, (d i - 1)) + ∑ i ∈ Finset.range p, ((p : ℤ) + t - i) * d i
      = ((2 - (s : ℤ)) * ∑ i ∈ Finset.range p, d i
          + ∑ i ∈ Finset.range p, ((p : ℤ) + s + t - 1 - i) * d i) - p := by
    have hcard : ((p : ℤ)) = ∑ _i ∈ Finset.range p, (1 : ℤ) := by simp
    rw [eq_sub_iff_add_eq, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      hcard, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  -- Compare the collapsed inner-block contribution on the two sides.
  have hII : suspExp s (fun j ↦ d (p + j)) + (t : ℤ) * blockDeg d p s
      = (∑ j ∈ Finset.range s, ((t : ℤ) + s - 1 - j) * d (p + j)) + (t : ℤ) * (2 - s) := by
    have hsum : (∑ j ∈ Finset.range s, ((t : ℤ) + s - 1 - j) * d (p + j))
        = (∑ j ∈ Finset.range s, ((s : ℤ) - 1 - j) * d (p + j))
          + (t : ℤ) * ∑ j ∈ Finset.range s, d (p + j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hsum, suspExp_def, blockDeg_def]
    ring
  rw [hA, hB]
  linear_combination hI + hII

end Degrees

/-! ### The Stasheff identities -/

section Stasheff

variable [CommRing R] [AddCommMonoid A] [Module R A]
variable (m : ∀ k : ℕ, MultilinearMap R (fun _ : Fin k ↦ A) A) (d : ℕ → ℤ) (x : ℕ → A)

/-- The `(p, s, t)` term of the unsuspended Stasheff identity in arity `p + s + t`: the arity-`s`
operation is substituted into the `p`-th slot of the arity-`p + 1 + t` operation.  Its sign is the
structural Stasheff coefficient `(-1) ^ (p + s * t)` together with the Koszul coefficient
`(-1) ^ ((2 - s) * (d 0 + ⋯ + d (p - 1)))` of the degree-`2 - s` operation `m_s` crossing the `p`
prefix inputs. -/
def stasheffTerm (p s t : ℕ) : A :=
  negOnePowCast R ((p : ℤ) + s * t + (2 - s) * ∑ i ∈ Finset.range p, d i) •
    evalNat (m (p + 1 + t)) (replaceBlock x p s (evalNat (m s) fun j ↦ x (p + j)))

/-- The defining expression for an unsuspended Stasheff term. -/
theorem stasheffTerm_def (p s t : ℕ) : stasheffTerm m d x p s t =
    negOnePowCast R ((p : ℤ) + s * t + (2 - s) * ∑ i ∈ Finset.range p, d i) •
      evalNat (m (p + 1 + t))
        (replaceBlock x p s (evalNat (m s) fun j ↦ x (p + j))) := (rfl)

/-- Up to the structural coefficient `(-1) ^ (p + s * t)`, a Stasheff term is the existing signed
one-slot substitution evaluated after the canonical reindexing of its three input blocks. -/
theorem stasheffTerm_eq_smul_signedOneSlot (p s t : ℕ) :
    stasheffTerm m d x p s t =
      negOnePowCast R ((p : ℤ) + s * t) •
        (((m (p + 1 + t)).domDomCongr (Fin.oneSlotEquiv p t).symm).signedOneSlot
          (2 - (s : ℤ)) (fun i : Fin p ↦ d i) (m s))
            (fun i ↦ x (Fin.blockEquiv p s t i)) := by
  rw [stasheffTerm_def, MultilinearMap.signedOneSlot_apply,
    MultilinearMap.koszulSign_eq_negOnePowCast, Fin.sum_univ_eq_sum_range, smul_smul,
    ← negOnePowCast_add]
  congr 1
  rw [evalNat_def, MultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  obtain ⟨j, rfl⟩ := (Fin.oneSlotEquiv p t).surjective i
  rcases j with j | (j | j)
  · rw [Fin.oneSlotEquiv_inl_val, replaceBlock_of_lt _ _ _ _ j.isLt]
    simp only [Equiv.symm_apply_apply, Sum.elim_inl, Fin.blockEquiv_inl_val]
  · rcases j with ⟨⟩
    rw [Fin.oneSlotEquiv_middle_val, replaceBlock_self]
    simp only [Equiv.symm_apply_apply, Sum.elim_inr, Sum.elim_inl,
      Fin.blockEquiv_middle_val, evalNat_def]
  · have hsuffix : p < p + 1 + (j : ℕ) := by omega
    rw [Fin.oneSlotEquiv_suffix_val, replaceBlock_of_gt _ _ _ _ hsuffix]
    simp only [Equiv.symm_apply_apply, Sum.elim_inr, Fin.blockEquiv_suffix_val]
    congr 1
    omega

/-- A Stasheff term only reads the degrees and inputs below its total arity. -/
theorem stasheffTerm_congr {e : ℕ → ℤ} {y : ℕ → A} (p s t : ℕ)
    (hd : ∀ i < p + s + t, d i = e i) (hx : ∀ i < p + s + t, x i = y i) :
    stasheffTerm m d x p s t = stasheffTerm m e y p s t := by
  have hsum : ∑ i ∈ Finset.range p, d i = ∑ i ∈ Finset.range p, e i :=
    Finset.sum_congr rfl fun i hi ↦ hd i (by have := Finset.mem_range.1 hi; omega)
  have hinner : evalNat (m s) (fun j ↦ x (p + j)) =
      evalNat (m s) (fun j ↦ y (p + j)) := by
    apply evalNat_congr
    intro j hj
    exact hx (p + j) (by omega)
  rw [stasheffTerm_def, stasheffTerm_def, hsum, hinner]
  congr 1
  apply evalNat_congr
  intro i hi
  rcases lt_trichotomy i p with hip | rfl | hip
  · rw [replaceBlock_of_lt _ _ _ _ hip, replaceBlock_of_lt _ _ _ _ hip]
    exact hx i (by omega)
  · simp
  · rw [replaceBlock_of_gt _ _ _ _ hip, replaceBlock_of_gt _ _ _ _ hip]
    exact hx (i + s - 1) (by omega)

/-- The `(p, s, t)` term of the suspended Stasheff identity: the same substitution performed with
the suspended operations, with no structural coefficient and with the Koszul coefficient of the
degree-one operation `b_s` crossing the `p` suspended prefix inputs, whose degrees are `d i - 1`.
-/
def suspendedStasheffTerm (p s t : ℕ) : A :=
  negOnePowCast R (∑ i ∈ Finset.range p, (d i - 1)) •
    evalNat (suspend (replaceDeg d p s) (m (p + 1 + t)))
      (replaceBlock x p s (evalNat (suspend (fun j ↦ d (p + j)) (m s)) fun j ↦ x (p + j)))

/-- The defining expression for a suspended Stasheff term. -/
theorem suspendedStasheffTerm_def (p s t : ℕ) : suspendedStasheffTerm m d x p s t =
    negOnePowCast R (∑ i ∈ Finset.range p, (d i - 1)) •
      evalNat (suspend (replaceDeg d p s) (m (p + 1 + t)))
        (replaceBlock x p s
          (evalNat (suspend (fun j ↦ d (p + j)) (m s)) fun j ↦ x (p + j))) := (rfl)

/-- The left-hand side `(SI_n)` of the arity-`n` Stasheff identity: the sum of
`TauCeti.AInfinity.stasheffTerm` over the decompositions `n = p + s + t` with `1 ≤ s`. -/
def stasheffSum (n : ℕ) : A :=
  ∑ p ∈ Finset.range (n + 1), ∑ s ∈ Finset.Icc 1 (n - p), stasheffTerm m d x p s (n - p - s)

/-- The defining double sum for the unsuspended Stasheff identity. -/
theorem stasheffSum_def (n : ℕ) : stasheffSum m d x n =
    ∑ p ∈ Finset.range (n + 1),
      ∑ s ∈ Finset.Icc 1 (n - p), stasheffTerm m d x p s (n - p - s) := (rfl)

@[simp]
theorem stasheffSum_zero : stasheffSum m d x 0 = 0 := by
  simp [stasheffSum_def]

/-- The left-hand side of the arity-`n` Stasheff identity in the suspended encoding: the sum of
`TauCeti.AInfinity.suspendedStasheffTerm` over the same decompositions `n = p + s + t`, with no
structural coefficient. Its identification with the arity-`n` component of `b ∘ b` on the bar
coalgebra belongs to the tensor-coalgebra layer and is not proved here. -/
def suspendedStasheffSum (n : ℕ) : A :=
  ∑ p ∈ Finset.range (n + 1),
    ∑ s ∈ Finset.Icc 1 (n - p), suspendedStasheffTerm m d x p s (n - p - s)

/-- The defining double sum for the suspended Stasheff identity. -/
theorem suspendedStasheffSum_def (n : ℕ) : suspendedStasheffSum m d x n =
    ∑ p ∈ Finset.range (n + 1),
      ∑ s ∈ Finset.Icc 1 (n - p), suspendedStasheffTerm m d x p s (n - p - s) := (rfl)

theorem suspendedStasheffSum_zero : suspendedStasheffSum m d x 0 = 0 := by
  simp [suspendedStasheffSum_def]

/-- **The suspended and unsuspended Stasheff terms agree up to the suspension sign of the whole
arity.**  The sign does not depend on the decomposition, which is why the two identities are
equivalent. -/
@[simp]
theorem suspendedStasheffTerm_eq_smul (p s t : ℕ) :
    suspendedStasheffTerm m d x p s t =
      negOnePowCast R (suspExp (p + s + t) d) • stasheffTerm m d x p s t := by
  have hexp : (∑ i ∈ Finset.range p, (d i - 1)) + suspExp (p + 1 + t) (replaceDeg d p s)
        + suspExp s (fun j ↦ d (p + j))
      = suspExp (p + s + t) d +
          ((p : ℤ) + s * t + (2 - s) * ∑ i ∈ Finset.range p, d i)
        + 2 * ((t : ℤ) - p - s * t) := by
    rw [suspExp_replaceDeg]
    ring
  rw [suspendedStasheffTerm, stasheffTerm, evalNat_suspend, evalNat_suspend,
    evalNat_replaceBlock_smul _ _ _ (by omega), smul_smul, smul_smul, smul_smul]
  congr 1
  rw [← negOnePowCast_add, ← negOnePowCast_add, hexp, negOnePowCast_add,
    negOnePowCast_two_mul, mul_one, negOnePowCast_add]

/-- A suspended Stasheff term only reads the degrees and inputs below its total arity. -/
theorem suspendedStasheffTerm_congr {e : ℕ → ℤ} {y : ℕ → A} (p s t : ℕ)
    (hd : ∀ i < p + s + t, d i = e i) (hx : ∀ i < p + s + t, x i = y i) :
    suspendedStasheffTerm m d x p s t = suspendedStasheffTerm m e y p s t := by
  rw [suspendedStasheffTerm_eq_smul, suspendedStasheffTerm_eq_smul, suspExp_congr hd,
    stasheffTerm_congr m d x p s t hd hx]

/-- The arity-`n` Stasheff sum only reads the first `n` supplied degrees and inputs. -/
theorem stasheffSum_congr {e : ℕ → ℤ} {y : ℕ → A} (n : ℕ)
    (hd : ∀ i < n, d i = e i) (hx : ∀ i < n, x i = y i) :
    stasheffSum m d x n = stasheffSum m e y n := by
  rw [stasheffSum_def, stasheffSum_def]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.mem_range] at hp
  rw [Finset.mem_Icc] at hs
  apply stasheffTerm_congr m d x
  · intro i hi
    exact hd i (by omega)
  · intro i hi
    exact hx i (by omega)

/-- **The suspended and unsuspended Stasheff identities agree up to a global sign.** -/
@[simp]
theorem suspendedStasheffSum_eq_smul (n : ℕ) :
    suspendedStasheffSum m d x n = negOnePowCast R (suspExp n d) • stasheffSum m d x n := by
  rw [suspendedStasheffSum, stasheffSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.mem_range] at hp
  rw [Finset.mem_Icc] at hs
  have harity : p + s + (n - p - s) = n := by omega
  rw [suspendedStasheffTerm_eq_smul, harity]

/-- The arity-`n` suspended Stasheff sum only reads the first `n` supplied degrees and inputs. -/
theorem suspendedStasheffSum_congr {e : ℕ → ℤ} {y : ℕ → A} (n : ℕ)
    (hd : ∀ i < n, d i = e i) (hx : ∀ i < n, x i = y i) :
    suspendedStasheffSum m d x n = suspendedStasheffSum m e y n := by
  rw [suspendedStasheffSum_eq_smul, suspendedStasheffSum_eq_smul, suspExp_congr hd,
    stasheffSum_congr m d x n hd hx]

/-- **The suspended Stasheff identity free of the structural coefficient holds exactly when the
unsuspended one does.** -/
theorem suspendedStasheffSum_eq_zero_iff (n : ℕ) :
    suspendedStasheffSum m d x n = 0 ↔ stasheffSum m d x n = 0 := by
  rw [suspendedStasheffSum_eq_smul, negOnePowCast_smul_eq_zero_iff]

end Stasheff

/-! ### The identities in arities one to four -/

section LowArity

variable [CommRing R] [AddCommGroup A] [Module R A]
variable (m : ∀ k : ℕ, MultilinearMap R (fun _ : Fin k ↦ A) A) (d : ℕ → ℤ) (x : ℕ → A)

/- Keep the implementation-level sign and tuple normalization in this private layer.  The
displayed identities below then only choose the relevant terms and collect them additively. -/
private theorem stasheffTerm_normalize (p s t : ℕ) :
    stasheffTerm m d x p s t =
      negOnePowCast R ((p : ℤ) + s * t) •
        negOnePowCast R ((2 - s) * ∑ i ∈ Finset.range p, d i) •
          evalNat (m (p + 1 + t))
            (replaceBlock x p s (evalNat (m s) fun j ↦ x (p + j))) := by
  rw [stasheffTerm_def, negOnePowCast_add, mul_smul]

private theorem evalNat_replaceBlock_one (s : ℕ) (v : A) :
    evalNat (m 1) (replaceBlock x 0 s v) = m 1 ![v] := by
  simp only [evalNat_one, replaceBlock_self]

private theorem evalNat_replaceBlock_two_zero (s : ℕ) (v : A) :
    evalNat (m 2) (replaceBlock x 0 s v) = m 2 ![v, x s] := by
  simp [evalNat_two]

private theorem evalNat_replaceBlock_two_one (s : ℕ) (v : A) :
    evalNat (m 2) (replaceBlock x 1 s v) = m 2 ![x 0, v] := by
  simp [evalNat_two]

private theorem evalNat_replaceBlock_three_zero (s : ℕ) (v : A) :
    evalNat (m 3) (replaceBlock x 0 s v) = m 3 ![v, x s, x (s + 1)] := by
  simp [evalNat_three, Nat.add_comm]

private theorem evalNat_replaceBlock_three_one (s : ℕ) (v : A) :
    evalNat (m 3) (replaceBlock x 1 s v) = m 3 ![x 0, v, x (s + 1)] := by
  simp [evalNat_three, Nat.add_comm]

private theorem evalNat_replaceBlock_three_two (s : ℕ) (v : A) :
    evalNat (m 3) (replaceBlock x 2 s v) = m 3 ![x 0, x 1, v] := by
  simp [evalNat_three]

private theorem evalNat_replaceBlock_four_zero (s : ℕ) (v : A) :
    evalNat (m 4) (replaceBlock x 0 s v) = m 4 ![v, x s, x (s + 1), x (s + 2)] := by
  simp [evalNat_four, Nat.add_comm]

private theorem evalNat_replaceBlock_four_one (s : ℕ) (v : A) :
    evalNat (m 4) (replaceBlock x 1 s v) = m 4 ![x 0, v, x (s + 1), x (s + 2)] := by
  simp [evalNat_four, Nat.add_comm]

private theorem evalNat_replaceBlock_four_two (s : ℕ) (v : A) :
    evalNat (m 4) (replaceBlock x 2 s v) = m 4 ![x 0, x 1, v, x (s + 2)] := by
  simp [evalNat_four, Nat.add_comm]

private theorem evalNat_replaceBlock_four_three (s : ℕ) (v : A) :
    evalNat (m 4) (replaceBlock x 3 s v) = m 4 ![x 0, x 1, x 2, v] := by
  simp [evalNat_four]

/- These expansions isolate the finite indexing arithmetic from the element-level sign audit
below.  Keeping them private avoids adding arity-specific combinatorics to the public API. -/
private theorem stasheffSum_one_terms :
    stasheffSum m d x 1 = stasheffTerm m d x 0 1 0 := by
  simp only [stasheffSum_def, Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, tsub_zero, Finset.Icc_self, Nat.add_one_sub_one,
    Order.lt_one_iff, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, add_zero, zero_tsub]

private theorem stasheffSum_two_terms :
    stasheffSum m d x 2 = stasheffTerm m d x 0 1 1 + stasheffTerm m d x 0 2 0
      + stasheffTerm m d x 1 1 0 := by
  simp only [stasheffSum_def, Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, tsub_zero, Finset.sum_Icc_one_two, Nat.add_one_sub_one,
    Nat.reduceSub, Finset.Icc_self, Order.lt_one_iff,
    Finset.Icc_eq_empty_of_lt, Finset.sum_empty, add_zero, zero_tsub]

private theorem stasheffSum_three_terms :
    stasheffSum m d x 3 = stasheffTerm m d x 0 1 2 + stasheffTerm m d x 0 2 1
      + stasheffTerm m d x 0 3 0 + stasheffTerm m d x 1 1 1
      + stasheffTerm m d x 1 2 0 + stasheffTerm m d x 2 1 0 := by
  simp only [stasheffSum_def, Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, tsub_zero, Finset.sum_Icc_one_three, Nat.add_one_sub_one,
    Nat.reduceSub, Finset.sum_Icc_one_two, Finset.Icc_self,
    Order.lt_one_iff, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, add_zero, zero_tsub]
  ac_rfl

private theorem stasheffSum_four_terms :
    stasheffSum m d x 4 = stasheffTerm m d x 0 1 3 + stasheffTerm m d x 0 2 2
      + stasheffTerm m d x 0 3 1 + stasheffTerm m d x 0 4 0
      + stasheffTerm m d x 1 1 2 + stasheffTerm m d x 1 2 1
      + stasheffTerm m d x 1 3 0 + stasheffTerm m d x 2 1 1
      + stasheffTerm m d x 2 2 0 + stasheffTerm m d x 3 1 0 := by
  simp only [stasheffSum_def, Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, tsub_zero, Finset.sum_Icc_one_four, Nat.add_one_sub_one,
    Nat.reduceSub, Finset.sum_Icc_one_three, Finset.sum_Icc_one_two,
    Finset.Icc_self, Order.lt_one_iff, Finset.Icc_eq_empty_of_lt, Finset.sum_empty,
    add_zero, zero_tsub]
  ac_rfl

private theorem negOnePowCast_two_normalize : negOnePowCast R 2 = 1 :=
  negOnePowCast_even (by norm_num)

private theorem negOnePowCast_three_normalize : negOnePowCast R 3 = -1 :=
  negOnePowCast_odd (by use 1; norm_num)

private theorem negOnePowCast_four_normalize : negOnePowCast R 4 = 1 :=
  negOnePowCast_even (by use 2; norm_num)

/- Centralize the implementation-level reduction used after selecting the terms of a low-arity
Stasheff sum.  The public proofs below depend only on this local normalization interface. -/
local macro "normalize_stasheff" : tactic =>
  `(tactic|
    simp only [stasheffTerm_normalize, evalNat_replaceBlock_one,
      evalNat_replaceBlock_two_zero, evalNat_replaceBlock_two_one,
      evalNat_replaceBlock_three_zero, evalNat_replaceBlock_three_one,
      evalNat_replaceBlock_three_two, evalNat_replaceBlock_four_zero,
      evalNat_replaceBlock_four_one, evalNat_replaceBlock_four_two,
      evalNat_replaceBlock_four_three] <;>
    simp only [Nat.reduceAdd, CharP.cast_eq_zero,
      Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, Finset.range_zero,
      Finset.sum_empty, mul_zero, mul_one, one_mul, zero_add, add_zero, Nat.cast_one,
      Nat.cast_ofNat, Int.reduceAdd, Int.reduceMul, Int.reduceSub, neg_mul,
      evalNat_one, evalNat_two, evalNat_three, evalNat_four, sub_self, zero_mul] <;>
    simp only [negOnePowCast_zero, negOnePowCast_one, negOnePowCast_two_normalize,
      negOnePowCast_three_normalize, negOnePowCast_four_normalize, negOnePowCast_neg,
      one_smul, neg_smul])

/-- The arity-one identity is `m₁ m₁ = 0`. -/
theorem stasheffSum_one : stasheffSum m d x 1 = m 1 ![m 1 ![x 0]] := by
  rw [stasheffSum_one_terms]
  normalize_stasheff

/-- The arity-two identity, evaluated: `m₁ m₂ - m₂ (m₁ ⊗ 1) - m₂ (1 ⊗ m₁)`, where the Koszul rule
turns the last term into `(-1) ^ (d 0)` times `m₂ (a, m₁ b)`. -/
theorem stasheffSum_two : stasheffSum m d x 2
    = m 1 ![m 2 ![x 0, x 1]] - m 2 ![m 1 ![x 0], x 1]
      - negOnePowCast R (d 0) • m 2 ![x 0, m 1 ![x 1]] := by
  rw [stasheffSum_two_terms]
  normalize_stasheff
  abel

/-- The arity-three identity, evaluated using the supplied degrees `d 0, d 1, d 2` (without a
homogeneity hypothesis):
`m₁ m₃ + m₂ (m₂ ⊗ 1) - m₂ (1 ⊗ m₂) + m₃ (m₁ ⊗ 1 ⊗ 1 + 1 ⊗ m₁ ⊗ 1 + 1 ⊗ 1 ⊗ m₁)`.
This display suppresses the degree-dependent Koszul factors, which are explicit in the statement. -/
theorem stasheffSum_three : stasheffSum m d x 3
    = m 1 ![m 3 ![x 0, x 1, x 2]]
      + m 2 ![m 2 ![x 0, x 1], x 2] - m 2 ![x 0, m 2 ![x 1, x 2]]
      + m 3 ![m 1 ![x 0], x 1, x 2]
      + negOnePowCast R (d 0) • m 3 ![x 0, m 1 ![x 1], x 2]
      + negOnePowCast R (d 0 + d 1) • m 3 ![x 0, x 1, m 1 ![x 2]] := by
  rw [stasheffSum_three_terms]
  normalize_stasheff
  abel

/-- The arity-four identity, evaluated using the supplied degrees `d 0, d 1, d 2, d 3` (without a
homogeneity hypothesis):
`m₁ m₄ - m₂ (m₃ ⊗ 1) - m₂ (1 ⊗ m₃) + m₃ (m₂ ⊗ 1 ⊗ 1) - m₃ (1 ⊗ m₂ ⊗ 1) + m₃ (1 ⊗ 1 ⊗ m₂)
- m₄ (m₁ ⊗ 1 ⊗ 1 ⊗ 1 + 1 ⊗ m₁ ⊗ 1 ⊗ 1 + 1 ⊗ 1 ⊗ m₁ ⊗ 1 + 1 ⊗ 1 ⊗ 1 ⊗ m₁)`.
This display suppresses the degree-dependent Koszul factors, which are explicit in the statement. -/
theorem stasheffSum_four : stasheffSum m d x 4
    = m 1 ![m 4 ![x 0, x 1, x 2, x 3]]
      - m 2 ![m 3 ![x 0, x 1, x 2], x 3]
      - negOnePowCast R (d 0) • m 2 ![x 0, m 3 ![x 1, x 2, x 3]]
      + m 3 ![m 2 ![x 0, x 1], x 2, x 3] - m 3 ![x 0, m 2 ![x 1, x 2], x 3]
        + m 3 ![x 0, x 1, m 2 ![x 2, x 3]]
      - m 4 ![m 1 ![x 0], x 1, x 2, x 3]
      - negOnePowCast R (d 0) • m 4 ![x 0, m 1 ![x 1], x 2, x 3]
      - negOnePowCast R (d 0 + d 1) • m 4 ![x 0, x 1, m 1 ![x 2], x 3]
      - negOnePowCast R (d 0 + d 1 + d 2) • m 4 ![x 0, x 1, x 2, m 1 ![x 3]] := by
  rw [stasheffSum_four_terms]
  normalize_stasheff
  abel

/-- The arity-two identity is the Leibniz rule for `m₁` and `m₂`, with the Koszul sign
`(-1) ^ (d 0)` on the second term. -/
theorem stasheffSum_two_eq_zero_iff : stasheffSum m d x 2 = 0 ↔
    m 1 ![m 2 ![x 0, x 1]]
      = m 2 ![m 1 ![x 0], x 1] + negOnePowCast R (d 0) • m 2 ![x 0, m 1 ![x 1]] := by
  rw [stasheffSum_two, sub_sub, sub_eq_zero]

/-- When `m 3` vanishes, the arity-three identity is associativity of `m₂`. -/
theorem stasheffSum_three_eq_zero_iff_of_m_three_eq_zero (h₃ : m 3 = 0) :
    stasheffSum m d x 3 = 0 ↔ m 2 ![m 2 ![x 0, x 1], x 2] = m 2 ![x 0, m 2 ![x 1, x 2]] := by
  have hz1 : m 1 ![(0 : A)] = 0 := (m 1).map_coord_zero 0 rfl
  rw [stasheffSum_three, h₃]
  simp only [_root_.zero_apply, hz1, smul_zero, add_zero, zero_add]
  rw [sub_eq_zero]

/-- When `m 3` and `m 4` vanish, the arity-four identity is vacuous. -/
theorem stasheffSum_four_eq_zero_of_m_three_eq_zero_of_m_four_eq_zero
    (h₃ : m 3 = 0) (h₄ : m 4 = 0) :
    stasheffSum m d x 4 = 0 := by
  have hz1 : m 1 ![(0 : A)] = 0 := (m 1).map_coord_zero 0 rfl
  have hz2 : ∀ y : A, m 2 ![0, y] = 0 := fun y ↦ (m 2).map_coord_zero 0 rfl
  have hz2' : ∀ y : A, m 2 ![y, 0] = 0 := fun y ↦ (m 2).map_coord_zero 1 rfl
  rw [stasheffSum_four, h₃, h₄]
  simp only [_root_.zero_apply, hz1, hz2, sub_self, hz2', smul_zero, add_zero]

end LowArity

/-! ### Comparison with homogeneous inputs -/

section Comparison

variable [Semiring R] [AddCommMonoid A] [Module R A]
variable {σ : Type*} [SetLike σ A] (𝒜 : ℤ → σ)

/-- `TauCeti.AInfinity.blockDeg` is the degree of the value of an operation of degree `2 - s` on a
block of homogeneous inputs. -/
theorem evalNat_mem_blockDeg {s : ℕ} (f : MultilinearMap R (fun _ : Fin s ↦ A) A)
    {d : ℕ → ℤ} {x : ℕ → A}
    (hf : MultilinearMap.IsHomogeneous f (fun _ ↦ 𝒜) 𝒜 (2 - s))
    (p : ℕ) (hx : ∀ j < s, x (p + j) ∈ 𝒜 (d (p + j))) :
    evalNat f (fun j ↦ x (p + j)) ∈ 𝒜 (blockDeg d p s) := by
  rw [blockDeg_def, ← Fin.sum_univ_eq_sum_range (fun j ↦ d (p + j)) s, add_sub_assoc,
    evalNat_def]
  exact hf.map_mem _ _ fun j ↦ hx j j.isLt

/-- **The supplied degrees of a Stasheff term are the actual ones.** If an arity-`s` operation is
homogeneous of degree `2 - s` and the inputs are homogeneous of degrees `d`, then `replaceDeg`
records the degrees of the inputs of the outer operation after inserting its value. -/
theorem replaceBlock_mem_replaceDeg {s : ℕ}
    (f : MultilinearMap R (fun _ : Fin s ↦ A) A) {d : ℕ → ℤ} {x : ℕ → A}
    (hf : MultilinearMap.IsHomogeneous f (fun _ ↦ 𝒜) 𝒜 (2 - s))
    (hx : ∀ i, x i ∈ 𝒜 (d i)) (p i : ℕ) :
    replaceBlock x p s (evalNat f fun j ↦ x (p + j)) i ∈ 𝒜 (replaceDeg d p s i) := by
  rcases lt_trichotomy i p with h | rfl | h
  · rw [replaceBlock_of_lt _ _ _ _ h, replaceDeg_of_lt _ _ _ h]
    exact hx i
  · rw [replaceBlock_self, replaceDeg_self]
    exact evalNat_mem_blockDeg 𝒜 f hf i (fun j _ ↦ hx (i + j))
  · rw [replaceBlock_of_gt _ _ _ _ h, replaceDeg_of_gt _ _ _ h]
    exact hx _

end Comparison

end AInfinity

end TauCeti
