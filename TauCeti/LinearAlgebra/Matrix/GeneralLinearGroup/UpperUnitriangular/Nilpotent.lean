/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Nilpotent
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Nilpotence of upper-unitriangular matrix groups

For a ring `R`, filter `U_n(R)` by requiring the entries on the first `r - 1`
superdiagonals to vanish. Multiplication of matrices supported at least `r` and `s`
superdiagonals above the diagonal is supported at least `r + s` superdiagonals above it. This
gives the central-series estimate

```text
[U^r, U^s] ⊆ U^(r+s).
```

The first term is all of `U_n(R)`, while the `n`-th term is trivial. Hence `U_n(R)` is
nilpotent, and therefore solvable, over every ring.

## Main declarations

* `TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup`: the subgroup `U^r` whose first
  `r - 1` superdiagonals vanish.
* `TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup_antitone`: the filtration is
  decreasing.
* `TauCeti.UpperUnitriangularGroup.commutator_superdiagonalSubgroup_le`: the central-series
  estimate `[U^r, U^s] ≤ U^(r+s)`.
* `TauCeti.UpperUnitriangularGroup.instIsNilpotent`: upper-unitriangular matrix groups are
  nilpotent.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

This is the nilpotence input for Layer 5, "Lie--Kolchin; solvable groups", of the
ReductiveGroups roadmap. Combined with the upper-unitriangular embedding characterization, it
gives the implication from unipotence to solvability.
-/

public section

open Matrix
open scoped commutatorElement

namespace TauCeti.UpperUnitriangularGroup

universe u

variable {R : Type u} [Ring R] {n : ℕ}

/-- A matrix vanishes strictly below its `r`-th superdiagonal. This private predicate is the
calculation behind `superdiagonalSubgroup`; the public membership theorem is its stable API. -/
private def VanishesBelow (r : ℕ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, j.val < i.val + r → M i j = 0

private theorem VanishesBelow.zero (r : ℕ) :
    VanishesBelow (R := R) r (0 : Matrix (Fin n) (Fin n) R) := by
  intro i j hij
  rfl

private theorem VanishesBelow.add {r : ℕ} {M N : Matrix (Fin n) (Fin n) R}
    (hM : VanishesBelow r M) (hN : VanishesBelow r N) :
    VanishesBelow r (M + N) := by
  intro i j hij
  simp [hM i j hij, hN i j hij]

private theorem VanishesBelow.neg {r : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hM : VanishesBelow r M) : VanishesBelow r (-M) := by
  intro i j hij
  simp [hM i j hij]

private theorem VanishesBelow.sub {r : ℕ} {M N : Matrix (Fin n) (Fin n) R}
    (hM : VanishesBelow r M) (hN : VanishesBelow r N) :
    VanishesBelow r (M - N) := by
  simpa only [sub_eq_add_neg] using hM.add hN.neg

private theorem VanishesBelow.mono {r s : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hM : VanishesBelow s M) (hrs : r ≤ s) : VanishesBelow r M := by
  intro i j hij
  exact hM i j (by omega)

/-- Products add the number of forced zero superdiagonals. -/
private theorem VanishesBelow.mul {r s : ℕ} {M N : Matrix (Fin n) (Fin n) R}
    (hM : VanishesBelow r M) (hN : VanishesBelow s N) :
    VanishesBelow (r + s) (M * N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : k.val < i.val + r
  · rw [hM i k hik, zero_mul]
  · rw [hN k j (by omega), mul_zero]

/-- Right multiplication by an upper-triangular matrix preserves the number of forced zero
superdiagonals. -/
private theorem VanishesBelow.mul_isUpperTriangular {r : ℕ}
    {M N : Matrix (Fin n) (Fin n) R} (hM : VanishesBelow r M)
    (hN : N.IsUpperTriangular) : VanishesBelow r (M * N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : k.val < i.val + r
  · rw [hM i k hik, zero_mul]
  · have hjk : j < k := by omega
    rw [hN hjk, mul_zero]

private theorem sub_one_vanishesBelow_one
    (g : upperUnitriangularGroup (Fin n) R) :
    VanishesBelow 1
      (((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1) := by
  intro i j hij
  by_cases hji : j < i
  · simp [Matrix.sub_apply, isUpperTriangular g hji, ne_of_gt hji]
  · have hji' : j = i := by
      apply Fin.ext
      omega
    subst j
    simp [Matrix.sub_apply, apply_diag]

private theorem sub_one_isUpperTriangular
    (g : upperUnitriangularGroup (Fin n) R) :
    Matrix.IsUpperTriangular
      (((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1) :=
  (isUpperTriangular g).sub Matrix.blockTriangular_one

/-- The subgroup `U^r` of upper-unitriangular matrices whose entries below the `r`-th
superdiagonal vanish. Thus `U^1 = U_n`, and `U^n = 1` for `n × n` matrices. -/
def superdiagonalSubgroup (r : ℕ) : Subgroup (upperUnitriangularGroup (Fin n) R) where
  carrier := {g | VanishesBelow r
    (((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1)}
  one_mem' := by
    simpa using VanishesBelow.zero (R := R) (n := n) r
  mul_mem' := by
    intro g h hg hh
    let G := ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
    let H := ((h : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
    have hprod : VanishesBelow r ((G - 1) * (H - 1)) :=
      hg.mul_isUpperTriangular (sub_one_isUpperTriangular h)
    have hsum : VanishesBelow r ((G - 1) + (H - 1) + (G - 1) * (H - 1)) :=
      (hg.add hh).add hprod
    have heq : G * H - 1 = (G - 1) + (H - 1) + (G - 1) * (H - 1) := by
      noncomm_ring
    -- Reduce subgroup membership to the matrix filtration used to define it.
    change VanishesBelow r (G * H - 1)
    rw [heq]
    exact hsum
  inv_mem' := by
    intro g hg
    let G := ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
    let Ginv := (((g⁻¹ : upperUnitriangularGroup (Fin n) R) :
      Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
    have hprod : VanishesBelow r ((G - 1) * Ginv) :=
      hg.mul_isUpperTriangular (isUpperTriangular (g⁻¹))
    have heq : Ginv - 1 = -((G - 1) * Ginv) := by
      have hmul : G * Ginv = 1 := by
        -- The two matrices are the values of a unit and its inverse.
        change (g.1 : Matrix (Fin n) (Fin n) R) *
          (g.1⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) = 1
        exact Units.mul_inv g.1
      calc
        Ginv - 1 = -(1 - Ginv) := by abel
        _ = -(G * Ginv - 1 * Ginv) := by rw [hmul, one_mul]
        _ = -((G - 1) * Ginv) := by rw [sub_mul]
    -- Reduce subgroup membership to the matrix filtration used to define it.
    change VanishesBelow r (Ginv - 1)
    rw [heq]
    exact hprod.neg

/-- Membership in `U^r` means that the matrix differs from the identity only on the `r`-th and
higher superdiagonals. -/
@[simp]
theorem mem_superdiagonalSubgroup_iff (r : ℕ)
    (g : upperUnitriangularGroup (Fin n) R) :
    g ∈ superdiagonalSubgroup (R := R) r ↔
      ∀ i j, j.val < i.val + r →
        ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
          (1 : Matrix (Fin n) (Fin n) R) i j := by
  constructor
  · intro hg i j hij
    have h := hg i j hij
    simpa only [Matrix.sub_apply, sub_eq_zero] using h
  · intro hg i j hij
    simpa only [Matrix.sub_apply, sub_eq_zero] using hg i j hij

/-- The superdiagonal filtration is decreasing: requiring more initial superdiagonals to vanish
gives a smaller subgroup. -/
theorem superdiagonalSubgroup_antitone :
    Antitone (superdiagonalSubgroup (R := R) (n := n)) := by
  intro r s hrs g hg
  exact hg.mono hrs

/-- The first superdiagonal subgroup is the whole upper-unitriangular group. -/
@[simp]
theorem superdiagonalSubgroup_one :
    superdiagonalSubgroup (R := R) (n := n) 1 = ⊤ := by
  rw [eq_top_iff]
  intro g _
  exact sub_one_vanishesBelow_one g

/-- Once the filtration index reaches the matrix size, the superdiagonal subgroup is trivial. -/
theorem superdiagonalSubgroup_eq_bot_of_le {r : ℕ} (hnr : n ≤ r) :
    superdiagonalSubgroup (R := R) (n := n) r = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  apply UpperUnitriangularGroup.ext
  intro i j hij
  have h := (mem_superdiagonalSubgroup_iff r g).mp hg i j (by omega)
  simpa [Matrix.one_apply, hij.ne] using h

/-- Commutators add filtration degrees: `[U^r, U^s] ≤ U^(r+s)`. -/
theorem commutator_superdiagonalSubgroup_le (r s : ℕ) :
    ⁅superdiagonalSubgroup (R := R) (n := n) r,
        superdiagonalSubgroup (R := R) (n := n) s⁆ ≤
      superdiagonalSubgroup (R := R) (n := n) (r + s) := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  let G := ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
  let H := ((h : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
  have hGH : VanishesBelow (r + s) ((G - 1) * (H - 1)) := hg.mul hh
  have hHG : VanishesBelow (r + s) ((H - 1) * (G - 1)) := by
    simpa only [Nat.add_comm] using hh.mul hg
  have hdiff : VanishesBelow (r + s) (G * H - H * G) := by
    have heq : G * H - H * G = (G - 1) * (H - 1) - (H - 1) * (G - 1) := by
      noncomm_ring
    exact heq.symm ▸ hGH.sub hHG
  let Ginv := (((g⁻¹ : upperUnitriangularGroup (Fin n) R) :
    Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
  let Hinv := (((h⁻¹ : upperUnitriangularGroup (Fin n) R) :
    Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
  let K := (((h * g)⁻¹ : upperUnitriangularGroup (Fin n) R) :
    Matrix.GeneralLinearGroup (Fin n) R)
  have hright : VanishesBelow (r + s) ((G * H - H * G) * (K : Matrix (Fin n) (Fin n) R)) :=
    hdiff.mul_isUpperTriangular (isUpperTriangular ((h * g)⁻¹))
  have heq :
      (((⁅g, h⁆ : upperUnitriangularGroup (Fin n) R) :
          Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1 =
        (G * H - H * G) * (K : Matrix (Fin n) (Fin n) R) := by
    have hmul : H * G * (K : Matrix (Fin n) (Fin n) R) = 1 := by
      -- The product and `K` are the values of a unit and its inverse.
      change ((h * g).1 : Matrix (Fin n) (Fin n) R) *
        ((h * g).1⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) = 1
      exact Units.mul_inv (h * g).1
    have hK :
        Ginv * Hinv = (K : Matrix (Fin n) (Fin n) R) := by
      simp [Ginv, Hinv, K]
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Units.val_mul]
    -- The group wrappers have reduced; name their four underlying matrices explicitly.
    change G * H * Ginv * Hinv - 1 = (G * H - H * G) * (K : Matrix (Fin n) (Fin n) R)
    rw [mul_assoc (G * H), hK]
    calc
      G * H * (K : Matrix (Fin n) (Fin n) R) - 1 =
          G * H * (K : Matrix (Fin n) (Fin n) R) -
            H * G * (K : Matrix (Fin n) (Fin n) R) := by rw [hmul]
      _ = (G * H - H * G) * (K : Matrix (Fin n) (Fin n) R) := by rw [sub_mul]
  -- Reduce subgroup membership to the matrix filtration used to define it.
  change VanishesBelow (r + s)
    (((((⁅g, h⁆ : upperUnitriangularGroup (Fin n) R) :
      Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)) - 1)
  exact heq.symm ▸ hright

private theorem lowerCentralSeries_le_superdiagonalSubgroup (r : ℕ) :
    (⊤ : Subgroup (upperUnitriangularGroup (Fin n) R)).lowerCentralSeries r ≤
      superdiagonalSubgroup (R := R) (n := n) (r + 1) := by
  induction r with
  | zero =>
      simpa only [Subgroup.lowerCentralSeries_zero, zero_add, superdiagonalSubgroup_one] using
        (le_refl (⊤ : Subgroup (upperUnitriangularGroup (Fin n) R)))
  | succ r ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      refine (Subgroup.commutator_mono ih le_top).trans ?_
      simpa only [superdiagonalSubgroup_one, Nat.succ_eq_add_one, add_assoc] using
        commutator_superdiagonalSubgroup_le (R := R) (n := n) (r + 1) 1

/-- Upper-unitriangular matrices form a nilpotent group over every ring. -/
instance instIsNilpotent : Group.IsNilpotent (upperUnitriangularGroup (Fin n) R) := by
  rw [Subgroup.nilpotent_iff_lowerCentralSeries]
  refine ⟨n, le_antisymm ?_ bot_le⟩
  refine (lowerCentralSeries_le_superdiagonalSubgroup (R := R) n).trans ?_
  rw [superdiagonalSubgroup_eq_bot_of_le (R := R) (n := n) (Nat.le_add_right n 1)]

end TauCeti.UpperUnitriangularGroup
