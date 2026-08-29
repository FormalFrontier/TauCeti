/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.RootGenerators

/-!
# Cartan action on the split type-B root generators

This file records the coordinates of the Bourbaki simple coroots in the split diagonal Cartan and
uses them to compute their action on both signs of every simple root. If `dᵢ` is the coordinate
vector of the `i`th simple coroot, the formulas are

```text
[hᵢ, eⱼ] = dᵢ(j) eⱼ                         (j the short node),
[hᵢ, eⱼ] = (dᵢ(j) - dᵢ(j+1)) eⱼ            (j a long node),
```

with the negatives of these scalars on the negative-root generators. These are the coordinate
form of the Cartan relations. Identifying the scalars uniformly with entries of Mathlib's type-`B`
Cartan matrix, and proving the remaining mixed and higher Serre relations, are subsequent steps.

## Main results

* `TauCeti.typeBSimpleCorootCoordinate`: the diagonal coordinate of a simple coroot.
* `TauCeti.typeBSimpleCorootGenerator_eq_diagonal`: the corresponding matrix identity.
* `TauCeti.typeBSimpleCorootGenerator_lie_eq_zero`: simple coroots commute.
* `TauCeti.typeBSimpleCorootGenerator_lie_root_last` and
  `TauCeti.typeBSimpleCorootGenerator_lie_root_castSucc`: Cartan action on positive generators.
* `TauCeti.typeBSimpleCorootGenerator_lie_negativeRoot_last` and
  `TauCeti.typeBSimpleCorootGenerator_lie_negativeRoot_castSucc`: Cartan action on negative
  generators.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
* R. W. Carter, *Simple Groups of Lie Type*, Section 4.2.

This supplies the next matrix-model input to the Chevalley--Demazure construction and pinnings in
Layer 9 of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

universe u

variable {K : Type u} [CommRing K]
variable {n : ℕ}

/-- The coordinate vector of a Bourbaki simple coroot of `Bₙ₊₁` in the split diagonal Cartan.
The first `n` nodes are `εᵢ - εᵢ₊₁`, while the final short node has coroot `2εₙ`. -/
def typeBSimpleCorootCoordinate (i : Fin (n + 1)) : Fin (n + 1) → K :=
  Fin.lastCases (2 • Pi.single (Fin.last n) 1)
    (fun j => Pi.single j.castSucc 1 - Pi.single j.succ 1) i

@[simp]
theorem typeBSimpleCorootCoordinate_last :
    typeBSimpleCorootCoordinate (K := K) (Fin.last n) =
      2 • Pi.single (Fin.last n) 1 := by
  simp [typeBSimpleCorootCoordinate]

@[simp]
theorem typeBSimpleCorootCoordinate_castSucc (i : Fin n) :
    typeBSimpleCorootCoordinate (K := K) i.castSucc =
      Pi.single i.castSucc 1 - Pi.single i.succ 1 := by
  simp [typeBSimpleCorootCoordinate]

/-- A simple coroot generator is the split diagonal element with the corresponding coordinate
vector. -/
theorem typeBSimpleCorootGenerator_eq_diagonal (i : Fin (n + 1)) :
    typeBSimpleCorootGenerator (K := K) i =
      ((typeBDiagonalEquiv (K := K) (ι := Fin (n + 1))
        (typeBSimpleCorootCoordinate i) : typeBDiagonalCartan K (Fin (n + 1))) :
          LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K) := by
  refine Fin.lastCases ?_ (fun i₀ => ?_) i
  · simp [typeBShortCorootGenerator_eq_diagonal]
  · simp [typeBLongCorootGenerator_eq_diagonal]

/-- The simple coroot generators in the standard split type-`B` model commute. -/
@[simp]
theorem typeBSimpleCorootGenerator_lie_eq_zero (i j : Fin (n + 1)) :
    ⁅typeBSimpleCorootGenerator (K := K) i, typeBSimpleCorootGenerator (K := K) j⁆ = 0 := by
  rw [typeBSimpleCorootGenerator_eq_diagonal,
    typeBSimpleCorootGenerator_eq_diagonal]
  have h : ⁅typeBDiagonalEquiv (K := K) (ι := Fin (n + 1))
      (typeBSimpleCorootCoordinate i),
      typeBDiagonalEquiv (K := K) (ι := Fin (n + 1))
        (typeBSimpleCorootCoordinate j)⁆ = 0 :=
    LieModule.IsTrivial.trivial _ _
  exact congrArg Subtype.val h

/-- The action of a simple coroot on the positive generator at the final short node. -/
@[simp]
theorem typeBSimpleCorootGenerator_lie_root_last (i : Fin (n + 1)) :
    ⁅typeBSimpleCorootGenerator (K := K) i,
      typeBShortRootGenerator (K := K) (Fin.last n)⁆ =
        typeBSimpleCorootCoordinate (K := K) i (Fin.last n) •
          typeBShortRootGenerator (K := K) (Fin.last n) := by
  rw [typeBSimpleCorootGenerator_eq_diagonal]
  simpa only [coe_typeBDiagonalEquiv_apply] using
    (typeBDiagonalEquiv_lie_shortRootGenerator
      (typeBSimpleCorootCoordinate (K := K) i) (Fin.last n))

/-- The action of a simple coroot on a positive generator at a long node. -/
@[simp]
theorem typeBSimpleCorootGenerator_lie_root_castSucc (i : Fin (n + 1)) (j : Fin n) :
    ⁅typeBSimpleCorootGenerator (K := K) i,
      typeBLongRootGenerator (K := K) j.castSucc j.succ
        (ne_of_lt j.castSucc_lt_succ)⁆ =
        (typeBSimpleCorootCoordinate (K := K) i j.castSucc -
          typeBSimpleCorootCoordinate (K := K) i j.succ) •
            typeBLongRootGenerator (K := K) j.castSucc j.succ
              (ne_of_lt j.castSucc_lt_succ) := by
  rw [typeBSimpleCorootGenerator_eq_diagonal]
  simpa only [coe_typeBDiagonalEquiv_apply] using
    (typeBDiagonalEquiv_lie_longRootGenerator
      (typeBSimpleCorootCoordinate (K := K) i) j.castSucc j.succ
        (ne_of_lt j.castSucc_lt_succ))

/-- The action of a simple coroot on the negative generator at the final short node. -/
@[simp]
theorem typeBSimpleCorootGenerator_lie_negativeRoot_last (i : Fin (n + 1)) :
    ⁅typeBSimpleCorootGenerator (K := K) i,
      typeBShortNegativeRootGenerator (K := K) (Fin.last n)⁆ =
        -(typeBSimpleCorootCoordinate (K := K) i (Fin.last n)) •
          typeBShortNegativeRootGenerator (K := K) (Fin.last n) := by
  rw [typeBSimpleCorootGenerator_eq_diagonal]
  simpa only [coe_typeBDiagonalEquiv_apply] using
    (typeBDiagonalEquiv_lie_shortNegativeRootGenerator
      (typeBSimpleCorootCoordinate (K := K) i) (Fin.last n))

/-- The action of a simple coroot on a negative generator at a long node. -/
@[simp]
theorem typeBSimpleCorootGenerator_lie_negativeRoot_castSucc (i : Fin (n + 1)) (j : Fin n) :
    ⁅typeBSimpleCorootGenerator (K := K) i,
      typeBLongRootGenerator (K := K) j.succ j.castSucc
        (ne_of_gt j.castSucc_lt_succ)⁆ =
        (typeBSimpleCorootCoordinate (K := K) i j.succ -
          typeBSimpleCorootCoordinate (K := K) i j.castSucc) •
            typeBLongRootGenerator (K := K) j.succ j.castSucc
              (ne_of_gt j.castSucc_lt_succ) := by
  rw [typeBSimpleCorootGenerator_eq_diagonal]
  simpa only [coe_typeBDiagonalEquiv_apply] using
    (typeBDiagonalEquiv_lie_longRootGenerator
      (typeBSimpleCorootCoordinate (K := K) i) j.succ j.castSucc
        (ne_of_gt j.castSucc_lt_succ))

end TauCeti
