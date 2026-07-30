/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

@[expose] public section

/-!
# Dynkin types

The Cartan-Killing classification says that an irreducible reduced crystallographic finite root
system is described by one of a short list of combinatorial types. This file introduces that list as
a plain enumeration `TauCeti.DynkinType`, equips it with a rank, a validity predicate carving out
the rank ranges in which the types are pairwise distinct and irreducible, and attaches to each type
its standard integer Cartan matrix, taken from Mathlib's `CartanMatrix` family. The predicate
`TauCeti.HasCartanType` then says that the Cartan matrix of a base agrees with the standard matrix
of a given type under a single simultaneous relabelling of rows and columns.

The enumeration is deliberately plain: the rank ranges `A n (1 ≤ n)`, `B n (2 ≤ n)`, `C n (3 ≤ n)`,
`D n (4 ≤ n)` are carried by `TauCeti.DynkinType.Valid` rather than baked into the constructors.
Those bounds remove the degenerate matrices and the low-rank coincidences `B₁ = C₁ = A₁`,
`C₂ = B₂`, `D₂ = A₁ × A₁` and `D₃ = A₃`; without them neither realization nor uniqueness of the
type holds. Note in particular that `Valid` is *not* preserved by exchanging `B n` and `C n`: `B 2`
is valid while `C 2` is not, precisely because they name the same root system.

The matching in `TauCeti.HasCartanType` is oriented, using one relabelling `e` on both indices
rather than allowing the matrix to be transposed. This is what keeps `Bₙ` and `Cₙ` apart, since
their standard Cartan matrices are transposes of one another
(`TauCeti.DynkinType.cartanMatrix_B_transpose`) and an unoriented match would identify them.

## Main definitions

* `TauCeti.DynkinType`: the enumeration `A n`, `B n`, `C n`, `D n`, `E6`, `E7`, `E8`, `F4`, `G2`.
* `TauCeti.DynkinType.rank`: the number of simple roots of a type.
* `TauCeti.DynkinType.Valid`: the rank ranges on which the types are the classification list.
* `TauCeti.DynkinType.IsSimplyLaced`: the types `A`, `D`, `E` with only single edges.
* `TauCeti.DynkinType.cartanMatrix`: the standard integer Cartan matrix of a type.
* `TauCeti.HasCartanType`: a base whose Cartan matrix reindexes to a standard one.

## Main results

* `TauCeti.DynkinType.cartanMatrix_apply_self` and
  `TauCeti.DynkinType.cartanMatrix_apply_le_zero_of_ne`: the standard matrices have diagonal `2`
  and nonpositive off-diagonal entries.
* `TauCeti.DynkinType.cartanMatrix_apply_eq_zero_comm`: their zero pattern is symmetric, so each is
  a generalized Cartan matrix.
* `TauCeti.DynkinType.isSimplyLaced_cartanMatrix_iff`: among valid types, the simply-laced Cartan
  matrices are exactly those of types `A`, `D` and `E`.
* `TauCeti.HasCartanType.isSimplyLaced_iff`: a base of valid type `t` is simply laced exactly when
  `t` is.

## References

This file implements the `DynkinType` enumeration of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, following the target signatures in
`TauCetiRoadmap/RepresentationTheory/RootSystems/Suggested.lean`. See Bourbaki, *Lie Groups and Lie
Algebras, Chapters 4-6*, plates I-IX, and Humphreys, *Introduction to Lie Algebras and
Representation Theory*, Chapter 11, for the standard Cartan matrices.
-/

namespace TauCeti

open Matrix

/-- Transporting simple-lacedness of a square matrix along a relabelling of its index type. -/
lemma isSimplyLaced_congr {α β : Type*} {A : Matrix α α ℤ} {B : Matrix β β ℤ} (e : α ≃ β)
    (he : ∀ i j, A i j = B (e i) (e j)) : A.IsSimplyLaced ↔ B.IsSimplyLaced := by
  constructor
  · intro h i j hij
    have hij' : e.symm i ≠ e.symm j := fun hh ↦ hij (by simpa using congrArg e hh)
    simpa only [he, Equiv.apply_symm_apply] using h hij'
  · intro h i j hij
    simpa only [he] using h (e.injective.ne hij)

/-- The finite list of Dynkin types. The rank ranges on which these are the types occurring in the
Cartan-Killing classification are carried by `TauCeti.DynkinType.Valid`, not by the constructors. -/
inductive DynkinType where
  /-- Type `Aₙ`, the type of `slₙ₊₁`. -/
  | A (n : ℕ)
  /-- Type `Bₙ`, the type of `so₂ₙ₊₁`. -/
  | B (n : ℕ)
  /-- Type `Cₙ`, the type of `sp₂ₙ`. -/
  | C (n : ℕ)
  /-- Type `Dₙ`, the type of `so₂ₙ`. -/
  | D (n : ℕ)
  /-- The exceptional type `E₆`. -/
  | E6
  /-- The exceptional type `E₇`. -/
  | E7
  /-- The exceptional type `E₈`. -/
  | E8
  /-- The exceptional type `F₄`. -/
  | F4
  /-- The exceptional type `G₂`. -/
  | G2
  deriving DecidableEq

namespace DynkinType

/-- The rank of a Dynkin type: the number of simple roots, equivalently the size of its Cartan
matrix. -/
def rank : DynkinType → ℕ
  | .A n | .B n | .C n | .D n => n
  | .E6 => 6
  | .E7 => 7
  | .E8 => 8
  | .F4 => 4
  | .G2 => 2

@[simp] lemma rank_A (n : ℕ) : (A n).rank = n := rfl
@[simp] lemma rank_B (n : ℕ) : (B n).rank = n := rfl
@[simp] lemma rank_C (n : ℕ) : (C n).rank = n := rfl
@[simp] lemma rank_D (n : ℕ) : (D n).rank = n := rfl
@[simp] lemma rank_E6 : E6.rank = 6 := rfl
@[simp] lemma rank_E7 : E7.rank = 7 := rfl
@[simp] lemma rank_E8 : E8.rank = 8 := rfl
@[simp] lemma rank_F4 : F4.rank = 4 := rfl
@[simp] lemma rank_G2 : G2.rank = 2 := rfl

/-- The rank ranges on which the Dynkin types are pairwise distinct and irreducible. Outside them
the standard Cartan matrices are degenerate or coincide: `B 1 = C 1 = A 1`, `C 2` is `B 2`
transposed, `D 2` is `A 1 × A 1` and `D 3` is `A 3` relabelled. -/
def Valid : DynkinType → Prop
  | .A n => 1 ≤ n
  | .B n => 2 ≤ n
  | .C n => 3 ≤ n
  | .D n => 4 ≤ n
  | .E6 | .E7 | .E8 | .F4 | .G2 => True

instance : DecidablePred Valid := fun t ↦
  match t with
  | .A n => inferInstanceAs (Decidable (1 ≤ n))
  | .B n => inferInstanceAs (Decidable (2 ≤ n))
  | .C n => inferInstanceAs (Decidable (3 ≤ n))
  | .D n => inferInstanceAs (Decidable (4 ≤ n))
  | .E6 | .E7 | .E8 | .F4 | .G2 => inferInstanceAs (Decidable True)

@[simp] lemma valid_A {n : ℕ} : (A n).Valid ↔ 1 ≤ n := Iff.rfl
@[simp] lemma valid_B {n : ℕ} : (B n).Valid ↔ 2 ≤ n := Iff.rfl
@[simp] lemma valid_C {n : ℕ} : (C n).Valid ↔ 3 ≤ n := Iff.rfl
@[simp] lemma valid_D {n : ℕ} : (D n).Valid ↔ 4 ≤ n := Iff.rfl

/-- A valid Dynkin type has at least one simple root. -/
lemma rank_pos {t : DynkinType} (ht : t.Valid) : 0 < t.rank := by
  cases t
  case A n => rw [rank_A]; exact valid_A.mp ht
  case B n => rw [rank_B]; have := valid_B.mp ht; omega
  case C n => rw [rank_C]; have := valid_C.mp ht; omega
  case D n => rw [rank_D]; have := valid_D.mp ht; omega
  all_goals simp

/-- The simply-laced Dynkin types are those all of whose edges are single, namely `A`, `D` and the
exceptional `E` types; equivalently (`isSimplyLaced_cartanMatrix_iff`) those whose standard Cartan
matrix has all off-diagonal entries `0` or `-1`. -/
def IsSimplyLaced : DynkinType → Prop
  | .A _ | .D _ | .E6 | .E7 | .E8 => True
  | .B _ | .C _ | .F4 | .G2 => False

instance : DecidablePred IsSimplyLaced := fun t ↦
  match t with
  | .A _ | .D _ | .E6 | .E7 | .E8 => inferInstanceAs (Decidable True)
  | .B _ | .C _ | .F4 | .G2 => inferInstanceAs (Decidable False)

/-- The standard integer Cartan matrix of a Dynkin type, indexed by `Fin t.rank`. The classical
families and the exceptional matrices are Mathlib's `CartanMatrix.A`, `.B`, `.C`, `.D`, `.E₆`,
`.E₇`, `.E₈`, `.F₄` and `.G₂`, whose conventions this enumeration adopts. -/
def cartanMatrix : (t : DynkinType) → Matrix (Fin t.rank) (Fin t.rank) ℤ
  | .A n => CartanMatrix.A n
  | .B n => CartanMatrix.B n
  | .C n => CartanMatrix.C n
  | .D n => CartanMatrix.D n
  | .E6 => CartanMatrix.E₆
  | .E7 => CartanMatrix.E₇
  | .E8 => CartanMatrix.E₈
  | .F4 => CartanMatrix.F₄
  | .G2 => CartanMatrix.G₂

@[simp] lemma cartanMatrix_A (n : ℕ) : (A n).cartanMatrix = CartanMatrix.A n := rfl
@[simp] lemma cartanMatrix_B (n : ℕ) : (B n).cartanMatrix = CartanMatrix.B n := rfl
@[simp] lemma cartanMatrix_C (n : ℕ) : (C n).cartanMatrix = CartanMatrix.C n := rfl
@[simp] lemma cartanMatrix_D (n : ℕ) : (D n).cartanMatrix = CartanMatrix.D n := rfl
@[simp] lemma cartanMatrix_E6 : E6.cartanMatrix = CartanMatrix.E₆ := rfl
@[simp] lemma cartanMatrix_E7 : E7.cartanMatrix = CartanMatrix.E₇ := rfl
@[simp] lemma cartanMatrix_E8 : E8.cartanMatrix = CartanMatrix.E₈ := rfl
@[simp] lemma cartanMatrix_F4 : F4.cartanMatrix = CartanMatrix.F₄ := rfl
@[simp] lemma cartanMatrix_G2 : G2.cartanMatrix = CartanMatrix.G₂ := rfl

/-- Type `Cₙ` is type `Bₙ` with the double edge reversed. This is the only way the two differ, and
it is why `TauCeti.HasCartanType` matches Cartan matrices without transposing them. -/
lemma cartanMatrix_B_transpose (n : ℕ) :
    ((B n).cartanMatrix)ᵀ = (C n).cartanMatrix :=
  CartanMatrix.B_transpose n

/-- Every diagonal entry of a standard Cartan matrix is `2`. -/
@[simp] lemma cartanMatrix_apply_self (t : DynkinType) (i : Fin t.rank) :
    t.cartanMatrix i i = 2 := by
  cases t <;> simp [CartanMatrix.A]

/-- Every off-diagonal entry of a standard Cartan matrix is nonpositive. -/
lemma cartanMatrix_apply_le_zero_of_ne (t : DynkinType) {i j : Fin t.rank} (h : i ≠ j) :
    t.cartanMatrix i j ≤ 0 := by
  cases t
  case A n => exact CartanMatrix.A_apply_le_zero_of_ne n i j h
  case B n => exact CartanMatrix.B_off_diag_nonpos n i j h
  case C n => exact CartanMatrix.C_off_diag_nonpos n i j h
  case D n => exact CartanMatrix.D_off_diag_nonpos n i j h
  case E6 => exact CartanMatrix.E₆_off_diag_nonpos i j h
  case E7 => exact CartanMatrix.E₇_off_diag_nonpos i j h
  case E8 => exact CartanMatrix.E₈_off_diag_nonpos i j h
  case F4 => exact CartanMatrix.F₄_off_diag_nonpos i j h
  case G2 => exact CartanMatrix.G₂_off_diag_nonpos i j h

/-- The zero pattern of a standard Cartan matrix is symmetric: two simple roots are orthogonal in
one order exactly when they are in the other. With `cartanMatrix_apply_self` and
`cartanMatrix_apply_le_zero_of_ne` this says each standard matrix is a generalized Cartan matrix. -/
lemma cartanMatrix_apply_eq_zero_comm (t : DynkinType) (i j : Fin t.rank) :
    t.cartanMatrix i j = 0 ↔ t.cartanMatrix j i = 0 := by
  have symm_case {k : ℕ} {X : Matrix (Fin k) (Fin k) ℤ} (hX : X.IsSymm) (i j : Fin k) :
      X i j = 0 ↔ X j i = 0 := by rw [hX.apply]
  cases t
  case A n => exact symm_case (CartanMatrix.A_isSymm n) i j
  case D n => exact symm_case (CartanMatrix.D_isSymm n) i j
  case E6 => exact symm_case CartanMatrix.E₆_isSymm i j
  case E7 => exact symm_case CartanMatrix.E₇_isSymm i j
  case E8 => exact symm_case CartanMatrix.E₈_isSymm i j
  case B n => simp only [cartanMatrix_B, CartanMatrix.B, Matrix.of_apply]; grind
  case C n => simp only [cartanMatrix_C, CartanMatrix.C, Matrix.of_apply]; grind
  case F4 => revert i j; decide
  case G2 => revert i j; decide

/-- The double edge of type `Bₙ`: with at least two simple roots, the last two are joined by an
entry `-2`. -/
lemma cartanMatrix_B_apply_eq_neg_two {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    (hi : (i : ℕ) = n - 2) (hj : (j : ℕ) = n - 1) : CartanMatrix.B n i j = -2 := by
  have hij : i ≠ j := by rintro rfl; omega
  simp only [CartanMatrix.B, Matrix.of_apply, if_neg hij]
  rw [if_pos (by omega : (i : ℕ) + 1 = (j : ℕ)), if_pos (by omega : (j : ℕ) = n - 1)]

/-- The double edge of type `Cₙ`, pointing the other way from that of type `Bₙ`. -/
lemma cartanMatrix_C_apply_eq_neg_two {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    (hi : (i : ℕ) = n - 1) (hj : (j : ℕ) = n - 2) : CartanMatrix.C n i j = -2 := by
  have hij : i ≠ j := by rintro rfl; omega
  simp only [CartanMatrix.C, Matrix.of_apply, if_neg hij]
  rw [if_neg (by omega : ¬ (i : ℕ) + 1 = (j : ℕ)), if_pos (by omega : (j : ℕ) + 1 = (i : ℕ)),
    if_pos (by omega : (i : ℕ) = n - 1)]

private lemma not_isSimplyLaced_cartanMatrix_B {n : ℕ} (hn : 2 ≤ n) :
    ¬ (CartanMatrix.B n).IsSimplyLaced := by
  intro h
  have hij : (⟨n - 2, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
    simp only [ne_eq, Fin.mk.injEq]; omega
  rcases h hij with h1 | h1 <;>
    rw [cartanMatrix_B_apply_eq_neg_two hn _ _ rfl rfl] at h1 <;> omega

private lemma not_isSimplyLaced_cartanMatrix_C {n : ℕ} (hn : 2 ≤ n) :
    ¬ (CartanMatrix.C n).IsSimplyLaced := by
  intro h
  have hij : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ := by
    simp only [ne_eq, Fin.mk.injEq]; omega
  rcases h hij with h1 | h1 <;>
    rw [cartanMatrix_C_apply_eq_neg_two hn _ _ rfl rfl] at h1 <;> omega

/-- **Among valid Dynkin types the simply-laced Cartan matrices are exactly those of types `A`, `D`
and `E`.** Validity is what rules out `B 1 = A 1`, whose matrix is simply laced. -/
theorem isSimplyLaced_cartanMatrix_iff {t : DynkinType} (ht : t.Valid) :
    t.cartanMatrix.IsSimplyLaced ↔ t.IsSimplyLaced := by
  cases t
  case A n => exact iff_of_true (CartanMatrix.isSimplyLaced_A n) trivial
  case D n => exact iff_of_true (CartanMatrix.isSimplyLaced_D n) trivial
  case E6 => exact iff_of_true CartanMatrix.isSimplyLaced_E₆ trivial
  case E7 => exact iff_of_true CartanMatrix.isSimplyLaced_E₇ trivial
  case E8 => exact iff_of_true CartanMatrix.isSimplyLaced_E₈ trivial
  case B n => exact iff_of_false (not_isSimplyLaced_cartanMatrix_B (valid_B.mp ht)) not_false
  case C n =>
    have : 3 ≤ n := valid_C.mp ht
    exact iff_of_false (not_isSimplyLaced_cartanMatrix_C (by omega)) not_false
  case F4 => exact iff_of_false CartanMatrix.not_isSimplyLaced_F₄ not_false
  case G2 => exact iff_of_false CartanMatrix.not_isSimplyLaced_G₂ not_false

/-- A simply-laced Dynkin type has a symmetric Cartan matrix. -/
lemma cartanMatrix_isSymm_of_isSimplyLaced {t : DynkinType} (ht : t.IsSimplyLaced) :
    t.cartanMatrix.IsSymm := by
  cases t
  case A n => exact CartanMatrix.A_isSymm n
  case D n => exact CartanMatrix.D_isSymm n
  case E6 => exact CartanMatrix.E₆_isSymm
  case E7 => exact CartanMatrix.E₇_isSymm
  case E8 => exact CartanMatrix.E₈_isSymm
  all_goals exact ht.elim

end DynkinType

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsCrystallographic]

/-- A base of a crystallographic root pairing **has Cartan type `t`** when its Cartan matrix agrees
with the standard Cartan matrix of `t` after a single simultaneous relabelling of rows and columns.
Matching without transposing is deliberate: `Bₙ` and `Cₙ` have transposed Cartan matrices
(`TauCeti.DynkinType.cartanMatrix_B_transpose`) and are different root systems. -/
def HasCartanType (b : P.Base) (t : DynkinType) : Prop :=
  ∃ e : b.support ≃ Fin t.rank, ∀ i j, b.cartanMatrix i j = t.cartanMatrix (e i) (e j)

variable {P}

/-- Having Cartan type `t`, expressed as a reindexing of matrices rather than entrywise. -/
lemma hasCartanType_iff_reindex (b : P.Base) (t : DynkinType) :
    HasCartanType P b t ↔
      ∃ e : b.support ≃ Fin t.rank, b.cartanMatrix.reindex e e = t.cartanMatrix := by
  refine exists_congr fun e ↦ ⟨fun h ↦ ?_, fun h i j ↦ ?_⟩
  · ext i j
    simpa using h (e.symm i) (e.symm j)
  · simpa using congrFun₂ h (e i) (e j)

/-- The rank of the Cartan type of a base is its number of simple roots. -/
lemma HasCartanType.card_support {b : P.Base} {t : DynkinType} (h : HasCartanType P b t) :
    b.support.card = t.rank := by
  obtain ⟨e, -⟩ := h
  simpa using Fintype.card_congr e

/-- **A base of valid Cartan type `t` is simply laced exactly when `t` is**, that is, exactly when
`t` is one of `A`, `D`, `E₆`, `E₇`, `E₈`. -/
theorem HasCartanType.isSimplyLaced_iff {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    b.cartanMatrix.IsSimplyLaced ↔ t.IsSimplyLaced := by
  obtain ⟨e, he⟩ := h
  rw [isSimplyLaced_congr e he, DynkinType.isSimplyLaced_cartanMatrix_iff ht]

end RootPairing

end TauCeti
