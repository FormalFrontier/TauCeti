/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Cyclic
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Checker
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Lift

/-!
# The cyclotomic Dixon computation for the cyclic group of order three

This file carries the Burnside--Dixon--Schneider computation beyond the rational-table stage for
the first time.  For `C₃ = Multiplicative (ZMod 3)`, it displays the exact table

```
1  1   1
1  ζ   ζ²
1  ζ²  ζ
```

in `TauCeti.Cyclotomic 3`, where `ζ` is the distinguished primitive cube root.  Since every
conjugacy class is a singleton and every irreducible degree is one, the ordinary and central
character tables coincide.

The certified Dixon prime is `7`, with primitive cube root `2`.  Reducing the displayed rows at
that root gives all three outputs of the executable modular central-character search.  The two
residues at the conjugate roots `2` and `4` then reconstruct every exact entry through the
structured cyclotomic lift.  Thus this example exercises the genuinely cyclotomic data which a
single signed integer lift cannot recover.

Finally, the distinguished embedding `TauCeti.Cyclotomic.complexEmbedding` sends the exact table
to a matrix satisfying `TauCeti.IsCharacterTableSpec`; labeled uniqueness therefore identifies it
with the complex character table up to row order.

## Main definitions

* `TauCeti.cyclicGroupThreeDixonPrimeData`: the prime `7` with primitive cube root `2`.
* `TauCeti.cyclicGroupThreeExactCharacterTable`: the exact `Cyclotomic 3` table.
* `TauCeti.cyclicGroupThreeModularCentralRows`: its three reductions modulo `7`.
* `TauCeti.cyclicGroupThreeComplexCharacterTable`: the embedded table, reindexed by conjugacy
  classes.

## Main results

* `TauCeti.cyclicGroupThree_centralCharacterSearch`: the modular search returns precisely the
  reductions of the displayed rows.
* `TauCeti.cyclicGroupThreeExactCharacterTable_lift_conjugateResidues`: the structured lift
  recovers every exact entry from its two conjugate residues.
* `TauCeti.isCharacterTableSpec_cyclicGroupThree`: the embedded exact table satisfies the complex
  character-table specification.

## References

This is the `C₃` case of “Small cyclotomic (second milestone)” in Layer 6 of the
[character theory roadmap][roadmap].

The worked computation follows
`TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.CyclicTwo`; its prime certificate
follows `TauCeti.RepresentationTheory.CharacterTable.Dixon.Dihedral`, and the specification bridge
follows `TauCeti.RepresentationTheory.CharacterTable.Dixon.IntegerChecker`.

[roadmap]: https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601--606.
-/

public section

namespace TauCeti

open Matrix

local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem exponent_cyclicGroup_three :
    Monoid.exponent (Multiplicative (ZMod 3)) = 3 := by
  simp

private theorem natCard_cyclicGroup_three : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  simp [Nat.card_eq_fintype_card]

private theorem sqrt_three : Nat.sqrt 3 = 1 := by
  have hlt : Nat.sqrt 3 < 2 := Nat.sqrt_lt.2 (by norm_num)
  have hle : 1 ≤ Nat.sqrt 3 := Nat.le_sqrt.mpr (by norm_num)
  omega

/-- **`7` is a good Dixon prime for the cyclic group of order three**: it does not divide `3`,
the exponent `3` divides `7 - 1`, and `2⌊√3⌋ = 2 < 7`. -/
theorem isGoodDixonPrime_cyclicGroup_three_seven :
    IsGoodDixonPrime (Multiplicative (ZMod 3)) 7 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · simp
  · rw [exponent_cyclicGroup_three]
    norm_num
  · rw [natCard_cyclicGroup_three]
    rw [sqrt_three]
    norm_num

/-- Dixon prime data for the cyclic group of order three: the prime `7`, with `2` as a primitive
cube root of unity. -/
@[expose] def cyclicGroupThreeDixonPrimeData :
    DixonPrimeData (Multiplicative (ZMod 3)) where
  p := 7
  root := 2
  isGoodDixonPrime := isGoodDixonPrime_cyclicGroup_three_seven
  isPrimitiveRoot_root := by
    simpa only [exponent_cyclicGroup_three] using
      (IsPrimitiveRoot.mk_of_lt (2 : ZMod 7) (by norm_num) (by decide)
      fun l hl0 hl3 => by interval_cases l <;> decide)

/-- The prime carried by `TauCeti.cyclicGroupThreeDixonPrimeData` is `7`. -/
@[simp]
theorem cyclicGroupThreeDixonPrimeData_p : cyclicGroupThreeDixonPrimeData.p = 7 := rfl

/-- The primitive cube root carried by `TauCeti.cyclicGroupThreeDixonPrimeData` is `2`. -/
@[simp]
theorem cyclicGroupThreeDixonPrimeData_root : cyclicGroupThreeDixonPrimeData.root = 2 := rfl

/-- The numbered conjugacy classes of the cyclic group of order three. -/
abbrev CyclicGroupThreeClassIndex := Fin (cyclicClassData 3).numClasses

/-- **The exact central and ordinary character table of the cyclic group of order three.**
Columns are the singleton classes of `0`, `1`, and `2` in that order. Row `i` is the linear
character sending `Multiplicative.ofAdd j` to `ζ ^ (i * j)`, so rows index the irreducible
characters even though they reuse the class numbering. -/
def cyclicGroupThreeExactCharacterTable :
    Matrix CyclicGroupThreeClassIndex CyclicGroupThreeClassIndex (Cyclotomic 3) :=
  !![1, 1, 1;
     1, Cyclotomic.zeta 3, Cyclotomic.zeta 3 ^ 2;
     1, Cyclotomic.zeta 3 ^ 2, Cyclotomic.zeta 3]

/-- **The entries of the exact `C₃` character table in closed form**: the entry in row `i` and
column `j` is `ζ ^ (i * j)`, the value of the `i`-th linear character at `Multiplicative.ofAdd j`.
This is the characteristic property of the displayed matrix; downstream reasoning uses it instead
of the matrix literal. -/
@[simp]
theorem cyclicGroupThreeExactCharacterTable_apply (i j : CyclicGroupThreeClassIndex) :
    cyclicGroupThreeExactCharacterTable i j = Cyclotomic.zeta 3 ^ ((i : ℕ) * (j : ℕ)) := by
  fin_cases i <;> fin_cases j <;> decide

/-- Every exact row is normalized at the identity class. -/
theorem cyclicGroupThreeExactCharacterTable_index_one (i : CyclicGroupThreeClassIndex) :
    cyclicGroupThreeExactCharacterTable i ((cyclicClassData 3).index 1) = 1 := by
  fin_cases i <;> decide

/-- Every exact row satisfies the numbered class-algebra eigenrow equations. -/
theorem isModularEigenrow_cyclicGroupThreeExactCharacterTable
    (i : CyclicGroupThreeClassIndex) :
    (cyclicClassData 3).IsModularEigenrow (cyclicGroupThreeExactCharacterTable i) := by
  rw [(cyclicClassData 3).isModularEigenrow_iff]
  fin_cases i <;> decide

/-- **The exact `C₃` table passes the cyclotomic character-table certificate.**  Its central and
ordinary tables coincide and all three character degrees are one. -/
theorem isCyclotomicCharacterTableSpec_cyclicGroupThree :
    (cyclicClassData 3).IsCyclotomicCharacterTableSpec 3
      cyclicGroupThreeExactCharacterTable cyclicGroupThreeExactCharacterTable (fun _ => 1) := by
  decide

/-- The executable exact cyclotomic checker accepts the displayed `C₃` table. -/
theorem cyclotomicCharacterTableChecker_cyclicGroupThree :
  (cyclicClassData 3).cyclotomicCharacterTableChecker 3
      cyclicGroupThreeExactCharacterTable cyclicGroupThreeExactCharacterTable (fun _ => 1) = true :=
  (cyclicClassData 3).cyclotomicCharacterTableChecker_eq_true_iff 3 _ _ _ |>.2
    isCyclotomicCharacterTableSpec_cyclicGroupThree

/-- The displayed exact rows reduced at the chosen primitive cube root modulo `7`. -/
def cyclicGroupThreeModularCentralRows :
    Finset (CyclicGroupThreeClassIndex → ZMod 7) :=
  (cyclicClassData 3).rowsOfMap
    (Cyclotomic.reduce 7 cyclicGroupThreeDixonPrimeData.root)
    cyclicGroupThreeExactCharacterTable

/-- A modular row is displayed exactly when it is the reduction of a row of the exact table. -/
@[simp]
theorem mem_cyclicGroupThreeModularCentralRows_iff
    {a : CyclicGroupThreeClassIndex → ZMod 7} :
    a ∈ cyclicGroupThreeModularCentralRows ↔
      ∃ i, (fun j => Cyclotomic.reduce 7 cyclicGroupThreeDixonPrimeData.root
        (cyclicGroupThreeExactCharacterTable i j)) = a := by
  simp [cyclicGroupThreeModularCentralRows]

/-- Reduction at the chosen root preserves the exact eigenrow equations. -/
theorem isModularEigenrow_cyclicGroupThreeExactCharacterTable_zmod
    (i : CyclicGroupThreeClassIndex) :
    (cyclicClassData 3).IsModularEigenrow fun j =>
      Cyclotomic.reduce 7 cyclicGroupThreeDixonPrimeData.root
        (cyclicGroupThreeExactCharacterTable i j) := by
  have hroot : IsPrimitiveRoot cyclicGroupThreeDixonPrimeData.root 3 := by
    simpa only [exponent_cyclicGroup_three] using
      cyclicGroupThreeDixonPrimeData.isPrimitiveRoot_root
  have hmap := (isModularEigenrow_cyclicGroupThreeExactCharacterTable i).map
    (Cyclotomic.reduceRingHom 7 cyclicGroupThreeDixonPrimeData.root hroot)
  rw [(cyclicClassData 3).isModularEigenrow_iff] at hmap ⊢
  intro a b
  simpa only [← Cyclotomic.reduceRingHom_apply 7 cyclicGroupThreeDixonPrimeData.root hroot]
    using hmap a b

/-- The three displayed reductions are pairwise distinct. -/
@[simp]
theorem card_cyclicGroupThreeModularCentralRows :
    cyclicGroupThreeModularCentralRows.card = 3 := by
  decide

/-- **The executable modular central-character search returns precisely the three reductions of
the exact `C₃` table.** -/
theorem cyclicGroupThree_centralCharacterSearch :
    (cyclicClassData 3).centralCharacterSearch (F := ZMod 7) =
      cyclicGroupThreeModularCentralRows := by
  rw [cyclicGroupThreeModularCentralRows]
  apply (cyclicClassData 3).centralCharacterSearch_eq_rowsOfMap_of_isGoodDixonPrime
    isGoodDixonPrime_cyclicGroup_three_seven
    (Cyclotomic.reduce 7 cyclicGroupThreeDixonPrimeData.root)
    cyclicGroupThreeExactCharacterTable
  · intro i
    fin_cases i <;> decide
  · exact isModularEigenrow_cyclicGroupThreeExactCharacterTable_zmod
  · simpa only [cyclicGroupThreeModularCentralRows, numClasses_cyclicClassData] using
      card_cyclicGroupThreeModularCentralRows

/-- Every coordinate of every displayed exact entry satisfies Dixon's coefficient bound. -/
theorem cyclicGroupThreeExactCharacterTable_natAbs_coeff_le_sqrt
    (i j : CyclicGroupThreeClassIndex) (k : Fin (3 : ℕ).totient) :
    ((cyclicGroupThreeExactCharacterTable i j).coeff k).natAbs ≤
      Nat.sqrt (Nat.card (Multiplicative (ZMod 3))) := by
  rw [natCard_cyclicGroup_three]
  rw [sqrt_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- **The structured cyclotomic lift recovers every exact table entry from its residues at the
two conjugate cube roots modulo `7`.** -/
theorem cyclicGroupThreeExactCharacterTable_lift_conjugateResidues
    (i j : CyclicGroupThreeClassIndex) :
    Cyclotomic.lift 3 cyclicGroupThreeDixonPrimeData.root
        (Cyclotomic.conjugateResidues cyclicGroupThreeDixonPrimeData.root
          (cyclicGroupThreeExactCharacterTable i j)) =
      cyclicGroupThreeExactCharacterTable i j := by
  have hLift : ∀ {x : Cyclotomic (Monoid.exponent (Multiplicative (ZMod 3)))},
      (∀ k : Fin (Monoid.exponent (Multiplicative (ZMod 3))).totient,
        (x.coeff k).natAbs ≤ Nat.sqrt (Nat.card (Multiplicative (ZMod 3)))) →
      Cyclotomic.lift (Monoid.exponent (Multiplicative (ZMod 3)))
        cyclicGroupThreeDixonPrimeData.root
        (Cyclotomic.conjugateResidues cyclicGroupThreeDixonPrimeData.root x) = x :=
    fun {_} => cyclicGroupThreeDixonPrimeData.lift_conjugateResidues
  -- Rewrite the group exponent first so that the dependent cyclotomic coefficient type is `3`.
  rw [exponent_cyclicGroup_three] at hLift
  exact hLift (cyclicGroupThreeExactCharacterTable_natAbs_coeff_le_sqrt i j)

/-- The displayed exact table, embedded in `ℂ` and reindexed by actual conjugacy classes. -/
noncomputable def cyclicGroupThreeComplexCharacterTable :
    Matrix (Fin (Nat.card (ConjClasses (Multiplicative (ZMod 3)))))
      (ConjClasses (Multiplicative (ZMod 3))) ℂ :=
  (cyclicClassData 3).complexTableOfCyclotomic 3 cyclicGroupThreeExactCharacterTable

/-- The embedded table evaluated at arbitrary row and conjugacy-class indices. -/
@[simp]
theorem cyclicGroupThreeComplexCharacterTable_apply
    (i : Fin (Nat.card (ConjClasses (Multiplicative (ZMod 3)))))
    (C : ConjClasses (Multiplicative (ZMod 3))) :
    cyclicGroupThreeComplexCharacterTable i C =
      Cyclotomic.complexEmbedding
        (cyclicGroupThreeExactCharacterTable
          ((finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses).symm i)
          ((cyclicClassData 3).equivConjClasses.symm C)) := by
  exact (cyclicClassData 3).complexTableOfCyclotomic_apply 3 _ _ _

/-- The embedded table evaluated at a numbered row and numbered conjugacy class. -/
theorem cyclicGroupThreeComplexCharacterTable_apply_classOf
    (i j : CyclicGroupThreeClassIndex) :
    cyclicGroupThreeComplexCharacterTable
        (finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses i)
        ((cyclicClassData 3).classOf j) =
      Cyclotomic.complexEmbedding (cyclicGroupThreeExactCharacterTable i j) := by
  exact (cyclicClassData 3).complexTableOfCyclotomic_apply_classOf 3 _ _ _

/-- The embedded exact `C₃` table satisfies the character-table specification and therefore is
the complex character table up to a permutation of rows. -/
theorem isCharacterTableSpec_cyclicGroupThree :
    IsCharacterTableSpec (Multiplicative (ZMod 3))
      cyclicGroupThreeComplexCharacterTable :=
  isCyclotomicCharacterTableSpec_cyclicGroupThree.isCharacterTableSpec

end TauCeti
