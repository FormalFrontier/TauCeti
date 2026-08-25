/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Cyclic
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Lift
public import TauCeti.RepresentationTheory.CharacterTable.Specification

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
* `TauCeti.cyclicGroupThree_lift_entry`: the structured lift recovers every exact entry from its
  two conjugate residues.
* `TauCeti.isCharacterTableSpec_cyclicGroupThree`: the embedded exact table satisfies the complex
  character-table specification.

## References

This is the `C₃` case of “Small cyclotomic (second milestone)” in Layer 6 of the
[character theory roadmap][roadmap].

[roadmap]: https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601--606.
-/

public section

namespace TauCeti

open Matrix

local instance cyclicGroupThreeFactPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem exponent_cyclicGroup_three :
    Monoid.exponent (Multiplicative (ZMod 3)) = 3 := by
  simp

private theorem natCard_cyclicGroup_three : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  simp [Nat.card_eq_fintype_card]

/-- **`7` is a good Dixon prime for the cyclic group of order three**: it does not divide `3`,
the exponent `3` divides `7 - 1`, and `2⌊√3⌋ = 2 < 7`. -/
theorem isGoodDixonPrime_cyclicGroup_three_seven :
    IsGoodDixonPrime (Multiplicative (ZMod 3)) 7 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · simp
  · rw [exponent_cyclicGroup_three]
    norm_num
  · rw [natCard_cyclicGroup_three]
    have h : Nat.sqrt 3 < 2 := Nat.sqrt_lt.2 (by norm_num)
    omega

/-- Dixon prime data for the cyclic group of order three: the prime `7`, with `2` as a primitive
cube root of unity. -/
@[expose] def cyclicGroupThreeDixonPrimeData :
    DixonPrimeData (Multiplicative (ZMod 3)) where
  p := 7
  root := 2
  isGoodDixonPrime := isGoodDixonPrime_cyclicGroup_three_seven
  isPrimitiveRoot_root := by
    simpa using (IsPrimitiveRoot.mk_of_lt (2 : ZMod 7) (by norm_num) (by decide)
      fun l hl0 hl3 => by interval_cases l <;> decide)

/-- The prime carried by `TauCeti.cyclicGroupThreeDixonPrimeData` is `7`. -/
@[simp]
theorem cyclicGroupThreeDixonPrimeData_p : cyclicGroupThreeDixonPrimeData.p = 7 := rfl

/-- The primitive cube root carried by `TauCeti.cyclicGroupThreeDixonPrimeData` is `2`. -/
@[simp]
theorem cyclicGroupThreeDixonPrimeData_root : cyclicGroupThreeDixonPrimeData.root = 2 := rfl

/-- The numbered conjugacy classes of the cyclic group of order three. -/
abbrev CyclicGroupThreeClassIndex := Fin (cyclicClassData 3).numClasses

private def cyclicGroupThreeClassIndexEquiv : CyclicGroupThreeClassIndex ≃ Fin 3 :=
  finCongr rfl

@[simp]
private theorem cyclicGroupThreeClassIndexEquiv_symm_apply (i : Fin 3) :
    cyclicGroupThreeClassIndexEquiv.symm i =
      ⟨i, by simpa only [numClasses_cyclicClassData] using i.isLt⟩ := by
  apply Fin.ext
  rfl

/-- **The exact central and ordinary character table of the cyclic group of order three.**
Columns are the singleton classes of `0`, `1`, and `2` in that order. -/
def cyclicGroupThreeExactCharacterTable :
    Matrix CyclicGroupThreeClassIndex CyclicGroupThreeClassIndex (Cyclotomic 3) :=
  !![1, 1, 1;
     1, Cyclotomic.zeta 3, Cyclotomic.zeta 3 ^ 2;
     1, Cyclotomic.zeta 3 ^ 2, Cyclotomic.zeta 3]

/-- The entries of the exact `C₃` character table. -/
@[simp]
theorem cyclicGroupThreeExactCharacterTable_apply (i j : CyclicGroupThreeClassIndex) :
    cyclicGroupThreeExactCharacterTable i j =
      !![1, 1, 1;
         1, Cyclotomic.zeta 3, Cyclotomic.zeta 3 ^ 2;
         1, Cyclotomic.zeta 3 ^ 2, Cyclotomic.zeta 3] i j := by
  rfl

@[simp]
private theorem cyclicGroupThreeExactCharacterTable_apply_reindex (i j : Fin 3) :
    cyclicGroupThreeExactCharacterTable
        (cyclicGroupThreeClassIndexEquiv.symm i)
        (cyclicGroupThreeClassIndexEquiv.symm j) =
      !![1, 1, 1;
         1, Cyclotomic.zeta 3, Cyclotomic.zeta 3 ^ 2;
         1, Cyclotomic.zeta 3 ^ 2, Cyclotomic.zeta 3] i j := by
  simp only [cyclicGroupThreeClassIndexEquiv_symm_apply]
  fin_cases i <;> fin_cases j <;> rfl

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

/-- The displayed exact rows reduced at the chosen primitive cube root modulo `7`. -/
def cyclicGroupThreeModularCentralRows :
    Finset (CyclicGroupThreeClassIndex → ZMod 7) :=
  Finset.univ.image fun i j =>
    Cyclotomic.reduce 7 cyclicGroupThreeDixonPrimeData.root
      (cyclicGroupThreeExactCharacterTable i j)

/-- A modular row is displayed exactly when it is the reduction of an exact row. -/
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
  symm
  apply Finset.eq_of_subset_of_card_le
  · rw [cyclicGroupThreeModularCentralRows, Finset.image_subset_iff]
    intro i _
    rw [(cyclicClassData 3).mem_centralCharacterSearch]
    exact ⟨by fin_cases i <;> decide,
      isModularEigenrow_cyclicGroupThreeExactCharacterTable_zmod i⟩
  · rw [(cyclicClassData 3).card_centralCharacterSearch_of_isGoodDixonPrime
      isGoodDixonPrime_cyclicGroup_three_seven,
      card_cyclicGroupThreeModularCentralRows, numClasses_cyclicClassData]

/-- Every coordinate of every displayed exact entry satisfies Dixon's coefficient bound. -/
theorem cyclicGroupThreeExactCharacterTable_coeff_bound
    (i j : CyclicGroupThreeClassIndex) (k : Fin (3 : ℕ).totient) :
    ((cyclicGroupThreeExactCharacterTable i j).coeff k).natAbs ≤
      Nat.sqrt (Nat.card (Multiplicative (ZMod 3))) := by
  rw [natCard_cyclicGroup_three]
  have hsqrt : Nat.sqrt 3 = 1 := by
    have hlt : Nat.sqrt 3 < 2 := Nat.sqrt_lt.2 (by norm_num)
    have hle : 1 ≤ Nat.sqrt 3 := Nat.le_sqrt.mpr (by norm_num)
    omega
  rw [hsqrt]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- **The structured cyclotomic lift recovers every exact table entry from its residues at the
two conjugate cube roots modulo `7`.** -/
@[simp]
theorem cyclicGroupThree_lift_entry (i j : CyclicGroupThreeClassIndex) :
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
  rw [exponent_cyclicGroup_three] at hLift
  exact hLift (cyclicGroupThreeExactCharacterTable_coeff_bound i j)

/-- The displayed exact table, embedded in `ℂ` and reindexed by actual conjugacy classes. -/
noncomputable def cyclicGroupThreeComplexCharacterTable :
    Matrix (Fin (Nat.card (ConjClasses (Multiplicative (ZMod 3)))))
      (ConjClasses (Multiplicative (ZMod 3))) ℂ :=
  (cyclicGroupThreeExactCharacterTable.map Cyclotomic.complexEmbedding).submatrix
    (finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses).symm
    (cyclicClassData 3).equivConjClasses.symm

/-- The embedded table evaluated at a numbered row and numbered conjugacy class. -/
theorem cyclicGroupThreeComplexCharacterTable_apply_classOf
    (i j : CyclicGroupThreeClassIndex) :
    cyclicGroupThreeComplexCharacterTable
        (finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses i)
        ((cyclicClassData 3).classOf j) =
      Cyclotomic.complexEmbedding (cyclicGroupThreeExactCharacterTable i j) := by
  rw [cyclicGroupThreeComplexCharacterTable, Matrix.submatrix_apply, Matrix.map_apply]
  have hj : (cyclicClassData 3).equivConjClasses.symm
      ((cyclicClassData 3).classOf j) = j := by
    rw [← (cyclicClassData 3).equivConjClasses_apply j, Equiv.symm_apply_apply]
  have hi : (finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses).symm
      (finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses i) = i :=
    (finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses).symm_apply_apply i
  rw [hi, hj]

private theorem cyclicGroupThree_complexRoot_sq_add_complexRoot_add_one :
    Cyclotomic.complexRoot 3 ^ 2 + Cyclotomic.complexRoot 3 + 1 = 0 := by
  have h := (Cyclotomic.isPrimitiveRoot_complexRoot (e := 3)).isRoot_cyclotomic (by norm_num)
  simpa [Polynomial.cyclotomic_three, Polynomial.IsRoot] using h

@[simp]
private theorem cyclicGroupThree_complexRoot_pow_three :
    Cyclotomic.complexRoot 3 ^ 3 = 1 :=
  Cyclotomic.isPrimitiveRoot_complexRoot.pow_eq_one

@[simp]
private theorem cyclicGroupThree_complexRoot_pow_four :
    Cyclotomic.complexRoot 3 ^ 4 = Cyclotomic.complexRoot 3 := by
  rw [show 4 = 3 + 1 by omega, pow_add, cyclicGroupThree_complexRoot_pow_three, one_mul,
    pow_one]

@[simp]
private theorem cyclicGroupThree_complexRoot_pow_five :
    Cyclotomic.complexRoot 3 ^ 5 = Cyclotomic.complexRoot 3 ^ 2 := by
  rw [show 5 = 3 + 2 by omega, pow_add, cyclicGroupThree_complexRoot_pow_three, one_mul]

@[simp]
private theorem cyclicGroupThree_complexRoot_pow_six :
    Cyclotomic.complexRoot 3 ^ 6 = 1 := by
  rw [show 6 = 3 + 3 by omega, pow_add, cyclicGroupThree_complexRoot_pow_three, one_mul]

private theorem star_cyclicGroupThree_complexRoot :
    starRingEnd ℂ (Cyclotomic.complexRoot 3) = Cyclotomic.complexRoot 3 ^ 2 := by
  let z := Cyclotomic.complexRoot 3
  have hz : IsPrimitiveRoot z 3 := Cyclotomic.isPrimitiveRoot_complexRoot
  have hn : ‖z‖ = 1 := hz.norm'_eq_one (by norm_num)
  have hnorm : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hn]
    norm_num
  have hmul : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, hnorm]
    norm_num
  apply mul_left_cancel₀ (hz.ne_zero (by norm_num))
  rw [hmul, ← pow_succ']
  exact hz.pow_eq_one.symm

/-- The embedded exact `C₃` table satisfies the character-table specification and therefore is
the complex character table up to a permutation of rows. -/
theorem isCharacterTableSpec_cyclicGroupThree :
    IsCharacterTableSpec (Multiplicative (ZMod 3))
      cyclicGroupThreeComplexCharacterTable where
  exists_degree i := by
    refine ⟨1, by simp, ?_, by simp⟩
    obtain ⟨i, rfl⟩ :=
      (finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses).surjective i
    rw [← (cyclicClassData 3).classOf_index (1 : Multiplicative (ZMod 3)),
      cyclicGroupThreeComplexCharacterTable_apply_classOf]
    rw [cyclicGroupThreeExactCharacterTable_index_one, map_one]
    norm_num
  sum_degree_sq := by
    rw [← (finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses).sum_comp]
    simp only [← (cyclicClassData 3).classOf_index (1 : Multiplicative (ZMod 3)),
      cyclicGroupThreeComplexCharacterTable_apply_classOf]
    simp_rw [cyclicGroupThreeExactCharacterTable_index_one, map_one]
    norm_num [Nat.card_eq_fintype_card, numClasses_cyclicClassData]
  row_orthonormal i j := by
    obtain ⟨i, rfl⟩ :=
      (finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses).surjective i
    obtain ⟨j, rfl⟩ :=
      (finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses).surjective j
    obtain ⟨i, rfl⟩ := cyclicGroupThreeClassIndexEquiv.symm.surjective i
    obtain ⟨j, rfl⟩ := cyclicGroupThreeClassIndexEquiv.symm.surjective j
    have hcard (k : CyclicGroupThreeClassIndex) :
        Nat.card ((cyclicClassData 3).classOf k).carrier = 1 := by
      rw [← (cyclicClassData 3).card_classFinset,
        card_classFinset_cyclicClassData]
    rw [← (cyclicClassData 3).equivConjClasses.sum_comp]
    simp only [(cyclicClassData 3).equivConjClasses_apply,
      cyclicGroupThreeComplexCharacterTable_apply_classOf, hcard, Nat.cast_one, one_mul,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    simp only [Equiv.apply_eq_iff_eq]
    rw [← cyclicGroupThreeClassIndexEquiv.symm.sum_comp, Fin.sum_univ_three]
    simp only [cyclicGroupThreeExactCharacterTable_apply_reindex]
    fin_cases i <;> fin_cases j <;>
      simp [star_cyclicGroupThree_complexRoot]
    all_goals ring_nf
    all_goals try rw [cyclicGroupThree_complexRoot_pow_three]
    all_goals try rw [cyclicGroupThree_complexRoot_pow_four]
    all_goals try rw [cyclicGroupThree_complexRoot_pow_five]
    all_goals try rw [cyclicGroupThree_complexRoot_pow_six]
    all_goals try norm_num
    all_goals (convert cyclicGroupThree_complexRoot_sq_add_complexRoot_add_one using 1; ring)
  row_eigen i := by
    obtain ⟨i, rfl⟩ :=
      (finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses).surjective i
    have heig : IsClassEigenrow ((cyclicClassData 3).reindexModularRow fun j =>
        Cyclotomic.complexEmbedding (cyclicGroupThreeExactCharacterTable i j)) :=
      ((cyclicClassData 3).isModularEigenrow_iff_isClassEigenrow _).mp <|
      (isModularEigenrow_cyclicGroupThreeExactCharacterTable i).map
        (Cyclotomic.complexEmbedding : Cyclotomic 3 →+* ℂ)
    suffices centralCharacterRow cyclicGroupThreeComplexCharacterTable
        (finCongr (cyclicClassData 3).numClasses_eq_card_conjClasses i) =
          (cyclicClassData 3).reindexModularRow fun j =>
            Cyclotomic.complexEmbedding (cyclicGroupThreeExactCharacterTable i j) by
      rwa [this]
    funext C
    obtain ⟨j, rfl⟩ := (cyclicClassData 3).equivConjClasses.surjective C
    rw [centralCharacterRow_apply, (cyclicClassData 3).equivConjClasses_apply,
      (cyclicClassData 3).reindexModularRow_classOf,
      cyclicGroupThreeComplexCharacterTable_apply_classOf,
      ← (cyclicClassData 3).classOf_index (1 : Multiplicative (ZMod 3)),
      cyclicGroupThreeComplexCharacterTable_apply_classOf,
      ← (cyclicClassData 3).card_classFinset,
      card_classFinset_cyclicClassData, Nat.cast_one, one_mul,
      cyclicGroupThreeExactCharacterTable_index_one, map_one, div_one]

end TauCeti
