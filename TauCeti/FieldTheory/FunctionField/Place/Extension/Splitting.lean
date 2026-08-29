/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois

/-!
# Places that split completely in an extension of function fields

Let `F' / k'` be a finite extension of `F / k`. A place `P` of `F / k` **splits completely**
when it has `[F' : F]` distinct extensions to `F' / k'`, the largest number allowed by the
fundamental inequality. This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed.,
Definition 3.1.13.

For a separable extension, the fundamental identity

`sum_{P' | P} e(P' | P) * f(P' | P) = [F' : F]`

shows that complete splitting is equivalent to every place above `P` having ramification index
and relative degree both equal to one. In the Galois case these invariants are constant on the
fibre, so it is enough to check either one place above `P`. Equivalently, the decomposition group
of such a place is trivial.

## Main definitions

* `TauCeti.Place.IsSplitCompletely`: a place has `[F' : F]` extensions.

## Main results

* `TauCeti.Place.isSplitCompletely_iff_forall_ramificationIdx_eq_one_and_relativeDegree_eq_one`:
  the non-Galois characterization by trivial ramification and residue extensions.
* `TauCeti.Place.isSplitCompletely_iff_ramificationIdx_eq_one_and_relativeDegree_eq_one`:
  in a Galois extension it is enough to test one place in the fibre.
* `TauCeti.Place.isSplitCompletely_iff_decompositionSubgroup_eq_bot`: in a Galois extension,
  complete splitting is equivalent to a trivial decomposition group.

## Provenance

The orbit--stabilizer proof of the Galois criterion follows the existing number-field analogue
`NumberField.ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot` in
`TauCeti/NumberTheory/NumberField/SplitsCompletely.lean`. The non-Galois criterion is proved
directly from the function-field fundamental identity.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.1 and III.7.
-/

public section

open scoped Pointwise

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [Algebra.IsIntegral F F']

/-- A place `P` of `F / k` **splits completely** in `F' / k'` if it has `[F' : F]`
distinct extensions to `F' / k'` (Stichtenoth, Definition 3.1.13). This is the maximal possible
cardinality by `TauCeti.Place.ncard_setOf_restrict_eq_le_finrank`. -/
def IsSplitCompletely (P : Place k F) : Prop :=
  FiniteDimensional F F' ∧
    {P' : Place k' F' | P'.restrict k F = P}.ncard = Module.finrank F F'

/-- The characteristic property of a place splitting completely. -/
theorem isSplitCompletely_iff (P : Place k F) :
    P.IsSplitCompletely (k' := k') (F' := F') ↔
      FiniteDimensional F F' ∧
        {P' : Place k' F' | P'.restrict k F = P}.ncard = Module.finrank F F' :=
  Iff.rfl

variable [FiniteDimensional F F']

/-- The definition of a place splitting completely, restated for rewriting. -/
theorem isSplitCompletely_def (P : Place k F) :
    P.IsSplitCompletely (k' := k') (F' := F') ↔
      {P' : Place k' F' | P'.restrict k F = P}.ncard = Module.finrank F F' := by
  rw [IsSplitCompletely, and_iff_right]
  infer_instance

/-- A place does not split completely exactly when the number of places above it is strictly
smaller than the extension degree. -/
theorem not_isSplitCompletely_iff_ncard_lt (P : Place k F) :
    ¬P.IsSplitCompletely (k' := k') (F' := F') ↔
      {P' : Place k' F' | P'.restrict k F = P}.ncard < Module.finrank F F' := by
  rw [isSplitCompletely_def]
  have hle := ncard_setOf_restrict_eq_le_finrank (k' := k') (F' := F') k F P
  omega

private theorem IsSplitCompletely.ramificationIdx_eq_one_and_relativeDegree_eq_one
    {P : Place k F} (hP : P.IsSplitCompletely (k' := k') (F' := F'))
    {P' : Place k' F'} (hP' : P'.restrict k F = P) :
    ramificationIdx F P' = 1 ∧ relativeDegree k F P' = 1 := by
  classical
  let s := (finite_setOf_restrict_eq (k' := k') (F' := F') k F P).toFinset
  have hs : ∀ Q : Place k' F', Q ∈ s ↔ Q.restrict k F = P :=
    fun Q ↦ Set.Finite.mem_toFinset _
  have hcard : s.card = Module.finrank F F' := by
    rw [← Set.ncard_eq_toFinset_card _ (finite_setOf_restrict_eq k F P)]
    exact (isSplitCompletely_def P).mp hP
  have hone : ∀ Q ∈ s, 1 ≤ ramificationIdx F Q * relativeDegree k F Q := fun Q _ ↦
    Nat.one_le_iff_ne_zero.mpr <| Nat.mul_ne_zero (ramificationIdx_pos F Q).ne'
      (Nat.one_le_iff_ne_zero.mp (one_le_relativeDegree k F Q))
  have hle := sum_ramificationIdx_mul_relativeDegree_le_finrank k F P s
    fun Q hQ ↦ (hs Q).mp hQ
  have hEqSum : ∑ _Q ∈ s, (1 : ℕ) =
      ∑ Q ∈ s, ramificationIdx F Q * relativeDegree k F Q := by
    apply Nat.le_antisymm
    · simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
        Finset.card_nsmul_le_sum s
          (fun Q ↦ ramificationIdx F Q * relativeDegree k F Q) 1 hone
    · simpa only [Finset.sum_const, smul_eq_mul, mul_one, hcard] using hle
  have hterm := (Finset.sum_eq_sum_iff_of_le hone).mp hEqSum P' ((hs P').mpr hP')
  exact ⟨Nat.eq_one_of_mul_eq_one_right hterm.symm,
    Nat.eq_one_of_mul_eq_one_left hterm.symm⟩

/-- A place above a completely split place has ramification index one. -/
theorem IsSplitCompletely.ramificationIdx_eq_one {P : Place k F}
    (hP : P.IsSplitCompletely (k' := k') (F' := F')) {P' : Place k' F'}
    (hP' : P'.restrict k F = P) :
    ramificationIdx F P' = 1 :=
  (hP.ramificationIdx_eq_one_and_relativeDegree_eq_one hP').1

/-- A place above a completely split place has relative residue degree one. -/
theorem IsSplitCompletely.relativeDegree_eq_one {P : Place k F}
    (hP : P.IsSplitCompletely (k' := k') (F' := F')) {P' : Place k' F'}
    (hP' : P'.restrict k F = P) :
    relativeDegree k F P' = 1 :=
  (hP.ramificationIdx_eq_one_and_relativeDegree_eq_one hP').2

/-- At a place above a completely split place, the map between residue fields is bijective. -/
theorem IsSplitCompletely.bijective_algebraMap_residueField (P' : Place k' F')
    (hP : (P'.restrict k F).IsSplitCompletely (k' := k') (F' := F')) :
    Function.Bijective
      (algebraMap (P'.restrict k F).ResidueField P'.ResidueField) := by
  have hfinrank : Module.finrank (P'.restrict k F).ResidueField P'.ResidueField = 1 := by
    rw [← relativeDegree_def k F P']
    exact hP.relativeDegree_eq_one rfl
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank

section FundamentalIdentity

variable [Algebra.IsIntegral k k'] [Algebra.IsSeparable F F']

/-- **Complete splitting is equivalent to trivial ramification and residue extensions at every
place above `P`** (Stichtenoth, Definition 3.1.13 and Theorem 3.1.11).

No Galois hypothesis is needed: if the number of summands in the fundamental identity already
equals `[F' : F]`, then every positive summand `e(P' | P) * f(P' | P)` must equal one. -/
theorem isSplitCompletely_iff_forall_ramificationIdx_eq_one_and_relativeDegree_eq_one
    (P : Place k F) :
    P.IsSplitCompletely (k' := k') (F' := F') ↔
      ∀ P' : Place k' F', P'.restrict k F = P →
      ramificationIdx F P' = 1 ∧ relativeDegree k F P' = 1 := by
  classical
  let s := (finite_setOf_restrict_eq (k' := k') (F' := F') k F P).toFinset
  have hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P :=
    fun P' ↦ Set.Finite.mem_toFinset _
  have hsum := sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable k F P hs
  constructor
  · intro hsplit P' hP'
    exact hsplit.ramificationIdx_eq_one_and_relativeDegree_eq_one hP'
  · intro htrivial
    rw [isSplitCompletely_def, Set.ncard_eq_toFinset_card _
      (finite_setOf_restrict_eq k F P)]
    calc
      s.card = ∑ _P' ∈ s, (1 : ℕ) := by simp
      _ = ∑ P' ∈ s, ramificationIdx F P' * relativeDegree k F P' :=
        Finset.sum_congr rfl fun P' hP' ↦ by
          obtain ⟨he, hf⟩ := htrivial P' ((hs P').mp hP')
          rw [he, hf]
      _ = Module.finrank F F' := hsum

end FundamentalIdentity

section Galois

variable [IsGalois F F']

/-- **In a finite Galois extension, one place detects complete splitting** (Stichtenoth,
Corollary 3.7.2): the place below `P'` splits completely exactly when the common ramification
index and relative degree on its fibre are both one. -/
theorem isSplitCompletely_iff_ramificationIdx_eq_one_and_relativeDegree_eq_one
    (P' : Place k F') :
    (P'.restrict k F).IsSplitCompletely (k' := k) (F' := F') ↔
      ramificationIdx F P' = 1 ∧ relativeDegree k F P' = 1 := by
  rw [isSplitCompletely_iff_forall_ramificationIdx_eq_one_and_relativeDegree_eq_one]
  refine ⟨fun h ↦ h P' rfl, fun h Q hQ ↦ ?_⟩
  rw [ramificationIdx_eq_of_restrict_eq hQ, relativeDegree_eq_of_restrict_eq hQ]
  exact h

/-- **Complete splitting is equivalent to a trivial stabilizer** in a finite Galois extension.
The fibre of restriction is the orbit of `P'`, so this is the orbit--stabilizer form of complete
splitting. -/
theorem isSplitCompletely_iff_stabilizer_eq_bot (P' : Place k F') :
    (P'.restrict k F).IsSplitCompletely (k' := k) (F' := F') ↔
      MulAction.stabilizer (F' ≃ₐ[F] F') P' = ⊥ := by
  let _ := Fintype.ofFinite (F' ≃ₐ[F] F')
  let _ := (Finite.finite_mulAction_orbit (M := F' ≃ₐ[F] F') P').fintype
  let _ := Fintype.ofFinite (MulAction.stabilizer (F' ≃ₐ[F] F') P')
  have horbit : MulAction.orbit (F' ≃ₐ[F] F') P' =
      {Q : Place k F' | Q.restrict k F = P'.restrict k F} :=
    (setOf_restrict_eq_eq_orbit P').symm
  have hkey : {Q : Place k F' | Q.restrict k F = P'.restrict k F}.ncard *
      Nat.card (MulAction.stabilizer (F' ≃ₐ[F] F') P') = Module.finrank F F' := by
    rw [← Nat.card_coe_set_eq, ← horbit, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, MulAction.card_orbit_mul_card_stabilizer_eq_card_group,
      ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  have hpos : 0 < Module.finrank F F' := Module.finrank_pos
  constructor
  · intro hsplit
    rw [isSplitCompletely_def] at hsplit
    rw [hsplit] at hkey
    have hcard : Nat.card (MulAction.stabilizer (F' ≃ₐ[F] F') P') = 1 :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hkey)
    exact Subgroup.card_eq_one.mp hcard
  · intro hstabilizer
    rw [hstabilizer] at hkey
    rw [isSplitCompletely_def]
    simpa using hkey

/-- **Complete splitting is equivalent to a trivial decomposition group** in a finite Galois
extension (Stichtenoth, Definitions 3.1.13 and 3.8.1). -/
theorem isSplitCompletely_iff_decompositionSubgroup_eq_bot (P' : Place k F') :
    (P'.restrict k F).IsSplitCompletely (k' := k) (F' := F') ↔
      P'.integers.decompositionSubgroup F = ⊥ := by
  rw [isSplitCompletely_iff_stabilizer_eq_bot, stabilizer_eq_decompositionSubgroup]

end Galois

end Place

end TauCeti
