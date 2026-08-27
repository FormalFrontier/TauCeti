/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic

/-!
# Over a finite constant field there are finitely many places of bounded degree

Let `F / k` be an algebraic function field whose constant field `k` is **finite**. Then for every
bound `r` only finitely many places of `F / k` have degree at most `r`.

On the rational function field this is a count of polynomials: by the classification of the
places of `k(x)` they are the place at infinity together with the monic irreducible polynomials,
and the degree of the place of `q` is `deg q`, so a bound on the degree of a place is a bound on
the degree of a polynomial over a finite field. In general one chooses a transcendental `x`,
which makes `F` a finite extension of `k(x)`; a place of `F` is at least as large as the place of
`k(x)` below it (`TauCeti.Place.degree_restrict_le`), and each place of `k(x)` has only finitely
many extensions (`TauCeti.Place.finite_setOf_restrict_eq`), so the bounded-degree places of `F`
sit in finitely many finite fibres.

This is the counting input of Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed.,
Lemma 5.1.1, on the way to the finiteness of the degree-zero divisor class group; it is not the
lemma itself, which counts effective divisors.

## Main results

* `TauCeti.Place.finite_setOf_degree_le_ratFunc`: the bounded-degree places of `k(x)`.
* `TauCeti.Place.finite_setOf_degree_le`: the bounded-degree places of an arbitrary algebraic
  function field over a finite constant field.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section V.1.
-/

public section

namespace TauCeti

namespace Place

open IntermediateField Polynomial

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- Over a finite field there are only finitely many polynomials of bounded degree. -/
private theorem finite_setOf_natDegree_le [Finite k] (r : ℕ) :
    {p : k[X] | p.natDegree ≤ r}.Finite := by
  have hfin : Finite (Polynomial.degreeLT k (r + 1)) :=
    Finite.of_equiv _ (Polynomial.degreeLTEquiv k (r + 1)).toEquiv.symm
  refine Set.Finite.subset (Set.toFinite (Polynomial.degreeLT k (r + 1) : Set k[X])) ?_
  intro p hp
  refine Polynomial.mem_degreeLT.mpr (lt_of_le_of_lt Polynomial.degree_le_natDegree ?_)
  exact_mod_cast Nat.lt_succ_of_le hp

/-- **The places of the rational function field of bounded degree are finite in number** when the
constant field is finite: under the classification of the places of `k(x)` they are the place at
infinity and the monic irreducible polynomials of degree at most `r`. -/
theorem finite_setOf_degree_le_ratFunc (k : Type u) [Field k] [Finite k] (r : ℕ) :
    {P : Place k (RatFunc k) | P.degree ≤ r}.Finite := by
  have hmonic : {q : {q : k[X] // q.Monic ∧ Irreducible q} | (q : k[X]).natDegree ≤ r}.Finite :=
    (finite_setOf_natDegree_le r).preimage Subtype.val_injective.injOn
  have hopt : {o : Option {q : k[X] // q.Monic ∧ Irreducible q} |
      (ratFuncEquivMonicIrreducible k o).degree ≤ r}.Finite := by
    refine Set.Finite.subset ((hmonic.image some).insert none) ?_
    rintro (_ | q) ho
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨q, by simpa using ho, rfl⟩
  refine (hopt.image (ratFuncEquivMonicIrreducible k)).subset fun P hP ↦ ?_
  exact ⟨(ratFuncEquivMonicIrreducible k).symm P, by simpa using hP, by simp⟩

/-- The bounded-degree places of a finite extension of a base field whose own bounded-degree
places are finite in number. -/
private theorem finite_setOf_degree_le_of_tower {K : Type*} [Field K] [Algebra k K]
    [Algebra K F] [IsScalarTower k K F] [FiniteDimensional K F] (r : ℕ)
    (hK : {P : Place k K | P.degree ≤ r}.Finite) :
    {P : Place k F | P.degree ≤ r}.Finite := by
  refine (hK.biUnion fun P _ ↦ finite_setOf_restrict_eq k K P).subset fun P hP ↦ ?_
  exact Set.mem_biUnion (le_trans (degree_restrict_le k K P) hP) rfl

/-- **Over a finite constant field an algebraic function field has only finitely many places of
degree at most `r`** (Stichtenoth, the counting input of Lemma 5.1.1). -/
theorem finite_setOf_degree_le (hF : IsFunctionField k F) [Finite k] (r : ℕ) :
    {P : Place k F | P.degree ≤ r}.Finite := by
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  let e := RatFunc.algEquivOfTranscendental x hx
  let : Algebra (RatFunc k) k⟮x⟯ := e.toRingEquiv.toRingHom.toAlgebra
  let : Algebra (RatFunc k) F :=
    ((IsScalarTower.toAlgHom k k⟮x⟯ F).comp e.toAlgHom).toRingHom.toAlgebra
  have : IsScalarTower (RatFunc k) k⟮x⟯ F := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k (RatFunc k) F :=
    .of_algebraMap_eq fun c ↦
      (((IsScalarTower.toAlgHom k k⟮x⟯ F).comp e.toAlgHom).commutes c).symm
  have : Module.Finite (RatFunc k) k⟮x⟯ :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc k) k⟮x⟯) e.surjective
  have : FiniteDimensional (RatFunc k) F := Module.Finite.trans k⟮x⟯ F
  exact finite_setOf_degree_le_of_tower r (finite_setOf_degree_le_ratFunc k r)

end Place

end TauCeti
