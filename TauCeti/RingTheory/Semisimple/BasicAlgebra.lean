/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: `IsSemisimpleRing` and `IsReduced` are the two clauses of the definition below,
-- Artin--Wedderburn supplies the shape of the main equivalence, and the semisimplicity of the
-- quotient by the radical is what makes the definition usable over a finite-dimensional algebra.
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import TauCeti.RingTheory.Jacobson.FiniteDimensional
-- Non-public: used only inside proofs.  The matrix units produce the square-zero element that
-- rules out a block of size at least two, a one-by-one matrix ring collapses to its base ring, and
-- an equivalence of rings carries the Jacobson radical onto the Jacobson radical and so descends
-- to the quotients.
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Basic algebras

A ring `A` is **basic** when its quotient by the Jacobson radical, `A ⧸ Ring.jacobson A`, is a
finite product of division rings.  The definition states this as the quotient being *semisimple* and
*reduced*, which says the same thing (`TauCeti.isBasic_iff_pi_divisionRing`): Artin--Wedderburn
writes a semisimple ring as a finite product of matrix algebras over division rings, one block for
each simple module, and a matrix algebra of size at least two is never reduced, the matrix unit
`Eᵢⱼ` with `i ≠ j` being nonzero and square-zero.  So over a semisimple ring reducedness says
exactly that **every block has size one**, that is, that the ring is a product of division rings
rather than of matrix algebras over them; equivalently, that no indecomposable projective is
repeated in a decomposition of the regular module.

That reformulation is the main result.  Its ring-level form,
`TauCeti.isReduced_iff_pi_divisionRing`, holds for an arbitrary semisimple ring and mentions no
algebra structure.

The condition is aimed at a finite-dimensional algebra over a field, where the quotient by the
radical is semisimple because the algebra is Artinian: there the semisimplicity clause is automatic
and basicness is reducedness alone (`TauCeti.isBasic_iff_isReduced`), which is the form the roadmap
pins.  Outside that setting the clause has to be asked for: `ℤ` has zero Jacobson radical and is
reduced, but is not a product of division rings and is not a basic ring.

Basicness is the normalization step of Morita theory: every finite-dimensional algebra is Morita
equivalent to a basic one, obtained by keeping one indecomposable projective per simple module.
That reduction is not proved here.  The model example is on the quiver side: the path algebra of a
finite acyclic quiver is basic (`TauCeti.PathAlgebra.isBasic`).

## Main definitions

* `TauCeti.IsBasic`: a ring whose quotient by the Jacobson radical is semisimple and reduced.

## Main results

* `TauCeti.isBasic_def`: unfolding lemma for `TauCeti.IsBasic`.
* `TauCeti.RingEquiv.isBasic_iff`: basicness is invariant under a ring equivalence.
* `TauCeti.Matrix.isReduced_iff_subsingleton`: a matrix ring over a nonzero reduced semiring is
  reduced exactly when it has at most one index.
* `TauCeti.isReduced_iff_pi_divisionRing`: a semisimple ring is reduced if and only if it is a
  finite product of division rings.
* `TauCeti.isBasic_iff_pi_divisionRing`: a ring is basic if and only if its quotient by the
  Jacobson radical is a finite product of division rings.
* `TauCeti.isBasic_iff_isReduced`: a finite-dimensional algebra is basic if and only if its
  semisimple quotient is reduced.
* `TauCeti.isBasic_of_commRing`: a finite-dimensional commutative algebra is basic.

## Implementation notes

Mathlib's `Matrix.uniqueRingEquiv` fixes the `Fintype` structure on the one-element index type to
the one manufactured from `Unique`, so its type does not match a matrix ring formed with a `Fintype`
structure coming from elsewhere -- the two are equal but not definitionally so, and the
multiplication of a matrix ring depends on which one is used.  Both uses below therefore rewrite
along `Subsingleton.elim` first; the index types in question are a `Fin`-indexed one, as produced by
Artin--Wedderburn, and one carrying a `Fintype` hypothesis.

`TauCeti.IsBasic` keeps its body private; `TauCeti.isBasic_def` is the unfolding lemma through which
importing modules use the definition.

`TauCeti.IsBasic` takes only the ring, where the roadmap signature also carries a base field and
finite-dimensionality over it.  Neither appears in the condition, so the environment linter rejects
them as unused arguments; they are carried instead by `TauCeti.isBasic_iff_isReduced`, which
recovers the roadmap's formulation -- reducedness of the quotient -- under exactly those
hypotheses, and by nothing else.  Dropping them is what puts semisimplicity of the quotient into
the definition: over a finite-dimensional algebra it is automatic, but for a general ring
reducedness alone is strictly weaker than being a product of division rings.

## References

This implements the `IsBasic` target of the "Basic algebras and Morita reduction" item of Layer 3 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, together with the companion
lemma named there: a semisimple ring is a product of division rings if and only if it is reduced.
See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras I*, CUP (2006), Ch. I.6.
-/

public section

namespace TauCeti

universe u v w

/-! ### Reduced products and reduced matrix rings -/

open scoped Classical in
/-- **A factor of a reduced product is reduced.**  The witness is `Pi.single`: a nilpotent element
of one factor extends by zero to a nilpotent element of the product. -/
theorem isReduced_of_isReduced_pi {ι : Type w} {R : ι → Type u} [∀ i, MonoidWithZero (R i)]
    [IsReduced (∀ i, R i)] (i : ι) : IsReduced (R i) where
  eq_zero y hy := by
    obtain ⟨n, hn⟩ := hy
    have hx : (Pi.single i y : ∀ j, R j) ^ (n + 1) = 0 := by
      funext j
      rcases eq_or_ne i j with rfl | hj
      · simp [Pi.single_eq_same, pow_succ, hn]
      · simp [Pi.single_eq_of_ne (Ne.symm hj), zero_pow]
    simpa using congrFun (IsReduced.eq_zero _ ⟨n + 1, hx⟩) i

/-- **A matrix ring of size at least two is never reduced.**  For `i ≠ j` the matrix unit `Eᵢⱼ` is
nonzero and squares to zero, so a reduced matrix ring over a nonzero semiring has at most one
index. -/
theorem Matrix.subsingleton_of_isReduced {m : Type w} {A : Type u} [DecidableEq m] [Fintype m]
    [Semiring A] [Nontrivial A] [IsReduced (Matrix m m A)] : Subsingleton m := by
  refine ⟨fun i j => by_contra fun hij => ?_⟩
  have hji : j ≠ i := Ne.symm hij
  have hsq : (_root_.Matrix.single i j 1 : Matrix m m A) ^ 2 = 0 := by
    rw [pow_two]; simp [hji]
  have h0 : (_root_.Matrix.single i j 1 : Matrix m m A) = 0 := IsReduced.eq_zero _ ⟨2, hsq⟩
  have h1 := congrFun (congrFun h0 i) j
  simp at h1

/-- **A matrix ring over a nonzero reduced semiring is reduced exactly in size at most one.**  In
one direction this is `TauCeti.Matrix.subsingleton_of_isReduced`; in the other, a matrix ring on an
empty index is the zero ring, and on a one-element index it is the base semiring. -/
@[simp]
theorem Matrix.isReduced_iff_subsingleton {m : Type w} {A : Type u} [DecidableEq m]
    [inst : Fintype m] [Semiring A] [Nontrivial A] [IsReduced A] :
    IsReduced (Matrix m m A) ↔ Subsingleton m := by
  refine ⟨fun _ => Matrix.subsingleton_of_isReduced (A := A), fun hm => ?_⟩
  rcases isEmpty_or_nonempty m with hempty | ⟨⟨i⟩⟩
  · exact ⟨fun x _ => funext fun i => (hempty.false i).elim⟩
  · have : Unique m := uniqueOfSubsingleton i
    let e : Matrix m m A ≃+* A := by
      have he : inst = Unique.fintype := Subsingleton.elim _ _
      rw [he]
      exact _root_.Matrix.uniqueRingEquiv
    exact isReduced_of_injective e e.injective

/-! ### Reduced semisimple rings are products of division rings -/

/-- **A semisimple ring is reduced exactly when it is a finite product of division rings.**  Read
through Artin--Wedderburn, reducedness says that every block `Matₙᵢ(Dᵢ)` has `nᵢ = 1`, a larger
matrix block carrying a nonzero square-zero matrix unit; the converse is immediate, a division ring
having no nonzero nilpotent element. -/
theorem isReduced_iff_pi_divisionRing (R : Type u) [Ring R] [IsSemisimpleRing R] :
    IsReduced R ↔ ∃ (n : ℕ) (D : Fin n → Type u) (_ : ∀ i, DivisionRing (D i)),
      Nonempty (R ≃+* ∀ i, D i) := by
  refine ⟨fun _ => ?_, fun ⟨n, D, hD, ⟨e⟩⟩ => isReduced_of_injective (e : R ≃+* ∀ i, D i)
    e.injective⟩
  obtain ⟨n, D, d, hD, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  have hpi : IsReduced (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
    isReduced_of_injective (e.symm : (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) ≃+* R)
      e.symm.injective
  have huniq : ∀ i, Unique (Fin (d i)) := fun i => by
    have hfac : IsReduced (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      isReduced_of_isReduced_pi (R := fun j => Matrix (Fin (d j)) (Fin (d j)) (D j)) i
    have hsub : Subsingleton (Fin (d i)) := Matrix.subsingleton_of_isReduced (A := D i)
    exact uniqueOfSubsingleton (⟨0, (hd i).pos⟩ : Fin (d i))
  refine ⟨n, D, hD, ⟨e.trans <| RingEquiv.piCongrRight fun i => ?_⟩⟩
  have hu := huniq i
  have he : Fin.fintype (d i) = Unique.fintype := Subsingleton.elim _ _
  rw [he]
  exact _root_.Matrix.uniqueRingEquiv

/-! ### Basic algebras -/

/-- A ring is **basic** when its quotient by the Jacobson radical is a finite product of division
rings, stated as that quotient being semisimple and reduced; the two readings agree by
`TauCeti.isBasic_iff_pi_divisionRing`.  For a finite-dimensional algebra over a field the quotient
is semisimple anyway, and the condition is reducedness alone -- every Wedderburn block has size one
-- which is `TauCeti.isBasic_iff_isReduced`. -/
def IsBasic (A : Type v) [Ring A] : Prop :=
  IsSemisimpleRing (A ⧸ Ring.jacobson A) ∧ IsReduced (A ⧸ Ring.jacobson A)

/-- Unfolding lemma for `TauCeti.IsBasic`: it is semisimplicity together with reducedness of the
quotient by the Jacobson radical. -/
@[simp]
theorem isBasic_def (A : Type v) [Ring A] :
    IsBasic A ↔ IsSemisimpleRing (A ⧸ Ring.jacobson A) ∧ IsReduced (A ⧸ Ring.jacobson A) := Iff.rfl

/-- **Basicness is invariant under ring equivalence.**  A ring equivalence carries the Jacobson
radical onto the Jacobson radical, hence descends to an equivalence of the quotients, along which
both semisimplicity and reducedness transport. -/
theorem RingEquiv.isBasic_iff {A : Type v} {B : Type w} [Ring A] [Ring B] (e : A ≃+* B) :
    IsBasic A ↔ IsBasic B := by
  have hmap : Ring.jacobson B = (Ring.jacobson A).map (e : A →+* B) :=
    le_antisymm (by rw [Ideal.map_comap_of_equiv]; exact Ring.le_comap_jacobson (e.symm : B →+* A))
      (Ideal.map_le_iff_le_comap.mpr (Ring.le_comap_jacobson (e : A →+* B)))
  let q : (A ⧸ Ring.jacobson A) ≃+* (B ⧸ Ring.jacobson B) :=
    Ideal.quotientEquiv _ _ e hmap
  refine and_congr q.isSemisimpleRing_iff ⟨fun _ => ?_, fun _ => ?_⟩
  · exact isReduced_of_injective q.symm q.symm.injective
  · exact isReduced_of_injective q q.injective

/-- **A ring is basic exactly when its quotient by the Jacobson radical is a finite product of
division rings.**  This is `TauCeti.isReduced_iff_pi_divisionRing`, read at that quotient; the
semisimplicity asked for by the definition is what makes the criterion applicable, and it comes
back from a product of division rings, each of which is a semisimple ring. -/
theorem isBasic_iff_pi_divisionRing (A : Type v) [Ring A] :
    IsBasic A ↔ ∃ (n : ℕ) (D : Fin n → Type v) (_ : ∀ i, DivisionRing (D i)),
      Nonempty ((A ⧸ Ring.jacobson A) ≃+* ∀ i, D i) := by
  refine ⟨fun ⟨_, h⟩ => (isReduced_iff_pi_divisionRing _).mp h, fun ⟨n, D, _, ⟨e⟩⟩ => ?_⟩
  have := e.symm.isSemisimpleRing
  exact ⟨this, isReduced_of_injective e e.injective⟩

/-- **A finite-dimensional algebra is basic exactly when its semisimple quotient is reduced.**  The
quotient by the radical is semisimple because a finite-dimensional algebra is Artinian, so that
half of `TauCeti.IsBasic` is automatic here and only reducedness is a condition; this is the form
the definition takes in the setting it is aimed at. -/
theorem isBasic_iff_isReduced (k : Type u) (A : Type v) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] :
    IsBasic A ↔ IsReduced (A ⧸ Ring.jacobson A) :=
  have := isSemisimpleRing_quotient_jacobson (K := k) (A := A)
  ⟨fun h => h.2, fun h => ⟨this, h⟩⟩

/-- **A finite-dimensional commutative algebra is basic.**  Its quotient by the Jacobson radical is
semisimple, and a commutative semisimple ring is reduced. -/
theorem isBasic_of_commRing (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [FiniteDimensional k A] : IsBasic A :=
  have := isSemisimpleRing_quotient_jacobson (K := k) (A := A)
  ⟨this, inferInstance⟩

end TauCeti
