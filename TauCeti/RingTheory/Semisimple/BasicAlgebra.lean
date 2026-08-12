/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: `IsReduced` is the content of the definition below, Artin--Wedderburn supplies the shape
-- of the main equivalence, the collapse of a one-by-one matrix ring is repackaged as an exported
-- definition, and the semisimplicity of the quotient by the radical is what makes the definition
-- usable.
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import TauCeti.RingTheory.Jacobson.FiniteDimensional
-- Non-public: used only inside proofs.  The matrix units produce the square-zero element that
-- rules out a block of size at least two, and the nilradical of a commutative ring is bounded by
-- its Jacobson radical.
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Basic algebras

A ring `A` is **basic** when its quotient by the Jacobson radical, `A ⧸ Ring.jacobson A`, is
*reduced*.  The condition is aimed at a finite-dimensional algebra over a field, where that quotient
is semisimple: Artin--Wedderburn writes it as a finite product of matrix algebras over division
rings, one block for each simple module, and a matrix algebra of size at least two is never reduced,
the matrix unit `Eᵢⱼ` with `i ≠ j` being nonzero and square-zero.  So for such an algebra
reducedness says exactly that **every block has size one**, that is, that the semisimple quotient is
a product of division rings rather than of matrix algebras over them; equivalently, that no
indecomposable projective is repeated in a decomposition of the regular module.

That reformulation is the main result.  Its ring-level form,
`TauCeti.isReduced_iff_exists_ringEquiv_pi_divisionRing`, holds for an arbitrary semisimple ring and
mentions no algebra structure; `TauCeti.isBasic_iff_exists_ringEquiv_pi_divisionRing` reads it at
the semisimple quotient of a finite-dimensional algebra, which is semisimple because that algebra
is Artinian.

Basicness is the normalization step of Morita theory: every finite-dimensional algebra is Morita
equivalent to a basic one, obtained by keeping one indecomposable projective per simple module.
That reduction is not proved here.  The model example is on the quiver side: the path algebra of a
finite acyclic quiver is basic (`TauCeti.PathAlgebra.isBasic`).

## Main definitions

* `TauCeti.IsBasic`: a ring whose quotient by the Jacobson radical is reduced.
* `TauCeti.Matrix.ringEquivOfUnique`: the one-by-one matrix ring over `A`, as `A`, with its two
  evaluation lemmas.

## Main results

* `TauCeti.Matrix.isReduced_iff_subsingleton`: a matrix ring over a nonzero reduced ring is reduced
  exactly when it has at most one index.
* `TauCeti.isReduced_iff_exists_ringEquiv_pi_divisionRing`: a semisimple ring is reduced if and only
  if it is a finite product of division rings.
* `TauCeti.isBasic_iff_exists_ringEquiv_pi_divisionRing`: a finite-dimensional algebra is basic if
  and only if its semisimple quotient is a finite product of division rings.
* `TauCeti.isBasic_iff_isReduced`: the definitional unfolding of `TauCeti.IsBasic`.
* `TauCeti.isBasic_of_commRing`: a commutative ring is basic.

## Implementation notes

`TauCeti.Matrix.ringEquivOfUnique` repeats Mathlib's `Matrix.uniqueRingEquiv` with the `Fintype`
structure on the index type taken from the context rather than manufactured from `Unique`.  The two
`Fintype` structures are equal, but not definitionally so, and the multiplication of a matrix ring
depends on which one is used; a `Fin`-indexed matrix ring, as produced by Artin--Wedderburn, carries
the former.

`TauCeti.IsBasic` takes only the ring, where the roadmap signature also carries a base field and
finite-dimensionality over it.  Neither appears in the condition, so the environment linter rejects
them as unused arguments; they are carried instead by
`TauCeti.isBasic_iff_exists_ringEquiv_pi_divisionRing`, the result that needs them, and by nothing
else.

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

/-- The one-by-one matrix ring over `A` is `A`.  This is Mathlib's `Matrix.uniqueRingEquiv` with the
`Fintype` structure on the index taken from the ambient context instead of from `Unique`; see the
implementation notes. -/
def Matrix.ringEquivOfUnique {m : Type w} {A : Type u} [Fintype m] [Unique m]
    [NonUnitalNonAssocSemiring A] : Matrix m m A ≃+* A := by
  have he : ‹Fintype m› = Unique.fintype := Subsingleton.elim _ _
  rw [he]
  exact _root_.Matrix.uniqueRingEquiv

@[simp]
theorem Matrix.ringEquivOfUnique_apply {m : Type w} {A : Type u} [inst : Fintype m] [Unique m]
    [NonUnitalNonAssocSemiring A] (M : Matrix m m A) :
    Matrix.ringEquivOfUnique M = M default default := by
  have he : inst = Unique.fintype := Subsingleton.elim _ _
  subst he
  rfl

@[simp]
theorem Matrix.ringEquivOfUnique_symm_apply {m : Type w} {A : Type u} [inst : Fintype m] [Unique m]
    [NonUnitalNonAssocSemiring A] (a : A) (i j : m) :
    (Matrix.ringEquivOfUnique (m := m)).symm a i j = a := by
  have he : inst = Unique.fintype := Subsingleton.elim _ _
  subst he
  rfl

/-- **A matrix ring of size at least two is never reduced.**  For `i ≠ j` the matrix unit `Eᵢⱼ` is
nonzero and squares to zero, so a reduced matrix ring over a nonzero ring has at most one index. -/
theorem Matrix.subsingleton_of_isReduced {m : Type w} {A : Type u} [DecidableEq m] [Fintype m]
    [Ring A] [Nontrivial A] [IsReduced (Matrix m m A)] : Subsingleton m := by
  refine ⟨fun i j => by_contra fun hij => ?_⟩
  have hji : j ≠ i := Ne.symm hij
  have hsq : (_root_.Matrix.single i j 1 : Matrix m m A) ^ 2 = 0 := by
    rw [pow_two]; simp [hji]
  have h0 : (_root_.Matrix.single i j 1 : Matrix m m A) = 0 := IsReduced.eq_zero _ ⟨2, hsq⟩
  have h1 := congrFun (congrFun h0 i) j
  simp at h1

/-- **A matrix ring over a nonzero reduced ring is reduced exactly in size at most one.**  In one
direction this is `TauCeti.Matrix.subsingleton_of_isReduced`; in the other, a matrix ring on an
empty index is the zero ring, and on a one-element index it is the base ring. -/
theorem Matrix.isReduced_iff_subsingleton {m : Type w} {A : Type u} [DecidableEq m] [Fintype m]
    [Ring A] [Nontrivial A] [IsReduced A] :
    IsReduced (Matrix m m A) ↔ Subsingleton m := by
  refine ⟨fun _ => Matrix.subsingleton_of_isReduced (A := A), fun hm => ?_⟩
  rcases isEmpty_or_nonempty m with hempty | ⟨⟨i⟩⟩
  · exact ⟨fun x _ => funext fun i => (hempty.false i).elim⟩
  · have : Unique m := uniqueOfSubsingleton i
    exact isReduced_of_injective (Matrix.ringEquivOfUnique (m := m) (A := A))
      Matrix.ringEquivOfUnique.injective

/-! ### Reduced semisimple rings are products of division rings -/

/-- **A semisimple ring is reduced exactly when it is a finite product of division rings.**  Read
through Artin--Wedderburn, reducedness says that every block `Matₙᵢ(Dᵢ)` has `nᵢ = 1`, a larger
matrix block carrying a nonzero square-zero matrix unit; the converse is immediate, a division ring
having no nonzero nilpotent element. -/
theorem isReduced_iff_exists_ringEquiv_pi_divisionRing (R : Type u) [Ring R] [IsSemisimpleRing R] :
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
  exact ⟨n, D, hD, ⟨e.trans <| RingEquiv.piCongrRight fun i =>
    @Matrix.ringEquivOfUnique (Fin (d i)) (D i) inferInstance (huniq i) inferInstance⟩⟩

/-! ### Basic algebras -/

/-- A ring is **basic** when its quotient by the Jacobson radical is reduced.  For a
finite-dimensional algebra over a field, where that quotient is semisimple, this says that the
quotient is a product of division rings rather than of matrix algebras over them, so that no
Wedderburn block is repeated; see `TauCeti.isBasic_iff_exists_ringEquiv_pi_divisionRing`. -/
def IsBasic (A : Type v) [Ring A] : Prop :=
  IsReduced (A ⧸ Ring.jacobson A)

/-- Unfolding of `TauCeti.IsBasic`: a ring is basic exactly when its quotient by the Jacobson
radical is reduced. -/
theorem isBasic_iff_isReduced (A : Type v) [Ring A] :
    IsBasic A ↔ IsReduced (A ⧸ Ring.jacobson A) := Iff.rfl

/-- **A finite-dimensional algebra is basic exactly when its semisimple quotient is a finite product
of division rings.**  This is `TauCeti.isReduced_iff_exists_ringEquiv_pi_divisionRing`, read at the
quotient by the radical; that quotient is semisimple because a finite-dimensional algebra is
Artinian. -/
theorem isBasic_iff_exists_ringEquiv_pi_divisionRing (k : Type u) (A : Type v) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] :
    IsBasic A ↔ ∃ (n : ℕ) (D : Fin n → Type v) (_ : ∀ i, DivisionRing (D i)),
      Nonempty ((A ⧸ Ring.jacobson A) ≃+* ∀ i, D i) :=
  have := isSemisimpleRing_quotient_jacobson (K := k) (A := A)
  isReduced_iff_exists_ringEquiv_pi_divisionRing (A ⧸ Ring.jacobson A)

/-- **A commutative ring is basic.**  Its quotient by the Jacobson radical has vanishing Jacobson
radical, and in a commutative ring the nilradical is contained in the Jacobson radical. -/
theorem isBasic_of_commRing (A : Type v) [CommRing A] : IsBasic A :=
  (nilradical_eq_bot_iff (R := A ⧸ Ring.jacobson A)).mp <| le_bot_iff.mp <|
    (nilradical_le_jacobson _).trans (Ring.jacobson_quotient_jacobson A).le

end TauCeti
