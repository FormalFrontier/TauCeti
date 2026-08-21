/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.RepresentationTheory.Quiver.Radical
public import TauCeti.RingTheory.Semisimple.BasicAlgebra

/-!
# The semisimple quotient of a path algebra

Killing the arrows of a quiver leaves its vertices. This file makes that precise at the level of
algebras: reading off the coordinates of an element of `pathAlgebra k Q` on the trivial paths is an
algebra homomorphism `TauCeti.PathAlgebra.trivialCoeff` onto the product algebra `Q → k`, and its
kernel is exactly the arrow ideal. So the arrow ideal is the kernel of a map onto a product of
copies of the base semiring, and

`pathAlgebra k Q ⧸ arrowIdeal k Q ≃ₐ[k] (Q → k)`.

Multiplicativity is the one point that needs an argument, and it is the length filtration again:
concatenation adds lengths, so a product of paths is trivial only when both factors are, and the
coordinate of `f * g` on the trivial path at `v` is the product of the coordinates of `f` and of
`g` there.

For a **finite acyclic** quiver over a field the arrow ideal is the Jacobson radical
(`TauCeti.jacobson_pathAlgebra_eq_arrowIdeal`), so the displayed equivalence becomes

`pathAlgebra k Q ⧸ Ring.jacobson (pathAlgebra k Q) ≃ₐ[k] (Q → k)`,

which is the Wedderburn decomposition of the semisimple quotient: one block for each vertex, and
every block is the base field itself. In particular the semisimple quotient is commutative and
reduced -- the path algebra of a finite acyclic quiver is a **basic** algebra, with every matrix
block of size one -- and its dimension is the number of vertices.

## Main definitions

* `TauCeti.PathAlgebra.trivialCoeff`: the algebra homomorphism `pathAlgebra k Q →ₐ[k] (Q → k)`
  reading off the coordinates on the trivial paths.
* `TauCeti.PathAlgebra.quotientArrowIdealAlgEquiv`: the induced equivalence
  `pathAlgebra k Q ⧸ arrowIdeal k Q ≃ₐ[k] (Q → k)`.
* `TauCeti.PathAlgebra.quotientJacobsonAlgEquiv`: the same equivalence for a finite acyclic quiver
  over a field, stated for the Jacobson radical.

## Main results

* `TauCeti.PathAlgebra.trivialCoeff_surjective` and `TauCeti.PathAlgebra.ker_trivialCoeff`: the
  trivial-coefficient map is onto `Q → k` with kernel the arrow ideal.
* `TauCeti.PathAlgebra.isSemisimpleRing_quotient_jacobson`,
  `TauCeti.PathAlgebra.isReduced_quotient_jacobson` and `TauCeti.PathAlgebra.isBasic`: the quotient
  by the radical is semisimple and reduced, that is, **the path algebra of a finite acyclic quiver
  is a basic algebra**.
* `TauCeti.PathAlgebra.finrank_quotient_jacobson`: the semisimple quotient has dimension the number
  of vertices.

## Implementation notes

`trivialCoeff` is built by hand rather than through a universal property, the path algebra having
no `lift` yet. Its multiplicativity is proved by reducing to basis paths with
`TauCeti.PathAlgebra.induction_linear` and then splitting on composability, which is where
`TauCeti.Quiver.TotalPath.eq_nil_iff` -- an indexed path is the trivial path at `v` exactly when it
starts at `v` and has length zero -- does the work of avoiding dependent rewriting.

The construction needs no acyclicity and no field: it is stated for a commutative base semiring and
a quiver with finitely many vertices, which may well have infinitely many paths. Acyclicity enters
only to identify the arrow ideal with the Jacobson radical, which is imported.

## References

* [Quiver representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md),
  Layer 3, "The radical, packaged" and "Basic algebras and Morita reduction".
* I. Assem, D. Simson, A. Skowronski, *Elements of the Representation Theory of Associative
  Algebras I*, CUP (2006), Chapters II and III.
-/

public section

universe u v w

namespace TauCeti

namespace PathAlgebra

/-! ### The trivial-coefficient homomorphism -/

section TrivialCoeff

variable (k : Type w) (Q : Type u) [CommSemiring k] [Quiver.{v} Q]

variable {k Q} in
/-- The coordinate of a basis path on the trivial path at its own vertex. -/
private theorem repr_nil_single_self (v : Q) (c : k) :
    (pathAlgebraBasis k Q).repr
        (single (⟨v, v, Quiver.Path.nil⟩ : Quiver.TotalPath Q) c) ⟨v, v, Quiver.Path.nil⟩ = c := by
  rw [pathAlgebraBasis_repr_single, Finsupp.single_eq_same]

variable {k Q} in
/-- The coordinate of any other basis path on the trivial path at `v` vanishes. -/
private theorem repr_nil_single_of_ne {v : Q} {x : Quiver.TotalPath Q}
    (hx : x ≠ ⟨v, v, Quiver.Path.nil⟩) (c : k) :
    (pathAlgebraBasis k Q).repr (single x c) ⟨v, v, Quiver.Path.nil⟩ = 0 := by
  rw [pathAlgebraBasis_repr_single, Finsupp.single_eq_of_ne' hx]

variable {k Q} in
/-- Multiplicativity of the trivial coordinates on two basis paths: concatenation adds lengths, so
the concatenation is trivial exactly when both factors are. -/
private theorem repr_nil_single_mul_single (v : Q) (x y : Quiver.TotalPath Q) (a b : k) :
    (pathAlgebraBasis k Q).repr (single x a * single y b : pathAlgebra k Q)
        ⟨v, v, Quiver.Path.nil⟩ =
      (pathAlgebraBasis k Q).repr (single x a : pathAlgebra k Q) ⟨v, v, Quiver.Path.nil⟩ *
        (pathAlgebraBasis k Q).repr (single y b : pathAlgebra k Q) ⟨v, v, Quiver.Path.nil⟩ := by
  by_cases hx : x = (⟨v, v, Quiver.Path.nil⟩ : Quiver.TotalPath Q)
  · subst hx
    by_cases hy : y = (⟨v, v, Quiver.Path.nil⟩ : Quiver.TotalPath Q)
    · subst hy
      rw [single_mul_single_of_comp Quiver.Path.nil Quiver.Path.nil, Quiver.Path.nil_comp,
        repr_nil_single_self, repr_nil_single_self, repr_nil_single_self]
    · rw [repr_nil_single_of_ne hy, mul_zero]
      -- the product is either zero or the second factor again, and the second factor is not
      -- the trivial path at `v`
      by_cases hcomp : y.2.1 = v
      · obtain ⟨c, d, q⟩ := y
        subst hcomp
        rw [single_mul_single_of_comp Quiver.Path.nil q, Quiver.Path.comp_nil]
        exact repr_nil_single_of_ne hy _
      · rw [single_mul_single_of_not_composable hcomp, map_zero, Finsupp.zero_apply]
  · rw [repr_nil_single_of_ne hx, zero_mul]
    by_cases hcomp : y.2.1 = x.1
    · obtain ⟨s, t, p⟩ := x
      obtain ⟨c, d, q⟩ := y
      subst hcomp
      rw [single_mul_single_of_comp p q]
      refine repr_nil_single_of_ne (fun hz => hx ?_) _
      obtain ⟨hc, hlen⟩ := Quiver.TotalPath.eq_nil_iff.1 hz
      rw [Quiver.Path.length_comp, Nat.add_eq_zero_iff] at hlen
      refine Quiver.TotalPath.eq_nil_iff.2 ⟨?_, hlen.2⟩
      exact (q.eq_of_length_zero hlen.1).symm.trans hc
    · rw [single_mul_single_of_not_composable hcomp, map_zero, Finsupp.zero_apply]

variable {k Q} in
/-- Multiplicativity of the trivial coordinates. -/
private theorem repr_nil_mul (v : Q) (f g : pathAlgebra k Q) :
    (pathAlgebraBasis k Q).repr (f * g) ⟨v, v, Quiver.Path.nil⟩ =
      (pathAlgebraBasis k Q).repr f ⟨v, v, Quiver.Path.nil⟩ *
        (pathAlgebraBasis k Q).repr g ⟨v, v, Quiver.Path.nil⟩ := by
  induction f using induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ =>
    rw [add_mul, map_add, Finsupp.add_apply, ih₁, ih₂, map_add, Finsupp.add_apply, add_mul]
  | single x a =>
    induction g using induction_linear with
    | zero => simp
    | add g₁ g₂ ih₁ ih₂ =>
      rw [mul_add, map_add, Finsupp.add_apply, ih₁, ih₂, map_add, Finsupp.add_apply, mul_add]
    | single y b => exact repr_nil_single_mul_single v x y a b

variable [Finite Q]

variable {k Q} in
/-- The unit has coordinate `1` on every trivial path. -/
private theorem repr_nil_one (v : Q) :
    (pathAlgebraBasis k Q).repr (1 : pathAlgebra k Q) ⟨v, v, Quiver.Path.nil⟩ = 1 := by
  let := Fintype.ofFinite Q
  rw [one_def, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single v]
  · rw [vertexIdempotent_eq_single, repr_nil_single_self]
  · intro w _ hw
    rw [vertexIdempotent_eq_single]
    exact repr_nil_single_of_ne (fun h => hw (Quiver.TotalPath.eq_nil_iff.1 h).1) _
  · intro h
    exact absurd (Finset.mem_univ v) h

/-- **The trivial-coefficient homomorphism** of a path algebra: an element is sent to the family of
its coordinates on the trivial paths, one for each vertex. Concatenation adds lengths, so this is
multiplicative, and it is the projection onto the quotient by the arrow ideal. Over a field and for
a finite acyclic quiver that quotient is the semisimple quotient, but no such hypothesis is needed
here. -/
noncomputable def trivialCoeff : pathAlgebra k Q →ₐ[k] (Q → k) where
  toFun f v := (pathAlgebraBasis k Q).repr f ⟨v, v, Quiver.Path.nil⟩
  map_one' := funext fun v => repr_nil_one v
  map_mul' f g := funext fun v => repr_nil_mul v f g
  map_zero' := funext fun _ => by simp
  map_add' f g := funext fun _ => by simp
  commutes' r := funext fun v => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply, repr_nil_one v,
      smul_eq_mul, mul_one, Pi.algebraMap_apply, Algebra.algebraMap_self_apply]

variable {k Q}

/-- The trivial-coefficient homomorphism reads off a coordinate for the path basis. -/
@[simp]
theorem trivialCoeff_apply (f : pathAlgebra k Q) (v : Q) :
    trivialCoeff k Q f v = (pathAlgebraBasis k Q).repr f ⟨v, v, Quiver.Path.nil⟩ :=
  (rfl)

/-- A basis path of positive length has all its trivial coordinates zero. -/
@[simp]
theorem trivialCoeff_ofPath_of_length_pos {x : Quiver.TotalPath Q} (hx : 0 < x.2.2.length) :
    trivialCoeff k Q (ofPath x) = 0 := by
  funext v
  rw [trivialCoeff_apply, ofPath_eq_single]
  exact repr_nil_single_of_ne (fun h => (Nat.ne_of_gt hx) (Quiver.TotalPath.eq_nil_iff.1 h).2) 1

/-- An arrow has all its trivial coordinates zero: the arrows are what the trivial-coefficient
homomorphism kills. Deliberately not a `simp` lemma, `TauCeti.PathAlgebra.ofArrow_eq_ofPath`
already rewriting its left-hand side. -/
theorem trivialCoeff_ofArrow {a b : Q} (e : a ⟶ b) : trivialCoeff k Q (ofArrow e) = 0 := by
  rw [ofArrow_eq_ofPath]
  exact trivialCoeff_ofPath_of_length_pos (by simp)

/-- The vertex idempotent at `v` is sent to the indicator of `v`. -/
@[simp]
theorem trivialCoeff_vertexIdempotent [DecidableEq Q] (v : Q) :
    trivialCoeff k Q (vertexIdempotent k v) = Pi.single v 1 := by
  funext w
  rw [trivialCoeff_apply, vertexIdempotent_eq_single]
  by_cases hvw : v = w
  · subst hvw
    rw [repr_nil_single_self, Pi.single_eq_same]
  · rw [repr_nil_single_of_ne (fun h => hvw (Quiver.TotalPath.eq_nil_iff.1 h).1) 1,
      Pi.single_eq_of_ne (Ne.symm hvw)]

variable (k Q)

/-- **Every family of scalars is the family of trivial coordinates of an element**: the
trivial-coefficient homomorphism is onto, a preimage of `c` being `∑ᵥ c v • eᵥ`. -/
theorem trivialCoeff_surjective : Function.Surjective (trivialCoeff k Q) := by
  let := Fintype.ofFinite Q
  intro c
  refine ⟨∑ v : Q, c v • vertexIdempotent k v, funext fun w => ?_⟩
  rw [trivialCoeff_apply, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single w]
  · rw [vertexIdempotent_eq_single, smul_single, mul_one, repr_nil_single_self]
  · intro u _ hu
    rw [vertexIdempotent_eq_single, smul_single]
    exact repr_nil_single_of_ne (fun h => hu (Quiver.TotalPath.eq_nil_iff.1 h).1) _
  · intro h
    exact absurd (Finset.mem_univ w) h

/-- **The kernel of the trivial-coefficient homomorphism is the arrow ideal**: an element has all
its trivial coordinates zero exactly when it is supported on the paths of positive length. -/
theorem ker_trivialCoeff : RingHom.ker (trivialCoeff k Q) = arrowIdeal k Q := by
  ext f
  rw [RingHom.mem_ker, mem_arrowIdeal_iff_repr_nil, funext_iff]
  simp only [trivialCoeff_apply, Pi.zero_apply]

end TrivialCoeff

/-! ### The quotient by the arrow ideal -/

section Quotient

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q] [Finite Q]

/-- **Killing the arrows leaves the vertices**: the quotient of the path algebra by the arrow ideal
is the product of one copy of the base ring for each vertex. -/
noncomputable def quotientArrowIdealAlgEquiv :
    (pathAlgebra k Q ⧸ arrowIdeal k Q) ≃ₐ[k] (Q → k) :=
  (Ideal.quotientEquivAlgOfEq k (ker_trivialCoeff k Q).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (trivialCoeff_surjective k Q))

/-- The equivalence out of the quotient by the arrow ideal is the trivial-coefficient
homomorphism. -/
@[simp]
theorem quotientArrowIdealAlgEquiv_mk (f : pathAlgebra k Q) :
    quotientArrowIdealAlgEquiv k Q (Ideal.Quotient.mk (arrowIdeal k Q) f) =
      trivialCoeff k Q f := by
  rw [quotientArrowIdealAlgEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

end Quotient

/-! ### The semisimple quotient -/

section Jacobson

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Finite Q]

/-- **The semisimple quotient of the path algebra of a finite acyclic quiver is a product of copies
of the base field, one for each vertex.** This is its Wedderburn decomposition: every block is the
base field, so every block is one-dimensional, matching the vertex simple modules. -/
noncomputable def quotientJacobsonAlgEquiv (h : Quiver.IsAcyclic Q) :
    (pathAlgebra k Q ⧸ Ring.jacobson (pathAlgebra k Q)) ≃ₐ[k] (Q → k) :=
  (Ideal.quotientEquivAlgOfEq k (jacobson_pathAlgebra_eq_arrowIdeal k Q h)).trans
    (quotientArrowIdealAlgEquiv k Q)

/-- The equivalence out of the semisimple quotient is the trivial-coefficient homomorphism. -/
@[simp]
theorem quotientJacobsonAlgEquiv_mk (h : Quiver.IsAcyclic Q) (f : pathAlgebra k Q) :
    quotientJacobsonAlgEquiv k Q h (Ideal.Quotient.mk (Ring.jacobson (pathAlgebra k Q)) f) =
      trivialCoeff k Q f := by
  rw [quotientJacobsonAlgEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    quotientArrowIdealAlgEquiv_mk]

/-- The semisimple quotient of the path algebra of a finite acyclic quiver is indeed semisimple:
a finite product of fields is a semisimple ring. -/
theorem isSemisimpleRing_quotient_jacobson (h : Quiver.IsAcyclic Q) :
    IsSemisimpleRing (pathAlgebra k Q ⧸ Ring.jacobson (pathAlgebra k Q)) :=
  (quotientJacobsonAlgEquiv k Q h).toRingEquiv.symm.isSemisimpleRing

/-- The semisimple quotient of the path algebra of a finite acyclic quiver is reduced: no Wedderburn
block of it is a matrix algebra of size greater than one. -/
theorem isReduced_quotient_jacobson (h : Quiver.IsAcyclic Q) :
    IsReduced (pathAlgebra k Q ⧸ Ring.jacobson (pathAlgebra k Q)) :=
  isReduced_of_injective (quotientJacobsonAlgEquiv k Q h).toRingEquiv
    (quotientJacobsonAlgEquiv k Q h).toRingEquiv.injective

/-- **The path algebra of a finite acyclic quiver is a basic algebra.**  This is the previous two
results read through `TauCeti.IsBasic`: by `TauCeti.isBasic_iff_pi_divisionRing` the quotient by the
radical is then a product of division rings -- here, one copy of `k` for each vertex -- so the
vertices index the simple modules and the indecomposable projectives without repetition. -/
theorem isBasic (h : Quiver.IsAcyclic Q) : IsBasic (pathAlgebra k Q) :=
  (isBasic_def _).mpr
    ⟨isSemisimpleRing_quotient_jacobson k Q h, isReduced_quotient_jacobson k Q h⟩

/-- The semisimple quotient of the path algebra of a finite acyclic quiver is commutative. -/
theorem mul_comm_quotient_jacobson (h : Quiver.IsAcyclic Q)
    (x y : pathAlgebra k Q ⧸ Ring.jacobson (pathAlgebra k Q)) :
    x * y = y * x :=
  (quotientJacobsonAlgEquiv k Q h).injective (by
    rw [map_mul, map_mul, mul_comm])

/-- The semisimple quotient of the path algebra of a finite acyclic quiver has dimension the number
of vertices: one for each vertex simple module. -/
theorem finrank_quotient_jacobson (h : Quiver.IsAcyclic Q) :
    Module.finrank k (pathAlgebra k Q ⧸ Ring.jacobson (pathAlgebra k Q)) = Nat.card Q := by
  let := Fintype.ofFinite Q
  rw [(quotientJacobsonAlgEquiv k Q h).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Jacobson

end PathAlgebra

end TauCeti
