/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.CentralIdempotent
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis
public import TauCeti.RepresentationTheory.CharacterTable.Completeness
public import TauCeti.RingTheory.Idempotents.LinearIndependent

/-!
# The primitive central idempotents decompose the identity

Let `G` be a finite group and `k` an algebraically closed field in which `|G|` is invertible. To an
irreducible representation `ρ` with character `χ`,
`TauCeti/RepresentationTheory/CharacterTable/CentralIdempotent.lean` attaches the central element
`e_ρ = (χ(1)/|G|) ∑_g χ(g⁻¹) g` and proves it idempotent, nonzero, orthogonal to the idempotent of
an inequivalent irreducible, and equal to the Wedderburn projector onto the block of `ρ`. What that
file leaves open is the completeness statement `∑_ρ e_ρ = 1`, which is not about one idempotent but
about a whole complete list of irreducibles; this file proves it.

The proof is a coefficient computation. The coefficient of `x` in `∑ᵢ e_{ρᵢ}` is
`|G|⁻¹ ∑ᵢ χᵢ(1) χᵢ(x⁻¹)`, and the inner sum pairs the column of the character table at `x` against
the column at `1`. The second orthogonality relation
`TauCeti.ClassFunction.sum_char_mul_char_inv` evaluates it as `|G|` when `x` is conjugate to `1` --
that is, when `x = 1`, the conjugacy class of `1` being a singleton -- and as `0` otherwise. Those
are exactly the coefficients of `1 : k[G]`.

Completeness of the family is therefore what the theorem rests on, and it enters through the same
hypotheses `hind` and `hcard` that
`TauCeti/RepresentationTheory/CharacterTable/Completeness.lean` uses: the representations are
pairwise inequivalent and there are as many of them as `G` has conjugacy classes. Since a primitive
central idempotent depends only on the isomorphism class of its representation
(`TauCeti.Representation.primitiveCentralIdempotent_eq_of_nonempty_equiv`), such a family lists
each primitive central idempotent exactly once
(`TauCeti.Representation.exists_eq_primitiveCentralIdempotent` and
`TauCeti.Representation.primitiveCentralIdempotent_injective`), so the sum really is the sum over
*all* of them.

Two things follow. The idempotents form a complete orthogonal family in Mathlib's sense
(`CompleteOrthogonalIdempotents`), which is the interface the ring-theoretic consequences are read
off; and, being `Nat.card (ConjClasses G)` linearly independent elements of the centre, whose
dimension is that same number (`TauCeti.finrank_center_monoidAlgebra`), they are a **basis of the
centre** of the group algebra, with the central characters as the coordinate functionals. That
basis is the idempotent side of the splitting of `Z(k[G])` by central characters.

## Main definitions

* `TauCeti.Representation.basisPrimitiveCentralIdempotentCenter`: the primitive central idempotents
  of a complete family of irreducibles, as a basis of the centre of the group algebra.

## Main statements

* `TauCeti.Representation.sum_primitiveCentralIdempotent`: **the primitive central idempotents of a
  complete family of irreducible representations sum to `1`**, with
  `TauCeti.Representation.sum_primitiveCentralIdempotentCenter` the same identity in the centre.
* `TauCeti.Representation.completeOrthogonalIdempotents_primitiveCentralIdempotent`: they are a
  complete orthogonal family of idempotents.
* `TauCeti.Representation.sum_primitiveCentralIdempotent_mul`: consequently every element of the
  group algebra is the sum of its blocks `e_ρ a`.
* `TauCeti.Representation.basisPrimitiveCentralIdempotentCenter_repr_apply`: the coordinates in
  that basis are the central characters, so that
  `TauCeti.Representation.sum_centralCharacter_smul_primitiveCentralIdempotentCenter` expands a
  central element as the combination of the primitive central idempotents whose coefficients are
  its central characters.

## References

This proves the `∑ᵢ eᵢ = 1` item of Layer 3 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
left open by `TauCeti/RepresentationTheory/CharacterTable/CentralIdempotent.lean`. See
I. M. Isaacs, *Character Theory of Finite Groups* (1976), Theorem 2.12, or J.-P. Serre, *Linear
Representations of Finite Groups*, Section 6.3.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

namespace Representation

universe u v w x

/-! ### Orthogonality along a family -/

section Orthogonal

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)] {ι : Type*} {V : ι → Type w} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (ρ : ∀ i, Representation k G (V i))
  [∀ i, (ρ i).IsIrreducible] (hind : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))

include hind

/-- **The primitive central idempotents of a pairwise inequivalent family are orthogonal.** -/
@[simp]
theorem primitiveCentralIdempotent_mul_eq_zero {i j : ι} (hij : i ≠ j) :
    primitiveCentralIdempotent (ρ i) * primitiveCentralIdempotent (ρ j) = 0 := by
  classical
  rw [primitiveCentralIdempotent_mul_primitiveCentralIdempotent,
    ite_eq_right (fun h => hij ((nonempty_equiv_iff_eq ρ hind).mp h))]

/-- **A member of the family other than `ρ i` sees `e_{ρ i}` as `0`.** -/
@[simp]
theorem centralCharacter_primitiveCentralIdempotentCenter_eq_zero {i j : ι} (hij : i ≠ j) :
    centralCharacter (ρ j) (primitiveCentralIdempotentCenter (ρ i)) = 0 := by
  classical
  rw [centralCharacter_primitiveCentralIdempotentCenter,
    ite_eq_right (fun h => hij ((nonempty_equiv_iff_eq ρ hind).mp h))]

/-- **The idempotents of the family are a family of orthogonal idempotents.** -/
theorem orthogonalIdempotents_primitiveCentralIdempotent :
    OrthogonalIdempotents fun i => primitiveCentralIdempotent (ρ i) where
  idem i := isIdempotentElem_primitiveCentralIdempotent (ρ i)
  ortho _ _ hij := primitiveCentralIdempotent_mul_eq_zero ρ hind hij

/-- **The primitive central idempotents of a pairwise inequivalent family are linearly
independent.** They are orthogonal and nonzero, and that is all the general
`TauCeti.linearIndependent_of_orthogonalIdempotents` asks for. -/
theorem linearIndependent_primitiveCentralIdempotent :
    LinearIndependent k fun i => primitiveCentralIdempotent (ρ i) :=
  linearIndependent_of_orthogonalIdempotents
    (orthogonalIdempotents_primitiveCentralIdempotent ρ hind)
    fun i => primitiveCentralIdempotent_ne_zero (ρ i)

/-- **The idempotents of the family are pairwise distinct**, being linearly independent. -/
theorem primitiveCentralIdempotent_injective :
    Function.Injective fun i => primitiveCentralIdempotent (ρ i) :=
  (linearIndependent_primitiveCentralIdempotent ρ hind).injective

/-- The primitive central idempotents of the family are linearly independent in the centre of the
group algebra, the inclusion of the centre being injective. -/
theorem linearIndependent_primitiveCentralIdempotentCenter :
    LinearIndependent k fun i => primitiveCentralIdempotentCenter (ρ i) := by
  refine LinearIndependent.of_comp (Subalgebra.center k k[G]).toSubmodule.subtype ?_
  have hcomp : (⇑(Subalgebra.center k k[G]).toSubmodule.subtype ∘
      fun i => primitiveCentralIdempotentCenter (ρ i)) =
      fun i => primitiveCentralIdempotent (ρ i) :=
    funext fun i => primitiveCentralIdempotentCenter_coe (ρ i)
  rw [hcomp]
  exact linearIndependent_primitiveCentralIdempotent ρ hind

end Orthogonal

/-! ### Complete families: the decomposition of the identity -/

section Complete

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)] {ι : Type*} {V : ι → Type w} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (ρ : ∀ i, Representation k G (V i))
  [∀ i, (ρ i).IsIrreducible] (hind : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
  (hcard : Nat.card ι = Nat.card (ConjClasses G))

section Exhaust

variable [Finite ι]

include hind hcard

/-- **A complete family lists every primitive central idempotent.** Every irreducible
representation is equivalent to a member of the family, and equivalent representations have the
same idempotent. -/
theorem exists_eq_primitiveCentralIdempotent {W : Type x} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (σ : Representation k G W) [σ.IsIrreducible] :
    ∃ i, primitiveCentralIdempotent σ = primitiveCentralIdempotent (ρ i) := by
  obtain ⟨i, hi⟩ := ClassFunction.exists_nonempty_equiv ρ hind hcard σ
  exact ⟨i, primitiveCentralIdempotent_eq_of_nonempty_equiv σ (ρ i) hi⟩

end Exhaust

variable [Fintype ι]

include hind hcard

/-- **The primitive central idempotents of a complete family of irreducible representations sum to
`1`.**

The coefficient of `x` in the sum is `|G|⁻¹ ∑ᵢ χᵢ(1) χᵢ(x⁻¹)`, which the second orthogonality
relation evaluates as `1` when `x = 1` and as `0` otherwise: the conjugacy class of `1` is a
singleton, so `x` is conjugate to `1` exactly when `x = 1`. Those are the coefficients of
`1 : k[G]`. -/
theorem sum_primitiveCentralIdempotent :
    ∑ i, primitiveCentralIdempotent (ρ i) = 1 := by
  classical
  -- The conjugacy class of `1` is the singleton `{1}`, so its size contributes nothing.
  have hcarrier : (ConjClasses.mk (1 : G)).carrier = {1} := by
    ext y
    simp
  have hone : ((Nat.card (ConjClasses.mk (1 : G)).carrier : ℕ) : k) = 1 := by
    rw [hcarrier]
    simp
  refine MonoidAlgebra.ext (Finsupp.ext fun y => ?_)
  have hcoeff : (∑ i, primitiveCentralIdempotent (ρ i)).coeff y =
      (Nat.card G : k)⁻¹ * ∑ i, (ρ i).character 1 * (ρ i).character y⁻¹ := by
    rw [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [primitiveCentralIdempotent_coeff, mul_assoc]
  rw [hcoeff, ClassFunction.sum_char_mul_char_inv ρ hind hcard 1 y, hone, div_one,
    MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hy : (1 : G) = y
  · rw [ite_eq_left hy, ite_eq_left (hy ▸ IsConj.refl (1 : G)),
      inv_mul_cancel₀ (Invertible.ne_zero _)]
  · rw [ite_eq_right hy, ite_eq_right (fun h => hy (isConj_one_right.mp h).symm), mul_zero]

/-- **The primitive central idempotents of a complete family sum to `1`**, read in the centre of
the group algebra. -/
theorem sum_primitiveCentralIdempotentCenter :
    ∑ i, primitiveCentralIdempotentCenter (ρ i) = 1 := by
  refine Subtype.ext ?_
  rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
  simpa only [primitiveCentralIdempotentCenter_coe] using
    sum_primitiveCentralIdempotent ρ hind hcard

/-- **The primitive central idempotents of a complete family of irreducible representations are a
complete orthogonal family of idempotents** in the group algebra. -/
theorem completeOrthogonalIdempotents_primitiveCentralIdempotent :
    CompleteOrthogonalIdempotents fun i => primitiveCentralIdempotent (ρ i) where
  toOrthogonalIdempotents := orthogonalIdempotents_primitiveCentralIdempotent ρ hind
  complete := sum_primitiveCentralIdempotent ρ hind hcard

/-- **Every element of the group algebra is the sum of its blocks.** Multiplying by `e_ρ` projects
onto the block of `ρ`, and the blocks of a complete family exhaust the group algebra. -/
theorem sum_primitiveCentralIdempotent_mul (a : k[G]) :
    ∑ i, primitiveCentralIdempotent (ρ i) * a = a := by
  rw [← Finset.sum_mul, sum_primitiveCentralIdempotent ρ hind hcard, one_mul]

/-- **The primitive central idempotents of a complete family of irreducible representations are a
basis of the centre of the group algebra.** They are linearly independent, and there are as many of
them as the dimension `Nat.card (ConjClasses G)` of the centre. -/
noncomputable def basisPrimitiveCentralIdempotentCenter :
    Module.Basis ι k (Subalgebra.center k k[G]) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun i => primitiveCentralIdempotentCenter (ρ i))
    (linearIndependent_primitiveCentralIdempotentCenter ρ hind)
    (by rw [finrank_center_monoidAlgebra, ← hcard, Nat.card_eq_fintype_card])

@[simp]
theorem coe_basisPrimitiveCentralIdempotentCenter :
    ⇑(basisPrimitiveCentralIdempotentCenter ρ hind hcard) =
      fun i => primitiveCentralIdempotentCenter (ρ i) :=
  coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _

/-- **The central characters are the coordinates in the idempotent basis.** Applying the `i`-th
central character to the basis expansion of a central element `z` reads off its `i`-th coordinate,
because the `i`-th idempotent is the only member of the basis that character does not kill. -/
@[simp]
theorem basisPrimitiveCentralIdempotentCenter_repr_apply (z : Subalgebra.center k k[G]) (i : ι) :
    (basisPrimitiveCentralIdempotentCenter ρ hind hcard).repr z i = centralCharacter (ρ i) z := by
  have hbj : ∀ j, basisPrimitiveCentralIdempotentCenter ρ hind hcard j =
      primitiveCentralIdempotentCenter (ρ j) := fun j =>
    congrFun (coe_basisPrimitiveCentralIdempotentCenter ρ hind hcard) j
  conv_rhs => rw [← (basisPrimitiveCentralIdempotentCenter ρ hind hcard).sum_repr z]
  rw [map_sum, Finset.sum_eq_single i]
  · rw [map_smul, hbj i, centralCharacter_primitiveCentralIdempotentCenter_self (ρ i),
      smul_eq_mul, mul_one]
  · intro j _ hji
    rw [map_smul, hbj j,
      centralCharacter_primitiveCentralIdempotentCenter_eq_zero ρ hind hji, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **A central element is the combination of the primitive central idempotents whose coefficients
are its central characters.** This is the expansion of `z` in the idempotent basis, with the
coordinates identified by
`TauCeti.Representation.basisPrimitiveCentralIdempotentCenter_repr_apply`. -/
theorem sum_centralCharacter_smul_primitiveCentralIdempotentCenter
    (z : Subalgebra.center k k[G]) :
    ∑ i, centralCharacter (ρ i) z • primitiveCentralIdempotentCenter (ρ i) = z := by
  have hsum := (basisPrimitiveCentralIdempotentCenter ρ hind hcard).sum_repr z
  simpa only [basisPrimitiveCentralIdempotentCenter_repr_apply,
    coe_basisPrimitiveCentralIdempotentCenter] using hsum

end Complete

end Representation

end TauCeti
