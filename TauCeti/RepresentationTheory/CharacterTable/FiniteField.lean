/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.Algebra.MonoidAlgebra.Trace
public import TauCeti.FieldTheory.Finite.FrobeniusFixed
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis

/-!
# A finite field containing the roots of unity splits the centre of the group algebra

Let `G` be a finite group and `K` a finite field whose characteristic does not divide `|G|` and
whose multiplicative order kills `G`, that is `g ^ |K| = g` for every `g : G` -- equivalently, the
exponent of `G` divides `|K| - 1`, so that `K` already contains the roots of unity that the
eigenvalues of `G` need. This file proves that under exactly those hypotheses the centre of `K[G]`
is *split*: it is `K`-algebra isomorphic to a product of copies of `K`, one for each conjugacy
class of `G`.

The point is that `K` is not algebraically closed, so nothing forces the residue fields of
`Z(K[G])` to be `K` rather than proper extensions of it -- for some coefficient fields they can be
proper extensions, and splitting can fail. What rules that out is the following trace argument,
which is the whole content of the file.

For any `u : K[G]`, the trace of the matrix `M` of left multiplication by `u` in the group basis
is `|G|` times the coefficient of `u` at `1` (`TauCeti.trace_leftMulMatrix_monoidAlgebra`), and
over a finite field
`Matrix.trace (M ^ |K|) = (Matrix.trace M) ^ |K|` (`FiniteField.trace_pow_card`). Since
`a ^ |K| = a` in `K`, the coefficient at `1` is unchanged by raising to the `|K|`-th power, once
`|G|` is invertible. Now apply this to `u = y * g⁻¹` for a *central* `y`: there
`(y * g⁻¹) ^ |K| = y ^ |K| * g⁻¹`, because `y` is central and `g⁻¹ ^ |K| = g⁻¹`, so the identity
compares the coefficients of `y ^ |K|` and of `y` at each `g`. Hence `y ^ |K| = y`.

A commutative ring on which the `|K|`-th power map is the identity is reduced, and a finite domain
on which it is the identity is `K` itself; so the centre, being reduced and Artinian, is the
product of its residue fields, all of which are `K`. Counting `K`-dimensions against the class-sum
basis identifies the number of factors with the number of conjugacy classes.

This is the good-prime structure theorem of the Burnside--Dixon--Schneider algorithm, stated for a
general finite coefficient field; the specialization to `ZMod p` at a good Dixon prime is
`TauCeti/RepresentationTheory/CharacterTable/Dixon/Structure.lean`.

## Main results

* `TauCeti.pow_card_eq_self_of_mem_center`: the centre of `K[G]` is fixed by `x ↦ x ^ |K|`.
* `TauCeti.algebraMap_center_quotient_bijective`: every residue field of the centre is `K`.
* `TauCeti.centerAlgEquivPi`: the centre is the algebra of functions on its own maximal spectrum.
* `TauCeti.card_maximalSpectrum_center`: that spectrum has one point per conjugacy class.
* `TauCeti.nonempty_center_algEquiv_conjClasses`: `Z(K[G]) ≃ₐ[K] (ConjClasses G → K)`.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* The roadmap `RepresentationTheory/CharacterTheory`, Layer 6, "The good-prime structure theorem".
-/

public section

namespace TauCeti

/-! ### Frobenius fixes the centre -/

section Frobenius

variable {K G : Type*} [Field K] [Fintype K] [Group G] [Finite G]

/-- **Raising to the `|K|`-th power fixes the coefficient at the identity.** Over a finite field
`K` whose characteristic does not divide `|G|`, the identity coefficient of `u ^ |K|` is that of
`u`, for *every* `u` in the group algebra.

This is the trace identity `tr (M ^ |K|) = (tr M) ^ |K|` for the left regular matrix `M` of `u`,
combined with `a ^ |K| = a` in `K`. -/
theorem coeff_one_pow_card (hG : (Nat.card G : K) ≠ 0) (u : MonoidAlgebra K G) :
    (u ^ Fintype.card K).coeff 1 = u.coeff 1 := by
  classical
  let _ := Fintype.ofFinite G
  have hG' : (Fintype.card G : K) ≠ 0 := by
    rwa [← Nat.card_eq_fintype_card]
  have h := FiniteField.trace_pow_card
    (Algebra.leftMulMatrix (MonoidAlgebra.basis G K) u)
  rw [← map_pow, trace_leftMulMatrix_monoidAlgebra, trace_leftMulMatrix_monoidAlgebra, mul_pow,
    FiniteField.pow_card, FiniteField.pow_card] at h
  exact mul_left_cancel₀ hG' h

/-- **The centre of the group algebra is fixed by the Frobenius of `K`.** Let `K` be a finite field
whose characteristic does not divide `|G|` and whose multiplicative order kills `G`, that is
`g ^ |K| = g` for every `g` (equivalently, the exponent of `G` divides `|K| - 1`). Then every
central element `y` of `K[G]` satisfies `y ^ |K| = y`.

The proof tests `y` against the group elements: `(y * g⁻¹) ^ |K| = y ^ |K| * g⁻¹` because `y` is
central and `g⁻¹` is fixed by the `|K|`-th power map, so `TauCeti.coeff_one_pow_card` applied to
`y * g⁻¹` compares the coefficients of `y ^ |K|` and `y` at `g`. -/
theorem pow_card_eq_self_of_mem_center (hG : (Nat.card G : K) ≠ 0)
    (hexp : ∀ g : G, g ^ Fintype.card K = g) {y : MonoidAlgebra K G}
    (hy : y ∈ Subalgebra.center K (MonoidAlgebra K G)) :
    y ^ Fintype.card K = y := by
  classical
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  have hcomm : Commute y (MonoidAlgebra.single g⁻¹ (1 : K)) :=
    (Subalgebra.mem_center_iff.mp hy _).symm
  have key := coeff_one_pow_card hG (y * MonoidAlgebra.single g⁻¹ (1 : K))
  rw [hcomm.mul_pow, MonoidAlgebra.single_pow, hexp g⁻¹, one_pow,
    MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_mul_single_apply] at key
  simpa using key

end Frobenius

/-! ### The splitting of the centre -/

section Finiteness

variable (K G : Type*) [CommRing K] [Finite K] [Group G] [Finite G]

/-- The centre of a finite group algebra over a finite coefficient ring is finite: it is a finitely
generated module over a finite ring, by its class-sum basis. -/
instance instFiniteCenterMonoidAlgebra : Finite (Subalgebra.center K (MonoidAlgebra K G)) :=
  Module.finite_of_finite K

/-- The centre of a finite group algebra over a finite Artinian commutative ring is Artinian. -/
instance instIsArtinianRingCenterMonoidAlgebra [IsArtinianRing K] :
    IsArtinianRing (Subalgebra.center K (MonoidAlgebra K G)) :=
  IsArtinianRing.of_finite K _

end Finiteness

section Splitting

variable {K G : Type*} [Field K] [Fintype K] [Group G] [Finite G]
variable (hG : (Nat.card G : K) ≠ 0) (hexp : ∀ g : G, g ^ Fintype.card K = g)

include hG hexp

/-- The `|K|`-th power map is the identity on the centre of `K[G]`, in the bundled form used by
the structure theorem. -/
theorem center_pow_card (z : Subalgebra.center K (MonoidAlgebra K G)) :
    z ^ Fintype.card K = z :=
  Subtype.ext (by simpa using pow_card_eq_self_of_mem_center hG hexp z.2)

/-- The centre of `K[G]` is reduced. -/
theorem isReduced_center : IsReduced (Subalgebra.center K (MonoidAlgebra K G)) :=
  (isReduced_iff_pow_one_lt (Fintype.card K) Fintype.one_lt_card).2 fun z hz => by
    rw [center_pow_card hG hexp] at hz
    exact hz

/-- **Every residue field of the centre of `K[G]` is `K` itself.** This is the sense in which `K`
splits `K[G]`: no residue field of `Z(K[G])` is a proper extension of `K`. -/
theorem algebraMap_center_quotient_bijective
    (I : MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G))) :
    Function.Bijective
      (algebraMap K (Subalgebra.center K (MonoidAlgebra K G) ⧸ I.asIdeal)) := by
  have hmax := I.isMaximal
  have : Finite (Subalgebra.center K (MonoidAlgebra K G) ⧸ I.asIdeal) :=
    Finite.of_surjective _ Ideal.Quotient.mk_surjective
  refine algebraMap_bijective_of_pow_card_eq_self (K := K)
    (L := Subalgebra.center K (MonoidAlgebra K G) ⧸ I.asIdeal) fun x => ?_
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  calc Ideal.Quotient.mk I.asIdeal z ^ Fintype.card K
      = Ideal.Quotient.mk I.asIdeal (z ^ Fintype.card K) := (map_pow _ _ _).symm
    _ = Ideal.Quotient.mk I.asIdeal z := by rw [center_pow_card hG hexp]

/-- **The centre of `K[G]` is split.** For a finite field `K` whose characteristic does not divide
`|G|` and whose multiplicative order kills `G`, the centre of `K[G]` is a product of copies of `K`,
indexed by its own maximal ideals.

The centre is reduced, hence a product of its residue fields by Artinian structure theory, and each
residue field is `K` by `TauCeti.algebraMap_center_quotient_bijective`. -/
noncomputable def centerAlgEquivPi :
    Subalgebra.center K (MonoidAlgebra K G) ≃ₐ[K]
      (MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G)) → K) :=
  haveI : IsReduced (Subalgebra.center K (MonoidAlgebra K G)) := isReduced_center hG hexp
  haveI : IsScalarTower K (Subalgebra.center K (MonoidAlgebra K G))
      (Subalgebra.center K (MonoidAlgebra K G)) := IsScalarTower.right
  haveI : ∀ I : MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G)),
      IsScalarTower K (Subalgebra.center K (MonoidAlgebra K G))
        (Subalgebra.center K (MonoidAlgebra K G) ⧸ I.asIdeal) := fun _ => inferInstance
  ((IsArtinianRing.equivPi _).restrictScalars K).trans
    (AlgEquiv.piCongrRight fun I =>
      (AlgEquiv.ofBijective (Algebra.ofId K _)
        (algebraMap_center_quotient_bijective hG hexp I)).symm)

/-- Evaluating `TauCeti.centerAlgEquivPi` at a maximal ideal is the quotient map followed by the
inverse equivalence from that residue field to `K`. -/
@[simp]
theorem centerAlgEquivPi_apply (z : Subalgebra.center K (MonoidAlgebra K G))
    (I : MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G))) :
    centerAlgEquivPi hG hexp z I =
      (AlgEquiv.ofBijective (Algebra.ofId K _)
        (algebraMap_center_quotient_bijective hG hexp I)).symm
        (Ideal.Quotient.mk I.asIdeal z) := by
  simp only [centerAlgEquivPi, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.piCongrRight_apply, IsArtinianRing.equivPi_apply]
  -- the two sides now differ only in the (irrelevant) bijectivity proof carried by `ofBijective`
  rfl

/-- **The number of blocks is the number of conjugacy classes.** Comparing `K`-dimensions in
`TauCeti.centerAlgEquivPi` with the class-sum basis of the centre. -/
theorem card_maximalSpectrum_center :
    Nat.card (MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G))) =
      Nat.card (ConjClasses G) := by
  have := Fintype.ofFinite (MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G)))
  rw [← finrank_center_monoidAlgebra K G, (centerAlgEquivPi hG hexp).toLinearEquiv.finrank_eq,
    Module.finrank_pi, Nat.card_eq_fintype_card]

/-- **The good-splitting structure theorem for a finite coefficient field.** The centre of `K[G]`
is `K`-algebra isomorphic to the functions on the conjugacy classes of `G`.

The indexing is by cardinality only: the canonical indexing of the factors is by the maximal ideals
of the centre (`TauCeti.centerAlgEquivPi`), which `TauCeti.card_maximalSpectrum_center` counts. -/
theorem nonempty_center_algEquiv_conjClasses :
    Nonempty (Subalgebra.center K (MonoidAlgebra K G) ≃ₐ[K] (ConjClasses G → K)) := by
  have := Fintype.ofFinite (MaximalSpectrum (Subalgebra.center K (MonoidAlgebra K G)))
  have := Fintype.ofFinite (ConjClasses G)
  have hcard := card_maximalSpectrum_center hG hexp
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcard
  exact ⟨(centerAlgEquivPi hG hexp).trans
    (AlgEquiv.piCongrLeft' K (fun _ => K) (Fintype.equivOfCardEq hcard))⟩

end Splitting

end TauCeti
