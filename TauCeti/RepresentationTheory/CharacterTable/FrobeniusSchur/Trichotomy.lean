/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Squares
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Basic
public import TauCeti.RepresentationTheory.Dual
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# The Frobenius-Schur trichotomy

`TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariants` computes the indicator
`ν₂(ρ) = |G|⁻¹ ∑_g χ(g²)` as the signed count `dim (Sym²V)ᴳ - dim (Λ²V)ᴳ` of invariants in the two
squares.  This file identifies those two invariant counts with counts of **bilinear forms** on `V`,
and reads the trichotomy off the identification.

The dictionary is elementary.  A functional on `Sym²V` becomes a bilinear form on `V` by composing
with the universal multilinear map, and the form it produces is symmetric because the symmetric
square does not see the order of its two arguments; a functional on `Λ²V` becomes a form in the
same way, and the form it produces is alternating because a repeated argument wedges to zero.
Both assignments are injective.  So the
invariant functionals on the two squares inject into the invariant symmetric and the invariant
alternating forms, which meet only in `0`.  Counting on the other side, the invariant forms are the
intertwiners from `ρ` to its dual, and the character sum that counts those is the character sum that
counts the invariants of the tensor square, read along `g⁻¹` instead of `g`; so the two injections
account for every invariant form, and

`ν₂(ρ) = dim {invariant symmetric forms} - dim {invariant alternating forms}`.

On an **irreducible** representation over an algebraically closed field the invariant forms are at
most a line, and `TauCeti.Representation.IsInvariantForm.isSymm_or_isAlt` says a nonzero one is
symmetric or alternating.  The two counts are therefore `1, 0` or `0, 1` or `0, 0`, which is the
**trichotomy**: `ν₂(ρ)` is `1` when `ρ` carries a nonzero invariant symmetric form (the orthogonal
case), `-1` when it carries a nonzero invariant alternating form (the symplectic, or quaternionic,
case), and `0` when it carries no nonzero invariant form at all (the complex case).  The nonzero
invariant form of the first two cases is automatically nondegenerate, by
`TauCeti.Representation.IsInvariantForm.nondegenerate`.

Characteristic zero does three jobs, and nothing else: it moves the counting identities from
equations in `k` to equations of natural numbers, it keeps a form from being symmetric and
alternating at once, and it supplies `Invertible (Nat.card G : k)` in the statements that do not
assume it.  Averaging characters produces identities in `k` and nothing more, so the two
counting identities are stated first in that form, needing only an invertible `|G|`
(`TauCeti.Representation.finrank_invariants_dual_cast` and
`TauCeti.Representation.finrank_invariantForms_cast`); in characteristic `p` they are identities
of residues, and it is the injectivity of `ℕ → k` that turns them into equalities of dimensions.

Three ingredients come from earlier modules and are only applied here.  The invariant forms
themselves, the symmetric and the alternating ones among them, and their identification with the
intertwiners into the dual are in `TauCeti/RepresentationTheory/InvariantForm.lean`; the dictionary
turning a functional on either square into a form is `TauCeti.BilinForm.ofSymmetricSquareDual` and
`TauCeti.BilinForm.ofExteriorSquareDual`, in `TauCeti/LinearAlgebra/BilinearForm/Squares.lean`; and
the invariants of a dual representation, with their count, are in
`TauCeti/RepresentationTheory/Dual.lean`.  What this file adds is that the dictionary carries
invariants to invariant forms, and the counting that follows.

## Main results

* `TauCeti.Representation.finrank_invariantForms`: **the invariant forms are as many as the
  invariants of the two squares together**, as an identity in `k` whenever `|G|` is invertible
  (`TauCeti.Representation.finrank_invariantForms_cast`) and as natural numbers in characteristic
  zero.
* `TauCeti.Representation.finrank_symmetricInvariantForms` and
  `TauCeti.Representation.finrank_alternatingInvariantForms`: the two invariant form counts are the
  invariant counts of the two squares.
* `TauCeti.Representation.map_ofSymmetricSquareDual_eq_symmetricInvariantForms` and
  `TauCeti.Representation.map_ofExteriorSquareDual_eq_alternatingInvariantForms`: **every invariant
  symmetric, respectively alternating, form comes from an invariant functional on the corresponding
  square**.
* `TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariantForms`: **the indicator is
  the signed count of invariant forms**, `ν₂(ρ) = dim {symmetric} - dim {alternating}`.
* `TauCeti.Representation.frobeniusSchurIndicator_eq_one_iff`,
  `TauCeti.Representation.frobeniusSchurIndicator_eq_neg_one_iff` and
  `TauCeti.Representation.frobeniusSchurIndicator_eq_zero_iff`: **the trichotomy**, each value of
  the indicator characterized by the invariant forms, for an irreducible representation over an
  algebraically closed field of characteristic zero.
* `TauCeti.Representation.frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one`: the indicator
  of such a representation takes only the values `1`, `0` and `-1`.

## Implementation notes

The two maps out of the dual squares are only ever used through their images: injectivity plus the
dimension count is what forces them onto the symmetric and the alternating forms, in
`TauCeti.Representation.map_ofSymmetricSquareDual_eq_symmetricInvariantForms` and
`TauCeti.Representation.map_ofExteriorSquareDual_eq_alternatingInvariantForms`.  Neither
surjectivity is proved directly: on the symmetric side that would need a universal property of the
symmetric square, which Mathlib does not have.

What connects the submodule of invariant forms to the character machinery is
`TauCeti.Representation.invariantFormsEquivIntertwiningMapDual`: an equivalence with a space of
intertwiners is the shape Mathlib's
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank` counts.

The dimension lemmas used below are stated for an abstract module and applied with that module
supplied explicitly.  The reason is mechanical: the `AddCommMonoid` structure on a space of
bilinear forms is the one on linear maps, and asking the elaborator to solve for an `AddCommGroup`
structure inducing it does not terminate quickly.  The same is why the two range identities are
stated with the image on the left: they come out of such a lemma in that orientation, and turning
one round asks for exactly that comparison of structures.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 7, “Invariant bilinear forms” and “The trichotomy”.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 4.
-/

public section

open scoped TensorProduct

open Module (finrank)

universe v w

variable {k : Type} {G : Type v} {V : Type w}

namespace TauCeti

namespace Representation

open LinearMap (BilinForm)

/-! ### Dimension helpers on a space of bilinear forms -/

section Helpers

/-
The lemma below is stated for an abstract module `W` and applied with `W` given explicitly.
Leaving `W` to unification at that application makes the elaborator look for an `AddCommGroup`
structure on a space of linear maps whose `AddCommMonoid` structure is already fixed, which it
does not find quickly.  The same holds of the Mathlib lemmas `Submodule.eq_of_le_of_finrank_le`,
`finrank_span_singleton` and `Submodule.one_le_finrank_iff` where they are used below.
-/

/-- Two submodules meeting only in `0` have dimensions adding to at most that of any submodule
containing them both. -/
private theorem finrank_add_finrank_le_of_inf_eq_bot {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W]
    {S T U : Submodule K W} (hS : S ≤ U) (hT : T ≤ U) (h : S ⊓ T = ⊥) :
    finrank K S + finrank K T ≤ finrank K U := by
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq S T
  rw [h, finrank_bot, add_zero] at hsup
  rw [← hsup]
  exact Submodule.finrank_mono (sup_le hS hT)

end Helpers

/-! ### Invariant forms from invariant functionals on the two squares -/

section SymmetricSquare

variable [CommRing k] [Group G] [AddCommMonoid V] [Module k V]

/-- An invariant functional on the symmetric square gives an invariant symmetric form. -/
theorem ofSymmetricSquareDual_mem_symmetricInvariantForms (ρ : Representation k G V)
    {ψ : Module.Dual k (Sym[k]^2V)} (hψ : ψ ∈ ((ρ.symmetricPower 2).dual).invariants) :
    BilinForm.ofSymmetricSquareDual ψ ∈ symmetricInvariantForms ρ := by
  refine mem_symmetricInvariantForms.mpr
    ⟨isInvariantForm_iff.mpr fun g x y => ?_, BilinForm.isSymm_ofSymmetricSquareDual ψ⟩
  have hvec : (fun i => ρ g (![x, y] i)) = ![ρ g x, ρ g y] := (FinVec.map_eq _ _).symm
  simp only [BilinForm.ofSymmetricSquareDual_apply]
  rw [← hvec, ← ρ.symmetricPower_apply_tprod 2 g ![x, y],
    apply_of_mem_invariants_dual hψ g]

end SymmetricSquare

section ExteriorSquare

variable [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- An invariant functional on the exterior square gives an invariant alternating form. -/
theorem ofExteriorSquareDual_mem_alternatingInvariantForms (ρ : Representation k G V)
    {ψ : Module.Dual k (⋀[k]^2 V)} (hψ : ψ ∈ ((ρ.exteriorPower 2).dual).invariants) :
    BilinForm.ofExteriorSquareDual ψ ∈ alternatingInvariantForms ρ := by
  refine mem_alternatingInvariantForms.mpr
    ⟨isInvariantForm_iff.mpr fun g x y => ?_, BilinForm.isAlt_ofExteriorSquareDual ψ⟩
  have hvec : (ρ g ∘ ![x, y]) = ![ρ g x, ρ g y] := (FinVec.map_eq _ _).symm
  simp only [BilinForm.ofExteriorSquareDual_apply]
  rw [← hvec, ← ρ.exteriorPower_apply_ιMulti 2 g ![x, y],
    apply_of_mem_invariants_dual hψ g]

end ExteriorSquare

/-! ### Counting the invariant forms -/

section Counting

variable [Field k] [Group G] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V] [Finite G]

section Invertible

variable [Invertible (Nat.card G : k)]

/-- **The invariant forms are as many as the invariants of the tensor square**, as an identity in
`k`: the invariant forms are the intertwiners `ρ → ρ.dual`, and the character sum counting those is
the character sum counting the invariants of `ρ ⊗ ρ`, read along `g⁻¹` instead of `g`.

As with `TauCeti.Representation.finrank_invariants_dual_cast`, in characteristic `p` this is an
identity of residues only. -/
theorem finrank_invariantForms_eq_finrank_invariants_tprod_self_cast (ρ : Representation k G V) :
    (finrank k (invariantForms ρ) : k) =
      (finrank k (Representation.tprod ρ ρ).invariants : k) := by
  have : Fintype G := Fintype.ofFinite G
  rw [(invariantFormsEquivIntertwiningMapDual ρ).finrank_eq,
    ← Representation.card_inv_mul_sum_char_mul_char_eq_finrank,
    ← Representation.card_inv_mul_sum_char_eq_finrank]
  refine congrArg _ ?_
  simp only [Representation.char_dual, Representation.char_tensor, Pi.mul_apply]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun _ => rfl

/-- **The invariant forms are as many as the invariants of the two squares together**, as an
identity in `k`: they are as many as the invariants of the tensor square, and
`TauCeti.Representation.finrank_invariants_tprod_self_cast` splits that count in two.

As with `TauCeti.Representation.finrank_invariants_dual_cast`, in characteristic `p` this is an
identity of residues only; see `TauCeti.Representation.finrank_invariantForms` for the
characteristic-zero form. -/
theorem finrank_invariantForms_cast (ρ : Representation k G V) :
    (finrank k (invariantForms ρ) : k) =
      (finrank k (ρ.symmetricPower 2).invariants : k) +
        (finrank k (ρ.exteriorPower 2).invariants : k) := by
  rw [finrank_invariantForms_eq_finrank_invariants_tprod_self_cast,
    finrank_invariants_tprod_self_cast]

end Invertible

variable [CharZero k]

/-- **The invariant forms are as many as the invariants of the two squares together**, as natural
numbers.  Characteristic zero is what lifts
`TauCeti.Representation.finrank_invariantForms_cast` from an identity in `k`. -/
theorem finrank_invariantForms (ρ : Representation k G V) :
    finrank k (invariantForms ρ) =
      finrank k (ρ.symmetricPower 2).invariants + finrank k (ρ.exteriorPower 2).invariants := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact_mod_cast finrank_invariantForms_cast ρ

/- The image of the invariant functionals on the symmetric square, and its dimension.  Both halves
are used twice: once for the inequality that feeds the squeeze, and once for the surjectivity that
the squeeze then delivers. -/
omit [FiniteDimensional k V] [Finite G] [CharZero k] in
private theorem map_ofSymmetricSquareDual_le (ρ : Representation k G V) :
    Submodule.map (BilinForm.ofSymmetricSquareDual (k := k) (V := V))
      ((ρ.symmetricPower 2).dual).invariants ≤ symmetricInvariantForms ρ := by
  rintro _ ⟨ψ, hψ, rfl⟩
  exact ofSymmetricSquareDual_mem_symmetricInvariantForms ρ hψ

private theorem finrank_map_ofSymmetricSquareDual (ρ : Representation k G V) :
    finrank k (Submodule.map (BilinForm.ofSymmetricSquareDual (k := k) (V := V))
        ((ρ.symmetricPower 2).dual).invariants) =
      finrank k (ρ.symmetricPower 2).invariants := by
  rw [← (Submodule.equivMapOfInjective (BilinForm.ofSymmetricSquareDual (k := k) (V := V))
    BilinForm.ofSymmetricSquareDual_injective
    ((ρ.symmetricPower 2).dual).invariants).finrank_eq, finrank_invariants_dual]

omit [FiniteDimensional k V] [Finite G] [CharZero k] in
private theorem map_ofExteriorSquareDual_le (ρ : Representation k G V) :
    Submodule.map (BilinForm.ofExteriorSquareDual (k := k) (V := V))
      ((ρ.exteriorPower 2).dual).invariants ≤ alternatingInvariantForms ρ := by
  rintro _ ⟨ψ, hψ, rfl⟩
  exact ofExteriorSquareDual_mem_alternatingInvariantForms ρ hψ

private theorem finrank_map_ofExteriorSquareDual (ρ : Representation k G V) :
    finrank k (Submodule.map (BilinForm.ofExteriorSquareDual (k := k) (V := V))
        ((ρ.exteriorPower 2).dual).invariants) =
      finrank k (ρ.exteriorPower 2).invariants := by
  rw [← (Submodule.equivMapOfInjective (BilinForm.ofExteriorSquareDual (k := k) (V := V))
    BilinForm.ofExteriorSquareDual_injective
    ((ρ.exteriorPower 2).dual).invariants).finrank_eq, finrank_invariants_dual]

private theorem finrank_invariants_symmetricPower_le (ρ : Representation k G V) :
    finrank k (ρ.symmetricPower 2).invariants ≤ finrank k (symmetricInvariantForms ρ) := by
  rw [← finrank_map_ofSymmetricSquareDual ρ]
  exact Submodule.finrank_mono (map_ofSymmetricSquareDual_le ρ)

private theorem finrank_invariants_exteriorPower_le (ρ : Representation k G V) :
    finrank k (ρ.exteriorPower 2).invariants ≤ finrank k (alternatingInvariantForms ρ) := by
  rw [← finrank_map_ofExteriorSquareDual ρ]
  exact Submodule.finrank_mono (map_ofExteriorSquareDual_le ρ)

omit [Finite G] in
private theorem finrank_symmetricInvariantForms_add_le (ρ : Representation k G V) :
    finrank k (symmetricInvariantForms ρ) + finrank k (alternatingInvariantForms ρ)
      ≤ finrank k (invariantForms ρ) :=
  finrank_add_finrank_le_of_inf_eq_bot (K := k) (W := BilinForm k V) (symmetricInvariantForms_le ρ)
    (alternatingInvariantForms_le ρ)
    (symmetricInvariantForms_inf_alternatingInvariantForms
      (IsRegular.of_ne_zero (two_ne_zero (α := k))).left ρ)

/- The two counts are squeezed together: each of the two injections gives one inequality, and the
two subspaces meeting only in `0` inside a space of the total dimension gives the third, which
together leave no room. -/
private theorem finrank_symmetricInvariantForms_and_alternatingInvariantForms
    (ρ : Representation k G V) :
    finrank k (symmetricInvariantForms ρ) = finrank k (ρ.symmetricPower 2).invariants ∧
      finrank k (alternatingInvariantForms ρ) = finrank k (ρ.exteriorPower 2).invariants := by
  have h₁ := finrank_invariants_symmetricPower_le ρ
  have h₂ := finrank_invariants_exteriorPower_le ρ
  have h₃ := finrank_symmetricInvariantForms_add_le ρ
  have h₄ := finrank_invariantForms ρ
  omega

/-- **The invariant symmetric forms are as many as the invariants of the symmetric square.** -/
theorem finrank_symmetricInvariantForms (ρ : Representation k G V) :
    finrank k (symmetricInvariantForms ρ) = finrank k (ρ.symmetricPower 2).invariants :=
  (finrank_symmetricInvariantForms_and_alternatingInvariantForms ρ).1

/-- **The invariant alternating forms are as many as the invariants of the exterior square.** -/
theorem finrank_alternatingInvariantForms (ρ : Representation k G V) :
    finrank k (alternatingInvariantForms ρ) = finrank k (ρ.exteriorPower 2).invariants :=
  (finrank_symmetricInvariantForms_and_alternatingInvariantForms ρ).2

/-- **Every invariant symmetric form comes from an invariant functional on the symmetric square.**
The injection is onto: it lands in the invariant symmetric forms, and the two have the same
dimension. -/
theorem map_ofSymmetricSquareDual_eq_symmetricInvariantForms (ρ : Representation k G V) :
    Submodule.map (BilinForm.ofSymmetricSquareDual (k := k) (V := V))
        ((ρ.symmetricPower 2).dual).invariants = symmetricInvariantForms ρ :=
  Submodule.eq_of_le_of_finrank_le (K := k) (V := BilinForm k V)
    (map_ofSymmetricSquareDual_le ρ)
    (by rw [finrank_map_ofSymmetricSquareDual, finrank_symmetricInvariantForms])

/-- **Every invariant alternating form comes from an invariant functional on the exterior square.**
The injection is onto: it lands in the invariant alternating forms, and the two have the same
dimension. -/
theorem map_ofExteriorSquareDual_eq_alternatingInvariantForms (ρ : Representation k G V) :
    Submodule.map (BilinForm.ofExteriorSquareDual (k := k) (V := V))
        ((ρ.exteriorPower 2).dual).invariants = alternatingInvariantForms ρ :=
  Submodule.eq_of_le_of_finrank_le (K := k) (V := BilinForm k V)
    (map_ofExteriorSquareDual_le ρ)
    (by rw [finrank_map_ofExteriorSquareDual, finrank_alternatingInvariantForms])

/-- **The two invariant form counts add to the number of invariant forms.** -/
theorem finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms
    (ρ : Representation k G V) :
    finrank k (symmetricInvariantForms ρ) + finrank k (alternatingInvariantForms ρ) =
      finrank k (invariantForms ρ) := by
  rw [finrank_symmetricInvariantForms, finrank_alternatingInvariantForms, finrank_invariantForms]

end Counting

/-! ### The indicator as a signed count of invariant forms -/

section Indicator

variable [Field k] [CharZero k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- **The Frobenius-Schur indicator is the signed count of invariant bilinear forms**,
`ν₂(ρ) = dim {invariant symmetric forms} - dim {invariant alternating forms}`. -/
theorem frobeniusSchurIndicator_eq_sub_finrank_invariantForms (ρ : Representation k G V) :
    frobeniusSchurIndicator ρ = (finrank k (symmetricInvariantForms ρ) : k) -
      (finrank k (alternatingInvariantForms ρ) : k) := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariants, finrank_symmetricInvariantForms,
    finrank_alternatingInvariantForms]

end Indicator

/-! ### The trichotomy -/

section Trichotomy

variable [Field k] [CharZero k] [IsAlgClosed k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] {B : BilinForm k V}

omit [IsAlgClosed k] [ρ.IsIrreducible] in
/-- **The complex case.** A representation with no nonzero invariant form has Frobenius-Schur
indicator `0`. -/
theorem frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot (h : invariantForms ρ = ⊥) :
    frobeniusSchurIndicator ρ = 0 := by
  have hs : symmetricInvariantForms ρ = ⊥ :=
    le_bot_iff.mp (le_of_le_of_eq (symmetricInvariantForms_le ρ) h)
  have ha : alternatingInvariantForms ρ = ⊥ :=
    le_bot_iff.mp (le_of_le_of_eq (alternatingInvariantForms_le ρ) h)
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariantForms, hs, ha]
  simp

/-- **The orthogonal case.** An irreducible representation carrying a nonzero invariant symmetric
form has Frobenius-Schur indicator `1`.  Such a form is automatically nondegenerate, by
`TauCeti.Representation.IsInvariantForm.nondegenerate`. -/
theorem frobeniusSchurIndicator_eq_one_of_isSymm (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0)
    (hsymm : B.IsSymm) : frobeniusSchurIndicator ρ = 1 := by
  have hone : finrank k (invariantForms ρ) = 1 := by
    rw [hB.invariantForms_eq_span hB0]
    exact finrank_span_singleton (K := k) (V := BilinForm k V) hB0
  have hle : 1 ≤ finrank k (symmetricInvariantForms ρ) :=
    Submodule.one_le_finrank_iff (R := k) (M := BilinForm k V) |>.mpr
      ((Submodule.ne_bot_iff _).mpr ⟨B, mem_symmetricInvariantForms.mpr ⟨hB, hsymm⟩, hB0⟩)
  have hadd := finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms ρ
  have hs : finrank k (symmetricInvariantForms ρ) = 1 := by omega
  have ha : finrank k (alternatingInvariantForms ρ) = 0 := by omega
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariantForms, hs, ha]
  simp

/-- **The symplectic case.** An irreducible representation carrying a nonzero invariant alternating
form has Frobenius-Schur indicator `-1`.  Such a form is automatically nondegenerate, by
`TauCeti.Representation.IsInvariantForm.nondegenerate`. -/
theorem frobeniusSchurIndicator_eq_neg_one_of_isAlt (hB : IsInvariantForm ρ B) (hB0 : B ≠ 0)
    (halt : B.IsAlt) : frobeniusSchurIndicator ρ = -1 := by
  have hone : finrank k (invariantForms ρ) = 1 := by
    rw [hB.invariantForms_eq_span hB0]
    exact finrank_span_singleton (K := k) (V := BilinForm k V) hB0
  have hle : 1 ≤ finrank k (alternatingInvariantForms ρ) :=
    Submodule.one_le_finrank_iff (R := k) (M := BilinForm k V) |>.mpr
      ((Submodule.ne_bot_iff _).mpr ⟨B, mem_alternatingInvariantForms.mpr ⟨hB, halt⟩, hB0⟩)
  have hadd := finrank_symmetricInvariantForms_add_finrank_alternatingInvariantForms ρ
  have hs : finrank k (symmetricInvariantForms ρ) = 0 := by omega
  have ha : finrank k (alternatingInvariantForms ρ) = 1 := by omega
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariantForms, hs, ha]
  simp

omit [CharZero k] [Fintype G] in
/-- **An irreducible representation is orthogonal, symplectic or complex.** Away from
characteristic two, over an algebraically closed field it carries a nonzero invariant symmetric
form, or a nonzero invariant alternating form, or no nonzero invariant form at all.  This is the
case split the three values of the indicator are read off from. -/
theorem exists_isSymm_or_exists_isAlt_or_invariantForms_eq_bot (h2 : (2 : k) ≠ 0) :
    (∃ B : BilinForm k V, IsInvariantForm ρ B ∧ B ≠ 0 ∧ B.IsSymm) ∨
      (∃ B : BilinForm k V, IsInvariantForm ρ B ∧ B ≠ 0 ∧ B.IsAlt) ∨ invariantForms ρ = ⊥ := by
  by_cases hbot : invariantForms ρ = ⊥
  · exact Or.inr (Or.inr hbot)
  · obtain ⟨C, hCmem, hC0⟩ := (Submodule.ne_bot_iff _).mp hbot
    have hC : IsInvariantForm ρ C := mem_invariantForms.mp hCmem
    rcases hC.isSymm_or_isAlt h2 hC0 with hsymm | halt
    · exact Or.inl ⟨C, hC, hC0, hsymm⟩
    · exact Or.inr (Or.inl ⟨C, hC, hC0, halt⟩)

/-- **The Frobenius-Schur trichotomy.** The indicator of an irreducible representation over an
algebraically closed field of characteristic zero takes only the values `1`, `0` and `-1`. -/
theorem frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one :
    frobeniusSchurIndicator ρ = 1 ∨ frobeniusSchurIndicator ρ = 0 ∨
      frobeniusSchurIndicator ρ = -1 := by
  rcases exists_isSymm_or_exists_isAlt_or_invariantForms_eq_bot ρ (by norm_num) with
    ⟨_, hB, hB0, hsymm⟩ | ⟨_, hB, hB0, halt⟩ | hbot
  · exact Or.inl (frobeniusSchurIndicator_eq_one_of_isSymm ρ hB hB0 hsymm)
  · exact Or.inr (Or.inr (frobeniusSchurIndicator_eq_neg_one_of_isAlt ρ hB hB0 halt))
  · exact Or.inr (Or.inl (frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot ρ hbot))

/-- **The indicator is `1` exactly in the orthogonal case**, that is, exactly when the
representation carries a nondegenerate invariant symmetric form.  Nondegeneracy is nonvanishing
here, by `TauCeti.Representation.IsInvariantForm.nondegenerate_iff_ne_zero`. -/
theorem frobeniusSchurIndicator_eq_one_iff :
    frobeniusSchurIndicator ρ = 1 ↔
      ∃ B : BilinForm k V, IsInvariantForm ρ B ∧ B.IsSymm ∧ B.Nondegenerate := by
  refine ⟨fun h => ?_, fun ⟨_, hB, hsymm, hnd⟩ =>
    frobeniusSchurIndicator_eq_one_of_isSymm ρ hB (hB.nondegenerate_iff_ne_zero.mp hnd) hsymm⟩
  rcases exists_isSymm_or_exists_isAlt_or_invariantForms_eq_bot ρ (by norm_num) with
    ⟨C, hC, hC0, hsymm⟩ | ⟨_, hB, hB0, halt⟩ | hbot
  · exact ⟨C, hC, hsymm, hC.nondegenerate hC0⟩
  · rw [frobeniusSchurIndicator_eq_neg_one_of_isAlt ρ hB hB0 halt] at h
    exact absurd h (by norm_num)
  · rw [frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot ρ hbot] at h
    exact absurd h.symm one_ne_zero

/-- **The indicator is `-1` exactly in the symplectic case**, that is, exactly when the
representation carries a nondegenerate invariant alternating form.  Nondegeneracy is nonvanishing
here, by `TauCeti.Representation.IsInvariantForm.nondegenerate_iff_ne_zero`. -/
theorem frobeniusSchurIndicator_eq_neg_one_iff :
    frobeniusSchurIndicator ρ = -1 ↔
      ∃ B : BilinForm k V, IsInvariantForm ρ B ∧ B.IsAlt ∧ B.Nondegenerate := by
  refine ⟨fun h => ?_, fun ⟨_, hB, halt, hnd⟩ =>
    frobeniusSchurIndicator_eq_neg_one_of_isAlt ρ hB (hB.nondegenerate_iff_ne_zero.mp hnd) halt⟩
  rcases exists_isSymm_or_exists_isAlt_or_invariantForms_eq_bot ρ (by norm_num) with
    ⟨_, hB, hB0, hsymm⟩ | ⟨C, hC, hC0, halt⟩ | hbot
  · rw [frobeniusSchurIndicator_eq_one_of_isSymm ρ hB hB0 hsymm] at h
    exact absurd h (by norm_num)
  · exact ⟨C, hC, halt, hC.nondegenerate hC0⟩
  · rw [frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot ρ hbot] at h
    exact absurd h (by norm_num)

/-- **The indicator is `0` exactly in the complex case**, that is, exactly when the representation
carries no nonzero invariant bilinear form at all. -/
theorem frobeniusSchurIndicator_eq_zero_iff :
    frobeniusSchurIndicator ρ = 0 ↔ invariantForms ρ = ⊥ := by
  refine ⟨fun h => ?_, frobeniusSchurIndicator_eq_zero_of_invariantForms_eq_bot ρ⟩
  rcases exists_isSymm_or_exists_isAlt_or_invariantForms_eq_bot ρ (by norm_num) with
    ⟨_, hB, hB0, hsymm⟩ | ⟨_, hB, hB0, halt⟩ | hbot
  · rw [frobeniusSchurIndicator_eq_one_of_isSymm ρ hB hB0 hsymm] at h
    exact absurd h one_ne_zero
  · rw [frobeniusSchurIndicator_eq_neg_one_of_isAlt ρ hB hB0 halt] at h
    exact absurd h (by norm_num)
  · exact hbot

end Trichotomy

end Representation

end TauCeti
