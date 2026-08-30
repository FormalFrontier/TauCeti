/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.TrivialIntersection
public import TauCeti.RepresentationTheory.Induction.VirtualCharacter

/-!
# The exceptional character attached to a trivial-intersection subgroup

Let `H` be a trivial-intersection subgroup of a finite group `G` (`TauCeti.IsTISubgroup`): one
meeting each of its distinct conjugates trivially, as a Frobenius complement does.  Induction from
such an `H` is an isometry on the class functions that vanish at the identity
(`TauCeti.characterPairing_ind_ind`, whose support form is `TauCeti.isometry_ind_of_isTISet`), but
it does not send characters to characters: `Ind_H^G φ` has
degree `|G : H| · φ(1)`, not `φ(1)`.  The classical repair is to induce not `φ` but `φ` corrected by
a multiple of the trivial character, and to add that multiple back on `G`:

`φ* = Ind_H^G (φ - φ(1) · 1_H) + φ(1) · 1_G`.

This file builds that class function, `TauCeti.ClassFunction.indExtend H φ`, as a `k`-linear map in
`φ`, and proves what makes it useful.  It has the same degree
(`TauCeti.ClassFunction.indExtend_apply_one`) and **restricts back to `φ`**
(`TauCeti.ClassFunction.comap_subtype_indExtend`); and the assignment `φ ↦ φ*` **preserves the
character pairing**
(`TauCeti.ClassFunction.characterPairing_indExtend_indExtend`), so it carries a norm-`1` virtual
character of `H` to a norm-`1` virtual character of `G`.  Over an algebraically closed field of
characteristic zero in which `|G|` is invertible, a norm-`1` virtual character is `±` an irreducible
character, and the degree pins down the sign: `φ*` is an **irreducible character of `G`**
(`TauCeti.ClassFunction.indExtend_mem_irreducibleCharacters`).  Restriction inverts the assignment,
so `φ ↦ φ*` is injective (`TauCeti.ClassFunction.indExtend_injective`), and `Irr(H)` embeds into
`Irr(G)` with `Res_H φ* = φ`.

That embedding is the exceptional-character correspondence, the step at which the
character-theoretic proof of Frobenius's theorem produces the irreducible characters of `G` whose
common kernel is the Frobenius kernel.  Nothing here asserts that the kernel is a subgroup; that
uses the family of these characters and is a separate target.

## Why the correction term is needed

Two properties of `φ*` are in tension, and the correction is exactly what reconciles them.  The
pairing is preserved only for class functions vanishing at the identity — `Ind` is an isometry
*there*, and `Ind 1_H` has norm `#(H \ G / H)`, not `1` — while a character of `G` must take the
value `φ(1)` at the identity, and `Ind φ` takes `|G : H| · φ(1)`.  Subtracting `φ(1) · 1_H` before
inducing buys the first, and adding `φ(1) · 1_G` afterwards buys the second, without disturbing the
first: the trivial character of `G` is itself the extension of the trivial character of `H`, and the
cross terms cancel.  This is why `TauCeti.ClassFunction.characterPairing_indExtend_indExtend` is an
identity of pairings on the nose, with no error term.

## Main definitions

* `TauCeti.ClassFunction.indExtend`: the `k`-linear map `φ ↦ φ*` above, with
  `TauCeti.ClassFunction.indExtend_def` its defining formula.

## Main results

* `TauCeti.ClassFunction.comap_subtype_indExtend`: `Res_H φ* = φ`, and
  `TauCeti.ClassFunction.indExtend_apply_one`: `φ*(1) = φ(1)`.
* `TauCeti.ClassFunction.characterPairing_indExtend_indExtend`: `⟨φ*, ψ*⟩_G = ⟨φ, ψ⟩_H`.
* `TauCeti.ClassFunction.indExtend_ofCharacter_trivial`: the trivial character of `H` extends to the
  trivial character of `G`.
* `TauCeti.ClassFunction.indExtend_mem_virtualCharacters`: `φ*` is a virtual character of `G` when
  `φ` is one of `H` of integral degree.
* `TauCeti.ClassFunction.indExtend_mem_irreducibleCharacters`: **`φ*` is an irreducible character
  of `G` when `φ` is one of `H`**, and `TauCeti.ClassFunction.indExtend_injective`: distinct class
  functions have distinct extensions.

## Implementation notes

`TauCeti.ClassFunction.indExtend` is bundled as a `k`-linear map, matching
`TauCeti.ClassFunction.ind`: the value at the identity is a linear functional of `φ`, so the
correction is linear in `φ` too, and the pairing identity then says exactly that the map is an
isometry for `TauCeti.ClassFunction.characterPairing`.  Because the definition is not exposed,
`TauCeti.ClassFunction.indExtend_def` records the defining formula for consumers.

The trivial character is spelled `TauCeti.ClassFunction.ofCharacter (Representation.trivial k _ k)`,
as elsewhere in this directory, rather than as a bundled constant function; the private lemmas
`comap_subtype_ofCharacter_trivial` and `characterPairing_ofCharacter_trivial_self` are what the
proofs need of it, and neither belongs in this file's interface.

`TauCeti.ClassFunction.indExtend_mem_virtualCharacters` carries the hypothesis that `φ(1)` is the
image of an integer.  That is not decoration: the correction term is the scalar multiple
`φ(1) · 1_G`, which lies in the virtual-character lattice — an additive subgroup, not a
`k`-submodule — only for an integral scalar.  For a virtual character `φ` over an algebraically
closed field the degree is automatically integral, and
`TauCeti.ClassFunction.indExtend_mem_irreducibleCharacters` discharges the hypothesis with the
degree of an irreducible character.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 7, Lemma 7.2 and Theorem 7.5.
* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 8, the exceptional-character correspondence.
-/

public section

namespace TauCeti

universe u v

namespace ClassFunction

variable {k : Type u} {G : Type v} [Field k] [Group G] {H : Subgroup G}

variable (H) in
/-- **The exceptional extension `φ*` of a class function `φ` of a subgroup `H`**: induce `φ`
corrected by `φ(1)` times the trivial character of `H`, then add `φ(1)` times the trivial character
of `G`.

The corrected class function vanishes at the identity, which is what makes induction from a
trivial-intersection subgroup an isometry on it; adding the multiple of the trivial character of `G`
back restores the degree, `φ*(1) = φ(1)`. -/
noncomputable def indExtend [H.FiniteIndex] : ClassFunction k H →ₗ[k] ClassFunction k G where
  toFun φ := ind H (φ - φ.1 1 • ofCharacter (Representation.trivial k H k)) +
    φ.1 1 • ofCharacter (Representation.trivial k G k)
  map_add' φ ψ := by
    have hval : ((φ + ψ : ClassFunction k H) : H → k) 1 = φ.1 1 + ψ.1 1 := rfl
    have hinner : (φ + ψ : ClassFunction k H) -
        ((φ + ψ : ClassFunction k H) : H → k) 1 • ofCharacter (Representation.trivial k H k) =
          (φ - φ.1 1 • ofCharacter (Representation.trivial k H k)) +
            (ψ - ψ.1 1 • ofCharacter (Representation.trivial k H k)) := by
      rw [hval, add_smul]
      abel
    rw [hinner, hval, map_add, add_smul]
    abel
  map_smul' c φ := by
    have hval : ((c • φ : ClassFunction k H) : H → k) 1 = c * φ.1 1 := rfl
    have hinner : (c • φ : ClassFunction k H) -
        ((c • φ : ClassFunction k H) : H → k) 1 • ofCharacter (Representation.trivial k H k) =
          c • (φ - φ.1 1 • ofCharacter (Representation.trivial k H k)) := by
      rw [hval, smul_sub, mul_smul]
    rw [hinner, hval, map_smul, RingHom.id_apply, smul_add, mul_smul]

/-- **The defining formula of the exceptional extension.**  The definition itself is not exposed,
so this is what a consumer unfolds it with. -/
theorem indExtend_def [H.FiniteIndex] (φ : ClassFunction k H) :
    indExtend H φ = ind H (φ - φ.1 1 • ofCharacter (Representation.trivial k H k)) +
      φ.1 1 • ofCharacter (Representation.trivial k G k) :=
  (rfl)

/-- **The exceptional extension of the trivial character is the trivial character.**

Here the correction cancels the induction outright, `1_H - 1_H = 0`, so nothing is induced and the
whole value is the correction term on `G`.  No hypothesis on `H` is needed, and the normalization
this records is what makes the extension an *extension* rather than an arbitrary repair. -/
@[simp]
theorem indExtend_ofCharacter_trivial [H.FiniteIndex] :
    indExtend H (ofCharacter (Representation.trivial k H k)) =
      ofCharacter (Representation.trivial k G k) := by
  rw [indExtend_def]
  simp

/-- The corrected class function `φ - φ(1) · 1_H` vanishes at the identity, as designed. -/
private theorem sub_smul_trivial_apply_one (φ : ClassFunction k H) :
    ((φ - φ.1 1 • ofCharacter (Representation.trivial k H k) : ClassFunction k H) : H → k) 1 =
      0 := by
  simp

/-- Forgetting the class-function bundling of an induced class function. -/
private theorem coe_ind [H.FiniteIndex] (f : ClassFunction k H) :
    ((ind H f : ClassFunction k G) : G → k) = indClassFun H (f : H → k) :=
  funext fun g => ind_apply f g

/-- The trivial character of `G` restricts to the trivial character of `H`. -/
private theorem comap_subtype_ofCharacter_trivial :
    comap H.subtype (ofCharacter (Representation.trivial k G k)) =
      ofCharacter (Representation.trivial k H k) :=
  Subtype.ext (funext fun _ => by simp)

/-- The trivial character has norm `1`. -/
private theorem characterPairing_ofCharacter_trivial_self [Fintype G]
    (hG : IsUnit (Nat.card G : k)) :
    characterPairing (ofCharacter (Representation.trivial k G k))
      (ofCharacter (Representation.trivial k G k)) = (1 : k) := by
  rw [characterPairing_apply]
  simp only [ofCharacter_apply, Representation.char_trivial, Module.finrank_self, Nat.cast_one,
    mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  exact inv_mul_cancel₀ hG.ne_zero

/-- The trivial character of `G` is the constant function `1`. -/
private theorem coe_ofCharacter_trivial :
    ((ofCharacter (Representation.trivial k G k) : ClassFunction k G) : G → k) = 1 :=
  funext fun _ => by simp

/-- Induction takes a class function vanishing at the identity to one vanishing at the identity:
every summand of the coset sum at the identity is the value of `f` at the identity. -/
private theorem ind_apply_one_of_apply_one_eq_zero [H.FiniteIndex] {f : ClassFunction k H}
    (hf : (f : H → k) 1 = 0) : (ind H f).1 1 = 0 := by
  classical
  rw [ind_apply, indClassFun_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  -- the representative conjugates the identity to the identity, so every summand is `f 1`
  simp only [mul_one, inv_mul_cancel, one_mem, ↓reduceDIte]
  exact hf

/-- Expanding the pairing of two class functions each corrected by a multiple of the trivial
character. -/
private theorem characterPairing_sub_smul_trivial [Fintype G] (hG : IsUnit (Nat.card G : k))
    (f g : ClassFunction k G) (c d : k) :
    characterPairing (f - c • ofCharacter (Representation.trivial k G k))
        (g - d • ofCharacter (Representation.trivial k G k)) =
      characterPairing f g - d * characterPairing f (ofCharacter (Representation.trivial k G k)) -
        c * characterPairing g (ofCharacter (Representation.trivial k G k)) + c * d := by
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    characterPairing_ofCharacter_trivial_self hG,
    characterPairing_symm (ofCharacter (Representation.trivial k G k)) g]
  ring

/-- Expanding the pairing of a corrected class function against the trivial character. -/
private theorem characterPairing_sub_smul_trivial_right [Fintype G]
    (hG : IsUnit (Nat.card G : k)) (f : ClassFunction k G) (c : k) :
    characterPairing (f - c • ofCharacter (Representation.trivial k G k))
        (ofCharacter (Representation.trivial k G k)) =
      characterPairing f (ofCharacter (Representation.trivial k G k)) - c := by
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    characterPairing_ofCharacter_trivial_self hG]
  ring

/-- **The exceptional extension has the same degree as the class function it came from.**

The correction term is what makes this work: `φ - φ(1) · 1_H` vanishes at the identity, so its
induction does too, and the value at the identity is the correction term alone. -/
@[simp]
theorem indExtend_apply_one [H.FiniteIndex] (φ : ClassFunction k H) :
    (indExtend H φ).1 1 = φ.1 1 := by
  rw [indExtend_def, Submodule.coe_add, Pi.add_apply,
    ind_apply_one_of_apply_one_eq_zero (sub_smul_trivial_apply_one φ), SetLike.val_smul,
    coe_ofCharacter_trivial]
  simp

section Restriction

variable [Finite G]

/-- **The exceptional extension restricts back to the class function it came from**, for a
trivial-intersection subgroup whose order is invertible in `k`.

The correction term is what makes this work: `φ - φ(1) · 1_H` vanishes at the identity, so
restriction undoes its induction (`TauCeti.ClassFunction.comap_subtype_ind_eq_self`), and the
trivial character of `G` restricts to that of `H`, returning the term that was subtracted. -/
theorem comap_subtype_indExtend (hH : IsTISubgroup H) (hk : IsUnit (Nat.card H : k))
    (φ : ClassFunction k H) : comap H.subtype (indExtend H φ) = φ := by
  rw [indExtend_def, map_add, map_smul,
    comap_subtype_ind_eq_self hH hk _ (sub_smul_trivial_apply_one φ),
    comap_subtype_ofCharacter_trivial, sub_add_cancel]

/-- **Distinct class functions have distinct exceptional extensions**, restriction being a left
inverse of the extension. -/
theorem indExtend_injective (hH : IsTISubgroup H) (hk : IsUnit (Nat.card H : k)) :
    Function.Injective (indExtend (k := k) H) := fun φ ψ h => by
  rw [← comap_subtype_indExtend hH hk φ, ← comap_subtype_indExtend hH hk ψ, h]

end Restriction

section Pairing

variable [Fintype G]

open scoped Classical in
/-- **The exceptional extension preserves the character pairing**, for a trivial-intersection
subgroup of a finite group whose order is invertible in `k`.

Both the induction isometry and the correction term are used, and the point is that the correction
costs nothing.  Writing `θ = φ - φ(1) · 1_H`, induction is an isometry on `θ` because `θ` vanishes
at the identity; the cross terms `⟨Ind θ, 1_G⟩` collapse to `⟨θ, 1_H⟩` by Frobenius reciprocity,
because the trivial character of `G` restricts to that of `H`; and `1_G` has norm `1`.  Expanding,
every occurrence of `φ(1)` and `ψ(1)` cancels. -/
theorem characterPairing_indExtend_indExtend (hG : IsUnit (Nat.card G : k)) (hH : IsTISubgroup H)
    (φ ψ : ClassFunction k H) :
    characterPairing (indExtend H φ) (indExtend H ψ) = characterPairing φ ψ := by
  have hk : IsUnit (Nat.card H : k) := isUnit_natCard_subgroup H hG
  -- Frobenius reciprocity against the trivial character, which restricts to the trivial character
  have hcross : ∀ f : ClassFunction k H,
      characterPairing (ind H f) (ofCharacter (Representation.trivial k G k)) =
        characterPairing f (ofCharacter (Representation.trivial k H k)) :=
    fun f => by rw [characterPairing_ind hG, comap_subtype_ofCharacter_trivial]
  -- the induction isometry on the two corrected class functions
  have hAB : characterPairing
      (ind H (φ - φ.1 1 • ofCharacter (Representation.trivial k H k)))
      (ind H (ψ - ψ.1 1 • ofCharacter (Representation.trivial k H k))) =
        characterPairing φ ψ -
          ψ.1 1 * characterPairing φ (ofCharacter (Representation.trivial k H k)) -
          φ.1 1 * characterPairing ψ (ofCharacter (Representation.trivial k H k)) +
          φ.1 1 * ψ.1 1 := by
    rw [characterPairing_ind_ind hG hH _ _ (sub_smul_trivial_apply_one ψ),
      characterPairing_sub_smul_trivial hk]
  have hAtG : characterPairing
      (ind H (φ - φ.1 1 • ofCharacter (Representation.trivial k H k)))
      (ofCharacter (Representation.trivial k G k)) =
        characterPairing φ (ofCharacter (Representation.trivial k H k)) - φ.1 1 := by
    rw [hcross, characterPairing_sub_smul_trivial_right hk]
  have htGB : characterPairing (ofCharacter (Representation.trivial k G k))
      (ind H (ψ - ψ.1 1 • ofCharacter (Representation.trivial k H k))) =
        characterPairing ψ (ofCharacter (Representation.trivial k H k)) - ψ.1 1 := by
    rw [characterPairing_symm, hcross, characterPairing_sub_smul_trivial_right hk]
  -- expand both extensions by bilinearity and cancel
  simp only [indExtend_def, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hAB, hAtG, htGB, characterPairing_ofCharacter_trivial_self hG]
  ring

end Pairing

section VirtualCharacter

variable [Finite G]

/-- **The exceptional extension of a virtual character of integral degree is a virtual
character.**

Both summands are accounted for: induction preserves the virtual-character lattice, and the
correction terms are integer multiples of the trivial character, which is the character of the
trivial representation.  Integrality of `φ(1)` is what makes those multiples lie in the lattice,
which is an additive subgroup and not a `k`-submodule. -/
theorem indExtend_mem_virtualCharacters {φ : ClassFunction k H} {n : ℤ}
    (hφ : (φ : H → k) ∈ virtualCharacters k H) (hn : φ.1 1 = (n : k)) :
    ((indExtend H φ : ClassFunction k G) : G → k) ∈ virtualCharacters k G := by
  have hsub : ((φ - φ.1 1 • ofCharacter (Representation.trivial k H k) : ClassFunction k H) :
      H → k) ∈ virtualCharacters k H := by
    have : ((φ - φ.1 1 • ofCharacter (Representation.trivial k H k) : ClassFunction k H) :
        H → k) = (φ : H → k) - n • (1 : H → k) := by
      rw [Submodule.coe_sub, SetLike.val_smul, coe_ofCharacter_trivial, hn,
        Int.cast_smul_eq_zsmul]
    rw [this]
    exact sub_mem hφ (zsmul_mem one_mem_virtualCharacters n)
  have hind : ((ind H (φ - φ.1 1 • ofCharacter (Representation.trivial k H k)) :
      ClassFunction k G) : G → k) ∈ virtualCharacters k G := by
    rw [coe_ind]
    exact indClassFun_mem_virtualCharacters H hsub
  have hcorr : ((φ.1 1 • ofCharacter (Representation.trivial k G k) : ClassFunction k G) :
      G → k) ∈ virtualCharacters k G := by
    have : ((φ.1 1 • ofCharacter (Representation.trivial k G k) : ClassFunction k G) : G → k) =
        n • (1 : G → k) := by
      rw [SetLike.val_smul, coe_ofCharacter_trivial, hn, Int.cast_smul_eq_zsmul]
    rw [this]
    exact zsmul_mem one_mem_virtualCharacters n
  rw [indExtend_def, Submodule.coe_add]
  exact add_mem hind hcorr

end VirtualCharacter

section Irreducible

variable [Finite G] [IsAlgClosed k] [CharZero k] [Invertible (Nat.card G : k)]

open scoped Classical in
/-- **The exceptional extension of an irreducible character of a trivial-intersection subgroup is
an irreducible character of the whole group.**

This is the exceptional-character correspondence: over an algebraically closed field of
characteristic zero in which `|G|` is invertible, `φ ↦ φ*` sends `Irr(H)` into `Irr(G)`, injectively
by `TauCeti.ClassFunction.indExtend_injective`, and with `Res_H φ* = φ` by
`TauCeti.ClassFunction.comap_subtype_indExtend`.

The proof is the norm-`1` test.  The extension is a virtual character of norm `1`, hence `±` an
irreducible character (`TauCeti.exists_eq_irreducibleCharacter_or_neg`); its value at the identity
is the degree of `φ`, a positive natural number, while the negative alternative would make that
value the negative of a positive natural number.  Characteristic zero is what rules the negative
alternative out. -/
theorem indExtend_mem_irreducibleCharacters (hH : IsTISubgroup H) {φ : ClassFunction k H}
    (hφ : (φ : H → k) ∈ irreducibleCharacters k H) :
    ((indExtend H φ : ClassFunction k G) : G → k) ∈ irreducibleCharacters k G := by
  have hG : IsUnit (Nat.card G : k) := isUnit_of_invertible _
  have hk : IsUnit (Nat.card H : k) := isUnit_natCard_subgroup H hG
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card H : k) := invertibleOfNonzero hk.ne_zero
  obtain ⟨j, hj⟩ := exists_irreducibleCharacter_eq (k := k) hφ
  -- the degree of `φ`, a positive natural number
  have hdeg : φ.1 1 = (characterDegree k j : k) := by
    rw [← hj, irreducibleCharacter_one]
  have hpos : 0 < characterDegree k j := characterDegree_pos k j
  -- `φ` has norm `1` and is a virtual character
  have hφclass : φ = ofCharacter (irreducibleRepresentation k j) :=
    Subtype.ext (funext fun x => by
      rw [ofCharacter_apply, character_irreducibleRepresentation, hj])
  have hnorm : characterPairing φ φ = 1 := by
    rw [hφclass]
    simp
  have hvirt : (φ : H → k) ∈ virtualCharacters k H := by
    rw [← hj]
    exact irreducibleCharacter_mem_virtualCharacters j
  -- so the extension is a virtual character of norm `1`
  have hstarnorm : characterPairing (indExtend H φ) (indExtend H φ) = 1 := by
    rw [characterPairing_indExtend_indExtend hG hH φ φ, hnorm]
  obtain ⟨i, hi⟩ := exists_eq_irreducibleCharacter_or_neg
    (indExtend_mem_virtualCharacters hvirt (n := (characterDegree k j : ℤ)) (by simpa using hdeg))
    hstarnorm
  rcases hi with hi | hi
  · rw [hi]
    exact irreducibleCharacter_mem k i
  -- the negative alternative would force a sum of two positive naturals to vanish in `k`
  · exfalso
    have hone : (indExtend H φ).1 1 = φ.1 1 := indExtend_apply_one φ
    rw [hdeg] at hone
    have hval : -(irreducibleCharacter k i (1 : G)) = (characterDegree k j : k) := by
      rw [← hone, hi]; rfl
    rw [irreducibleCharacter_one] at hval
    have hsum : ((characterDegree k i + characterDegree k j : ℕ) : k) = 0 := by
      push_cast
      linear_combination -hval
    rw [Nat.cast_eq_zero] at hsum
    omega

end Irreducible

end ClassFunction

end TauCeti
