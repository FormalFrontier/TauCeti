/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.LongestElement
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit

public section

/-!
# The sign character of a Weyl group

The Weyl group of a root pairing carries a canonical homomorphism to `ℤˣ` sending every reflection
to `-1`. This file builds it as `TauCeti.weylSign`, from the parity of the inversion count: the
number of positive roots that an element sends to negative roots, taken modulo two.

Two facts make the construction work, and both are already available at the root level. A word in
the simple reflections spells an element whose inversion count has the parity of the word length
(`TauCeti.ncard_inversions_wordProd_modEq_length`), and every element is spelled by such a word
(`TauCeti.exists_wordProd_eq_and_length_eq_ncard_inversions`). Concatenating words therefore adds
inversion counts modulo two, which is exactly multiplicativity of `(-1) ^ (inversion count)`. No
Coxeter presentation is used: everything is stated in terms of `TauCeti.inversions` and
`TauCeti.wordProd`.

Although the definition names a base, the resulting character does not depend on it. Every root is
Weyl-conjugate to a simple root (`TauCeti.exists_mem_support_weylGroupToPerm_eq`), and `ℤˣ` is
commutative, so the reflection in *any* root — simple or not — has sign `-1`. Since the reflections
generate the Weyl group, a homomorphism to `ℤˣ` killing no reflection is unique, and two bases give
the same character.

## Main definitions

* `TauCeti.weylSign`: the sign character `P.weylGroup →* ℤˣ` of a base, `w ↦ (-1) ^ ℓ(w)` with
  `ℓ(w)` the number of inversions.

## Main results

* `TauCeti.ncard_inversions_mul_modEq`: the inversion count is additive modulo two, the fact that
  makes `TauCeti.weylSign` a homomorphism.
* `TauCeti.weylSign_ofIdx`: **every reflection has sign `-1`**, not only the simple ones.
* `TauCeti.weylSign_wordProd`: a word of `n` letters spells an element of sign `(-1) ^ n`.
* `TauCeti.weylSign_eq_one_iff` and `TauCeti.weylSign_eq_neg_one_iff`: the sign reads off the
  parity of the inversion count.
* `TauCeti.eq_weylSign_of_forall_ofIdx`: **the sign character is the unique homomorphism to `ℤˣ`
  sending every reflection to `-1`**, whence `TauCeti.weylSign_eq_weylSign`: **it does not depend
  on the base**.
* `TauCeti.weylSign_longestElement`: the longest element has sign `(-1) ^ |Φ⁺|`.

## Implementation notes

The target is `ℤˣ` rather than a two-element type of one's own, matching Mathlib's
`Equiv.Perm.sign` and the `(-1 : ℤˣ) ^ _` spelling that the Weyl numerator of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md` asks for.

`TauCeti.weylSign_apply` is deliberately not a `simp` lemma. Unfolding the character back to a
power of `-1` would take every lemma below out of simp-normal form, `TauCeti.weylSign_ofIdx` first
among them; the computations are meant to be done through the named lemmas, not by re-exposing the
inversion count.

The base-independence statement is an equality of homomorphisms rather than a definition of a
base-free `weylSign P`, because a base is what the inversion count is measured against: there is no
canonical choice to build the definition on, only the theorem that the choice does not matter.

## References

The sign character is the "`sgn(w)`" of the Weyl numerator
`∑_{w ∈ W} sgn(w) e^{w(λ+ρ) - ρ}` in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md` (the Weyl character formula, the
Weyl dimension formula and Kostant's multiplicity formula are all stated with it), and of the
Tits-sign criterion in the same layer. Its well-definedness is the length-parity statement
`TauCeti.length_modEq_length_of_wordProd_eq` recorded in Layer 1 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, whose docstring names this character
as its purpose; this file is that prerequisite, built where the inversion combinatorics lives.

The convention follows Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Ch. VI §1, and
J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. III §10.3.
-/

namespace TauCeti

open Set

universe u v w x

/-- Powers of `-1` in `ℤˣ` at exponents of the same parity agree. This is
`neg_one_pow_congr` in the spelling the inversion-count congruences below produce. -/
private lemma neg_one_pow_eq_of_modEq {m n : ℕ} (h : m ≡ n [MOD 2]) :
    (-1 : ℤˣ) ^ m = (-1 : ℤˣ) ^ n :=
  neg_one_pow_congr (by rw [Nat.even_iff, Nat.even_iff, (h : m % 2 = n % 2)])

/-- `ℤˣ` really has two elements, which is what makes the sign character detect parity. -/
private lemma intUnits_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := fun h ↦ by
  have h' : ((-1 : ℤˣ) : ℤ) = ((1 : ℤˣ) : ℤ) := congrArg Units.val h
  simp at h'

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-! ### The inversion count modulo two -/

/-- **The inversion count is additive modulo two.** Spell each factor by a word of exactly as many
letters as it has inversions and concatenate: the product is spelled by a word whose length is the
sum of the two lengths, and a word spells an element whose inversion count has the parity of the
word length.

Additivity itself fails — `TauCeti.ncard_inversions_mul_le` is only an inequality — so the parity
is the sharpest statement available, and it is exactly what a sign character needs. -/
theorem ncard_inversions_mul_modEq (v w : P.weylGroup) :
    (inversions P b (v * w)).ncard
      ≡ (inversions P b v).ncard + (inversions P b w).ncard [MOD 2] := by
  obtain ⟨l, hl, hlen⟩ := exists_wordProd_eq_and_length_eq_ncard_inversions P b v
  obtain ⟨l', hl', hlen'⟩ := exists_wordProd_eq_and_length_eq_ncard_inversions P b w
  have h := ncard_inversions_wordProd_modEq_length P b (l ++ l')
  rwa [wordProd_append, hl, hl', List.length_append, hlen, hlen'] at h

/-! ### The sign character -/

/-- **The sign character of a Weyl group**, relative to a base: `w ↦ (-1) ^ ℓ(w)`, where `ℓ(w)` is
the number of positive roots that `w` sends to negative roots. It is a homomorphism because the
inversion count is additive modulo two, and it does not depend on the base
(`TauCeti.weylSign_eq_weylSign`). -/
noncomputable def weylSign : P.weylGroup →* ℤˣ where
  toFun w := (-1) ^ (inversions P b w).ncard
  map_one' := by rw [ncard_inversions_one, pow_zero]
  map_mul' v w := by
    rw [neg_one_pow_eq_of_modEq (ncard_inversions_mul_modEq P b v w), pow_add]

/-- The sign character is the corresponding power of `-1`. Not a `simp` lemma; see the
implementation notes. -/
theorem weylSign_apply (w : P.weylGroup) :
    weylSign P b w = (-1) ^ (inversions P b w).ncard := (rfl)

/-- A simple reflection has sign `-1`: it has exactly one inversion, its own simple root. This is
the stepping stone to `TauCeti.weylSign_ofIdx`, which drops the simplicity hypothesis. -/
private lemma weylSign_ofIdx_of_mem_support {i : ι} (hi : i ∈ b.support) :
    weylSign P b (RootPairing.weylGroup.ofIdx P i) = -1 := by
  rw [weylSign_apply, ncard_inversions_ofIdx P b hi, pow_one]

/-- **Every reflection has sign `-1`**, and not merely the simple ones: a reflection in an
arbitrary root is conjugate to a simple reflection, and `ℤˣ` is commutative, so conjugation cannot
change the sign. -/
@[simp]
theorem weylSign_ofIdx (i : ι) :
    weylSign P b (RootPairing.weylGroup.ofIdx P i) = -1 := by
  obtain ⟨j, hj, v, hv⟩ := exists_mem_support_weylGroupToPerm_eq b i
  rw [← hv, RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj, map_mul, map_mul, map_inv,
    weylSign_ofIdx_of_mem_support P b hj, mul_right_comm, mul_inv_cancel, one_mul]

/-- **A word of `n` letters spells an element of sign `(-1) ^ n`.** In particular all the words
spelling one element have the same length parity, which is the well-definedness that
`TauCeti.length_modEq_length_of_wordProd_eq` records at the level of inversion counts. -/
theorem weylSign_wordProd (l : List b.support) :
    weylSign P b (wordProd P b l) = (-1) ^ l.length := by
  rw [weylSign_apply, neg_one_pow_eq_of_modEq (ncard_inversions_wordProd_modEq_length P b l)]

/-- Appending a reflection flips the sign. For a simple reflection this is the multiplicative
form of the exchange step `TauCeti.ncard_inversions_mul_ofIdx`, which moves the inversion count by
exactly one; here the reflecting root need not be simple. -/
theorem weylSign_mul_ofIdx (w : P.weylGroup) (i : ι) :
    weylSign P b (w * RootPairing.weylGroup.ofIdx P i) = - weylSign P b w := by
  rw [map_mul, weylSign_ofIdx, mul_neg, mul_one]

/-- Prefixing a reflection flips the sign. -/
theorem weylSign_ofIdx_mul (i : ι) (w : P.weylGroup) :
    weylSign P b (RootPairing.weylGroup.ofIdx P i * w) = - weylSign P b w := by
  rw [map_mul, weylSign_ofIdx, neg_one_mul]

/-- **The sign is trivial exactly on the elements with an even number of inversions.** -/
theorem weylSign_eq_one_iff (w : P.weylGroup) :
    weylSign P b w = 1 ↔ Even (inversions P b w).ncard := by
  rw [weylSign_apply, neg_one_pow_eq_one_iff_even intUnits_neg_one_ne_one]

/-- **The sign is `-1` exactly on the elements with an odd number of inversions.** -/
theorem weylSign_eq_neg_one_iff (w : P.weylGroup) :
    weylSign P b w = -1 ↔ Odd (inversions P b w).ncard := by
  rw [weylSign_apply, neg_one_pow_eq_neg_one_iff_odd intUnits_neg_one_ne_one]

/-- **The sign character is onto `ℤˣ`** as soon as there is a root to reflect in, so the elements
with an even number of inversions form a *proper* subgroup: the character is not the trivial one,
and the parity it measures is genuine information. -/
theorem weylSign_surjective [Nonempty ι] : Function.Surjective (weylSign P b) := by
  intro u
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨RootPairing.weylGroup.ofIdx P i, weylSign_ofIdx P b i⟩

/-! ### The sign character is intrinsic -/

/-- **The sign character is the only homomorphism to `ℤˣ` sending every reflection to `-1`.** The
reflections generate the Weyl group, so a homomorphism out of it is determined by its values on
them; the content is that `TauCeti.weylSign` takes the prescribed values, which is
`TauCeti.weylSign_ofIdx`. -/
theorem eq_weylSign_of_forall_ofIdx {f : P.weylGroup →* ℤˣ}
    (hf : ∀ i : ι, f (RootPairing.weylGroup.ofIdx P i) = -1) : f = weylSign P b := by
  -- `ext` would descend past `MonoidHom.ext` into `Units.ext`, leaving the goal about the
  -- underlying integers; the homomorphism extensionality is the one the induction needs.
  refine MonoidHom.ext fun w ↦ ?_
  have hw : w ∈ Subgroup.closure (range fun i : b.support =>
      RootPairing.weylGroup.ofIdx P (i : ι)) := by
    rw [← weylGroup_eq_closure_simple P b]
    exact Subgroup.mem_top w
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [hf, weylSign_ofIdx]
  | one => rw [map_one, map_one]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
  | inv x _ hx => rw [map_inv, map_inv, hx]

/-- **The sign character does not depend on the base.** Both characters send every reflection to
`-1`, and that pins a homomorphism to `ℤˣ` uniquely. So the sign is an invariant of the Weyl group
of the root pairing, even though the inversion count defining it is not. -/
theorem weylSign_eq_weylSign (b₁ b₂ : P.Base) : weylSign P b₁ = weylSign P b₂ :=
  eq_weylSign_of_forall_ofIdx P b₂ (weylSign_ofIdx P b₁)

/-- **The parity of the inversion count does not depend on the base either**, the pointwise
reading of `TauCeti.weylSign_eq_weylSign`. The counts themselves need not agree: moving the base
by a Weyl-group element conjugates the element whose inversions are being counted, and conjugate
elements have different lengths in general. -/
theorem even_ncard_inversions_iff (b₁ b₂ : P.Base) (w : P.weylGroup) :
    Even (inversions P b₁ w).ncard ↔ Even (inversions P b₂ w).ncard := by
  rw [← weylSign_eq_one_iff, ← weylSign_eq_one_iff, weylSign_eq_weylSign P b₁ b₂]

/-! ### The longest element -/

section IsRootSystem

variable [P.IsRootSystem]

/-- **The longest element has sign `(-1) ^ |Φ⁺|`**: it inverts every positive root, so its
inversion count is the number of positive roots. -/
theorem weylSign_longestElement :
    weylSign P b (longestElement P b) = (-1) ^ (posRoots P b).ncard := by
  rw [weylSign_apply, ncard_inversions_longestElement]

end IsRootSystem

end TauCeti
