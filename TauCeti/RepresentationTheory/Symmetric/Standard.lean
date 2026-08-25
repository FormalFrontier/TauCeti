/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Augmentation
public import TauCeti.RepresentationTheory.Irreducible

/-!
# The standard representation of the symmetric group

The symmetric group on a finite type `α` acts on `k[α]` by permuting the standard basis.  Inside
that permutation representation sit the invariant line spanned by the sum of the basis, carrying the
trivial representation, and the **standard representation**, the subrepresentation of dimension
`|α| - 1` on which the coefficients sum to zero; when `|α|` is invertible in `k` the two are
complementary and the permutation representation splits as their direct sum.  This file proves that
the standard representation is irreducible whenever `|α| ≥ 2` and either `|α| = 2` or `|α|` is
invertible in `k`.

The hypothesis `2 ≤ |α|` is needed: for `|α| ≤ 1` the standard representation is zero, and the zero
representation is not irreducible.  Given `2 ≤ |α|`, the disjunction is sharp.  Invertibility of
`|α|` cannot simply be dropped: as soon as `3 ≤ |α|` and `|α| = 0` in `k`, the sum of the standard
basis itself has vanishing coefficient sum, so the invariant line lies *inside* the standard
subrepresentation, and it is a proper subrepresentation because the standard one has dimension
`|α| - 1 ≥ 2`, so the latter is reducible -- this is the first place the modular theory departs
from the ordinary one, and it is excluded here rather than developed.  The remaining case is the
first disjunct: for `|α| = 2` the standard subrepresentation is a line -- in characteristic `2` it
*is* the invariant line -- and hence irreducible whatever the characteristic.

The argument is elementary and uses only transpositions.  If `v` has vanishing coefficient sum and
is nonzero, two of its coefficients differ, say at `x` and `y`; subtracting the transposition
`(x y)` applied to `v` from `v` leaves exactly `(v x - v y) • (x - y)`, so any nonzero invariant
subspace contains one difference `x - y` of basis vectors.  Transposing `y` with an arbitrary `z`
produces all the others, and those differences span.

## Main definitions

* `TauCeti.standardRepresentation`: the standard representation of `Equiv.Perm α` on the
  augmentation subrepresentation of `k[α]`.

## Main results

* `TauCeti.sub_ofMulAction_swap`: applying a transposition to `v` and subtracting leaves a multiple
  of a difference of two standard basis vectors.  This is the whole computational content.
* `TauCeti.isAtom_augmentationSubrepresentation`: the standard subrepresentation is an atom of the
  lattice of subrepresentations of `k[α]`, and
  `TauCeti.isIrreducible_standardRepresentation`: hence it is irreducible.

The two remaining halves of the picture hold for an arbitrary permutation representation and are
proved there, in `TauCeti.RepresentationTheory.Augmentation`: that `k[α]` is the direct sum of the
invariant line and the standard subrepresentation, again under `|α| ≠ 0` in `k` (or `α` empty), is
`TauCeti.isCompl_invariantLine_augmentationSubrepresentation`, and that the standard
subrepresentation has dimension `|α| - 1` is `TauCeti.finrank_augmentationSubrepresentation`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, §2.1, where the standard
  representation of `Sₙ` is introduced as the complement of the trivial summand in the permutation
  representation.
* G. D. James, *The Representation Theory of the Symmetric Groups*, §4, for the same
  representation as the Specht module of the shape `(n-1, 1)`.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "the named small irreducibles", which asks for `M^{(n-1,1)} = triv ⊕ standard` with the
  standard summand the `(n-1)`-dimensional irreducible.
-/

public section

namespace TauCeti

-- `_root_.`, since `TauCeti.MonoidAlgebra` is a namespace of its own
open _root_.MonoidAlgebra

/-! ### Transpositions and differences of basis vectors -/

section Swap

variable {k : Type*} [CommRing k] {α : Type*} [DecidableEq α]

/-- Subtracting from `v` the effect of the transposition `(x y)` leaves the difference of the two
coefficients times the difference of the two standard basis vectors: a transposition changes only
the two coefficients it swaps.  This is the step that produces a difference of basis vectors from
an arbitrary vector, and it needs no hypothesis relating `x` and `y`. -/
theorem sub_ofMulAction_swap (x y : α) (v : MonoidAlgebra k α) :
    v - Representation.ofMulAction k (Equiv.Perm α) α (Equiv.swap x y) v =
      (v.coeff x - v.coeff y) • (single x 1 - single y 1 : MonoidAlgebra k α) := by
  rw [← MonoidAlgebra.coeff_inj]
  ext z
  simp only [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_smul, Finsupp.sub_apply,
    Finsupp.smul_apply, Representation.coeff_ofMulAction, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, smul_eq_mul, Equiv.Perm.smul_def, Equiv.swap_inv]
  rcases eq_or_ne z x with rfl | hzx
  · rcases eq_or_ne z y with rfl | hzy
    · simp
    · rw [Equiv.swap_apply_left]
      simp [Ne.symm hzy]
  · rcases eq_or_ne z y with rfl | hzy
    · rw [Equiv.swap_apply_right]
      simp [Ne.symm hzx]
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
      simp [Ne.symm hzx, Ne.symm hzy]

end Swap

/-! ### The standard representation -/

section Defn

variable (k : Type*) [CommSemiring k] (α : Type*)

/-- The **standard representation** of the symmetric group on `α`: the action of `Equiv.Perm α` on
the vectors of `k[α]` whose coefficients sum to zero.  No hypothesis on `k` or on `α` is imposed
here; when `α` is finite and `(Fintype.card α : k) ≠ 0` it is a complement of the invariant line in
the permutation representation `k[α]`, by
`isCompl_invariantLine_augmentationSubrepresentation`, whereas when `(Fintype.card α : k) = 0` the
invariant line lies inside it instead.  Identifying it with the Specht module of the shape
`(|α|-1, 1)` is an aim for later: the polytabloid presentation needed to state that equivalence is
not yet in the repository. -/
noncomputable def standardRepresentation :
    Representation k (Equiv.Perm α)
      (augmentationSubrepresentation k (Equiv.Perm α) α).toSubmodule :=
  (augmentationSubrepresentation k (Equiv.Perm α) α).toRepresentation

variable {k α}

/-- The standard representation acts by permuting the standard basis: on underlying elements of
`k[α]` it is the permutation representation. -/
@[simp]
theorem coe_standardRepresentation_apply (g : Equiv.Perm α)
    (v : (augmentationSubrepresentation k (Equiv.Perm α) α).toSubmodule) :
    (standardRepresentation k α g v : MonoidAlgebra k α) =
      Representation.ofMulAction k (Equiv.Perm α) α g v :=
  -- `(rfl)`, not `rfl`: the body of `standardRepresentation` is not `@[expose]`d, so this must not
  -- be inferred `@[defeq]`.
  (rfl)

end Defn

section WeakScalars

variable {k : Type*} {α : Type*}

section SemiringNoZeroDivisors

variable [CommSemiring k] [NoZeroDivisors k] [Fintype α]

/-- A nonzero vector in the kernel of `sumCoords` has two different coefficients, provided
`(Fintype.card α : k) ≠ 0`.

Nonemptiness of `α` is not assumed — it follows from `(Fintype.card α : k) ≠ 0`. -/
private theorem exists_coeff_ne_of_ne_zero_of_sumCoords_eq_zero (hchar : (Fintype.card α : k) ≠ 0)
    {v : MonoidAlgebra k α} (hv0 : v ≠ 0)
    (hvker : (MonoidAlgebra.basis α k).sumCoords v = 0) :
    ∃ x y : α, x ≠ y ∧ v.coeff x ≠ v.coeff y := by
  classical
  -- Otherwise all coefficients agree, and their common value is killed by `Fintype.card α`.
  have hpos : 0 < Fintype.card α :=
    Nat.pos_of_ne_zero fun h => hchar (by rw [h]; simp)
  obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp hpos
  by_contra hcon
  push Not at hcon
  have hall : ∀ z : α, v.coeff z = v.coeff x₀ := fun z =>
    (eq_or_ne z x₀).elim (fun h => by rw [h]) fun h => hcon z x₀ h
  have hsum : (MonoidAlgebra.basis α k).sumCoords v = ∑ z : α, v.coeff z := by simp
  have hmul : (Fintype.card α : k) * v.coeff x₀ = 0 := by
    rw [← hvker, hsum, Finset.sum_congr rfl fun z _ => hall z]
    simp
  have hzero : v.coeff x₀ = 0 := (mul_eq_zero.mp hmul).resolve_left hchar
  exact hv0 (MonoidAlgebra.coeff_eq_zero.mp (Finsupp.ext fun z => by simp [hall z, hzero]))

end SemiringNoZeroDivisors

section Ring

variable [CommRing k]

/-- A subrepresentation containing one difference of standard basis vectors contains every
difference with the same base point `x`. -/
private theorem single_sub_single_mem_of_ne_of_single_sub_single_mem
    {τ : Subrepresentation (Representation.ofMulAction k (Equiv.Perm α) α)} {x y : α}
    (hxy : x ≠ y) (hmem : (single x 1 - single y 1 : MonoidAlgebra k α) ∈ τ.toSubmodule) (z : α) :
    (single z 1 - single x 1 : MonoidAlgebra k α) ∈ τ.toSubmodule := by
  classical
  -- Transpose `y` with `z`, which fixes `x`.
  rcases eq_or_ne z x with rfl | hzx
  · simp
  · have hswapx : (Equiv.swap y z) • x = x := by
      rw [Equiv.Perm.smul_def, Equiv.swap_apply_of_ne_of_ne hxy (Ne.symm hzx)]
    have hswapy : (Equiv.swap y z) • y = z := by
      rw [Equiv.Perm.smul_def, Equiv.swap_apply_left]
    have hm := τ.apply_mem_toSubmodule (Equiv.swap y z) hmem
    rw [map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single,
      hswapx, hswapy] at hm
    simpa using τ.toSubmodule.neg_mem hm

end Ring

end WeakScalars

section Standard

variable {k : Type*} [Field k] {α : Type*} [Fintype α]

/-- The standard subrepresentation is an atom when `Fintype.card α = 2`, with no hypothesis on the
characteristic of `k`. -/
private theorem isAtom_augmentationSubrepresentation_of_card_eq_two (hcard : Fintype.card α = 2) :
    IsAtom (augmentationSubrepresentation k (Equiv.Perm α) α) := by
  -- For two elements the subrepresentation is a line, and a line is an atom of the lattice of
  -- subspaces; the lattice of subrepresentations embeds in it by `toSubmodule`.
  have hatom : IsAtom (augmentationSubrepresentation k (Equiv.Perm α) α).toSubmodule :=
    Submodule.isAtom_iff_finrank_eq_one.mpr
      (by rw [finrank_augmentationSubrepresentation, hcard])
  refine ⟨fun h => hatom.1 (by rw [h, Subrepresentation.toSubmodule_bot]), fun τ hτ =>
    Subrepresentation.toSubmodule_injective
      ((hatom.2 _ ?_).trans Subrepresentation.toSubmodule_bot.symm)⟩
  exact lt_of_le_of_ne hτ.le fun hc => hτ.ne (Subrepresentation.toSubmodule_injective hc)

omit [Fintype α] in
/-- A subrepresentation containing a vector whose `x`- and `y`-coefficients differ contains the
difference `single x 1 - single y 1`.

The two indices need not be distinct as a hypothesis — differing coefficients already force it. -/
private theorem single_sub_single_mem_of_mem_of_coeff_ne
    {τ : Subrepresentation (Representation.ofMulAction k (Equiv.Perm α) α)}
    {v : MonoidAlgebra k α} (hv : v ∈ τ.toSubmodule) {x y : α}
    (hcoeff : v.coeff x ≠ v.coeff y) :
    (single x 1 - single y 1 : MonoidAlgebra k α) ∈ τ.toSubmodule := by
  classical
  -- Subtract the transposition `swap x y` from `v`, then rescale.
  have hsub : v - Representation.ofMulAction k (Equiv.Perm α) α (Equiv.swap x y) v ∈
      τ.toSubmodule :=
    Submodule.sub_mem _ hv (τ.apply_mem_toSubmodule _ hv)
  rw [sub_ofMulAction_swap] at hsub
  have hsmul := τ.toSubmodule.smul_mem (v.coeff x - v.coeff y)⁻¹ hsub
  rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hcoeff), one_smul] at hsmul

/-- **The standard subrepresentation is minimal.**  A nonzero subrepresentation of the permutation
representation contained in the standard one is the whole of it: from a nonzero vector with
vanishing coefficient sum one produces, by transpositions, every difference of standard basis
vectors, and those span.  For a two-element `α` the standard subrepresentation is a line, so it is
minimal whatever the characteristic. -/
theorem isAtom_augmentationSubrepresentation (h2 : 2 ≤ Fintype.card α)
    (hchar : Fintype.card α = 2 ∨ (Fintype.card α : k) ≠ 0) :
    IsAtom (augmentationSubrepresentation k (Equiv.Perm α) α) := by
  classical
  rcases hchar with hcard | hchar
  · exact isAtom_augmentationSubrepresentation_of_card_eq_two hcard
  obtain ⟨x₀, y₀, hx₀y₀⟩ := Fintype.exists_pair_of_one_lt_card (α := α) (by omega)
  constructor
  · -- the standard subrepresentation is nonzero
    intro hbot
    have hmem : (single x₀ 1 - single y₀ 1 : MonoidAlgebra k α) ∈
        augmentationSubrepresentation k (Equiv.Perm α) α :=
      single_sub_single_mem_augmentationSubrepresentation x₀ y₀
    rw [hbot] at hmem
    have hne : (single x₀ 1 - single y₀ 1 : MonoidAlgebra k α) ≠ 0 :=
      sub_ne_zero.mpr ((MonoidAlgebra.single_left_injective one_ne_zero).ne hx₀y₀)
    exact hne (Submodule.mem_bot k |>.mp hmem)
  · -- every strictly smaller subrepresentation is zero
    intro τ hτ
    by_contra hτbot
    have hτne : τ.toSubmodule ≠ ⊥ := fun hc =>
      hτbot (Subrepresentation.toSubmodule_injective hc)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hτne
    have hvker : (MonoidAlgebra.basis α k).sumCoords v = 0 :=
      mem_augmentationSubrepresentation_iff.mp (hτ.le hv)
    obtain ⟨x, y, hxy, hcoeff⟩ := exists_coeff_ne_of_ne_zero_of_sumCoords_eq_zero hchar hv0 hvker
    have hdiff := single_sub_single_mem_of_mem_of_coeff_ne hv hcoeff
    -- `τ` then contains every difference of standard basis vectors, which span
    have hle : augmentationSubrepresentation k (Equiv.Perm α) α ≤ τ := by
      intro w hw
      have hw' : w ∈ LinearMap.ker (MonoidAlgebra.basis α k).sumCoords :=
        mem_augmentationSubrepresentation_iff.mp hw
      rw [ker_sumCoords_basis_eq_span k α x] at hw'
      exact Submodule.span_le.mpr (by
        rintro _ ⟨z, rfl⟩
        exact single_sub_single_mem_of_ne_of_single_sub_single_mem hxy hdiff z) hw'
    exact absurd (le_antisymm hτ.le hle) hτ.ne

/-- **The standard representation is irreducible.**  Given `2 ≤ |α|`, the hypothesis is sharp: for
`|α| = 2` the standard representation is a line, hence irreducible whatever the characteristic,
and for `3 ≤ |α|` with `|α| = 0` in `k` the invariant line is a proper nonzero subrepresentation
of it. -/
theorem isIrreducible_standardRepresentation (h2 : 2 ≤ Fintype.card α)
    (hchar : Fintype.card α = 2 ∨ (Fintype.card α : k) ≠ 0) :
    (standardRepresentation k α).IsIrreducible :=
  Representation.isIrreducible_toRepresentation_of_isAtom
    (isAtom_augmentationSubrepresentation h2 hchar)

end Standard

end TauCeti
