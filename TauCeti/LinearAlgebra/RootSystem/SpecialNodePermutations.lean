/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.RootLength

/-!
# Special node permutations of a Dynkin type

A *graph automorphism* of a Dynkin diagram is a permutation of its Bourbaki-numbered nodes
preserving the standard Cartan matrix; those are pinned in
`TauCeti/LinearAlgebra/RootSystem/DiagramPermutations.lean`, and each of them lifts to an
automorphism of the pinned group scheme of the type. This file is about the other kind of node
permutation, the one that *transposes* the Cartan matrix while exchanging the long and the short
simple roots:

```text
A (σ i) (σ j) = A j i,      σ i long ↔ i short.
```

Such a `σ` is a symmetry of the *dual* diagram rather than of the diagram, so no automorphism of
the pinned group realises it. It is realised instead by a **special isogeny** `τ`, whose defining
action on the numbered simple root subgroups is `τ (x_i(a)) = x_{σ i}(a ^ q i)` with `q i = 1` on a
long node and `q i = p` on a short one, and which therefore satisfies `τ ^ 2 = Frob_p`. The
predicate defined here, `TauCeti.DynkinType.IsSpecialNodePerm`, is the root-level datum such an
isogeny carries.

The point of the file is that this datum is completely rigid, and the theorems saying so are what
make "the" special isogeny of a type well-defined data rather than a choice:

* it exists exactly for `B₂`, `F₄` and `G₂` among the valid types
  (`TauCeti.DynkinType.exists_isSpecialNodePerm_iff`);
* when it exists it is unique (`TauCeti.DynkinType.IsSpecialNodePerm.unique`), hence an involution
  (`TauCeti.DynkinType.IsSpecialNodePerm.sq_eq_one`);
* the two squared root lengths it exchanges multiply to `2` for `B₂` and `F₄` and to `3` for `G₂`
  (`TauCeti.DynkinType.exists_prime_rootLength_mul_rootLength`), which is the prime whose Frobenius
  the isogeny squares to.

The exclusions in the first item are the small-rank accidents. A length-exchanging permutation
restricts to a bijection between the long and the short nodes, so a type admitting one has as many
of each; a valid simply-laced type has no short node and a node to spare, `Bₙ` has `n - 1` long
nodes against one short one and `Cₙ` the reverse, so only `B₂`, `F₄` and `G₂` survive. Uniqueness
genuinely needs the Cartan condition and not only the length condition: four permutations of the
`F₄` nodes exchange its two long nodes with its two short ones, and only the diagram reversal
transposes its Cartan matrix. It is proved by composing two candidates into a permutation that
*preserves* the Cartan matrix, and observing that each of the three types has no such permutation
but the identity.

Nothing here constructs an isogeny, or any group or Lie algebra. This is the combinatorial input to
that construction, stated against the pinned Bourbaki numbering of
`TauCeti.DynkinType.cartanMatrix`, in which Bourbaki node `i` sits at `Fin` index `i - 1`.

## Main definitions

* `TauCeti.DynkinType.IsSpecialNodePerm`: a permutation of the nodes of a Dynkin type exchanging
  long and short simple roots and transposing the standard Cartan matrix.

## Main results

* `TauCeti.DynkinType.isSpecialNodePerm_B_two`, `TauCeti.DynkinType.isSpecialNodePerm_F4` and
  `TauCeti.DynkinType.isSpecialNodePerm_G2`: the three special node permutations, taken from the
  pinned length permutations of `TauCeti/LinearAlgebra/RootSystem/DiagramPermutations.lean`.
* `TauCeti.DynkinType.exists_isSpecialNodePerm_iff`: **a valid Dynkin type admits a special node
  permutation exactly when it is `B₂`, `F₄` or `G₂`.**
* `TauCeti.DynkinType.IsSpecialNodePerm.unique` and
  `TauCeti.DynkinType.IsSpecialNodePerm.sq_eq_one`: it is then unique, and an involution.
* `TauCeti.DynkinType.exists_prime_rootLength_mul_rootLength`: the two squared lengths it exchanges
  multiply to a prime, which is `2` or `3`.
* `TauCeti.DynkinType.IsSpecialNodePerm.submatrix_cartanMatrix_ne`: it is never a graph
  automorphism.

## References

This is the root-level combinatorics underlying the "special isogenies in characteristics two and
three" item of Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. See R. Steinberg, *Lectures
on Chevalley Groups*, §11, for the isogeny itself, and R. W. Carter, *Simple Groups of Lie Type*,
§12.3-12.4, for the Suzuki and Ree groups it produces.
-/

public section

namespace TauCeti

namespace DynkinType

/-- A permutation `σ` of the Bourbaki-numbered nodes of a Dynkin type is a **special node
permutation** when it exchanges the long and the short simple roots and carries the standard Cartan
matrix to the transposed matrix.

This is the root-level datum of a special isogeny: the isogeny sends the root subgroup of the
simple root `αᵢ` to the root subgroup of `α_{σ i}`, raising its parameter to the power `1` or `p`
according as `αᵢ` is long or short. Transposing rather than preserving the Cartan matrix is what
separates it from a graph automorphism
(`TauCeti.DynkinType.IsSpecialNodePerm.submatrix_cartanMatrix_ne`); accordingly no automorphism of
the pinned group realises it. -/
structure IsSpecialNodePerm (t : DynkinType) (σ : Equiv.Perm (Fin t.rank)) : Prop where
  /-- The permutation exchanges long and short simple roots. -/
  isLongSimpleRoot_apply (i : Fin t.rank) : t.IsLongSimpleRoot (σ i) ↔ ¬ t.IsLongSimpleRoot i
  /-- The permutation carries the standard Cartan matrix to the transposed matrix. -/
  cartanMatrix_apply (i j : Fin t.rank) : t.cartanMatrix (σ i) (σ j) = t.cartanMatrix j i

namespace IsSpecialNodePerm

variable {t : DynkinType} {σ τ : Equiv.Perm (Fin t.rank)}

/-- The inverse of a special node permutation is one: both defining conditions are symmetric in
`σ` and `σ⁻¹` once the roles of the two indices are exchanged. -/
theorem inv (h : t.IsSpecialNodePerm σ) : t.IsSpecialNodePerm σ⁻¹ where
  isLongSimpleRoot_apply i := by
    have hi : σ (σ⁻¹ i) = i := by simp
    have := h.isLongSimpleRoot_apply (σ⁻¹ i)
    rw [hi] at this
    tauto
  cartanMatrix_apply i j := by
    have hi : σ (σ⁻¹ i) = i := by simp
    have hj : σ (σ⁻¹ j) = j := by simp
    have := h.cartanMatrix_apply (σ⁻¹ j) (σ⁻¹ i)
    rwa [hi, hj, eq_comm] at this

/-- Composing a special node permutation with the inverse of another one gives a permutation that
*preserves* the Cartan matrix: the two transpositions cancel. This is how uniqueness is proved. -/
theorem cartanMatrix_apply_inv_mul (hσ : t.IsSpecialNodePerm σ) (hτ : t.IsSpecialNodePerm τ)
    (i j : Fin t.rank) :
    t.cartanMatrix ((τ⁻¹ * σ) i) ((τ⁻¹ * σ) j) = t.cartanMatrix i j := by
  simp only [Equiv.Perm.mul_apply]
  rw [hτ.inv.cartanMatrix_apply (σ i) (σ j), hσ.cartanMatrix_apply j i]

/-- A type carrying a special node permutation has a short simple root, so it is not simply
laced. -/
theorem not_isSimplyLaced (ht : t.Valid) (h : t.IsSpecialNodePerm σ) : ¬ t.IsSimplyLaced := by
  intro hs
  exact (h.isLongSimpleRoot_apply ⟨0, rank_pos ht⟩).mp (isLongSimpleRoot_of_isSimplyLaced hs _)
    (isLongSimpleRoot_of_isSimplyLaced hs _)

end IsSpecialNodePerm

/-! ### The three types that admit one -/

/-- Exchanging the two nodes of `B₂` is a special node permutation: the first node is long and the
second short, and the swap transposes the `B₂` Cartan matrix. -/
theorem isSpecialNodePerm_B_two : (B 2).IsSpecialNodePerm lengthPermRankTwo where
  isLongSimpleRoot_apply := isLongSimpleRoot_lengthPermRankTwo_iff_not_isLongSimpleRoot_B2
  cartanMatrix_apply := cartanMatrix_B2_lengthPermRankTwo

/-- Exchanging the two nodes of `G₂` is a special node permutation: the second node is long and the
first short, and the swap transposes the `G₂` Cartan matrix. -/
theorem isSpecialNodePerm_G2 : G2.IsSpecialNodePerm lengthPermRankTwo where
  isLongSimpleRoot_apply := isLongSimpleRoot_lengthPermRankTwo_iff_not_isLongSimpleRoot_G2
  cartanMatrix_apply := cartanMatrix_G2_lengthPermRankTwo

/-- Reversing the `F₄` diagram is a special node permutation: it exchanges the two long nodes `0`
and `1` with the two short nodes `2` and `3`, and transposes the `F₄` Cartan matrix. -/
theorem isSpecialNodePerm_F4 : F4.IsSpecialNodePerm lengthPermF4 where
  isLongSimpleRoot_apply := isLongSimpleRoot_lengthPermF4_iff_not_isLongSimpleRoot_F4
  cartanMatrix_apply := cartanMatrix_F4_lengthPermF4

/-! ### The types that do not

A length-exchanging permutation is a bijection between the long and the short nodes, so it forces
the two to be equinumerous. A valid simply-laced type is ruled out by
`TauCeti.DynkinType.IsSpecialNodePerm.not_isSimplyLaced`, and each proof below exhibits two nodes
of one kind whose images would have to be the single node of the other kind. -/

/-- `Bₙ` has no special node permutation once `3 ≤ n`: its nodes `0` and `1` are then both long,
while its only short node is the last one, so the two would have the same image. -/
theorem not_isSpecialNodePerm_B {n : ℕ} (hn : 3 ≤ n) (σ : Equiv.Perm (Fin (B n).rank)) :
    ¬ (B n).IsSpecialNodePerm σ := by
  intro h
  have hrank : (B n).rank = n := rank_B n
  -- A long node has a short image, and the only short node of `Bₙ` is the last one.
  have key : ∀ (m : ℕ) (hm : m < (B n).rank), m + 1 < n → ((σ ⟨m, hm⟩ : ℕ)) + 1 = n := by
    intro m hm hi
    have hlong : (B n).IsLongSimpleRoot ⟨m, hm⟩ := by simpa using hi
    have hshort : ¬ (B n).IsLongSimpleRoot (σ ⟨m, hm⟩) := fun hc =>
      (h.isLongSimpleRoot_apply ⟨m, hm⟩).mp hc hlong
    simp only [isLongSimpleRoot_B, not_lt] at hshort
    have := (σ ⟨m, hm⟩).isLt
    omega
  have hpos₀ : 0 < (B n).rank := by omega
  have hpos₁ : 1 < (B n).rank := by omega
  have h₀ := key 0 hpos₀ (by omega)
  have h₁ := key 1 hpos₁ (by omega)
  have hσ : σ ⟨0, hpos₀⟩ = σ ⟨1, hpos₁⟩ := Fin.eq_of_val_eq (by omega)
  simpa using congrArg Fin.val (σ.injective hσ)

/-- `Cₙ` has no special node permutation once `3 ≤ n`: its nodes `0` and `1` are then both short,
while its only long node is the last one, so the two would have the same image. -/
theorem not_isSpecialNodePerm_C {n : ℕ} (hn : 3 ≤ n) (σ : Equiv.Perm (Fin (C n).rank)) :
    ¬ (C n).IsSpecialNodePerm σ := by
  intro h
  have hrank : (C n).rank = n := rank_C n
  -- A short node has a long image, and the only long node of `Cₙ` is the last one.
  have key : ∀ (m : ℕ) (hm : m < (C n).rank), m + 1 ≠ n → ((σ ⟨m, hm⟩ : ℕ)) + 1 = n := by
    intro m hm hi
    have hshort : ¬ (C n).IsLongSimpleRoot ⟨m, hm⟩ := by simpa using hi
    simpa using (h.isLongSimpleRoot_apply ⟨m, hm⟩).mpr hshort
  have hpos₀ : 0 < (C n).rank := by omega
  have hpos₁ : 1 < (C n).rank := by omega
  have h₀ := key 0 hpos₀ (by omega)
  have h₁ := key 1 hpos₁ (by omega)
  have hσ : σ ⟨0, hpos₀⟩ = σ ⟨1, hpos₁⟩ := Fin.eq_of_val_eq (by omega)
  simpa using congrArg Fin.val (σ.injective hσ)

/-- **A valid Dynkin type admits a special node permutation exactly when it is `B₂`, `F₄` or
`G₂`.**

These are the three types whose finite groups of Lie type include a Suzuki--Ree family: the special
isogeny of `B₂` in characteristic two gives `²B₂`, that of `G₂` in characteristic three gives `²G₂`,
and that of `F₄` in characteristic two gives `²F₄` and the Tits group. -/
theorem exists_isSpecialNodePerm_iff {t : DynkinType} (ht : t.Valid) :
    (∃ σ : Equiv.Perm (Fin t.rank), t.IsSpecialNodePerm σ) ↔ t = B 2 ∨ t = F4 ∨ t = G2 := by
  constructor
  · rintro ⟨σ, h⟩
    cases t with
    | A n => exact absurd (isSimplyLaced_A n) (h.not_isSimplyLaced ht)
    | D n => exact absurd (isSimplyLaced_D n) (h.not_isSimplyLaced ht)
    | E6 => exact absurd isSimplyLaced_E6 (h.not_isSimplyLaced ht)
    | E7 => exact absurd isSimplyLaced_E7 (h.not_isSimplyLaced ht)
    | E8 => exact absurd isSimplyLaced_E8 (h.not_isSimplyLaced ht)
    | F4 => exact Or.inr (Or.inl rfl)
    | G2 => exact Or.inr (Or.inr rfl)
    | B n =>
        rcases eq_or_lt_of_le (valid_B.mp ht) with rfl | hn
        · exact Or.inl rfl
        · exact absurd h (not_isSpecialNodePerm_B hn σ)
    | C n => exact absurd h (not_isSpecialNodePerm_C (valid_C.mp ht) σ)
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, isSpecialNodePerm_B_two⟩
    · exact ⟨_, isSpecialNodePerm_F4⟩
    · exact ⟨_, isSpecialNodePerm_G2⟩

/-! ### Rigidity

Each of `B₂`, `F₄` and `G₂` has a trivial diagram automorphism group, in the strong sense that the
identity is the only permutation of its nodes preserving its standard Cartan matrix. Since the
composite of one special node permutation with the inverse of another preserves the Cartan matrix,
uniqueness follows. -/

/-- The identity is the only permutation of the two `B₂` nodes preserving its Cartan matrix, the
`B₂` matrix being asymmetric. -/
theorem eq_one_of_cartanMatrix_B_two {ρ : Equiv.Perm (Fin 2)}
    (h : ∀ i j : Fin 2, (B 2).cartanMatrix (ρ i) (ρ j) = (B 2).cartanMatrix i j) : ρ = 1 := by
  have key : ∀ f : Fin 2 → Fin 2,
      (∀ p : Fin 2 × Fin 2, CartanMatrix.B 2 (f p.1) (f p.2) = CartanMatrix.B 2 p.1 p.2) →
      ∀ i, f i = i := by decide
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply]
  exact key ρ (fun p => by simpa using h p.1 p.2) i

/-- The identity is the only permutation of the two `G₂` nodes preserving its Cartan matrix, the
`G₂` matrix being asymmetric. -/
theorem eq_one_of_cartanMatrix_G2 {ρ : Equiv.Perm (Fin 2)}
    (h : ∀ i j : Fin 2, G2.cartanMatrix (ρ i) (ρ j) = G2.cartanMatrix i j) : ρ = 1 := by
  have key : ∀ f : Fin 2 → Fin 2,
      (∀ p : Fin 2 × Fin 2, CartanMatrix.G₂.transpose (f p.1) (f p.2) =
        CartanMatrix.G₂.transpose p.1 p.2) →
      ∀ i, f i = i := by decide
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply]
  exact key ρ (fun p => by simpa using h p.1 p.2) i

/-- The identity is the only permutation of the four `F₄` nodes preserving its Cartan matrix.

The entry `-2` occurs once, at the double bond `(1, 2)`, so a Cartan-preserving permutation fixes
both of those nodes; the two end nodes are then pinned by the entries `-1` beside them. -/
theorem eq_one_of_cartanMatrix_F4 {ρ : Equiv.Perm (Fin 4)}
    (h : ∀ i j : Fin 4, F4.cartanMatrix (ρ i) (ρ j) = F4.cartanMatrix i j) : ρ = 1 := by
  have h' : ∀ i j : Fin 4, CartanMatrix.F₄ (ρ i) (ρ j) = CartanMatrix.F₄ i j := by
    intro i j; simpa using h i j
  have hneg : ∀ p : Fin 4 × Fin 4, CartanMatrix.F₄ p.1 p.2 = -2 → p.1 = 1 ∧ p.2 = 2 := by decide
  have hneg' : ∀ x y : Fin 4, CartanMatrix.F₄ x y = -2 → x = 1 ∧ y = 2 := fun x y => hneg (x, y)
  obtain ⟨hρ₁, hρ₂⟩ := hneg' (ρ 1) (ρ 2) (by rw [h' 1 2]; decide)
  have hcol : ∀ x : Fin 4, CartanMatrix.F₄ x 1 = -1 → x = 0 ∨ x = 2 := by decide
  have hrow : ∀ y : Fin 4, CartanMatrix.F₄ 2 y = -1 → y = 1 ∨ y = 3 := by decide
  have hρ₀ : ρ 0 = 0 := by
    have h01 := h' 0 1
    rw [hρ₁] at h01
    rcases hcol (ρ 0) (by rw [h01]; decide) with h0 | h0
    · exact h0
    · exact absurd (ρ.injective (h0.trans hρ₂.symm)) (by decide)
  have hρ₃ : ρ 3 = 3 := by
    have h23 := h' 2 3
    rw [hρ₂] at h23
    rcases hrow (ρ 3) (by rw [h23]; decide) with h3 | h3
    · exact absurd (ρ.injective (h3.trans hρ₁.symm)) (by decide)
    · exact h3
  refine Equiv.ext fun i => ?_
  simp only [Equiv.Perm.one_apply]
  fin_cases i
  exacts [hρ₀, hρ₁, hρ₂, hρ₃]

/-- **A valid Dynkin type has at most one special node permutation.** This is what lets a
downstream construction speak of *the* special isogeny of a type rather than of a chosen one. -/
theorem IsSpecialNodePerm.unique {t : DynkinType} (ht : t.Valid)
    {σ τ : Equiv.Perm (Fin t.rank)} (hσ : t.IsSpecialNodePerm σ) (hτ : t.IsSpecialNodePerm τ) :
    σ = τ := by
  have hmul : τ⁻¹ * σ = 1 := by
    rcases (exists_isSpecialNodePerm_iff ht).mp ⟨σ, hσ⟩ with rfl | rfl | rfl
    · exact eq_one_of_cartanMatrix_B_two (hσ.cartanMatrix_apply_inv_mul hτ)
    · exact eq_one_of_cartanMatrix_F4 (hσ.cartanMatrix_apply_inv_mul hτ)
    · exact eq_one_of_cartanMatrix_G2 (hσ.cartanMatrix_apply_inv_mul hτ)
  rw [← one_mul σ, ← mul_inv_cancel τ, mul_assoc, hmul, mul_one]

/-- A special node permutation of a valid type is an involution, because its inverse is one too and
there is only one. This is the node-level shadow of `τ ^ 2 = Frob_p`, whose square acts trivially on
the numbering and only raises the root-subgroup parameters to the power `p`. -/
theorem IsSpecialNodePerm.sq_eq_one {t : DynkinType} (ht : t.Valid)
    {σ : Equiv.Perm (Fin t.rank)} (h : t.IsSpecialNodePerm σ) : σ ^ 2 = 1 := by
  have hinv : σ = σ⁻¹ := IsSpecialNodePerm.unique ht h h.inv
  have hmul : σ * σ = 1 := by
    nth_rewrite 2 [hinv]
    exact mul_inv_cancel σ
  rwa [pow_two]

/-- A special node permutation is never a graph automorphism: it transposes the Cartan matrix, and
for the three types that carry one the transposed matrix is a different matrix. -/
theorem IsSpecialNodePerm.submatrix_cartanMatrix_ne {t : DynkinType} (ht : t.Valid)
    {σ : Equiv.Perm (Fin t.rank)} (h : t.IsSpecialNodePerm σ) :
    t.cartanMatrix.submatrix σ σ ≠ t.cartanMatrix := by
  rcases (exists_isSpecialNodePerm_iff ht).mp ⟨σ, h⟩ with rfl | rfl | rfl
  · rw [IsSpecialNodePerm.unique ht h isSpecialNodePerm_B_two]
    exact cartanMatrix_B2_submatrix_lengthPermRankTwo_ne
  · rw [IsSpecialNodePerm.unique ht h isSpecialNodePerm_F4]
    exact cartanMatrix_F4_submatrix_lengthPermF4_ne
  · rw [IsSpecialNodePerm.unique ht h isSpecialNodePerm_G2]
    exact cartanMatrix_G2_submatrix_lengthPermRankTwo_ne

/-! ### The prime attached to a special node permutation -/

/-- The lengths a special node permutation exchanges multiply to the common long length, once the
type is known to take the value `p` on its long nodes and `1` on its short ones. -/
private theorem rootLength_mul_rootLength_of_two_valued {t : DynkinType}
    {σ : Equiv.Perm (Fin t.rank)} (h : t.IsSpecialNodePerm σ) {p : ℤ}
    (hL : ∀ i, t.IsLongSimpleRoot i → t.rootLength i = p)
    (hS : ∀ i, ¬ t.IsLongSimpleRoot i → t.rootLength i = 1) (i : Fin t.rank) :
    t.rootLength i * t.rootLength (σ i) = p := by
  by_cases hi : t.IsLongSimpleRoot i
  · rw [hL i hi, hS _ fun hc => (h.isLongSimpleRoot_apply i).mp hc hi, mul_one]
  · rw [hS i hi, hL _ ((h.isLongSimpleRoot_apply i).mpr hi), one_mul]

/-- **The two squared root lengths that a special node permutation exchanges multiply to a prime,
namely `2` for `B₂` and `F₄` and `3` for `G₂`.**

That prime is the characteristic in which the corresponding special isogeny exists: the isogeny
raises a root-subgroup parameter to the power `1` on a long node and to the power `p` on a short
one, so either composite of the two exponents is `p`, and its square is the `p`-power Frobenius. -/
theorem exists_prime_rootLength_mul_rootLength {t : DynkinType} (ht : t.Valid)
    {σ : Equiv.Perm (Fin t.rank)} (h : t.IsSpecialNodePerm σ) :
    ∃ p : ℕ, p.Prime ∧ (p = 2 ∨ p = 3) ∧
      ∀ i, t.rootLength i * t.rootLength (σ i) = (p : ℤ) := by
  rcases (exists_isSpecialNodePerm_iff ht).mp ⟨σ, h⟩ with rfl | rfl | rfl
  · refine ⟨2, Nat.prime_two, Or.inl rfl, ?_⟩
    refine rootLength_mul_rootLength_of_two_valued h (fun i hi => ?_) fun i hi => ?_
    · have hne : (i : ℕ) + 1 ≠ 2 := by simp only [isLongSimpleRoot_B] at hi; omega
      simp [rootLength_B, hne]
    · have hlt : (i : ℕ) < 2 := by simpa using i.isLt
      have heq : (i : ℕ) + 1 = 2 := by
        simp only [isLongSimpleRoot_B, not_lt] at hi; omega
      simp [rootLength_B, heq]
  · refine ⟨2, Nat.prime_two, Or.inl rfl, ?_⟩
    refine rootLength_mul_rootLength_of_two_valued h (fun i hi => ?_) fun i hi => ?_
    · simp only [isLongSimpleRoot_F4] at hi
      simp [rootLength_F4, hi]
    · simp only [isLongSimpleRoot_F4] at hi
      simp [rootLength_F4, hi]
  · refine ⟨3, Nat.prime_three, Or.inr rfl, ?_⟩
    refine rootLength_mul_rootLength_of_two_valued h (fun i hi => ?_) fun i hi => ?_
    · have hne : (i : ℕ) ≠ 0 := by simp only [isLongSimpleRoot_G2] at hi; omega
      simp [rootLength_G2, hne]
    · have hlt : (i : ℕ) < 2 := by simpa using i.isLt
      have heq : (i : ℕ) = 0 := by simp only [isLongSimpleRoot_G2] at hi; omega
      simp [rootLength_G2, heq]

end DynkinType

end TauCeti
