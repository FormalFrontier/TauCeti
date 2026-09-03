/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Characters of a group of prime exponent

Let `p` be a prime and let `A` be a group whose elements commute and satisfy `a ^ p = 1`. Its
additive shadow `Additive A` is then a vector space over the field `ZMod p`, so the coordinate
functionals of any basis separate its points; translated back through the type-tag adjunction
`AddMonoidHom.toMultiplicativeRight`, those functionals are the homomorphisms
`A →* Multiplicative (ZMod p)`. This file records the resulting separation statement.

Commutativity is carried as a hypothesis rather than as a `CommGroup` instance because the
intended consumers are quotients `G ⧸ N` of a group by a normal subgroup containing the
commutator subgroup and all `p`-th powers: such a quotient carries no `CommGroup` instance,
only the proof that its elements commute.

No finiteness is needed: a vector space over a field has a basis regardless of its dimension.
Mathlib's separation theorem for finite commutative groups,
`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`, does not cover this: it needs the
target to contain enough roots of unity of the exponent of the group, and `ZMod p` contains no
`p`-th root of unity other than `1`.

## Main results

* `TauCeti.exists_monoidHom_multiplicative_zmod_apply_ne_one`: for `x ≠ 1` there is a
  homomorphism `A →* Multiplicative (ZMod p)` not killing `x`.
-/

public section

namespace TauCeti

/-- **Characters with values in `ZMod p` separate the points of a group of exponent `p`.**
If the elements of `A` commute and satisfy `a ^ p = 1` for a prime `p`, then every `x ≠ 1` is
detected by a homomorphism `A →* Multiplicative (ZMod p)`. Its kernel is a normal subgroup of
index `p` avoiding `x`. -/
theorem exists_monoidHom_multiplicative_zmod_apply_ne_one {A : Type*} [Group A] {p : ℕ}
    [Fact p.Prime] (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) {x : A}
    (hx : x ≠ 1) : ∃ φ : A →* Multiplicative (ZMod p), φ x ≠ 1 := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  -- `AddCommGroup.zmodModule` is a `match` on `p`, so as a local instance it blocks the
  -- coercion of a `ZMod p`-linear map to a function; obtaining it through `Nonempty` (legitimate
  -- since the goal is a proposition) keeps it opaque and unblocks that coercion.
  obtain ⟨_⟩ : Nonempty (Module (ZMod p) (Additive A)) :=
    ⟨AddCommGroup.zmodModule fun a ↦ Additive.toMul.injective (by simpa using hpow a.toMul)⟩
  let b := Module.Basis.ofVectorSpace (ZMod p) (Additive A)
  have hx0 : (Additive.ofMul x : Additive A) ≠ 0 := by simpa using hx
  obtain ⟨i, hi⟩ : ∃ i, b.coord i (Additive.ofMul x) ≠ 0 := by
    by_contra hall
    exact hx0 (b.forall_coord_eq_zero_iff.mp (by simpa using hall))
  exact ⟨AddMonoidHom.toMultiplicativeRight (b.coord i).toAddMonoidHom, by simpa using hi⟩

end TauCeti
