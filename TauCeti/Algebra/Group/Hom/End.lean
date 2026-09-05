/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Powers of an additively indexed family of monoid endomorphisms

Let `f : ℕ → M →* M` be a family of endomorphisms of a monoid `M` with `f 0 = MonoidHom.id M` and
`f (i + j) = (f i).comp (f j)`. Powers of its members are again members:

```text
f k ^ m = f (k * m),
```

the power being taken in the endomorphism monoid `Monoid.End M`, whose multiplication is
composition and whose unit is the identity.

The iterated Frobenius endomorphisms of the points of a Chevalley carrier are such a family, the
two hypotheses being their zeroth-iterate and iterate-addition laws.

## Main results

* `TauCeti.pow_eq_of_id_of_comp`: `f k ^ m = f (k * m)` for such a family.
-/

public section

namespace TauCeti

/-- **A family of monoid endomorphisms carrying addition to composition satisfies
`f k ^ m = f (k * m)`**, the power being taken in the endomorphism monoid `Monoid.End M`. -/
-- `Monoid.End M` is definitionally `M →* M` with composition for multiplication and the identity
-- for `1`. Mathlib records those identifications only at the level of the underlying functions, so
-- each induction step closes by `rfl` once the hypothesis has been applied.
theorem pow_eq_of_id_of_comp {M : Type*} [Monoid M] (f : ℕ → M →* M)
    (hid : f 0 = MonoidHom.id M) (hcomp : ∀ i j : ℕ, f (i + j) = (f i).comp (f j)) (k m : ℕ) :
    (show Monoid.End M from f k) ^ m = f (k * m) := by
  induction m with
  | zero => rw [pow_zero, Nat.mul_zero, hid]; rfl
  | succ m ih => rw [pow_succ, ih, Nat.mul_succ, hcomp (k * m) k]; rfl

end TauCeti
