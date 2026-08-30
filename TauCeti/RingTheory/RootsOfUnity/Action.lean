/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The roots of unity are preserved by an action by monoid endomorphisms

A monoid `G` acting on `Mˣ` by monoid endomorphisms preserves `ζ ^ n = 1`, so the subgroup
`rootsOfUnity n M` is `G`-stable and inherits the action. This file records that stability and
installs the inherited `MulDistribMulAction`.

The intended instance is the absolute Galois group acting on `μₙ ⊆ (Kˢ)ˣ`, where the action is in
general nontrivial and is exactly what the Kummer isomorphism depends on; the statement needs
nothing about fields, so it is proved for an arbitrary action by monoid endomorphisms.

## Main results

* `TauCeti.smul_mem_rootsOfUnity`: `rootsOfUnity n M` is stable under the action.
* `TauCeti.rootsOfUnity.mulDistribMulAction`: the inherited action on `rootsOfUnity n M`.
-/

public section

namespace TauCeti

variable {G M : Type*} [Monoid G] [CommMonoid M] [MulDistribMulAction G Mˣ] (n : ℕ)

variable {n} in
/-- An action by monoid endomorphisms preserves the `n`-th roots of unity. -/
theorem smul_mem_rootsOfUnity (g : G) {ζ : Mˣ} (hζ : ζ ∈ rootsOfUnity n M) :
    g • ζ ∈ rootsOfUnity n M := by
  rw [mem_rootsOfUnity] at hζ ⊢
  rw [← smul_pow', hζ, smul_one]

/-- The action of `G` on `rootsOfUnity n M` inherited from its action on `Mˣ`. -/
instance rootsOfUnity.mulDistribMulAction : MulDistribMulAction G (rootsOfUnity n M) where
  smul g ζ := ⟨g • (ζ : Mˣ), smul_mem_rootsOfUnity g ζ.2⟩
  one_smul _ := Subtype.ext (one_smul G _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_mul _ _ _ := Subtype.ext (smul_mul' _ _ _)
  smul_one _ := Subtype.ext (smul_one _)

@[simp]
theorem rootsOfUnity.coe_smul (g : G) (ζ : rootsOfUnity n M) :
    ((g • ζ : rootsOfUnity n M) : Mˣ) = g • (ζ : Mˣ) :=
  rfl

end TauCeti
