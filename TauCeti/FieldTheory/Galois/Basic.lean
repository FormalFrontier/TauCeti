/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# The Galois theory of separable quadratic extensions

Material complementing `Mathlib/FieldTheory/Galois/Basic.lean` for a separable quadratic
extension `L/K`: it has exactly two automorphisms, so the identity and any one nontrivial
automorphism exhaust `Gal(L/K)`, and an element fixed by a nontrivial automorphism lies in the
base field. `Algebra.IsQuadraticExtension.quadraticCharacter` records the resulting
`Gal(L/K) →* ℤˣ` — the identity to `1`, the nontrivial automorphism to `-1`. It is there so that
a quantity alternating with the Galois action can be described uniformly in `σ` rather than by
cases; `WeierstrassCurve.quadraticTwistPointEquiv_map_eq_quadraticCharacter_smul_map` is the
intended consumer. Mathlib's `quadraticChar` is a different object — the Legendre symbol of a
finite field, not a character of a Galois group.

The file closes with one lemma that is **not** about quadratic extensions:
`AlgEquiv.restrictNormal_eq_one_iff_algebraMap` says that in a tower `K ⊆ L ⊆ M` with `L/K`
normal, an automorphism of `M` restricts to the identity on `L` exactly when it fixes `L`
pointwise. Mathlib states this for an `IntermediateField`
(`AlgEquiv.restrictNormal_eq_one_iff`) while `AlgEquiv.restrictNormal` itself is already given for
an abstract algebra, so only the characterisation needed transporting; it is a bridge to Mathlib
rather than ported material, and it asks for `[Normal K L]` alone.

Mathlib already supplies the surrounding structure: `Algebra.IsQuadraticExtension` makes `L/K`
finite and normal (`Algebra.IsQuadraticExtension.normal`), hence Galois with separability
(`Algebra.IsQuadraticExtension.isGalois`); `IsGalois.card_aut_eq_finrank` counts the
automorphisms and `IsGalois.mem_range_algebraMap_iff_fixed` characterises the base field.

These are the descent inputs for the quadratic-twist layer of
`TauCetiRoadmap/EllipticCurves/README.md` (§Layer 5), consumed by
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisDescent.lean` and by
`TauCeti/RingTheory/Norm/Quadratic.lean`, which expresses the trace and norm of a
separable quadratic extension through its nontrivial automorphism.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/FieldTheory/Galois/Basic.lean` at the roadmap's pin `bc2fe8ff7396`, FLT PR #1088,
Apache 2.0). That file's own header reads `Authors: Kevin Buzzard, Claude`; following this
repository's convention for adapted material, the upstream authorship is credited here rather
than in the copyright header. Only the results consumed downstream are ported; the rest of
the source file is deferred to the Tau Ceti PRs that consume it.
-/

public section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

namespace Algebra.IsQuadraticExtension

/-- A separable quadratic extension has exactly two automorphisms. -/
theorem card_algEquiv_eq_two : Nat.card (L ≃ₐ[K] L) = 2 := by
  rw [IsGalois.card_aut_eq_finrank]
  exact finrank_eq_two K L

/-- The only automorphisms of a separable quadratic extension are the identity and any given
nontrivial automorphism. -/
theorem algEquiv_eq_one_or_eq {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (φ : L ≃ₐ[K] L) : φ = 1 ∨ φ = σ := by
  rcases eq_or_ne φ 1 with h1 | h1
  · exact .inl h1
  · exact .inr (((Nat.card_eq_two_iff' 1).mp (card_algEquiv_eq_two K L)).unique h1 hσ)

/-- **Every automorphism of a separable quadratic extension is an involution.** `Gal(L/K)` has
order two, so this needs no nontriviality hypothesis: it holds for the identity as well. -/
@[simp]
theorem algEquiv_mul_self (σ : L ≃ₐ[K] L) : σ * σ = 1 := by
  rw [← sq, ← card_algEquiv_eq_two K L]
  exact pow_card_eq_one'

/-- An element fixed by a nontrivial automorphism — hence, `Gal(L/K)` having order two, by all of
`Gal(L/K)` — lies in the base field. -/
theorem mem_range_algebraMap_of_apply_eq {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {x : L} (hx : σ x = x) :
    x ∈ Set.range (algebraMap K L) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro φ
  rcases algEquiv_eq_one_or_eq K L hσ φ with rfl | rfl
  · exact AlgEquiv.one_apply x
  · exact hx

/-- **A nontrivial automorphism moves every element outside the base field.** The difference
`σ x - x` is the square root of the discriminant of `x`'s minimal polynomial, so this is exactly
the nondegeneracy that makes such an `x` a generator. -/
theorem apply_sub_self_ne_zero {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) : σ x - x ≠ 0 :=
  sub_ne_zero.mpr fun heq ↦ hx (mem_range_algebraMap_of_apply_eq K L hσ heq)

/-- A separable quadratic extension has a nontrivial automorphism. -/
theorem exists_algEquiv_ne_one : ∃ σ : L ≃ₐ[K] L, σ ≠ 1 :=
  ((Nat.card_eq_two_iff' 1).mp (card_algEquiv_eq_two K L)).exists

/-- The automorphism group of a separable quadratic extension consists of the identity and one
nontrivial element. -/
theorem univ_eq_pair [DecidableEq (L ≃ₐ[K] L)] {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (Finset.univ : Finset (L ≃ₐ[K] L)) = {1, σ} :=
  (Finset.eq_univ_of_forall fun φ ↦ by simpa using algEquiv_eq_one_or_eq K L hσ φ).symm

/-! ### The quadratic character -/

open scoped Classical in
/-- **The quadratic character of a separable quadratic extension**: the identity goes to `1` and
the nontrivial automorphism to `-1`. `Gal(L/K)` has order two, so this is a group isomorphism onto
`ℤˣ`, but the point of packaging it as a `MonoidHom` is that a statement which alternates in `σ` —
a Galois action twisted by the extension, as for the points of a quadratic twist — can then be
written uniformly in `σ` instead of split into a fixed and a moved branch by every consumer. -/
noncomputable def quadraticCharacter : (L ≃ₐ[K] L) →* ℤˣ where
  toFun σ := if σ = 1 then 1 else -1
  map_one' := by simp
  map_mul' σ τ := by
    rcases eq_or_ne σ 1 with rfl | hσ
    · simp
    · rcases eq_or_ne τ 1 with rfl | hτ
      · simp
      · obtain rfl := (algEquiv_eq_one_or_eq K L hσ τ).resolve_left hτ
        simp [algEquiv_mul_self, hσ]

/-- The quadratic character detects the identity: it takes the value `1` exactly there. -/
@[simp]
theorem quadraticCharacter_eq_one_iff {σ : L ≃ₐ[K] L} :
    quadraticCharacter K L σ = 1 ↔ σ = 1 := by
  classical
  simp only [quadraticCharacter, MonoidHom.coe_mk, OneHom.coe_mk]
  split <;> simp_all

/-- Off the identity the quadratic character takes the value `-1`, there being nowhere else to
go in `ℤˣ`. -/
theorem quadraticCharacter_eq_neg_one_of_ne_one {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    quadraticCharacter K L σ = -1 := by
  classical
  simp [quadraticCharacter, hσ]

end Algebra.IsQuadraticExtension

/-! ### Restriction to an intermediate field in a tower -/

section Tower

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Normal K L]
  (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- **`σ` restricts to the identity on `L` exactly when it fixes `L` pointwise.** Mathlib's
`AlgEquiv.restrictNormal_eq_one_iff` says this for an `IntermediateField`, while
`AlgEquiv.restrictNormal` itself is already stated for an abstract algebra `L`, so only the
characterisation needs transporting to a tower `K ⊆ L ⊆ M`. -/
theorem AlgEquiv.restrictNormal_eq_one_iff_algebraMap (σ : M ≃ₐ[K] M) :
    σ.restrictNormal L = 1 ↔ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
  constructor
  · intro h x
    rw [← AlgEquiv.restrictNormal_commutes σ L x, h, AlgEquiv.one_apply]
  · intro h
    ext x
    have hx := AlgEquiv.restrictNormal_commutes σ L x
    rw [h x] at hx
    exact (algebraMap L M).injective hx

end Tower


end
