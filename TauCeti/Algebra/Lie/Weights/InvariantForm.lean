/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.RootPositive

/-!
# The invariant form on the weights of a Killing Lie algebra

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero and let `H` be a splitting Cartan subalgebra. The Killing form restricts to a
non-degenerate form on `H`, which Mathlib packages as the linear equivalence
`LieAlgebra.IsKilling.cartanEquivDual : H ≃ₗ[K] Module.Dual K H`. Transporting the form along that
equivalence puts a symmetric non-degenerate bilinear form `⟨·,·⟩` on the space of weights
`Module.Dual K H`. This file builds that form as `TauCeti.invForm` and proves the two facts that
make it the right object: it is invariant under the reflections of the root system
(`TauCeti.rootInvariantForm`), and it is normalised against the coroots by

```text
⟨λ, α^∨⟩ ⟨α, α⟩ = 2 ⟨λ, α⟩,
```

that is, `α^∨` is the weight `2α / ⟨α, α⟩` (`TauCeti.invForm_coroot`).

That normalisation is what makes the form usable. The Cartan integers of
`LieAlgebra.IsKilling.rootSystem` are the numbers `λ(α^∨)`, whereas the Casimir scalar and the Weyl
character and dimension formulas are written with `⟨·,·⟩`; the identity above is the dictionary
between the two, and it is what makes an expression such as `⟨λ + ρ, λ + ρ⟩ - ⟨ρ, ρ⟩` agree with
the coroot pairings. So the form has to be pinned, with this normalisation proved, before any of
that can be stated.

## Main definitions

* `TauCeti.invForm`: the symmetric bilinear form `⟨·,·⟩` on `Module.Dual K H` induced by the
  Killing form through `LieAlgebra.IsKilling.cartanEquivDual`.
* `TauCeti.rootInvariantForm`: `invForm` packaged as an invariant form on the root system
  `LieAlgebra.IsKilling.rootSystem H`, which makes Mathlib's `RootPairing.InvariantForm` API
  available for it.

## Main results

* `TauCeti.invForm_isSymm` and `TauCeti.invForm_nondegenerate`: the form is symmetric and
  non-degenerate.
* `TauCeti.invForm_apply_apply_eq_traceForm`: the form is the transport of the Killing form.
* `TauCeti.invForm_cartanEquivDual_right` and `TauCeti.invForm_cartanEquivDual_left`: pairing a
  weight against one of the shape `cartanEquivDual H x` evaluates the other weight at `x`.
* `TauCeti.cartanEquivDual_coroot`: the coroot `α^∨` is the weight `2α / ⟨α, α⟩`, read through
  `cartanEquivDual`.
* `TauCeti.invForm_coroot` and `TauCeti.invForm_coroot_weight`: the normalisation
  `⟨λ, α^∨⟩ ⟨α, α⟩ = 2 ⟨λ, α⟩`.
* `TauCeti.traceForm_coroot_self_mul_invForm_self_eq_four`: `⟨α^∨, α^∨⟩ ⟨α, α⟩ = 4`, so a long
  root has a short coroot.

The compatibility with `LieAlgebra.IsKilling.rootSystem_pairing_apply` — that a Cartan integer is
`2 ⟨α, β⟩ / ⟨β, β⟩` — and the orthogonality criterion and reflection invariance of the form are not
restated here: `TauCeti.rootInvariantForm` makes them
`RootPairing.InvariantForm.two_mul_apply_root_root`,
`RootPairing.InvariantForm.apply_root_root_zero_iff` and
`RootPairing.InvariantForm.apply_reflection_reflection`.

## Implementation notes

`invForm` is bundled as a `LinearMap.BilinForm`, so that `invForm a b` still reads as the value of
the form at a pair of weights while the bilinearity is available as data; the latter is what
`RootPairing.InvariantForm` asks for.

The definition is Mathlib's transport combinator `LinearMap.BilinForm.congr` applied to
`cartanEquivDual`, and `TauCeti.invForm_apply_apply_eq_traceForm` is the resulting bridge back to
the restricted Killing form. The unfolding lemma `TauCeti.invForm_apply_apply` reads the form as a
dual pairing instead, because Mathlib's `LieAlgebra.IsKilling.coroot` is defined that way: keeping
the two on the same side of the equivalence is what makes `TauCeti.cartanEquivDual_coroot`, and
with it the normalisation, a computation rather than a transport argument.

The simp-normal form keeps `invForm` folded: `TauCeti.invForm_apply_apply` is not a `simp` lemma,
and it is the eliminators `TauCeti.invForm_cartanEquivDual_left` and
`TauCeti.invForm_cartanEquivDual_right` that carry `@[simp]`. That way `simp` normalises towards
the form rather than away from it, and the `RootPairing.InvariantForm` lemmas that
`TauCeti.rootInvariantForm` buys can still fire.

Only from `TauCeti.invForm_self_ne_zero` on do the results need the root-theory instances
`CharZero K` and `IsTriangularizable K H L`, so the general theory of the form is stated first
without them. The split is by typeclass, not by root-ness: `TauCeti.invForm_coroot_weight` still
takes an arbitrary weight.

## References

This file builds the invariant form on weights of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md` ("the induced symmetric bilinear
form on `Module.Dual K H`, transported from the Killing form on `H` via `cartanEquivDual`", with
"its normalization against coroots, `⟨λ, α^∨⟩ ⟨α, α⟩ = 2 ⟨λ, α⟩`" and "its compatibility with
`rootSystem_pairing_apply` and `IsKilling.coroot`"), the prerequisite that roadmap asks for before
the Casimir element. The material is J. E. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, GTM 9, §8.2-8.5.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-! ## The form -/

/-- The symmetric bilinear form `⟨·,·⟩` on the space of weights `Module.Dual K H` induced by the
Killing form of `L` through `LieAlgebra.IsKilling.cartanEquivDual`.

This is the form in which the Casimir scalar and the Weyl character and dimension formulas are
written; `TauCeti.invForm_coroot` is its normalisation against the coroots. -/
noncomputable def invForm : LinearMap.BilinForm K (Module.Dual K H) :=
  LinearMap.BilinForm.congr (cartanEquivDual H) (traceForm K H L)

/-- The form is the transport of the restricted Killing form along `cartanEquivDual`. -/
theorem invForm_apply_apply_eq_traceForm (a b : Module.Dual K H) :
    invForm a b =
      traceForm K H L ((cartanEquivDual H).symm a) ((cartanEquivDual H).symm b) :=
  LinearMap.BilinForm.congr_apply _ _ a b

/-- The form read as a dual pairing: `cartanEquivDual` is the Killing form, so the transport of
that form pairs `a` with the vector representing `b`. -/
theorem invForm_apply_apply (a b : Module.Dual K H) :
    invForm a b = a ((cartanEquivDual H).symm b) :=
  LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_cartan_nondegenerate K L H) a _

/-- Pairing a weight against one of the shape `cartanEquivDual H x` is evaluation at `x`. This is
the shape of the transport used most often, because it mentions no inverse equivalence. -/
@[simp]
theorem invForm_cartanEquivDual_right (a : Module.Dual K H) (x : H) :
    invForm a (cartanEquivDual H x) = a x := by
  rw [invForm_apply_apply, LinearEquiv.symm_apply_apply]

/-- The form is symmetric, inheriting the symmetry of the Killing form. -/
theorem invForm_isSymm : (invForm (H := H)).IsSymm := by
  constructor
  intro a b
  rw [invForm_apply_apply_eq_traceForm, invForm_apply_apply_eq_traceForm]
  exact ((traceForm_isSymm K H L).eq _ _).symm

/-- Pairing a weight of the shape `cartanEquivDual H x` on the left evaluates the other weight at
`x`; the left-hand companion of `TauCeti.invForm_cartanEquivDual_right`. -/
@[simp]
theorem invForm_cartanEquivDual_left (x : H) (a : Module.Dual K H) :
    invForm (cartanEquivDual H x) a = a x := by
  rw [(invForm_isSymm (H := H)).eq, invForm_cartanEquivDual_right]

/-- The form is non-degenerate, inheriting the non-degeneracy of the Killing form on `H`. -/
theorem invForm_nondegenerate : (invForm (H := H)).Nondegenerate :=
  (traceForm_cartan_nondegenerate K L H).congr (cartanEquivDual H)

/-- **The coroot as a weight**: `α^∨ = 2α / ⟨α, α⟩`, read through `cartanEquivDual`. This says that
`LieAlgebra.IsKilling.coroot` is the coroot *of the invariant form*, and every compatibility below
is a consequence of it.

No hypothesis on `α` is needed: at a zero weight both sides vanish. -/
theorem cartanEquivDual_coroot (α : Weight K H L) :
    cartanEquivDual H (coroot α) =
      (2 * (invForm (α : Module.Dual K H) α)⁻¹) • (α : Module.Dual K H) := by
  ext x
  simpa [invForm_apply_apply, Weight.toLinear_apply, mul_assoc, traceForm_apply_apply,
    Module.End.mul_eq_comp] using traceForm_coroot α x

/-! ## Roots and coroots -/

variable [CharZero K] [LieModule.IsTriangularizable K H L]

/-- A root has non-zero length for the form. -/
theorem invForm_self_ne_zero {α : Weight K H L} (hα : α.IsNonZero) :
    invForm (α : Module.Dual K H) α ≠ 0 := by
  simpa only [invForm_apply_apply, Weight.toLinear_apply] using
    root_apply_cartanEquivDual_symm_ne_zero hα

/-- **The normalisation of the invariant form against the coroots**: `⟨λ, α^∨⟩ ⟨α, α⟩ = 2 ⟨λ, α⟩`,
that is, `α^∨` is the weight `2α / ⟨α, α⟩`.

Like `TauCeti.cartanEquivDual_coroot`, this needs no hypothesis on `α`: at a zero weight both
sides vanish. -/
theorem invForm_coroot_weight (lam : Module.Dual K H) (α : Weight K H L) :
    lam (coroot α) * invForm (α : Module.Dual K H) α = 2 * invForm lam α := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, Weight.coe_toLinear_eq_zero_iff.mpr hα]
    simp
  · have hc := invForm_self_ne_zero hα
    have h : invForm lam (cartanEquivDual H (coroot α)) = lam (coroot α) :=
      invForm_cartanEquivDual_right _ _
    rw [cartanEquivDual_coroot, map_smul, smul_eq_mul] at h
    rw [← h]
    field_simp

/-- **The normalisation of the invariant form against the coroots**, indexed by the roots of
`LieAlgebra.IsKilling.rootSystem`: `⟨λ, α^∨⟩ ⟨α, α⟩ = 2 ⟨λ, α⟩`. -/
theorem invForm_coroot (lam : Module.Dual K H) (i : H.root) :
    lam ((rootSystem H).coroot i) *
        invForm ((rootSystem H).root i) ((rootSystem H).root i) =
      2 * invForm lam ((rootSystem H).root i) :=
  invForm_coroot_weight lam i.1

/-! ## The invariant form of the root system -/

/-- `TauCeti.invForm` as an invariant form on `LieAlgebra.IsKilling.rootSystem H`. -/
noncomputable def rootInvariantForm : (rootSystem H).InvariantForm where
  form := invForm
  symm := LinearMap.BilinForm.isSymm_iff.mp invForm_isSymm
  ne_zero i := by
    simpa only [rootSystem_root_apply] using invForm_self_ne_zero (H.isNonZero_coe_root i)
  isOrthogonal_reflection i := by
    intro a b
    have ha := invForm_coroot_weight a i.1
    have hb := invForm_coroot_weight b i.1
    rw [RootPairing.reflection_apply, RootPairing.reflection_apply]
    simp only [LinearMap.flip_apply, rootSystem_toLinearMap_apply,
      rootSystem_coroot_apply, rootSystem_root_apply, map_sub, LinearMap.sub_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    rw [(invForm_isSymm (H := H)).eq (i.1 : Module.Dual K H) b]
    linear_combination (b (coroot i.1) / 2) * ha + (a (coroot i.1) / 2) * hb

@[simp]
theorem rootInvariantForm_form : (rootInvariantForm (H := H)).form = invForm := (rfl)

/-- **The length of a coroot**: `⟨α^∨, α^∨⟩ ⟨α, α⟩ = 4`, so a long root has a short coroot.

The length `⟨α^∨, α^∨⟩` of the coroot is spelled as the Killing form of `α^∨` with itself rather
than as `invForm (cartanEquivDual H (coroot α)) (cartanEquivDual H (coroot α))`: the eliminator
`TauCeti.invForm_cartanEquivDual_right` is a `simp` lemma, so the latter shape does not survive a
`simp` call. -/
theorem traceForm_coroot_self_mul_invForm_self_eq_four {α : Weight K H L} (hα : α.IsNonZero) :
    traceForm K H L (coroot α) (coroot α) * invForm (α : Module.Dual K H) α = 4 := by
  have hi := invForm_self_ne_zero hα
  have h : traceForm K H L (coroot α) (coroot α) =
      invForm (cartanEquivDual H (coroot α)) (cartanEquivDual H (coroot α)) := by
    rw [invForm_cartanEquivDual_right, cartanEquivDual_apply_apply, traceForm_apply_apply,
      Module.End.mul_eq_comp]
  rw [h, cartanEquivDual_coroot]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp
  ring

end TauCeti
