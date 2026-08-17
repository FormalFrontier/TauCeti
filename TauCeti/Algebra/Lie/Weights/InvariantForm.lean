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
equivalence puts a symmetric non-degenerate bilinear form `⟨·,·⟩` on the weight space
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
* `TauCeti.invForm_eq_traceForm`, `TauCeti.invForm_cartanEquivDual_left` and
  `TauCeti.invForm_cartanEquivDual`: the form is the transport of the Killing form, in the three
  shapes in which that is used.
* `TauCeti.cartanEquivDual_coroot`: the coroot `α^∨` is the weight `2α / ⟨α, α⟩`, read through
  `cartanEquivDual`.
* `TauCeti.invForm_coroot` and `TauCeti.invForm_coroot_of_isNonZero`: the normalisation
  `⟨λ, α^∨⟩ ⟨α, α⟩ = 2 ⟨λ, α⟩`.
* `TauCeti.pairing_mul_invForm_root_self`: the Cartan integer of a pair of roots is
  `2 ⟨α, β⟩ / ⟨β, β⟩`, the compatibility with `LieAlgebra.IsKilling.rootSystem_pairing_apply`.
* `TauCeti.invForm_root_root_eq_zero_iff`: two roots are orthogonal for the form exactly when their
  Cartan integer vanishes.
* `TauCeti.invForm_cartanEquivDual_coroot_self`: `⟨α^∨, α^∨⟩ ⟨α, α⟩ = 4`, so a long root has a
  short coroot.

## Implementation notes

`invForm` is bundled as a `LinearMap.BilinForm`, so that `invForm a b` still reads as the value of
the form at a pair of weights while the bilinearity is available as data; the latter is what
`RootPairing.InvariantForm` asks for.

The definition, and the unfolding lemma `TauCeti.invForm_apply`, are stated through
`cartanEquivDual` rather than through the restricted Killing form directly, because Mathlib's
`LieAlgebra.IsKilling.coroot` is itself defined that way: keeping the two on the same side of the
equivalence is what makes `TauCeti.cartanEquivDual_coroot`, and with it the normalisation, a
computation rather than a transport argument. `TauCeti.invForm_eq_traceForm` is the bridge back.

Only `TauCeti.invForm_self_ne_zero` and what follows it need `α` to be a root, so the general
theory of the form is stated first, with neither `CharZero K` nor `IsTriangularizable K H L` in
scope.

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

/-- The symmetric bilinear form `⟨·,·⟩` on the weight space `Module.Dual K H` induced by the
Killing form of `L` through `LieAlgebra.IsKilling.cartanEquivDual`.

This is the form in which the Casimir scalar and the Weyl character and dimension formulas are
written; `TauCeti.invForm_coroot` is its normalisation against the coroots. -/
noncomputable def invForm : LinearMap.BilinForm K (Module.Dual K H) :=
  (LinearMap.id : Module.Dual K H →ₗ[K] Module.Dual K H).compl₂
    (cartanEquivDual H).symm.toLinearMap

@[simp]
theorem invForm_apply (a b : Module.Dual K H) :
    invForm a b = a ((cartanEquivDual H).symm b) :=
  (rfl)

/-- `LieAlgebra.IsKilling.cartanEquivDual` is the restricted Killing form, in the shape in which
`TauCeti.invForm_eq_traceForm` consumes it. Mathlib's `cartanEquivDual_apply_apply` states the same
identity with the trace form already unfolded to a trace. -/
theorem cartanEquivDual_apply_apply_eq_traceForm (x y : H) :
    (cartanEquivDual H x) y = traceForm K H L x y := by
  rw [cartanEquivDual_apply_apply, traceForm_apply_apply]
  rfl

/-- The form is the transport of the restricted Killing form along `cartanEquivDual`. -/
theorem invForm_eq_traceForm (a b : Module.Dual K H) :
    invForm a b =
      traceForm K H L ((cartanEquivDual H).symm a) ((cartanEquivDual H).symm b) := by
  rw [invForm_apply, ← cartanEquivDual_apply_apply_eq_traceForm, LinearEquiv.apply_symm_apply]

/-- Pairing a weight against one of the shape `cartanEquivDual H x` is evaluation at `x`. This is
the shape of the transport used most often, because it mentions no inverse equivalence. -/
theorem invForm_cartanEquivDual_right (a : Module.Dual K H) (x : H) :
    invForm a (cartanEquivDual H x) = a x := by
  rw [invForm_apply, LinearEquiv.symm_apply_apply]

theorem invForm_isSymm : (invForm (H := H)).IsSymm := by
  constructor
  intro a b
  rw [invForm_eq_traceForm, invForm_eq_traceForm]
  exact ((traceForm_isSymm K H L).eq _ _).symm

theorem invForm_comm (a b : Module.Dual K H) : invForm a b = invForm b a :=
  (invForm_isSymm (H := H)).eq a b

theorem invForm_cartanEquivDual_left (x : H) (a : Module.Dual K H) :
    invForm (cartanEquivDual H x) a = a x := by
  rw [invForm_comm, invForm_cartanEquivDual_right]

/-- On the image of `cartanEquivDual` the form is the restricted Killing form. -/
theorem invForm_cartanEquivDual (x y : H) :
    invForm (cartanEquivDual H x) (cartanEquivDual H y) = traceForm K H L x y := by
  rw [invForm_cartanEquivDual_right, cartanEquivDual_apply_apply_eq_traceForm]

/-- A weight orthogonal to every weight vanishes, because `cartanEquivDual` is onto the weight
space. -/
theorem invForm_separatingLeft : (invForm (H := H)).SeparatingLeft := by
  intro a ha
  ext x
  simpa using ha (cartanEquivDual H x)

/-- The form is non-degenerate, inheriting the non-degeneracy of the Killing form on `H`. -/
theorem invForm_nondegenerate : (invForm (H := H)).Nondegenerate :=
  ⟨invForm_separatingLeft, fun b hb ↦
    invForm_separatingLeft b fun a ↦ (invForm_comm b a).trans (hb a)⟩

/-- **The coroot as a weight**: `α^∨ = 2α / ⟨α, α⟩`, read through `cartanEquivDual`. This says that
`LieAlgebra.IsKilling.coroot` is the coroot *of the invariant form*, and every compatibility below
is a consequence of it.

No hypothesis on `α` is needed: at a zero weight both sides vanish. -/
theorem cartanEquivDual_coroot (α : Weight K H L) :
    cartanEquivDual H (coroot α) =
      (2 * (invForm (α : Module.Dual K H) α)⁻¹) • (α : Module.Dual K H) := by
  rw [coroot, map_nsmul, map_smul, LinearEquiv.apply_symm_apply, ← Nat.cast_smul_eq_nsmul K,
    smul_smul, invForm_apply, Weight.toLinear_apply]
  norm_num

/-! ## Roots and coroots -/

variable [CharZero K] [LieModule.IsTriangularizable K H L]

/-- A root has non-zero length for the form. -/
theorem invForm_self_ne_zero {α : Weight K H L} (hα : α.IsNonZero) :
    invForm (α : Module.Dual K H) α ≠ 0 := by
  simpa using root_apply_cartanEquivDual_symm_ne_zero hα

/-- **The normalisation of the invariant form against the coroots**: `⟨λ, α^∨⟩ ⟨α, α⟩ = 2 ⟨λ, α⟩`,
that is, `α^∨` is the weight `2α / ⟨α, α⟩`. -/
theorem invForm_coroot_of_isNonZero (lam : Module.Dual K H) {α : Weight K H L}
    (hα : α.IsNonZero) :
    lam (coroot α) * invForm (α : Module.Dual K H) α = 2 * invForm lam α := by
  have hc := invForm_self_ne_zero hα
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
  invForm_coroot_of_isNonZero lam (H.isNonZero_coe_root i)

/-- **Compatibility with `LieAlgebra.IsKilling.rootSystem_pairing_apply`**: the Cartan integer of a
pair of roots is `2 ⟨α, β⟩ / ⟨β, β⟩`. -/
theorem pairing_mul_invForm_root_self (i j : H.root) :
    (rootSystem H).pairing i j *
        invForm ((rootSystem H).root j) ((rootSystem H).root j) =
      2 * invForm ((rootSystem H).root i) ((rootSystem H).root j) :=
  invForm_coroot _ j

/-! ## The invariant form of the root system -/

/-- `TauCeti.invForm` as an invariant form on `LieAlgebra.IsKilling.rootSystem H`. -/
noncomputable def rootInvariantForm : (rootSystem H).InvariantForm where
  form := invForm
  symm := LinearMap.BilinForm.isSymm_iff.mp invForm_isSymm
  ne_zero i := by
    simpa only [rootSystem_root_apply] using invForm_self_ne_zero (H.isNonZero_coe_root i)
  isOrthogonal_reflection i := by
    intro a b
    have hd : i.1 ((cartanEquivDual H).symm i.1) ≠ 0 :=
      root_apply_cartanEquivDual_symm_ne_zero (H.isNonZero_coe_root i)
    have hai := invForm_comm a (i.1 : Module.Dual K H)
    have hbi := invForm_comm b (i.1 : Module.Dual K H)
    -- Definitional equality: `(rootSystem H).reflection i` expands to reflection along `i.1`.
    change invForm (a - a (coroot i.1) • (i.1 : Module.Dual K H))
      (b - b (coroot i.1) • (i.1 : Module.Dual K H)) = invForm a b
    simp only [map_sub, LinearMap.sub_apply, map_smul, map_nsmul, LinearMap.smul_apply,
      invForm_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, coroot]
    simp only [invForm_apply] at hai hbi
    rw [hai, hbi]
    simp only [Weight.toLinear_apply]
    field_simp
    ring

@[simp]
theorem rootInvariantForm_form : (rootInvariantForm (H := H)).form = invForm := (rfl)

/-- Two roots are orthogonal for the invariant form exactly when their Cartan integer vanishes. -/
theorem invForm_root_root_eq_zero_iff (i j : H.root) :
    invForm ((rootSystem H).root i) ((rootSystem H).root j) = 0 ↔
      (rootSystem H).pairing i j = 0 :=
  (rootInvariantForm (H := H)).apply_root_root_zero_iff i j

/-- The reflections of the root system preserve the form. -/
theorem invForm_reflection (i : H.root) (a b : Module.Dual K H) :
    invForm ((rootSystem H).reflection i a) ((rootSystem H).reflection i b) = invForm a b :=
  (rootInvariantForm (H := H)).apply_reflection_reflection i a b

/-- **The length of a coroot**: `⟨α^∨, α^∨⟩ ⟨α, α⟩ = 4`, so a long root has a short coroot. -/
theorem invForm_cartanEquivDual_coroot_self (i : H.root) :
    invForm (cartanEquivDual H (coroot i.1)) (cartanEquivDual H (coroot i.1)) *
        invForm (i.1 : Module.Dual K H) i.1 = 4 := by
  have hi := invForm_self_ne_zero (H.isNonZero_coe_root i)
  rw [cartanEquivDual_coroot]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp
  ring

end TauCeti
