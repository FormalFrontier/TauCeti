/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.MinimalProjectivePresentation

/-!
# The Auslander--Reiten transpose

Given a projective presentation `P₁ → P₀ → M`, applying `Hom_A(-, A)` reverses the first map.
The cokernel

`Hom_A(P₁, A) / range(Hom_A(P₀, A) → Hom_A(P₁, A))`

is the **Auslander--Reiten transpose** of the presentation.  It is naturally a left module over the
opposite ring `Aᵐᵒᵖ`: an element `op a` acts on a functional by multiplication by `a` on the right.
Mathlib already supplies this opposite-ring module structure on `Module.Dual A P` and the
precomposition map as `p.lcomp Aᵐᵒᵖ A`; this file forms its cokernel rather than rebuilding either.

The transpose is independent, up to linear equivalence, of the chosen minimal projective
presentation.  More precisely, an isomorphism of presentation diagrams induces an equivalence of
the two cokernels (`AuslanderReitenTranspose.linearEquiv`), characterized on representatives, and
the uniqueness theorem for minimal presentations then gives
`IsMinimalProjectivePresentation.nonempty_linearEquiv_auslanderReitenTranspose`.

This supplies the transpose construction in sublayer 6C of the quiver-representations roadmap.
The remaining part of 6C develops its stable equivalence; sublayer 6D then applies finite-field
duality `D = Hom_k(-, k)` to construct the Auslander--Reiten translate `τ = D Tr`.

## Main definitions

* `AuslanderReitenTranspose`: the cokernel of the dual of the first map in a projective
  presentation.
* `AuslanderReitenTranspose.linearEquiv`: the equivalence induced by an isomorphism of presentation
  diagrams.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section IV.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Cambridge University Press (2006), Section IV.2.
-/

public section

namespace TauCeti

universe u v w v' w'

variable {A : Type u} [Ring A]
variable {P₀ : Type v} {P₁ : Type w} [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁]

/-- The **Auslander--Reiten transpose** attached to a projective presentation whose first map is
`p₁ : P₁ → P₀`.  It is the cokernel of the opposite-linear precomposition map
`Hom_A(P₀, A) → Hom_A(P₁, A)`.

Minimality is not needed to form the cokernel.  It is used by
`IsMinimalProjectivePresentation.nonempty_linearEquiv_auslanderReitenTranspose` to show that the
result is independent, up to equivalence, of the chosen presentation of a module. -/
abbrev AuslanderReitenTranspose (p₁ : P₁ →ₗ[A] P₀) : Type _ :=
  Module.Dual A P₁ ⧸ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)

namespace AuslanderReitenTranspose

variable (p₁ : P₁ →ₗ[A] P₀)

/-- The quotient map from the dual of the first projective onto its Auslander--Reiten transpose. -/
def mk : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p₁ :=
  (LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)).mkQ

theorem mk_apply (φ : Module.Dual A P₁) :
    mk p₁ φ = Submodule.Quotient.mk φ :=
  (rfl)

/-- A functional represents zero in the transpose exactly when it factors through the first map of
the presentation. -/
@[simp]
theorem mk_eq_zero_iff (φ : Module.Dual A P₁) :
    mk p₁ φ = 0 ↔ φ ∈ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A) := by
  rw [mk_apply, Submodule.Quotient.mk_eq_zero]

/-- A functional precomposed with the first map of the presentation vanishes in its cokernel. -/
@[simp]
theorem mk_lcomp (φ : Module.Dual A P₀) :
    mk p₁ (p₁.lcomp Aᵐᵒᵖ A φ) = 0 := by
  rw [mk_eq_zero_iff]
  exact LinearMap.mem_range_self _ φ

variable {p₁}

section Equivalence

variable {Q₀ : Type v'} {Q₁ : Type w'} [AddCommGroup Q₀] [Module A Q₀]
  [AddCommGroup Q₁] [Module A Q₁]

/-- Dualizing a linear equivalence of left modules gives a linear equivalence of their
opposite-ring duals.  This file-local construction is used to transport the cokernel below. -/
private def opDualMap (e : P₁ ≃ₗ[A] Q₁) :
    Module.Dual A P₁ ≃ₗ[Aᵐᵒᵖ] Module.Dual A Q₁ where
  __ := e.symm.toLinearMap.lcomp Aᵐᵒᵖ A
  invFun := e.toLinearMap.lcomp Aᵐᵒᵖ A
  left_inv φ := by
    ext x
    exact congrArg φ (e.symm_apply_apply x)
  right_inv φ := by
    ext x
    exact congrArg φ (e.apply_symm_apply x)

private theorem map_range_lcomp_eq {q₁ : Q₁ →ₗ[A] Q₀} (e₀ : P₀ ≃ₗ[A] Q₀)
    (e₁ : P₁ ≃ₗ[A] Q₁)
    (hsquare : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap) :
    Submodule.map (opDualMap e₁ : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] Module.Dual A Q₁)
        (LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)) =
      LinearMap.range (q₁.lcomp Aᵐᵒᵖ A) := by
  apply le_antisymm
  · rintro _ ⟨φ, ⟨ψ, rfl⟩, rfl⟩
    refine ⟨e₀.symm.toLinearMap.lcomp Aᵐᵒᵖ A ψ, ?_⟩
    ext x
    have h := LinearMap.congr_fun hsquare (e₁.symm x)
    have h' : e₀ (p₁ (e₁.symm x)) = q₁ x := by
      simpa using h
    have h'' : p₁ (e₁.symm x) = e₀.symm (q₁ x) := by
      simpa using congrArg e₀.symm h'
    -- Expose the nested precomposition applications hidden by the linear-map coercions.
    change ψ (e₀.symm (q₁ x)) = ψ (p₁ (e₁.symm x))
    exact congrArg ψ h''.symm
  · rintro _ ⟨ψ, rfl⟩
    refine ⟨p₁.lcomp Aᵐᵒᵖ A (e₀.toLinearMap.lcomp Aᵐᵒᵖ A ψ), ?_, ?_⟩
    · exact LinearMap.mem_range_self _ _
    · ext x
      have h := LinearMap.congr_fun hsquare (e₁.symm x)
      have h' : e₀ (p₁ (e₁.symm x)) = q₁ x := by
        simpa using h
      -- Expose the nested precomposition applications hidden by the linear-map coercions.
      change ψ (e₀ (p₁ (e₁.symm x))) = ψ (q₁ x)
      exact congrArg ψ h'

/-- An isomorphism of the first square of two projective presentations induces an equivalence of
their Auslander--Reiten transposes.  On representatives it sends `φ : Hom_A(P₁, A)` to
`φ ∘ e₁⁻¹ : Hom_A(Q₁, A)`.

The equivalence depends only on the two presentation isomorphisms and their commutative square; the
maps from `P₀` and `Q₀` to the presented module do not enter the cokernel. -/
def linearEquiv {q₁ : Q₁ →ₗ[A] Q₀} (e₀ : P₀ ≃ₗ[A] Q₀)
    (e₁ : P₁ ≃ₗ[A] Q₁)
    (hsquare : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap) :
    AuslanderReitenTranspose p₁ ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose q₁ :=
  Submodule.Quotient.equiv _ _ (opDualMap e₁) (map_range_lcomp_eq e₀ e₁ hsquare)

/-- The presentation equivalence on transposes, evaluated on a functional representative. -/
@[simp]
theorem linearEquiv_mk {q₁ : Q₁ →ₗ[A] Q₀} (e₀ : P₀ ≃ₗ[A] Q₀)
    (e₁ : P₁ ≃ₗ[A] Q₁)
    (hsquare : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap)
    (φ : Module.Dual A P₁) :
    linearEquiv e₀ e₁ hsquare (mk p₁ φ) =
      mk q₁ (e₁.symm.toLinearMap.lcomp Aᵐᵒᵖ A φ) := by
  rw [mk_apply, linearEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, mk_apply]
  rfl

end Equivalence

end AuslanderReitenTranspose

namespace IsMinimalProjectivePresentation

variable {M : Type*} [AddCommGroup M] [Module A M]
variable {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}
variable {Q₀ : Type v'} {Q₁ : Type w'} [AddCommGroup Q₀] [Module A Q₀]
  [AddCommGroup Q₁] [Module A Q₁]
variable {q₁ : Q₁ →ₗ[A] Q₀} {q₀ : Q₀ →ₗ[A] M}

/-- The Auslander--Reiten transpose of a projective module is zero, represented here by the
stronger typeclass-friendly statement that its underlying quotient is a subsingleton. -/
theorem subsingleton_auslanderReitenTranspose_of_projective
    [Module.Projective A M] (h : IsMinimalProjectivePresentation p₁ p₀) :
    Subsingleton (AuslanderReitenTranspose p₁) := by
  let _ : Subsingleton P₁ := h.subsingleton_of_projective
  infer_instance

/-- The Auslander--Reiten transpose is independent, up to opposite-linear equivalence, of the
chosen minimal projective presentation of a module. -/
theorem nonempty_linearEquiv_auslanderReitenTranspose
    (h : IsMinimalProjectivePresentation p₁ p₀)
    (h' : IsMinimalProjectivePresentation q₁ q₀) :
    Nonempty (AuslanderReitenTranspose p₁ ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose q₁) := by
  obtain ⟨e₀, e₁, -, hsquare⟩ := h.exists_linearEquiv h'
  exact ⟨AuslanderReitenTranspose.linearEquiv e₀ e₁ hsquare⟩

end IsMinimalProjectivePresentation

end TauCeti
