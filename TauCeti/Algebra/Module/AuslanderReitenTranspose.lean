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
* `AuslanderReitenTranspose.lift`: the universal property of that cokernel, descending an
  opposite-linear map that kills the functionals factoring through `p₁`.
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

section Transpose

variable {P₀ : Type v} {P₁ : Type w} [AddCommMonoid P₀] [Module A P₀]
  [AddCommMonoid P₁] [Module A P₁]

/-- The **Auslander--Reiten transpose** attached to a projective presentation whose first map is
`p₁ : P₁ → P₀`.  It is the cokernel of the opposite-linear precomposition map
`Hom_A(P₀, A) → Hom_A(P₁, A)`.

Minimality is not needed to form the cokernel.  It is used by
`IsMinimalProjectivePresentation.nonempty_linearEquiv_auslanderReitenTranspose` to show that the
result is independent, up to equivalence, of the chosen presentation of a module. -/
def AuslanderReitenTranspose (p₁ : P₁ →ₗ[A] P₀) : Type _ :=
  Module.Dual A P₁ ⧸ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)

namespace AuslanderReitenTranspose

variable (p₁ : P₁ →ₗ[A] P₀)

instance : AddCommGroup (AuslanderReitenTranspose p₁) :=
  inferInstanceAs (AddCommGroup (Module.Dual A P₁ ⧸ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)))

instance : Module Aᵐᵒᵖ (AuslanderReitenTranspose p₁) :=
  inferInstanceAs (Module Aᵐᵒᵖ (Module.Dual A P₁ ⧸ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)))

/-- The quotient map from the dual of the first projective onto its Auslander--Reiten transpose. -/
def mk : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p₁ :=
  (LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)).mkQ

/-- A functional represents zero in the transpose exactly when it factors through the first map of
the presentation. -/
@[simp]
theorem mk_eq_zero_iff (φ : Module.Dual A P₁) :
    mk p₁ φ = 0 ↔ φ ∈ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A) :=
  Submodule.Quotient.mk_eq_zero _

/-- The quotient map onto the transpose kills exactly the functionals factoring through the first
map of the presentation. -/
@[simp]
theorem ker_mk : LinearMap.ker (mk p₁) = LinearMap.range (p₁.lcomp Aᵐᵒᵖ A) := by
  ext φ
  simp [LinearMap.mem_ker]

/-- A functional precomposed with the first map of the presentation vanishes in its cokernel. -/
@[simp]
theorem mk_lcomp (φ : Module.Dual A P₀) :
    mk p₁ (p₁.lcomp Aᵐᵒᵖ A φ) = 0 := by
  rw [mk_eq_zero_iff]
  exact LinearMap.mem_range_self _ φ

/-- Every element of the transpose is represented by a functional on `P₁`. -/
theorem mk_surjective : Function.Surjective (mk p₁) :=
  Submodule.mkQ_surjective _

/-- Two functionals represent the same element of the transpose exactly when their difference
factors through the first map of the presentation. -/
@[simp]
theorem mk_eq_mk_iff (φ ψ : Module.Dual A P₁) :
    mk p₁ φ = mk p₁ ψ ↔ φ - ψ ∈ LinearMap.range (p₁.lcomp Aᵐᵒᵖ A) :=
  Submodule.Quotient.eq _

/-- To prove a property of every element of the transpose it suffices to prove it of the classes
of functionals on `P₁`. -/
@[elab_as_elim]
theorem induction_on {motive : AuslanderReitenTranspose p₁ → Prop}
    (x : AuslanderReitenTranspose p₁) (h : ∀ φ : Module.Dual A P₁, motive (mk p₁ φ)) :
    motive x :=
  Submodule.Quotient.induction_on _ x h

section Lift

variable {N : Type*} [AddCommGroup N] [Module Aᵐᵒᵖ N]

/-- The universal property of the transpose: an opposite-linear map out of `Hom_A(P₁, A)` that
kills every functional factoring through `p₁` descends to the cokernel. -/
def lift (f : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] N)
    (hf : ∀ φ : Module.Dual A P₀, f (p₁.lcomp Aᵐᵒᵖ A φ) = 0) :
    AuslanderReitenTranspose p₁ →ₗ[Aᵐᵒᵖ] N :=
  Submodule.liftQ _ f <| by
    rintro _ ⟨φ, rfl⟩
    exact hf φ

@[simp]
theorem lift_mk (f : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] N)
    (hf : ∀ φ : Module.Dual A P₀, f (p₁.lcomp Aᵐᵒᵖ A φ) = 0) (φ : Module.Dual A P₁) :
    lift p₁ f hf (mk p₁ φ) = f φ :=
  Submodule.liftQ_apply _ f φ

/-- `AuslanderReitenTranspose.lift` factors the given map through the quotient map. -/
@[simp]
theorem lift_comp_mk (f : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] N)
    (hf : ∀ φ : Module.Dual A P₀, f (p₁.lcomp Aᵐᵒᵖ A φ) = 0) :
    (lift p₁ f hf).comp (mk p₁) = f :=
  LinearMap.ext fun φ => lift_mk p₁ f hf φ

/-- Opposite-linear maps out of the transpose are determined by their values on representatives. -/
@[ext]
theorem hom_ext {f g : AuslanderReitenTranspose p₁ →ₗ[Aᵐᵒᵖ] N}
    (h : ∀ φ : Module.Dual A P₁, f (mk p₁ φ) = g (mk p₁ φ)) : f = g :=
  LinearMap.ext fun x => induction_on p₁ x h

/-- `AuslanderReitenTranspose.lift` is the unique descent of `f` to the transpose. -/
theorem eq_lift (f : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] N)
    (hf : ∀ φ : Module.Dual A P₀, f (p₁.lcomp Aᵐᵒᵖ A φ) = 0)
    (g : AuslanderReitenTranspose p₁ →ₗ[Aᵐᵒᵖ] N)
    (hg : ∀ φ : Module.Dual A P₁, g (mk p₁ φ) = f φ) :
    g = lift p₁ f hf :=
  hom_ext p₁ fun φ => by rw [hg, lift_mk]

end Lift

variable {p₁}

section Equivalence

variable {Q₀ : Type v'} {Q₁ : Type w'} [AddCommMonoid Q₀] [Module A Q₀]
  [AddCommMonoid Q₁] [Module A Q₁]

private theorem map_range_lcomp_eq {q₁ : Q₁ →ₗ[A] Q₀} (e₀ : P₀ ≃ₗ[A] Q₀)
    (e₁ : P₁ ≃ₗ[A] Q₁)
    (hsquare : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap) :
    Submodule.map (e₁.congrLeft A Aᵐᵒᵖ : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] Module.Dual A Q₁)
        (LinearMap.range (p₁.lcomp Aᵐᵒᵖ A)) =
      LinearMap.range (q₁.lcomp Aᵐᵒᵖ A) := by
  rw [← LinearMap.range_comp]
  have hcomp :
      (e₁.congrLeft A Aᵐᵒᵖ).toLinearMap.comp (p₁.lcomp Aᵐᵒᵖ A) =
        (q₁.lcomp Aᵐᵒᵖ A).comp (e₀.congrLeft A Aᵐᵒᵖ).toLinearMap := by
    ext φ x
    simp only [LinearMap.comp_apply, LinearMap.lcomp_apply]
    apply congrArg φ
    simpa using congrArg e₀.symm (LinearMap.congr_fun hsquare (e₁.symm x))
  rw [hcomp, LinearEquiv.range_comp]

/-- An isomorphism of the first square of two projective presentations induces an equivalence of
their Auslander--Reiten transposes.  On representatives it sends `φ : Hom_A(P₁, A)` to
`φ ∘ e₁⁻¹ : Hom_A(Q₁, A)`.

The equivalence depends only on the two presentation isomorphisms and their commutative square; the
maps from `P₀` and `Q₀` to the presented module do not enter the cokernel. -/
def linearEquiv {q₁ : Q₁ →ₗ[A] Q₀} (e₀ : P₀ ≃ₗ[A] Q₀)
    (e₁ : P₁ ≃ₗ[A] Q₁)
    (hsquare : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap) :
    AuslanderReitenTranspose p₁ ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose q₁ :=
  Submodule.Quotient.equiv _ _ (e₁.congrLeft A Aᵐᵒᵖ) (map_range_lcomp_eq e₀ e₁ hsquare)

/-- The presentation equivalence on transposes, evaluated on a functional representative. -/
@[simp]
theorem linearEquiv_mk {q₁ : Q₁ →ₗ[A] Q₀} (e₀ : P₀ ≃ₗ[A] Q₀)
    (e₁ : P₁ ≃ₗ[A] Q₁)
    (hsquare : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap)
    (φ : Module.Dual A P₁) :
    linearEquiv e₀ e₁ hsquare (mk p₁ φ) =
      mk q₁ (e₁.symm.toLinearMap.lcomp Aᵐᵒᵖ A φ) := by
  have hrep : (e₁.congrLeft A Aᵐᵒᵖ : Module.Dual A P₁ →ₗ[Aᵐᵒᵖ] Module.Dual A Q₁) φ =
      e₁.symm.toLinearMap.lcomp Aᵐᵒᵖ A φ := by
    ext x
    simp [LinearMap.lcomp_apply]
  -- `linearEquiv`, `mk` and `AuslanderReitenTranspose` itself are not exposed, so neither the
  -- statement nor Mathlib's quotient lemmas reduce here on their own: an exported theorem may only
  -- unfold exposed definitions.  `with_unfolding_all` lets this proof see through them, and the
  -- `change` then presents the goal in the `Submodule.Quotient` form in which
  -- `Submodule.Quotient.equiv_apply` and `Submodule.mapQ_apply` apply; `hrep` then identifies the
  -- representative maps through public application lemmas rather than by definitional unfolding.
  with_unfolding_all
    change Submodule.Quotient.equiv _ _ _ _ (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk _
    rw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, hrep]

/-- Transport along the identity presentation equivalences is the identity. -/
@[simp]
theorem linearEquiv_refl :
    linearEquiv (LinearEquiv.refl A P₀) (LinearEquiv.refl A P₁) (by simp) =
      LinearEquiv.refl Aᵐᵒᵖ (AuslanderReitenTranspose p₁) := by
  apply LinearEquiv.ext
  intro x
  induction x using induction_on p₁ with
  | _ φ =>
    rw [linearEquiv_mk]
    apply congrArg (mk p₁)
    ext y
    simp only [LinearMap.lcomp_apply, LinearEquiv.refl_symm, LinearEquiv.refl_toLinearMap,
      LinearMap.id_apply]

/-- Transport along a composite of presentation equivalences is the composite transport. -/
@[simp]
theorem linearEquiv_trans {q₁ : Q₁ →ₗ[A] Q₀}
    {R₀ R₁ : Type*} [AddCommMonoid R₀] [Module A R₀] [AddCommMonoid R₁] [Module A R₁]
    {r₁ : R₁ →ₗ[A] R₀} (e₀ : P₀ ≃ₗ[A] Q₀) (e₁ : P₁ ≃ₗ[A] Q₁)
    (f₀ : Q₀ ≃ₗ[A] R₀) (f₁ : Q₁ ≃ₗ[A] R₁)
    (he : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap)
    (hf : f₀.toLinearMap ∘ₗ q₁ = r₁ ∘ₗ f₁.toLinearMap) :
    (linearEquiv e₀ e₁ he).trans (linearEquiv f₀ f₁ hf) =
      linearEquiv (e₀.trans f₀) (e₁.trans f₁)
        (by
          ext x
          have h₀ := LinearMap.congr_fun he x
          have h₁ := LinearMap.congr_fun hf (e₁ x)
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h₀ h₁ ⊢
          rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h₀, h₁]) := by
  apply LinearEquiv.ext
  intro x
  induction x using induction_on p₁ with
  | _ φ =>
    rw [LinearEquiv.trans_apply, linearEquiv_mk, linearEquiv_mk, linearEquiv_mk]
    apply congrArg (mk r₁)
    ext y
    simp only [LinearMap.lcomp_apply, LinearEquiv.trans_symm, LinearEquiv.coe_trans,
      LinearMap.comp_apply]

/-- The inverse of transport is transport along the inverse presentation equivalences. -/
@[simp]
theorem linearEquiv_symm {q₁ : Q₁ →ₗ[A] Q₀} (e₀ : P₀ ≃ₗ[A] Q₀)
    (e₁ : P₁ ≃ₗ[A] Q₁)
    (hsquare : e₀.toLinearMap ∘ₗ p₁ = q₁ ∘ₗ e₁.toLinearMap) :
    (linearEquiv e₀ e₁ hsquare).symm =
      linearEquiv e₀.symm e₁.symm
        (by
          ext x
          have h := LinearMap.congr_fun hsquare (e₁.symm x)
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
            LinearEquiv.apply_symm_apply] at h ⊢
          rw [← h, LinearEquiv.symm_apply_apply]) := by
  apply LinearEquiv.ext
  intro x
  induction x using induction_on q₁ with
  | _ φ =>
    apply (linearEquiv e₀ e₁ hsquare).injective
    rw [LinearEquiv.apply_symm_apply, linearEquiv_mk, linearEquiv_mk]
    apply congrArg (mk q₁)
    ext y
    simp only [LinearMap.lcomp_apply, LinearEquiv.symm_symm]
    exact congrArg φ (e₁.apply_symm_apply y).symm

end Equivalence

end AuslanderReitenTranspose

end Transpose

namespace IsMinimalProjectivePresentation

variable {M : Type*} [AddCommGroup M] [Module A M]
variable {P₀ : Type v} [AddCommGroup P₀] [Module A P₀]

section Projective

variable {P₁ : Type w} [AddCommMonoid P₁] [Module A P₁]
variable {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}

/-- The Auslander--Reiten transpose of a projective module is zero, represented here by the
stronger typeclass-friendly statement that its underlying quotient is a subsingleton. -/
theorem subsingleton_auslanderReitenTranspose_of_projective
    [Module.Projective A M] (h : IsMinimalProjectivePresentation p₁ p₀) :
    Subsingleton (AuslanderReitenTranspose p₁) := by
  let _ : Subsingleton P₁ := h.subsingleton_of_projective
  constructor
  intro x y
  induction x using AuslanderReitenTranspose.induction_on p₁ with
  | _ φ =>
    induction y using AuslanderReitenTranspose.induction_on p₁ with
    | _ ψ => exact congrArg (AuslanderReitenTranspose.mk p₁) (Subsingleton.elim φ ψ)

end Projective

section Comparison

variable {P₁ : Type w} [AddCommGroup P₁] [Module A P₁]
variable {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}
variable {Q₀ : Type v'} {Q₁ : Type w'} [AddCommGroup Q₀] [Module A Q₀]
  [AddCommGroup Q₁] [Module A Q₁]
variable {q₁ : Q₁ →ₗ[A] Q₀} {q₀ : Q₀ →ₗ[A] M}

/-- The Auslander--Reiten transpose is independent, up to opposite-linear equivalence, of the
chosen minimal projective presentation of a module. -/
theorem nonempty_linearEquiv_auslanderReitenTranspose
    (h : IsMinimalProjectivePresentation p₁ p₀)
    (h' : IsMinimalProjectivePresentation q₁ q₀) :
    Nonempty (AuslanderReitenTranspose p₁ ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose q₁) := by
  obtain ⟨e₀, e₁, -, hsquare⟩ := h.exists_linearEquiv h'
  exact ⟨AuslanderReitenTranspose.linearEquiv e₀ e₁ hsquare⟩

end Comparison

end IsMinimalProjectivePresentation

end TauCeti
