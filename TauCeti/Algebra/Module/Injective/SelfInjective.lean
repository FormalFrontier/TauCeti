/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Self-injective algebras

A ring is **self-injective** when its regular left module is injective, `Module.Injective A A`.
This file proves the criterion producing the examples which come from a Frobenius structure: an
algebra over a field carrying an associative perfect bilinear form is self-injective.

The form is a `k`-bilinear `B : A →ₗ[k] A →ₗ[k] k` which is *associative*,
`B (x * y) z = B x (y * z)`, and *perfect* in the sense of `LinearMap.IsPerfPair`. Associativity
already forces `B x y = B 1 (x * y)`, so the form is multiplication followed by the linear
functional `B 1`, the Frobenius trace; perfectness is nondegeneracy in the strong form which also
makes every functional on `A` of the shape `B · a`.

The proof is Baer's criterion. Given a left ideal `I` and an `A`-linear `f : I →ₗ[A] A`, the trace
turns `f` into a `k`-linear functional on `I`, which extends to a functional `ψ` on `A` because `I`
is a subspace of a vector space; perfectness writes `ψ` as `B · a` for some `a : A`, and right
multiplication by `a` is the required extension of `f`. Indeed `x * a` and `f x` pair identically
against every `y : A`, because associativity moves `y` inside `f`: `B y (x * a) = B (y * x) a` is
`ψ` at `y * x ∈ I`, which is `B 1 (f (y * x)) = B 1 (y * f x) = B y (f x)`. Only bijectivity of
`B.flip` is used, that is, nondegeneracy in the second variable together with surjectivity onto the
dual.

Two general facts about Baer modules are proved along the way and stated in Mathlib's `Module.Baer`
namespace, which has neither. A retract of a Baer module is Baer (`Module.Baer.of_leftInverse`),
and consequently the left ideal cut out by an idempotent is Baer over a self-injective ring
(`Module.Baer.of_isIdempotentElem`): over a self-injective ring the principal projective modules
are injective. Everything is stated for `Module.Baer` rather than `Module.Injective` because the
two convert freely in one direction only, `Module.Baer.of_injective` costing a smallness hypothesis
on the ring.

## Main results

* `Function.Bijective.moduleBaer_self` and `Function.Bijective.moduleInjective_self`: an algebra
  over a field carrying an associative bilinear form whose flip is bijective is self-injective.
* `Module.Baer.of_leftInverse`: a retract of a Baer module is Baer.
* `Module.Baer.of_isIdempotentElem`: over a self-injective ring, a left ideal consisting of the
  elements fixed by right multiplication by an idempotent is Baer.

## References

See Curtis--Reiner, *Methods of representation theory* I, Section 9, and Lam, *Lectures on modules
and rings*, Sections 3 and 16, for Frobenius algebras and self-injectivity.
-/

public section

namespace TauCeti

universe u v w

/-! ### Retracts and idempotent corners of a Baer module -/

section Retract

variable {R : Type u} [Ring R] {Q : Type v} [AddCommGroup Q] [Module R Q]
  {M : Type w} [AddCommGroup M] [Module R M]

/-- **A retract of a Baer module is Baer.** A map out of an ideal is pushed into `Q`, extended
there, and pulled back along the retraction. -/
theorem _root_.Module.Baer.of_leftInverse (hQ : Module.Baer R Q) (s : M →ₗ[R] Q) (r : Q →ₗ[R] M)
    (hrs : ∀ m, r (s m) = m) : Module.Baer R M := fun I g => by
  obtain ⟨g', hg'⟩ := hQ I (s ∘ₗ g)
  exact ⟨r ∘ₗ g', fun x hx => by rw [LinearMap.comp_apply, hg' x hx, LinearMap.comp_apply, hrs]⟩

end Retract

section Idempotent

variable {A : Type u} [Ring A]

/-- **Over a self-injective ring the principal projective modules are injective**, in Baer's form:
if the regular module is Baer then so is a left ideal `p` consisting of the elements fixed by right
multiplication by an idempotent `e`, such a `p` being a retract of the regular module by right
multiplication by `e`. For `p = Ideal.span {e}` the hypothesis `hp` is
`TauCeti.mem_span_singleton_iff_mul_eq_self`. -/
theorem _root_.Module.Baer.of_isIdempotentElem (hA : Module.Baer A A) {e : A}
    (he : IsIdempotentElem e) {p : Ideal A} (hp : ∀ x : A, x ∈ p ↔ x * e = x) :
    Module.Baer A p :=
  hA.of_leftInverse p.subtype
    { toFun := fun x => ⟨x * e, (hp _).2 (by rw [mul_assoc, he.eq])⟩
      map_add' := fun x y => Subtype.ext (add_mul x y e)
      map_smul' := fun a x => Subtype.ext (by simp [mul_assoc]) }
    fun m => Subtype.ext ((hp m).1 m.2)

end Idempotent

/-! ### Self-injectivity from an associative perfect form -/

section Frobenius

variable {k : Type w} [Field k] {A : Type u} [Ring A] [Algebra k A]
  {B : A →ₗ[k] A →ₗ[k] k}

/-- **An algebra over a field carrying an associative bilinear form whose flip is bijective is
self-injective**, in Baer's form: every linear map from a left ideal to the regular module extends
to the algebra. -/
theorem _root_.Function.Bijective.moduleBaer_self (hB : Function.Bijective B.flip)
    (hassoc : ∀ x y z : A, B (x * y) z = B x (y * z)) : Module.Baer A A := by
  -- The form is multiplication followed by the trace `B 1`.
  have hone : ∀ x y : A, B x y = B 1 (x * y) := fun x y => by rw [← hassoc, one_mul]
  intro I f
  -- The trace turns `f` into a `k`-linear functional on `I`, which extends to all of `A`.
  obtain ⟨ψ, hψ⟩ : ∃ ψ : A →ₗ[k] k, ∀ (x : A) (hx : x ∈ I), ψ x = B 1 (f ⟨x, hx⟩) := by
    let e : I.restrictScalars k →ₗ[k] I :=
      { toFun := fun x => ⟨x, x.2⟩
        map_add' := fun _ _ => Subtype.ext rfl
        map_smul' := fun _ _ => Subtype.ext rfl }
    obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend
      ((B 1).comp ((f.restrictScalars k).comp e))
    exact ⟨ψ, fun x hx => congr($hψ ⟨x, hx⟩)⟩
  -- Bijectivity of the flip writes that functional as the pairing against a fixed element `a`.
  obtain ⟨a, ha⟩ := hB.surjective ψ
  have hax : ∀ x : A, B x a = ψ x := fun x => congr($ha x)
  refine ⟨LinearMap.mulRight A a, fun x hx => ?_⟩
  rw [LinearMap.mulRight_apply]
  -- The two candidates pair identically against every element, since `f` is `A`-linear.
  refine hB.injective (LinearMap.ext fun y => ?_)
  have hyx : y * x ∈ I := I.mul_mem_left y hx
  have hf : f ⟨y * x, hyx⟩ = y * f ⟨x, hx⟩ := by
    calc
      f ⟨y * x, hyx⟩ = f (y • (⟨x, hx⟩ : I)) := by
        exact congrArg f (Subtype.ext (smul_eq_mul y x).symm)
      _ = y • f ⟨x, hx⟩ := map_smul f y ⟨x, hx⟩
      _ = y * f ⟨x, hx⟩ := smul_eq_mul y _
  simp only [LinearMap.flip_apply]
  rw [← hassoc, hax, hψ _ hyx, hf, ← hone]

/-- **An algebra over a field carrying an associative bilinear form whose flip is bijective is
self-injective**: its regular left module is an injective module. -/
theorem _root_.Function.Bijective.moduleInjective_self (hB : Function.Bijective B.flip)
    (hassoc : ∀ x y z : A, B (x * y) z = B x (y * z)) : Module.Injective A A :=
  Module.Baer.injective (hB.moduleBaer_self hassoc)

end Frobenius

end TauCeti
