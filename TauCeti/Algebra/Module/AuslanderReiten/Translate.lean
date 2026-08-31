/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The Auslander--Reiten translate

For an algebra `A` over a commutative ring `k`, the **duality** `D = Hom_k(-, k)` turns a right
`A`-module into a left `A`-module: a scalar `a` acts on a functional `φ` by precomposition with
multiplication by `a`, `(a • φ) x = φ (x * a)`.  This file records that action as the ring
homomorphism `TauCeti.dualRightAction` and uses it to define the **Auslander--Reiten translate**

`τ M = D (Tr M)`

of a module `M` presented by a minimal projective presentation `P₁ → P₀ → M → 0`, the `k`-dual of
the Auslander--Reiten transpose `TauCeti.AuslanderReitenTranspose` of that presentation.  The
transpose is a right `A`-module, so the translate is a left `A`-module again, as `M` was.

The translate is attached to a *presentation*, not directly to `M`: like the transpose it is
well defined only because a minimal projective presentation is unique up to isomorphism of the whole
diagram.  `TauCeti.IsMinimalProjectivePresentation.nonempty_linearEquiv_arTranslate` is that
statement, and it is what licenses the notation `τ M`.

## Main definitions

* `TauCeti.dualRightAction`: the left action of `A` on the `k`-dual of a right `A`-module, as a ring
  homomorphism into the `k`-linear endomorphisms of the dual.
* `TauCeti.arTranslate`: the Auslander--Reiten translate `D (Tr)` of a projective presentation,
  carrying the resulting `A`-module structure.
* `TauCeti.arTranslate.linearEquiv`: the transport of the translate along an isomorphism of
  transposes, contravariant by `TauCeti.arTranslate.linearEquiv_trans`.

## Main results

* `TauCeti.IsMinimalProjectivePresentation.nonempty_linearEquiv_arTranslate`: the translate is
  independent, up to `A`-linear equivalence, of the chosen minimal projective presentation.
* `TauCeti.IsMinimalProjectivePresentation.subsingleton_arTranslate_of_projective`: the translate of
  a projective module vanishes.

## Implementation notes

The `A`-action on the dual is *not* installed as an instance on `Module.Dual k N` for a general
right `A`-module `N`: the underlying type of `Module.Dual k N` is a type of linear maps, which
already carries the codomain-scaling `Module` instances of `Mathlib.Algebra.Module.LinearMap.Defs`,
and a second `Module` structure matching every dual would make instance search on those types
depend on an undetermined right-module structure.  Instead `TauCeti.dualRightAction` is a plain ring
homomorphism, and the single `Module` instance built from it is the one on the translate, whose
underlying transpose pins the right-module structure being dualized.

The translate is a reducible abbreviation of the dual rather than a fresh type, so that its
elements are literally `k`-linear functionals on the transpose and the whole `Module.Dual` API
applies to it unchanged: extensionality, the dimension count `Subspace.dual_finrank_eq` and the
finite-dimensionality of a dual are inherited verbatim and are not restated here.  Only the
`A`-action is new, and it is described by the single lemma `TauCeti.arTranslate.smul_apply`.

## References

This is sublayer 6D, "the AR translate `τ = D Tr` and AR duality", of Layer 6 of
[the quiver-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md),
which names it as the composite of the transpose of sublayer 6C with the duality
`D = Hom_k(-, k)`, "well-defined only up to projectives, through minimal presentations and duality
on finite-dimensional modules".

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section IV.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Cambridge University Press (2006), Section IV.2.
-/

public section

namespace TauCeti

universe u v v' w w' x

section Duality

variable (k : Type u) (N : Type w) {A : Type v} [CommSemiring k] [Semiring A] [AddCommMonoid N]
  [Module k N] [Module Aᵐᵒᵖ N] [SMulCommClass Aᵐᵒᵖ k N]

/-- The **duality** `D = Hom_k(-, k)` turns a right `A`-module `N` into a left `A`-module: the
scalar `a` sends a functional `φ` to `x ↦ φ (x * a)`.  This records that action as a ring
homomorphism from `A` to the `k`-linear endomorphisms of `Module.Dual k N`.

Precomposition reverses composition, which is exactly what makes a *right* action on `N` into a
*left* action on its dual; the hypothesis `SMulCommClass Aᵐᵒᵖ k N` is what makes multiplication by
`a` a `k`-linear endomorphism of `N` in the first place. -/
def dualRightAction : A →+* Module.End k (Module.Dual k N) where
  toFun a := (Module.toModuleEnd k N (MulOpposite.op a)).dualMap
  map_one' := by ext φ x; simp
  map_mul' a b := by ext φ x; simp [mul_smul]
  map_zero' := by ext φ x; simp
  map_add' a b := by ext φ x; simp [add_smul]

@[simp]
theorem dualRightAction_apply_apply (a : A) (φ : Module.Dual k N) (x : N) :
    dualRightAction k N a φ x = φ (MulOpposite.op a • x) :=
  (rfl)

end Duality

variable {A : Type u} [Ring A] {k : Type x} [CommSemiring k] [Algebra k A]

variable {P₀ : Type v} {P₁ : Type w} [AddCommMonoid P₀] [Module A P₀]
  [AddCommMonoid P₁] [Module A P₁]

/-- The **Auslander--Reiten translate** `τ = D Tr` of a projective presentation whose first map is
`p₁ : P₁ → P₀`: the `k`-dual of its Auslander--Reiten transpose.  The transpose is a right
`A`-module, so `TauCeti.dualRightAction` makes the translate a left `A`-module.

As with the transpose, minimality is not needed to form it; it is used by
`TauCeti.IsMinimalProjectivePresentation.nonempty_linearEquiv_arTranslate` to show that the result
is independent, up to equivalence, of the chosen presentation of a module. -/
abbrev arTranslate (k : Type x) [CommSemiring k] [Algebra k A] (p₁ : P₁ →ₗ[A] P₀) : Type _ :=
  Module.Dual k (AuslanderReitenTranspose p₁)

namespace arTranslate

variable {p₁ : P₁ →ₗ[A] P₀}

instance : Module A (arTranslate k p₁) :=
  Module.compHom (Module.Dual k (AuslanderReitenTranspose p₁))
    (dualRightAction k (AuslanderReitenTranspose p₁))

/-- The `A`-action on the translate is precomposition with the right action on the transpose. -/
@[simp]
theorem smul_apply (a : A) (φ : arTranslate k p₁)
    (x : AuslanderReitenTranspose p₁) :
    (a • φ) x = φ (MulOpposite.op a • x) :=
  (rfl)

/-- Scalars from `k` act on the translate through `A`, so the two actions on it are the layered
ones: the `k`-action is the restriction of the `A`-action along the algebra map. -/
instance : IsScalarTower k A (arTranslate k p₁) where
  smul_assoc c a φ := by
    ext x
    have hc : MulOpposite.op ((algebraMap k A) c) • x = c • x := by
      rw [← MulOpposite.algebraMap_apply, algebraMap_smul]
    rw [LinearMap.smul_apply, smul_apply, smul_apply, Algebra.smul_def,
      MulOpposite.op_mul, mul_smul, hc, smul_comm, map_smul, smul_eq_mul]

variable {Q₀ : Type v'} {Q₁ : Type w'} [AddCommMonoid Q₀] [Module A Q₀]
  [AddCommMonoid Q₁] [Module A Q₁]
variable {q₁ : Q₁ →ₗ[A] Q₀}

/-- An equivalence of transposes dualizes to an equivalence of translates, contravariantly: an
`Aᵐᵒᵖ`-linear equivalence `Tr q₁ ≃ Tr p₁` sends a functional on `Tr p₁` to its composite with that
equivalence.

The result is `A`-linear precisely because the equivalence is `Aᵐᵒᵖ`-linear: the two ways of moving
a scalar past it are the two sides of `LinearEquiv.map_smul`. -/
def linearEquiv (e : AuslanderReitenTranspose q₁ ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p₁) :
    arTranslate k p₁ ≃ₗ[A] arTranslate k q₁ where
  toFun φ := φ ∘ₗ (e.restrictScalars k : _ →ₗ[k] _)
  map_add' _ _ := rfl
  map_smul' a φ := by
    ext x
    simp
  invFun ψ := ψ ∘ₗ (e.symm.restrictScalars k : _ →ₗ[k] _)
  left_inv φ := by
    ext x
    simp
  right_inv ψ := by
    ext x
    simp

@[simp]
theorem linearEquiv_apply (e : AuslanderReitenTranspose q₁ ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p₁)
    (φ : arTranslate k p₁) (x : AuslanderReitenTranspose q₁) :
    linearEquiv (k := k) e φ x = φ (e x) :=
  (rfl)

@[simp]
theorem linearEquiv_symm (e : AuslanderReitenTranspose q₁ ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p₁) :
    (linearEquiv (k := k) e).symm = linearEquiv e.symm := by
  refine LinearEquiv.ext fun ψ => ?_
  ext x
  rfl

/-- Transport along the identity equivalence of transposes is the identity. -/
@[simp]
theorem linearEquiv_refl :
    linearEquiv (k := k) (LinearEquiv.refl Aᵐᵒᵖ (AuslanderReitenTranspose p₁)) =
      LinearEquiv.refl A (arTranslate k p₁) := by
  refine LinearEquiv.ext fun φ => ?_
  ext x
  simp

/-- Dualizing is **contravariant**: transporting along a composite of equivalences of transposes is
the composite of the transports in the reverse order. -/
@[simp]
theorem linearEquiv_trans {R₀ : Type*} {R₁ : Type*} [AddCommMonoid R₀] [Module A R₀]
    [AddCommMonoid R₁] [Module A R₁] {r₁ : R₁ →ₗ[A] R₀}
    (f : AuslanderReitenTranspose r₁ ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose q₁)
    (e : AuslanderReitenTranspose q₁ ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose p₁) :
    linearEquiv (k := k) (f.trans e) = (linearEquiv (k := k) e).trans (linearEquiv f) := by
  refine LinearEquiv.ext fun φ => ?_
  ext x
  simp

end arTranslate

namespace IsMinimalProjectivePresentation

variable {M : Type*} [AddCommGroup M] [Module A M]
variable {P₀ : Type v} [AddCommGroup P₀] [Module A P₀]
variable {P₁ : Type w} [AddCommGroup P₁] [Module A P₁]
variable {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}

/-- The Auslander--Reiten translate of a projective module vanishes: its transpose already does,
and the dual of a subsingleton is a subsingleton. -/
theorem subsingleton_arTranslate_of_projective [Module.Projective A M]
    (h : IsMinimalProjectivePresentation p₁ p₀) : Subsingleton (arTranslate k p₁) := by
  have hs : Subsingleton (AuslanderReitenTranspose p₁) :=
    h.subsingleton_auslanderReitenTranspose_of_projective
  refine ⟨fun φ ψ => ?_⟩
  ext x
  rw [hs.allEq x 0, map_zero, map_zero]

variable {Q₀ : Type v'} {Q₁ : Type w'} [AddCommGroup Q₀] [Module A Q₀]
  [AddCommGroup Q₁] [Module A Q₁]
variable {q₁ : Q₁ →ₗ[A] Q₀} {q₀ : Q₀ →ₗ[A] M}

/-- **The Auslander--Reiten translate is well defined**: it is independent, up to `A`-linear
equivalence, of the chosen minimal projective presentation of a module.  This is the statement that
licenses writing `τ M` for a module `M`. -/
theorem nonempty_linearEquiv_arTranslate (h : IsMinimalProjectivePresentation p₁ p₀)
    (h' : IsMinimalProjectivePresentation q₁ q₀) :
    Nonempty (arTranslate k p₁ ≃ₗ[A] arTranslate k q₁) :=
  (h'.nonempty_linearEquiv_auslanderReitenTranspose h).map arTranslate.linearEquiv

end IsMinimalProjectivePresentation

end TauCeti
