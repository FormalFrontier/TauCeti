/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: the tensor product algebra `B ⊗[K] Aᵐᵒᵖ` and `AlgHom` occur in the statements below, and
-- `AlgHom.mulLeftRight` and `Algebra.TensorProduct.map`, from which the action is built, occur in
-- the body of the public `toEnd`.
public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# An algebra as a module over `B ⊗[K] Aᵐᵒᵖ`

A `K`-algebra homomorphism `f : B →ₐ[K] A` turns `A` into a `B`-`A`-bimodule: `B` acts on the left
through `f` and `A` on the right by multiplication. Packaged as a left module over
`R = B ⊗[K] Aᵐᵒᵖ`, with `b ⊗ₜ op a` acting by `x ↦ f b * x * a`, this is `TauCeti.Bimodule f`.

Two theorems rest on this one construction, and neither can use `A` itself as the carrier:

* the **Skolem-Noether theorem** (`TauCeti/Algebra/CentralSimple/SkolemNoether.lean`) compares the
  structures coming from *two* homomorphisms `f` and `g` on the same underlying `K`-vector space, so
  the two module structures must coexist;
* the **centralizer theorem** (`TauCeti/Algebra/CentralSimple/Centralizer.lean`) identifies the
  endomorphism ring of `Bimodule f` with the centralizer of the image of `f`, and needs `A` to carry
  no competing `R`-module structure while it does so.

Indexing a type synonym by the homomorphism answers both: the structures are separated by `f`, and
none of them is an instance on `A`. Mathlib takes the same route for `A ⊗[R] Aᵐᵒᵖ` acting on `A`
in `Mathlib/Algebra/Azumaya/Defs.lean`, where `instModuleTensorProductMop` is deliberately not an
instance.

## Main definitions

* `TauCeti.Bimodule f`: the type synonym, with its `B ⊗[K] Aᵐᵒᵖ`-module structure.
* `TauCeti.Bimodule.of f : A ≃ₗ[K] Bimodule f`: the identification with `A` as a `K`-module, the
  only route between the two types that the interface offers.
* `TauCeti.Bimodule.toEnd f`: the action, as a `K`-algebra homomorphism into `Module.End K A`. It
  is Mathlib's `AlgHom.mulLeftRight` restricted along `f` on the left factor, so for
  `f = AlgHom.id K A` it is `AlgHom.mulLeftRight K A` itself.

## Implementation notes

`TauCeti.Bimodule.smul_of` and `TauCeti.Bimodule.symm_smul` are the working interface: they compute
the action of a pure tensor on either side of `of`, and every consumer is expected to reach the
module structure through them and through `TauCeti.Bimodule.smul_def` rather than by unfolding the
synonym. Only `Bimodule` is `@[expose]`d, and it has to be: a type synonym cannot carry transported
instances unless its body is visible. Everything else, `of` and `toEnd` included, stays opaque, so
that no consumer can depend on their bodies; `smul_def` is proved by `(rfl)` rather than by `rfl`,
which is what keeps it from being tagged `@[defeq]` — an exported `@[defeq]` theorem would demand
that the body of `of` be exposed too.

Nothing in the construction uses negation, so `A` and `B` are asked only to be semirings; the
additive group structure is inherited conditionally, when `A` happens to be a ring.

## References

This is the shared construction beneath the Layer 5 targets `skolemNoether` and
`finrank_mul_finrank_centralizer` of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 12.
-/

public section

namespace TauCeti

open scoped TensorProduct

variable {K A B : Type*} [CommSemiring K] [Semiring A] [Algebra K A] [Semiring B] [Algebra K B]

/-- `A` regarded as a left module over `B ⊗[K] Aᵐᵒᵖ` through an algebra homomorphism
`f : B →ₐ[K] A`: the element `b ⊗ₜ op a` acts by `x ↦ f b * x * a`.

Equivalently this is the `B`-`A`-bimodule `A` obtained by restricting the left action along `f`,
packaged as a left module over `B ⊗[K] Aᵐᵒᵖ` in the usual way. It is a type synonym for `A`
precisely so that the structures coming from two different homomorphisms can be compared, and so
that `A` itself is left without a `B ⊗[K] Aᵐᵒᵖ`-action. -/
@[expose] def Bimodule (_f : B →ₐ[K] A) : Type _ := A

namespace Bimodule

variable (f : B →ₐ[K] A)

instance : AddCommMonoid (Bimodule f) := inferInstanceAs (AddCommMonoid A)

-- Conditional, so that the endomorphism ring of `Bimodule f` is a ring and not merely a semiring
-- when `A` is one; nothing in the construction itself needs the negation.
instance {A : Type*} [Ring A] [Algebra K A] (f : B →ₐ[K] A) : AddCommGroup (Bimodule f) :=
  inferInstanceAs (AddCommGroup A)

instance : Module K (Bimodule f) := inferInstanceAs (Module K A)

instance [Nontrivial A] : Nontrivial (Bimodule f) := inferInstanceAs (Nontrivial A)

/-- `Bimodule f` is `A` again as a `K`-module: only the `B ⊗[K] Aᵐᵒᵖ`-action is new. -/
def of : A ≃ₗ[K] Bimodule f := LinearEquiv.refl K A

/-- The action of `B ⊗[K] Aᵐᵒᵖ` on `A` defining `Bimodule f`, as an algebra homomorphism into
`Module.End K A`. It is Mathlib's `AlgHom.mulLeftRight` restricted along `f` on the left factor, so
for `f = AlgHom.id K A` it is `AlgHom.mulLeftRight K A` itself. -/
noncomputable def toEnd : B ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A :=
  (AlgHom.mulLeftRight K A).comp (Algebra.TensorProduct.map f (AlgHom.id K Aᵐᵒᵖ))

/-- A pure tensor `b ⊗ₜ op a` acts on `x : A` through `toEnd f` by `x ↦ f b * x * a`. -/
@[simp]
theorem toEnd_tmul_apply (b : B) (a : Aᵐᵒᵖ) (x : A) :
    toEnd f (b ⊗ₜ a) x = f b * x * a.unop := by
  simp [toEnd]

noncomputable instance : Module (B ⊗[K] Aᵐᵒᵖ) (Bimodule f) :=
  Module.compHom (M := A) (toEnd f).toRingHom

/-- A scalar `r : B ⊗[K] Aᵐᵒᵖ` acts on `Bimodule f` through `toEnd f`. This is the defining equation
of the module structure, and the single place it is unfolded: everything else below rewrites with it
instead of reasoning up to definitional equality. -/
theorem smul_def (r : B ⊗[K] Aᵐᵒᵖ) (x : A) : r • of f x = of f (toEnd f r x) := (rfl)

instance : IsScalarTower K (B ⊗[K] Aᵐᵒᵖ) (Bimodule f) where
  smul_assoc c r x := by
    rw [← (of f).apply_symm_apply x, smul_def, smul_def, map_smul (toEnd f),
      LinearMap.smul_apply, map_smul (of f)]

instance [Module.Finite K A] : Module.Finite K (Bimodule f) :=
  inferInstanceAs (Module.Finite K A)

/-- A pure tensor `b ⊗ₜ op a` acts on `Bimodule f` by `x ↦ f b * x * a`: the left factor acts on the
left through `f`, the right factor on the right by multiplication. -/
@[simp]
theorem smul_of (b : B) (a : Aᵐᵒᵖ) (x : A) :
    (b ⊗ₜ a : B ⊗[K] Aᵐᵒᵖ) • of f x = of f (f b * x * a.unop) :=
  toEnd_tmul_apply f b a x

/-- `smul_of` read back through `of`: the action of a pure tensor `b ⊗ₜ op a`, transported to `A`,
is `x ↦ f b * x * a`. -/
@[simp]
theorem symm_smul (b : B) (a : Aᵐᵒᵖ) (y : Bimodule f) :
    (of f).symm ((b ⊗ₜ a : B ⊗[K] Aᵐᵒᵖ) • y) = f b * (of f).symm y * a.unop :=
  toEnd_tmul_apply f b a ((of f).symm y)

end Bimodule

end TauCeti
