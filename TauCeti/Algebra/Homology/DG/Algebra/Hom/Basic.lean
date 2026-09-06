/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import TauCeti.Algebra.Homology.DG.Algebra.Defs

/-!
# Morphisms of differential graded algebras

A morphism of differential graded algebras is a graded algebra homomorphism that commutes with the
differentials.  This file bundles those maps as `TauCeti.DGAlgHom` and supplies their
extensionality, identity, and composition API; the induced maps on cycles and cohomology are built
on top of it in `TauCeti.Algebra.Homology.DG.Algebra.Hom.Cohomology`.

## Main definitions

* `TauCeti.DGAlgHom`: a graded algebra homomorphism commuting with the differentials.
* `TauCeti.DGAlgHom.id` and `TauCeti.DGAlgHom.comp`: the identity morphism and the composition of
  two morphisms of differential graded algebras.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}

/-- A morphism of differential graded algebras: a degree-zero graded algebra homomorphism that
commutes with the differentials. -/
structure DGAlgHom (hA : IsDGAlgebra 𝒜 dA) (hB : IsDGAlgebra ℬ dB)
    extends 𝒜 →ₐᵍ[R] ℬ where
  /-- A DG algebra morphism commutes with the differentials. -/
  map_d' (a : A) : dB (toGradedAlgHom a) = toGradedAlgHom (dA a)

namespace DGAlgHom

variable {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {hC : IsDGAlgebra 𝒞 dC}

/-- Two DG algebra morphisms are equal if their underlying graded algebra homomorphisms are equal.
-/
theorem toGradedAlgHom_injective :
    Function.Injective (toGradedAlgHom : DGAlgHom hA hB → 𝒜 →ₐᵍ[R] ℬ) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  cases h
  rfl

instance : FunLike (DGAlgHom hA hB) A B where
  coe f := f.toGradedAlgHom
  coe_injective _f _g h := toGradedAlgHom_injective <| GradedAlgHom.ext fun a => congrFun h a

instance : GradedFunLike (DGAlgHom hA hB) 𝒜 ℬ where
  map_mem f := f.toGradedAlgHom.map_mem

instance : AlgHomClass (DGAlgHom hA hB) R A B where
  map_add f := f.toGradedAlgHom.map_add
  map_zero f := f.toGradedAlgHom.map_zero
  map_mul f := f.toGradedAlgHom.map_mul
  map_one f := f.toGradedAlgHom.map_one
  commutes f := f.toGradedAlgHom.commutes

instance : CoeOut (DGAlgHom hA hB) (𝒜 →ₐᵍ[R] ℬ) := ⟨toGradedAlgHom⟩

@[simp]
theorem coe_toGradedAlgHom (f : DGAlgHom hA hB) : ⇑f.toGradedAlgHom = f := rfl

@[simp]
theorem coe_mk (f : 𝒜 →ₐᵍ[R] ℬ) (hf) : ⇑(DGAlgHom.mk f hf : DGAlgHom hA hB) = f := rfl

/-- Two DG algebra morphisms are equal if they agree on every element. -/
@[ext]
theorem ext {f g : DGAlgHom hA hB} (h : ∀ a, f a = g a) : f = g :=
  toGradedAlgHom_injective <| GradedAlgHom.ext h

/-- A DG algebra morphism commutes with the differentials. -/
@[simp]
theorem map_d (f : DGAlgHom hA hB) (a : A) : dB (f a) = f (dA a) :=
  f.map_d' a

/-- The identity morphism of a differential graded algebra. -/
protected def id (hA : IsDGAlgebra 𝒜 dA) : DGAlgHom hA hA where
  toGradedAlgHom := GradedAlgHom.id R 𝒜
  map_d' _ := rfl

@[simp]
theorem id_toGradedAlgHom (hA : IsDGAlgebra 𝒜 dA) :
    (DGAlgHom.id hA).toGradedAlgHom = GradedAlgHom.id R 𝒜 := (rfl)

@[simp]
theorem coe_id (hA : IsDGAlgebra 𝒜 dA) : ⇑(DGAlgHom.id hA) = _root_.id := (rfl)

@[simp]
theorem id_apply (hA : IsDGAlgebra 𝒜 dA) (a : A) : DGAlgHom.id hA a = a :=
  congrFun (coe_id hA) a

/-- Composition of morphisms of differential graded algebras. -/
def comp (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) : DGAlgHom hA hC where
  toGradedAlgHom := g.toGradedAlgHom.comp f.toGradedAlgHom
  map_d' a := by
    rw [GradedAlgHom.comp_apply, GradedAlgHom.comp_apply, g.map_d', f.map_d']

@[simp]
theorem comp_toGradedAlgHom (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) :
    (g.comp f).toGradedAlgHom = g.toGradedAlgHom.comp f.toGradedAlgHom := (rfl)

@[simp]
theorem coe_comp (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) : ⇑(g.comp f) = g ∘ f := (rfl)

@[simp]
theorem comp_apply (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) (a : A) :
    g.comp f a = g (f a) :=
  congrFun (coe_comp g f) a

@[simp]
theorem comp_id (f : DGAlgHom hA hB) : f.comp (DGAlgHom.id hA) = f := by
  ext a
  rw [comp_apply, id_apply]

@[simp]
theorem id_comp (f : DGAlgHom hA hB) : (DGAlgHom.id hB).comp f = f := by
  ext a
  rw [comp_apply, id_apply]

/-- Composition of morphisms of differential graded algebras is associative. -/
@[simp]
theorem comp_assoc {D : Type*} [Ring D] [Algebra R D]
    {𝒟 : ℤ → Submodule R D} [GradedAlgebra 𝒟] {dD : D →ₗ[R] D}
    {hD : IsDGAlgebra 𝒟 dD} (k : DGAlgHom hC hD) (g : DGAlgHom hB hC)
    (f : DGAlgHom hA hB) : (k.comp g).comp f = k.comp (g.comp f) := by
  ext a
  simp only [comp_apply]

end DGAlgHom

end TauCeti
