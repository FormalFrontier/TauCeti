/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Submodule

public section

/-!
# General infrastructure for Lie modules

Mathlib gives the product of two Lie *algebras* its Lie ring structure
(`Mathlib/Algebra/Lie/Prod.lean`) and the product of a *family* of Lie modules its Lie module
structure (`Mathlib/Algebra/Lie/DirectSum.lean`), but not the binary product of two Lie modules over
a fixed Lie algebra. This file supplies it: for `L`-modules `M` and `N`, the componentwise bracket
makes `M × N` an `L`-module, and the four maps `fst`, `snd`, `inl`, `inr` are morphisms of
`L`-modules.

It also supplies `LieModuleEquiv.ofBijective`, the Lie-module analogue of
`LieEquiv.ofBijective`.

The binary product is what an argument comparing two Lie modules of *different* types needs: the
direct sum `⨁ i, M i` of a family forces all the summands into one universe, whereas `M × N` does
not. The first consumer is the uniqueness of the irreducible highest weight module of a given
weight, which compares two such modules by cutting out the graph of an isomorphism inside their
product.

## Main definitions

* `TauCeti.LieModuleEquiv.ofBijective`: a bijective morphism of Lie modules is an equivalence.
* `TauCeti.LieModuleHom.fst` and `TauCeti.LieModuleHom.snd`: the two projections.
* `TauCeti.LieModuleHom.inl` and `TauCeti.LieModuleHom.inr`: the two inclusions.
-/

namespace TauCeti

universe u v w w₁

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N]

namespace LieModuleEquiv

/-- A bijective morphism of Lie modules is an equivalence of Lie modules. This is the Lie module
analogue of `LieEquiv.ofBijective`. -/
noncomputable def ofBijective (f : M →ₗ⁅R,L⁆ N) (hf : Function.Bijective f) : M ≃ₗ⁅R,L⁆ N :=
  { LinearEquiv.ofBijective (f : M →ₗ[R] N) hf with
    toFun := f
    map_lie' := f.map_lie _ _ }

@[simp]
theorem ofBijective_apply (f : M →ₗ⁅R,L⁆ N) (hf : Function.Bijective f) (m : M) :
    ofBijective f hf m = f m :=
  (rfl)

end LieModuleEquiv

/-- The componentwise bracket makes the product of two `L`-modules an `L`-module. -/
instance instLieRingModuleProd : LieRingModule L (M × N) where
  bracket x p := (⁅x, p.1⁆, ⁅x, p.2⁆)
  add_lie x y p := Prod.ext (add_lie x y p.1) (add_lie x y p.2)
  lie_add x p q := Prod.ext (lie_add x p.1 q.1) (lie_add x p.2 q.2)
  leibniz_lie x y p := Prod.ext (leibniz_lie x y p.1) (leibniz_lie x y p.2)

@[simp]
theorem lie_prod_fst (x : L) (p : M × N) : (⁅x, p⁆ : M × N).1 = ⁅x, p.1⁆ := rfl

@[simp]
theorem lie_prod_snd (x : L) (p : M × N) : (⁅x, p⁆ : M × N).2 = ⁅x, p.2⁆ := rfl

@[simp]
theorem lie_prod_mk (x : L) (m : M) (n : N) : ⁅x, (m, n)⁆ = (⁅x, m⁆, ⁅x, n⁆) := rfl

instance instLieModuleProd [LieAlgebra R L] [LieModule R L M] [LieModule R L N] :
    LieModule R L (M × N) where
  smul_lie t x p := Prod.ext (smul_lie t x p.1) (smul_lie t x p.2)
  lie_smul t x p := Prod.ext (lie_smul t x p.1) (lie_smul t x p.2)

namespace LieModuleHom

variable (R L M N)

/-- The projection of a product of Lie modules onto its first factor. -/
def fst : M × N →ₗ⁅R,L⁆ M :=
  { LinearMap.fst R M N with map_lie' := rfl }

/-- The projection of a product of Lie modules onto its second factor. -/
def snd : M × N →ₗ⁅R,L⁆ N :=
  { LinearMap.snd R M N with map_lie' := rfl }

/-- The inclusion of the first factor into a product of Lie modules. -/
def inl : M →ₗ⁅R,L⁆ M × N :=
  { LinearMap.inl R M N with map_lie' := by simp [lie_prod_mk] }

/-- The inclusion of the second factor into a product of Lie modules. -/
def inr : N →ₗ⁅R,L⁆ M × N :=
  { LinearMap.inr R M N with map_lie' := by simp [lie_prod_mk] }

variable {R L M N}

@[simp] theorem fst_apply (p : M × N) : fst R L M N p = p.1 := (rfl)

@[simp] theorem snd_apply (p : M × N) : snd R L M N p = p.2 := (rfl)

@[simp] theorem inl_apply (m : M) : inl R L M N m = (m, 0) := (rfl)

@[simp] theorem inr_apply (n : N) : inr R L M N n = (0, n) := (rfl)

end LieModuleHom

end TauCeti
