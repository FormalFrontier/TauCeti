/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.Prod

public section

/-!
# Products of Lie modules

Mathlib gives the product of two Lie *algebras* its Lie ring structure
(`Mathlib/Algebra/Lie/Prod.lean`) and the direct sum of a *family* of Lie modules its Lie module
structure (`Mathlib/Algebra/Lie/DirectSum.lean`), but not the binary product of two Lie modules over
a fixed Lie algebra. This file supplies it: for `L`-modules `M` and `N`, the componentwise bracket
makes `M × N` an `L`-module, and the four maps `fst`, `snd`, `inl`, `inr` are morphisms of
`L`-modules.

The binary product is what an argument comparing two Lie modules of *different* types needs: the
direct sum `⨁ i, M i` of a family forces all the summands into one universe, whereas `M × N` does
not. The first consumer is the uniqueness of the irreducible highest weight module of a given
weight, which compares two such modules by cutting out the graph of an isomorphism inside their
product.

## Main definitions

* `TauCeti.LieModuleHom.fst` and `TauCeti.LieModuleHom.snd`: the two projections.
* `TauCeti.LieModuleHom.inl` and `TauCeti.LieModuleHom.inr`: the two inclusions.
* `TauCeti.LieModuleHom.prod`: the pairing of two morphisms with the same domain.
* `TauCeti.LieModuleEquiv.prodComm`: swapping the factors is an equivalence.
-/

namespace TauCeti

universe u v w w₁

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N]

namespace Prod

/-- The componentwise bracket makes the product of two `L`-modules an `L`-module. -/
instance instLieRingModule : LieRingModule L (M × N) where
  bracket x p := (⁅x, p.1⁆, ⁅x, p.2⁆)
  add_lie x y p := Prod.ext (add_lie x y p.1) (add_lie x y p.2)
  lie_add x p q := Prod.ext (lie_add x p.1 q.1) (lie_add x p.2 q.2)
  leibniz_lie x y p := Prod.ext (leibniz_lie x y p.1) (leibniz_lie x y p.2)

@[simp]
theorem lie_apply (x : L) (p : M × N) : ⁅x, p⁆ = (⁅x, p.1⁆, ⁅x, p.2⁆) := rfl

instance instLieModule [LieAlgebra R L] [LieModule R L M] [LieModule R L N] :
    LieModule R L (M × N) where
  smul_lie t x p := Prod.ext (smul_lie t x p.1) (smul_lie t x p.2)
  lie_smul t x p := Prod.ext (lie_smul t x p.1) (lie_smul t x p.2)

end Prod

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
  { LinearMap.inl R M N with map_lie' := by simp [Prod.lie_apply] }

/-- The inclusion of the second factor into a product of Lie modules. -/
def inr : N →ₗ⁅R,L⁆ M × N :=
  { LinearMap.inr R M N with map_lie' := by simp [Prod.lie_apply] }

variable {R L M N}
variable {P : Type*} [AddCommGroup P] [Module R P] [LieRingModule L P]

/-- Pair two morphisms of Lie modules with the same domain. -/
def prod (f : P →ₗ⁅R,L⁆ M) (g : P →ₗ⁅R,L⁆ N) : P →ₗ⁅R,L⁆ M × N :=
  { LinearMap.prod f g with map_lie' := by simp [Prod.lie_apply] }

@[simp] theorem fst_apply (p : M × N) : fst R L M N p = p.1 := (rfl)

@[simp] theorem snd_apply (p : M × N) : snd R L M N p = p.2 := (rfl)

@[simp] theorem inl_apply (m : M) : inl R L M N m = (m, 0) := (rfl)

@[simp] theorem inr_apply (n : N) : inr R L M N n = (0, n) := (rfl)

@[simp] theorem prod_apply (f : P →ₗ⁅R,L⁆ M) (g : P →ₗ⁅R,L⁆ N) (p : P) :
    prod f g p = (f p, g p) := by
  change LinearMap.prod (f : P →ₗ[R] M) (g : P →ₗ[R] N) p = (f p, g p)
  rfl

@[simp]
theorem fst_prod (f : P →ₗ⁅R,L⁆ M) (g : P →ₗ⁅R,L⁆ N) :
    (fst R L M N).comp (prod f g) = f := by
  ext p
  simp

@[simp]
theorem snd_prod (f : P →ₗ⁅R,L⁆ M) (g : P →ₗ⁅R,L⁆ N) :
    (snd R L M N).comp (prod f g) = g := by
  ext p
  simp

end LieModuleHom

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L N]

namespace LieModuleEquiv

/-- Swapping the factors is an equivalence of product Lie modules. -/
def prodComm : (M × N) ≃ₗ⁅R,L⁆ (N × M) where
  __ := LinearEquiv.prodComm R M N
  map_lie' := by simp [Prod.lie_apply]

omit [LieAlgebra R L] [LieModule R L M] [LieModule R L N] in
@[simp]
theorem prodComm_apply (p : M × N) : prodComm (R := R) (L := L) p = p.swap :=
  LinearEquiv.prodComm_apply R M N p

omit [LieAlgebra R L] [LieModule R L M] [LieModule R L N] in
@[simp]
theorem coe_prodComm_apply (p : M × N) :
    ((prodComm (R := R) (L := L) : (M × N) ≃ₗ⁅R,L⁆ (N × M)) :
      M × N →ₗ⁅R,L⁆ N × M) p = p.swap :=
  prodComm_apply p

end LieModuleEquiv

end TauCeti
