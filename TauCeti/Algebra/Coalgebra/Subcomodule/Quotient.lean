/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Comap

/-!
# Quotients by subcomodules

This file equips the quotient of a right comodule by a subcomodule with the induced
right-comodule structure. The quotient coaction is the unique linear map whose composite
with the quotient map is `(N.mkQ ⊗ id) ∘ ρ`.

This is Layer 1 infrastructure for the reductive-groups roadmap target on comodules and the
finite-dimensional comodule category: after subcomodules, images, and kernels, quotient
comodules provide the basic cokernel-style construction used by later representation-category
bookkeeping.

## Main declarations

* `TauCeti.Subcomodule.quotientCoact`: the descended coaction on `M ⧸ N`.
* `TauCeti.Subcomodule.instComoduleQuotient`: the induced comodule structure.
* `TauCeti.Subcomodule.mkQ`: the quotient map as a comodule morphism.
* `TauCeti.Subcomodule.liftQ`: the comodule morphism induced from a morphism killing `N`.

## References

This is the standard quotient comodule construction; see Sweedler, *Hopf Algebras*,
Chapter 2. The formalization uses Mathlib's quotient-module API and tensor-product
functoriality.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommRing R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommGroup M] [Module R M] [Comodule R C M]

namespace Subcomodule

variable (N : Subcomodule R C M)

private theorem le_ker_tensorProduct_mkQ_comp_coact :
    N.toSubmodule ≤
      LinearMap.ker
        ((TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)).comp
          (Comodule.coact (R := R) (C := C) (M := M))) := by
  intro m hm
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  rcases N.coact_mem hm with ⟨t, ht⟩
  rw [← ht]
  letI : AddCommGroup C := Module.addCommMonoidToAddCommGroup R (M := C)
  -- The goal is written with `TensorProduct.map`, while Mathlib's quotient-tensor exactness
  -- lemma is stated for `rTensor`; this is only the wrapper conversion between those forms.
  change LinearMap.rTensor C N.carrier.mkQ
    (LinearMap.rTensor C N.carrier.subtype t) = 0
  rw [← LinearMap.mem_ker, rTensor_mkQ]
  exact
    (LinearMap.mem_range_self (LinearMap.rTensor C N.carrier.subtype) t)

/-- The coaction induced on the quotient by a subcomodule. -/
def quotientCoact : M ⧸ N.toSubmodule →ₗ[R] (M ⧸ N.toSubmodule) ⊗[R] C :=
  N.toSubmodule.liftQ
    ((TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)).comp
      (Comodule.coact (R := R) (C := C) (M := M)))
    (le_ker_tensorProduct_mkQ_comp_coact N)

/-- The quotient coaction applied to a quotient class. -/
@[simp]
theorem quotientCoact_mk (m : M) :
    N.quotientCoact (Submodule.Quotient.mk m) =
      TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
        (Comodule.coact (R := R) (C := C) (M := M) m) :=
  Submodule.liftQ_apply _ _ _

/-- The descended quotient coaction is characterized after precomposition with the quotient map. -/
theorem quotientCoact_comp_mkQ :
    N.quotientCoact.comp N.toSubmodule.mkQ =
      (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)).comp
        (Comodule.coact (R := R) (C := C) (M := M)) := by
  ext m
  exact N.quotientCoact_mk m

private theorem tensor_assoc_quotient_coact (m : M) :
    TensorProduct.assoc R (M ⧸ N.toSubmodule) C C
        (TensorProduct.map
          ((TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)).comp
            (Comodule.coact (R := R) (C := C) (M := M)))
          (LinearMap.id : C →ₗ[R] C)
          (Comodule.coact (R := R) (C := C) (M := M) m)) =
      Coalgebra.comul.lTensor (M ⧸ N.toSubmodule)
        (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
          (Comodule.coact (R := R) (C := C) (M := M) m)) := by
  calc
    TensorProduct.assoc R (M ⧸ N.toSubmodule) C C
        (TensorProduct.map
          ((TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)).comp
            (Comodule.coact (R := R) (C := C) (M := M)))
          (LinearMap.id : C →ₗ[R] C)
          (Comodule.coact (R := R) (C := C) (M := M) m)) =
        TensorProduct.assoc R (M ⧸ N.toSubmodule) C C
          (TensorProduct.map
            (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C))
            (LinearMap.id : C →ₗ[R] C)
            ((Comodule.coact (R := R) (C := C) (M := M)).rTensor C
              (Comodule.coact (R := R) (C := C) (M := M) m))) := by
          rw [LinearMap.rTensor_def, TensorProduct.map_map]
          simp
    _ =
        TensorProduct.map N.toSubmodule.mkQ
          (TensorProduct.map (LinearMap.id : C →ₗ[R] C) (LinearMap.id : C →ₗ[R] C))
          (TensorProduct.assoc R M C C
            ((Comodule.coact (R := R) (C := C) (M := M)).rTensor C
              (Comodule.coact (R := R) (C := C) (M := M) m))) := by
          exact
            (TensorProduct.map_map_assoc N.toSubmodule.mkQ LinearMap.id LinearMap.id _).symm
    _ =
        TensorProduct.map N.toSubmodule.mkQ
          (LinearMap.id : C ⊗[R] C →ₗ[R] C ⊗[R] C)
          (Coalgebra.comul.lTensor M
            (Comodule.coact (R := R) (C := C) (M := M) m)) := by
          rw [Comodule.coassoc_apply]
          simp
    _ =
        Coalgebra.comul.lTensor (M ⧸ N.toSubmodule)
          (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
            (Comodule.coact (R := R) (C := C) (M := M) m)) := by
          rw [LinearMap.lTensor_map]
          simp

/-- The quotient of a right comodule by a subcomodule inherits a right-comodule structure. -/
instance instComoduleQuotient : Comodule R C (M ⧸ N.toSubmodule) where
  coact := N.quotientCoact
  coassoc := by
    apply Submodule.linearMap_qext
    ext m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, quotientCoact_mk, LinearMap.rTensor_map]
    rw [N.quotientCoact_comp_mkQ]
    calc
      TensorProduct.assoc R (M ⧸ N.toSubmodule) C C
          (TensorProduct.map
            ((TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)).comp
              (Comodule.coact (R := R) (C := C) (M := M)))
            (LinearMap.id : C →ₗ[R] C)
            (Comodule.coact (R := R) (C := C) (M := M) m)) =
          Coalgebra.comul.lTensor (M ⧸ N.toSubmodule)
            (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
              (Comodule.coact (R := R) (C := C) (M := M) m)) := by
            exact N.tensor_assoc_quotient_coact m
      _ = (LinearMap.lTensor (M ⧸ N.toSubmodule) Coalgebra.comul ∘ₗ N.quotientCoact)
            (Submodule.Quotient.mk m) := by
            rw [LinearMap.comp_apply, quotientCoact_mk]
  lTensor_counit_comp_coact := by
    apply Submodule.linearMap_qext
    ext m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, quotientCoact_mk]
    calc
      Coalgebra.counit.lTensor (M ⧸ N.toSubmodule)
          (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
            (Comodule.coact (R := R) (C := C) (M := M) m)) =
        TensorProduct.map N.toSubmodule.mkQ
          (Coalgebra.counit.comp (LinearMap.id : C →ₗ[R] C))
          (Comodule.coact (R := R) (C := C) (M := M) m) := by
          exact
            LinearMap.lTensor_map (R := R) M Coalgebra.counit N.toSubmodule.mkQ
              (LinearMap.id : C →ₗ[R] C)
              (Comodule.coact (R := R) (C := C) (M := M) m)
      _ =
        TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : R →ₗ[R] R)
          (Coalgebra.counit.lTensor M
            (Comodule.coact (R := R) (C := C) (M := M) m)) := by
          rw [LinearMap.lTensor_def, TensorProduct.map_map]
          simp
      _ = ((TensorProduct.mk R (M ⧸ N.toSubmodule) R).flip 1)
            (Submodule.Quotient.mk m) := by
          rw [Comodule.lTensor_counit_coact]
          simp only [LinearMap.flip_apply, TensorProduct.mk_apply, TensorProduct.map_tmul,
            LinearMap.id_coe, id_eq, Submodule.mkQ_apply]

/-- The coaction on the quotient comodule is `Subcomodule.quotientCoact`. -/
@[simp]
theorem quotient_coact :
    Comodule.coact (R := R) (C := C) (M := M ⧸ N.toSubmodule) = N.quotientCoact :=
  rfl

/-- The quotient map by a subcomodule as a comodule morphism. -/
@[expose] def mkQ : Comodule.Hom R C M (M ⧸ N.toSubmodule) where
  toLinearMap := N.toSubmodule.mkQ
  map_coact := by
    ext m
    simp

/-- The underlying linear map of the quotient comodule morphism is the quotient map. -/
@[simp]
theorem mkQ_toLinearMap : N.mkQ.toLinearMap = N.toSubmodule.mkQ :=
  rfl

/-- The quotient comodule morphism sends a vector to its quotient class. -/
@[simp]
theorem mkQ_apply (m : M) : N.mkQ m = Submodule.Quotient.mk m :=
  rfl

/-- The quotient comodule morphism sends exactly the subcomodule to zero. -/
theorem mkQ_eq_zero_iff (m : M) : N.mkQ m = 0 ↔ m ∈ N := by
  rw [mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Subcomodule.mem_toSubmodule

/-- The quotient comodule morphism is surjective. -/
theorem mkQ_surjective : Function.Surjective N.mkQ := by
  intro q
  obtain ⟨m, hm⟩ := N.toSubmodule.mkQ_surjective q
  exact ⟨m, by rw [N.mkQ_apply]; exact hm⟩

variable {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]

/-- A comodule morphism out of `M` that vanishes on `N` descends to the quotient by `N`. -/
def liftQ (f : Comodule.Hom R C M P) (hf : N.toSubmodule ≤ LinearMap.ker f.toLinearMap) :
    Comodule.Hom R C (M ⧸ N.toSubmodule) P :=
  -- `Submodule.liftQ` and the tensor rewrites need an additive group on the codomain, which we
  -- derive from its `R`-module structure while the exported API stays at the monoid level.
  letI : AddCommGroup P := Module.addCommMonoidToAddCommGroup R (M := P)
  { toLinearMap := N.toSubmodule.liftQ f.toLinearMap hf
    map_coact := by
      apply Submodule.linearMap_qext
      ext m
      rw [LinearMap.comp_apply, LinearMap.comp_apply, quotient_coact]
      rw [Submodule.mkQ_apply]
      rw [quotientCoact_mk]
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      rw [Submodule.mkQ_apply]
      rw [Submodule.liftQ_apply]
      calc
        TensorProduct.map (N.toSubmodule.liftQ f.toLinearMap hf)
            (LinearMap.id : C →ₗ[R] C)
            (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
              (Comodule.coact (R := R) (C := C) (M := M) m)) =
          TensorProduct.map f.toLinearMap (LinearMap.id : C →ₗ[R] C)
            (Comodule.coact (R := R) (C := C) (M := M) m) := by
            simp [TensorProduct.map_map]
        _ = Comodule.coact (R := R) (C := C) (M := P) (f m) := by
            exact Comodule.Hom.map_coact_apply f m }

/-- The descended quotient morphism applied to a quotient class. -/
@[simp]
theorem liftQ_apply (f : Comodule.Hom R C M P)
    (hf : N.toSubmodule ≤ LinearMap.ker f.toLinearMap) (m : M) :
    N.liftQ f hf (Submodule.Quotient.mk m) = f m :=
  letI : AddCommGroup P := Module.addCommMonoidToAddCommGroup R (M := P)
  Submodule.liftQ_apply _ _ _

/-- The underlying linear map of the descended quotient morphism is the quotient-module lift. -/
@[simp]
theorem liftQ_toLinearMap (f : Comodule.Hom R C M P)
    (hf : N.toSubmodule ≤ LinearMap.ker f.toLinearMap) : (N.liftQ f hf).toLinearMap =
      letI : AddCommGroup P := Module.addCommMonoidToAddCommGroup R (M := P)
      N.toSubmodule.liftQ f.toLinearMap hf := by
  letI : AddCommGroup P := Module.addCommMonoidToAddCommGroup R (M := P)
  apply Submodule.linearMap_qext
  ext m
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
  -- The left side is the bundled comodule morphism's coercion, while the right side is the
  -- quotient-module lift used as its underlying linear map; extensionality has reduced the goal
  -- to this definitional conversion on quotient representatives.
  change (N.liftQ f hf) (Submodule.Quotient.mk m) =
    (N.toSubmodule.liftQ f.toLinearMap hf) (Submodule.Quotient.mk m)
  rw [liftQ_apply, Submodule.liftQ_apply]
  rfl

/-- Precomposing the descended quotient morphism with the quotient map recovers the original
morphism. -/
@[simp]
theorem liftQ_mkQ (f : Comodule.Hom R C M P) (hf : N.toSubmodule ≤ LinearMap.ker f.toLinearMap) :
    (N.liftQ f hf).comp N.mkQ = f := by
  ext m
  simp

/-- Two morphisms out of a quotient are equal if they agree after precomposition with the
quotient map. -/
theorem hom_ext {f g : Comodule.Hom R C (M ⧸ N.toSubmodule) P}
    (h : f.comp N.mkQ = g.comp N.mkQ) : f = g := by
  ext q
  rcases N.mkQ_surjective q with ⟨m, rfl⟩
  exact congr_fun (congrArg DFunLike.coe h) m

/-- Uniqueness of the morphism descended to a quotient. -/
theorem liftQ_unique (f : Comodule.Hom R C M P) (hf : N.toSubmodule ≤ LinearMap.ker f.toLinearMap)
    (g : Comodule.Hom R C (M ⧸ N.toSubmodule) P) (hg : g.comp N.mkQ = f) :
    g = N.liftQ f hf := by
  apply N.hom_ext
  rw [hg, liftQ_mkQ]

variable [Module.Flat R C]

/-- The kernel of the quotient comodule morphism is the subcomodule being quotiented. -/
@[simp]
theorem ker_mkQ : Comodule.Hom.ker (R := R) (C := C) N.mkQ = N := by
  ext m
  rw [Comodule.Hom.mem_ker, mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Subcomodule.mem_toSubmodule

end Subcomodule

end TauCeti
