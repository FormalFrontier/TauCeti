/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.EqLocus
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# The fixed subcomodule

Let `C` be a coalgebra with a distinguished element `1`, and let `M` be a right `C`-comodule. The
vectors `v` with `coact v = v ⊗ 1` form a submodule, and it is a subcomodule because its own
coaction already lands in it. For the comodule attached to a representation of an affine group
this is the submodule of vectors the group fixes.

The consequences of complete reducibility for this subcomodule are proved in
`TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive`, which is where the notion of a
completely reducible comodule lives; they are the mechanism behind the Layer 6 comparison in the
ReductiveGroups roadmap between reductive and linearly reductive groups.

## Main declarations

* `TauCeti.Comodule.fixedSubcomodule`: the subcomodule of vectors with coaction `v ↦ v ⊗ 1`.
* `TauCeti.Comodule.mem_fixedSubcomodule` and `TauCeti.Comodule.fixedSubcomodule_eq_top_iff`: its
  membership and triviality characterizations.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable (R : Type u) (C : Type v) (M : Type w)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] [One C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The subcomodule of vectors fixed by the coaction: those `v` with `coact v = v ⊗ 1`.

For the comodule of a representation of an affine group this is the submodule of invariants. -/
def fixedSubcomodule : Subcomodule R C M where
  carrier :=
    LinearMap.eqLocus (coact (R := R) (C := C) (M := M)) ((TensorProduct.mk R M C).flip 1)
  coact_mem' := by
    intro m hm
    have hm' : coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) := by
      simpa only [LinearMap.flip_apply, TensorProduct.mk_apply] using
        LinearMap.mem_eqLocus.mp hm
    exact ⟨(⟨m, hm⟩ : LinearMap.eqLocus (coact (R := R) (C := C) (M := M))
        ((TensorProduct.mk R M C).flip 1)) ⊗ₜ[R] (1 : C), by
          simpa only [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.coe_subtype] using
            hm'.symm⟩

variable {R C M}

/-- Membership in the fixed subcomodule: `m` is fixed exactly when `coact m = m ⊗ 1`. -/
@[simp]
theorem mem_fixedSubcomodule {m : M} :
    m ∈ fixedSubcomodule R C M ↔ coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  Iff.rfl

/-- The fixed subcomodule is everything exactly when the coaction is trivial on every vector. -/
@[simp]
theorem fixedSubcomodule_eq_top_iff :
    fixedSubcomodule R C M = ⊤ ↔
      ∀ m : M, coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  ⟨fun h m ↦ mem_fixedSubcomodule.mp (h ▸ Subcomodule.mem_top m),
    fun h ↦ Subcomodule.ext fun m ↦ by simp [h m]⟩

end TauCeti.Comodule
