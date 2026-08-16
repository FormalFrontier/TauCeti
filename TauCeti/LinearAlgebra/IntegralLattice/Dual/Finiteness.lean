/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Dual.Basic
import TauCeti.Data.Int.CongrAllPrimes

/-!
# Finiteness of dual integral lattices

The dual carrier of an integral lattice always spans the ambient rational vector space: it
contains the original full carrier. Its finite generation is subtler. It is finitely generated
over `ℤ`, and hence a full lattice, exactly when the ambient bilinear form is nondegenerate.

The converse is the load-bearing direction. Every vector in the left radical, together with all
of its rational multiples, lies in the dual carrier. If that carrier were finitely generated, a
coordinate of such a vector in an integral basis would be divisible by every prime and therefore
zero. Applying this to every coordinate forces the radical vector itself to vanish. Symmetry then
gives nondegeneracy on both sides.

## Main results

* `TauCeti.IntegralLattice.span_dualCarrier_eq_top`: the dual carrier always spans the ambient
  rational vector space.
* `TauCeti.IntegralLattice.moduleFinite_dualCarrier_iff_nondegenerate`: the dual carrier is a
  finite `ℤ`-module exactly when the form is nondegenerate.
* `TauCeti.IntegralLattice.fg_dualCarrier_iff_nondegenerate`: the equivalent finite-generation
  formulation.
* `TauCeti.IntegralLattice.isLattice_dualCarrier_iff_nondegenerate`: the dual carrier is a full
  lattice exactly when the form is nondegenerate.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 2.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- The dual carrier always spans the rational ambient space, without a nondegeneracy
hypothesis. -/
theorem span_dualCarrier_eq_top (L : IntegralLattice V) :
    Submodule.span ℚ (L.dualCarrier : Set V) = ⊤ := by
  apply top_unique
  rw [← Submodule.IsLattice.span_eq_top (M := L.carrier)]
  exact Submodule.span_mono L.le_dualCarrier

/-- Every rational multiple of a vector in the left radical belongs to the dual carrier. -/
theorem smul_mem_dualCarrier_of_mem_ker (L : IntegralLattice V) {x : V}
    (hx : x ∈ LinearMap.ker L.form) (a : ℚ) : a • x ∈ L.dualCarrier := by
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro y _
  rw [map_smul, LinearMap.smul_apply, LinearMap.mem_ker.mp hx, LinearMap.zero_apply,
    smul_zero]
  exact Submodule.zero_mem _

private theorem eq_zero_of_forall_form_eq_zero_of_moduleFinite_dualCarrier
    (L : IntegralLattice V) [Module.Finite ℤ L.dualCarrier]
    (x : V) (hx : ∀ y : V, L.form x y = 0) : x = 0 := by
  let hV : Module.IsTorsionFree ℤ V :=
    Module.IsTorsionFree.trans_faithfulSMul ℤ ℚ V
  let hdual : Module.IsTorsionFree ℤ L.dualCarrier :=
    @Submodule.instIsTorsionFree ℤ V _ _ _ L.dualCarrier hV
  let xd : L.dualCarrier := ⟨x, by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y _
    rw [hx]
    exact Submodule.zero_mem _⟩
  let b := Module.Free.chooseBasis ℤ L.dualCarrier
  have hcoord (j) : b.repr xd j = 0 := by
    apply Int.eq_zero_of_dvd_all_primes_ne (p := 2)
    intro p hp _
    let yd : L.dualCarrier := ⟨(p : ℚ)⁻¹ • x, by
      rw [LinearMap.BilinForm.mem_dualSubmodule]
      intro y _
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx, mul_zero]
      exact Submodule.zero_mem _⟩
    refine ⟨b.repr yd j, ?_⟩
    have hsmul : (p : ℤ) • yd = xd := by
      apply Subtype.ext
      -- Expose the subtype coercion before comparing the integer and rational scalar actions.
      rw [show (((p : ℤ) • yd : L.dualCarrier) : V) = (p : ℤ) • (yd : V) by rfl]
      simp only [yd, xd]
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast, mul_inv_cancel₀,
        one_smul]
      exact_mod_cast hp.ne_zero
    rw [← hsmul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hrepr : b.repr xd = 0 := by
    ext j
    simpa using hcoord j
  have hxd : xd = 0 := b.repr.injective (by simpa using hrepr)
  exact Subtype.ext_iff.mp hxd

/-- If the dual carrier is finite as a `ℤ`-module, then the lattice form is nondegenerate. -/
theorem nondegenerate_of_moduleFinite_dualCarrier
    (L : IntegralLattice V) [Module.Finite ℤ L.dualCarrier] : L.form.Nondegenerate := by
  have hleft : L.form.SeparatingLeft := by
    intro x hx
    exact eq_zero_of_forall_form_eq_zero_of_moduleFinite_dualCarrier L x hx
  exact ⟨hleft, fun x hx ↦ hleft x fun y ↦ by rw [L.isSymm.eq]; exact hx y⟩

/-- The dual carrier is finite as a `ℤ`-module exactly when the lattice form is
nondegenerate. -/
theorem moduleFinite_dualCarrier_iff_nondegenerate (L : IntegralLattice V) :
    Module.Finite ℤ L.dualCarrier ↔ L.form.Nondegenerate := by
  constructor
  · intro h
    let hfinite : Module.Finite ℤ L.dualCarrier := h
    exact L.nondegenerate_of_moduleFinite_dualCarrier
  · intro h
    let hnondegenerate : L.IsNondegenerate := ⟨h⟩
    infer_instance

/-- The dual carrier is finitely generated over `ℤ` exactly when the lattice form is
nondegenerate. -/
theorem fg_dualCarrier_iff_nondegenerate (L : IntegralLattice V) :
    L.dualCarrier.FG ↔ L.form.Nondegenerate := by
  rw [← Module.Finite.iff_fg]
  exact L.moduleFinite_dualCarrier_iff_nondegenerate

/-- The dual carrier is a full integral lattice exactly when the lattice form is
nondegenerate. -/
theorem isLattice_dualCarrier_iff_nondegenerate (L : IntegralLattice V) :
    L.dualCarrier.IsLattice ℚ ↔ L.form.Nondegenerate := by
  constructor
  · intro h
    let hlattice : L.dualCarrier.IsLattice ℚ := h
    exact L.nondegenerate_of_moduleFinite_dualCarrier
  · intro h
    let hnondegenerate : L.IsNondegenerate := ⟨h⟩
    infer_instance

end TauCeti.IntegralLattice
