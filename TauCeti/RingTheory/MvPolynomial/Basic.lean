/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Finiteness of `MvPolynomial.map`

`MvPolynomial.map f` is a finite ring map whenever `f` is: a family generating `S` over `R`
generates `MvPolynomial σ S` over `MvPolynomial σ R` once its members are read as constants.

This is the coefficient-extension half of the finiteness that Stacks 10.161.13 (tag 032O)
records as "`R'[x^{1/q}]` is finite over `R[x]`"; the `expand` half lives in
`TauCeti/RingTheory/MvPolynomial/Expand.lean`. Nothing here mentions `expand`, which is why it
sits in this file rather than that one.

## Main results

* `TauCeti.MvPolynomial.finite_map`: `MvPolynomial.map f` is finite when `f` is.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`. The argument is Stacks 10.161.13 (tag 032O),
which is univariate and whose proof records it as "Since `R` is N-2 we see that `R′` is finite
over `R` and hence `R′[x^{1/q}]` is finite over `R[x]`"; the multivariate form is not claimed as
source material.
-/

public section

namespace TauCeti

/-- Polynomial rings preserve module-finiteness of the coefficient map: `MvPolynomial.map f` is
a finite ring map whenever `f` is. -/
theorem MvPolynomial.finite_map {σ R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.Finite) : (MvPolynomial.map (σ := σ) f).Finite := by
  classical
  let _ : Algebra R S := f.toAlgebra
  obtain ⟨t, htfin, ht⟩ := Submodule.fg_def.mp (Module.finite_def.mp hf)
  let _ : Algebra (MvPolynomial σ R) (MvPolynomial σ S) := (MvPolynomial.map (σ := σ) f).toAlgebra
  refine Module.finite_def.mpr (Submodule.fg_def.mpr
    ⟨MvPolynomial.C '' t, htfin.image _, eq_top_iff.mpr fun p _ ↦ ?_⟩)
  refine MvPolynomial.induction_on' p (fun α c ↦ ?_) (fun p q hp hq ↦ Submodule.add_mem _ hp hq)
  refine Submodule.span_induction
    (p := fun c _ ↦ MvPolynomial.monomial α c ∈
      Submodule.span (MvPolynomial σ R) (MvPolynomial.C '' t))
    ?_ ?_ ?_ ?_ (ht ▸ Submodule.mem_top : c ∈ Submodule.span R t)
  · -- a generator `x ∈ t`, as the constant `C x`, scaled by the monomial `X ^ α`
    intro x hx
    have hx' : MvPolynomial.monomial α x
        = (MvPolynomial.monomial α (1 : R)) • (MvPolynomial.C x : MvPolynomial σ S) := by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      rw [MvPolynomial.map_monomial, map_one, mul_comm, MvPolynomial.C_mul_monomial, mul_one]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · -- an `R`-scalar becomes the constant `C r` acting through `MvPolynomial.map f`
    intro r x _ hx
    have hr : MvPolynomial.monomial α (r • x)
        = (MvPolynomial.C r : MvPolynomial σ R) • MvPolynomial.monomial α x := by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, Algebra.smul_def,
        RingHom.algebraMap_toAlgebra, MvPolynomial.map_C, MvPolynomial.C_mul_monomial]
    rw [hr]
    exact Submodule.smul_mem _ _ hx

end TauCeti
