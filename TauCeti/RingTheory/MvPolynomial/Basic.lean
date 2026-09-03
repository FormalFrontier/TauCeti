/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.LinearAlgebra.Dimension.BaseChange

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

-- `MvPolynomial.algebraMvPolynomial` is deliberately not a global instance: it diamonds for
-- `Algebra (MvPolynomial σ R) (MvPolynomial σ (MvPolynomial σ S))`. Mathlib installs it locally
-- wherever the `MvPolynomial σ R`-algebra structure on `MvPolynomial σ S` is wanted, and the
-- pushout and scalar-tower instances used below are stated under it.
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Polynomial rings preserve module-finiteness of the coefficient map: `MvPolynomial.map f` is
a finite ring map whenever `f` is. -/
theorem MvPolynomial.finite_map {σ R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.Finite) : (MvPolynomial.map (σ := σ) f).Finite := by
  let _ : Algebra R S := f.toAlgebra
  have _ : Module.Finite R S := hf
  -- `MvPolynomial σ S` is the base change of `S` along `R → MvPolynomial σ R`. Stating that as a
  -- `have` is load-bearing: unifying `finite_of_isBaseChange` against the goal directly forces the
  -- `MvPolynomial σ R`-algebra structure to be `(MvPolynomial.map f).toAlgebra`, for which the
  -- scalar tower is not an instance, whereas Mathlib's pushout is stated for `algebraMvPolynomial`.
  have h : Module.Finite (MvPolynomial σ R) (MvPolynomial σ S) :=
    TauCeti.finite_of_isBaseChange
      (Algebra.IsPushout.out (R := R) (S := MvPolynomial σ R) (R' := S) (S' := MvPolynomial σ S))
  exact h

end TauCeti
