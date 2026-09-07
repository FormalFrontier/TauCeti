/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Basic
public import TauCeti.Algebra.Homology.Ext.DualNumbers

/-!
# The dual numbers: `Ext`-finite but not `Ext`-bounded

Let `k` be a field, let `A = k[ε]` be the dual numbers `k[ε]/(ε²)`, and let `S = A/(ε)` be the
residue field of `A`, viewed as an `A`-module. Every `Ext` group of the pair `(S, S)` is a
one-dimensional `k`-vector space (`TauCeti.extDualNumberResidueEquiv`), so `TauCeti.IsExtFinite`
holds while none of the groups vanishes and `TauCeti.IsExtBounded` fails: the alternating sum
`∑ n, (-1)ⁿ dim_k Extⁿ(S, S)` has no meaning. This is the example that separates the two halves
of `TauCeti.IsEulerAdmissible`. Since `TauCeti.extEuler` takes a proof of
`TauCeti.IsEulerAdmissible` as an argument, `TauCeti.not_isEulerAdmissible_dualNumberResidue` is
exactly the statement that this pair has no Ext-Euler characteristic; no totalised value is
available for it.

## Main results

* `TauCeti.not_isExtBounded_dualNumberResidue`: no degree bounds the `Ext`-support of `(S, S)`.
  This half needs only a nontrivial commutative ring of coefficients.
* `TauCeti.finrank_ext_dualNumberResidue`: over a field, every `Extⁿ(S, S)` is one-dimensional.
* `TauCeti.isExtFinite_dualNumberResidue`: every `Extⁿ(S, S)` is a finite-dimensional
  `k`-vector space.
* `TauCeti.not_isEulerAdmissible_dualNumberResidue`: the pair `(S, S)` is not Euler-admissible.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.5 and Chapter 4.
-/

open CategoryTheory CategoryTheory.Abelian

open scoped ModuleCat.Algebra

public section

namespace TauCeti

universe u

variable (k : Type u)

section Nontrivial

variable [CommRing k] [Nontrivial k]

/-- No degree is a vanishing bound for the `Ext` groups of `k[ε]/(ε)` against itself, because
none of them vanishes. -/
theorem not_isExtBoundedBy_dualNumberResidue (N : ℕ) :
    ¬ IsExtBoundedBy.{u} (dualNumberResidue k) (dualNumberResidue k) N := by
  intro h
  have hsub : Subsingleton (Ext.{u} (dualNumberResidue k) (dualNumberResidue k) N) :=
    h.subsingleton (le_refl N)
  have : Subsingleton k := (extDualNumberResidueEquiv k N).symm.injective.subsingleton
  exact false_of_nontrivial_of_subsingleton k

/-- **The dual-numbers rejection.** `Extⁿ(S, S)` never vanishes, so the pair `(S, S)` is not
`Ext`-bounded. -/
theorem not_isExtBounded_dualNumberResidue :
    ¬ IsExtBounded.{u} (dualNumberResidue k) (dualNumberResidue k) := by
  rintro ⟨N, hN⟩
  exact not_isExtBoundedBy_dualNumberResidue k N hN

end Nontrivial

section Field

variable [Field k]

/-- Over a field, every `Extⁿ(S, S)` of the residue field `S` of `k[ε]` is one-dimensional. -/
theorem finrank_ext_dualNumberResidue (n : ℕ) :
    Module.finrank k (Ext.{u} (dualNumberResidue k) (dualNumberResidue k) n) = 1 := by
  rw [(extDualNumberResidueEquiv k n).finrank_eq, Module.finrank_self]

/-- Every `Ext` group of `k[ε]/(ε)` against itself is a finite-dimensional `k`-vector space. -/
theorem isExtFinite_dualNumberResidue :
    IsExtFinite.{u} k (dualNumberResidue k) (dualNumberResidue k) :=
  ⟨fun n => (extDualNumberResidueEquiv k n).symm.finiteDimensional⟩

/-- **The dual-numbers rejection.** The residue field `S` of `k[ε]` is not Euler-admissible
against itself: its `Ext` groups are all one-dimensional, so `Ext`-finiteness holds
(`TauCeti.isExtFinite_dualNumberResidue`), but none of them vanishes, so the alternating sum
`∑ n, (-1)ⁿ dim_k Extⁿ(S, S)` is not a finite sum. Because `TauCeti.extEuler` consumes a proof of
`TauCeti.IsEulerAdmissible`, this pair has no Ext-Euler characteristic at all; no totalised value
is exposed for it. -/
theorem not_isEulerAdmissible_dualNumberResidue :
    ¬ IsEulerAdmissible.{u} k (dualNumberResidue k) (dualNumberResidue k) :=
  fun h => not_isExtBounded_dualNumberResidue k h.isExtBounded

end Field

end TauCeti
