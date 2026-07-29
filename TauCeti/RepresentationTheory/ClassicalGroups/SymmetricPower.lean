/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import TauCeti.RepresentationTheory.SymmetricPower

/-!
# Symmetric powers of the standard representation

This file specializes symmetric powers of representations to the standard representation of the
general linear group. The resulting action applies a matrix to every factor of a pure symmetric
tensor.

## Main definitions

* `TauCeti.symPowerRep` is the symmetric-power representation of `GL n k`.
* `TauCeti.symPowerFDRep` is its bundled finite-dimensional form.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “Symmetric and exterior power representations”.
* The standard-representation specialization is adapted from the formal template in
  `TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower`.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

variable (k : Type) (n d : ℕ) [CommRing k]

/-- The `d`th symmetric power of the standard representation of `GL n k`. -/
noncomputable abbrev symPowerRep :
    Representation k (GL (Fin n) k) (Sym[k]^d (Fin n → k)) :=
  (stdRep k n).symmetricPower d

/-- The symmetric power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev symPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (symPowerRep k n d)

end TauCeti
