/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Scheme-theoretic images

This file contains general results about Mathlib's scheme-theoretic image construction.

## Main declarations

* `TauCeti.specTargetImageIdeal_specMap`: the ideal defining the image of a spectrum map is the
  kernel of the corresponding ring homomorphism.
-/

public section

open CategoryTheory Opposite

namespace TauCeti

open AlgebraicGeometry

universe u

variable {R S : CommRingCat.{u}}

/-- The ideal defining the scheme-theoretic image of a spectrum map is the kernel of the
corresponding ring homomorphism. -/
@[simp]
theorem specTargetImageIdeal_specMap (f : R ⟶ S) :
    specTargetImageIdeal (Spec.map f) = RingHom.ker f.hom := by
  rw [specTargetImageIdeal]
  rw [Adjunction.homEquiv_symm_apply]
  -- The image ideal is phrased through the `Γ ⊣ Spec` adjunction. Normalize its recovered
  -- coordinate map to the explicit global-sections map before using naturality of `ΓSpecIso`.
  change RingHom.ker (((Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop).hom) = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  exact (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv.map_eq_zero_iff

end TauCeti
