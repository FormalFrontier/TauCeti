/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation on the group algebra of a normal subgroup

Let `N` be a normal subgroup of a group `G`.  Conjugating by `g : G` is an automorphism of `N`
(`MulAut.conjNormal`), so it permutes the basis of the group algebra `k[N]` and therefore induces an
algebra automorphism of `k[N]`.  This file packages that automorphism as a monoid homomorphism
`MonoidAlgebra.conjAlgAut : G →* (k[N] ≃ₐ[k] k[N])`, obtained by composing Mathlib's
`MonoidAlgebra.domCongrAut` with `MulAut.conjNormal`.

## Main definitions

* `MonoidAlgebra.conjAlgAut`: conjugation by `g : G` as an algebra automorphism of `k[N]`.

## Main statements

* `MonoidAlgebra.conjAlgAut_single`: conjugation acts on the group-algebra basis by conjugating the
  group element.
* `MonoidAlgebra.conjAlgAut_inv_self_apply`: conjugating by `g` and then by `g⁻¹` is the identity.
-/

public section

open scoped MonoidAlgebra

namespace MonoidAlgebra

variable (k : Type*) {G : Type*} [CommSemiring k] [Group G] (N : Subgroup G) [N.Normal]

/-- **Conjugation, read on the group algebra of a normal subgroup.**  Conjugating by `g : G`
permutes `N`, hence permutes the basis of `k[N]`, and the resulting algebra automorphism is what
translation by a representation of `G` is semilinear over. -/
noncomputable def conjAlgAut : G →* (k[N] ≃ₐ[k] k[N]) :=
  (domCongrAut (R := k) (A := k) (M := N)).comp MulAut.conjNormal

variable {k N}

/-- Conjugation acts on the group-algebra basis by conjugating the group element. -/
@[simp]
theorem conjAlgAut_single (g : G) (n : N) (a : k) :
    conjAlgAut k N g (single n a) = single (MulAut.conjNormal g n) a :=
  domCongr_single _ _ _

/-- Conjugating by `g` and then by `g⁻¹` is the identity.  Not a `simp` lemma: `simp` already
proves it from `map_inv` and `AlgEquiv.symm_apply_apply`, and tagging it fails `simpNF`. -/
theorem conjAlgAut_inv_self_apply (g : G) (a : k[N]) :
    conjAlgAut k N g⁻¹ (conjAlgAut k N g a) = a := by
  rw [map_inv, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

end MonoidAlgebra
