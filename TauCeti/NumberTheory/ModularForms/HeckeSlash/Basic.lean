/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.TransposeAntiInvolution
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# The slash sum over a double-coset decomposition

A Hecke operator acts on a modular form by slashing it against representatives of the double
coset and summing. This file defines that sum and records that it is `ℂ`-linear in `f`.

⚠ **It is not yet an action, and on a general `f : ℍ → ℂ` it is not even well defined.**
`heckeSlashSum` is a sum over *chosen* representatives — `D.out` for the double coset and
`i.out` for each of its left cosets — and on an arbitrary function the choice changes the
answer: replacing `σᵢ` by `hσᵢ` for `h ∈ SL₂(ℤ)` multiplies the representative `(σᵢδ)ᵀ` by
`hᵀ` on the right, and `f ∣[k] (Xhᵀ) = (f ∣[k] X) ∣[k] hᵀ` differs from `f ∣[k] X` unless the
slash by `hᵀ` is trivial on that function. Even the identity double coset can therefore send a
raw `f` to `f ∣[k] h` rather than to `f`.

What repairs it is slash-invariance of `f`, and that is the proof of Shimura's Proposition
3.37: for `f` invariant under `SL₂(ℤ)` the sum is again invariant, because right multiplication
merely permutes the representatives. That theorem, and the descent of this sum to a genuine
operator on
`SlashInvariantForm` and `ModularForm`, are deliberately **not** in this file — the reindexing
argument is substantial and is a different claim. Until then this is an auxiliary sum, named to
say so, and every consumer must supply the invariance hypothesis itself.

## The transpose, and why it is here

The Hecke ring is built from the decomposition of `HδH` into **left** cosets `σᵢδH`
(`DoubleCoset.DecompQuotient`, and `LeftCosetModule/Basic.lean` in this repository). But the
slash action is a *right* action, so invariance of `∑ᵢ f ∣[k] Xᵢ` under `f ↦ f ∣[k] γ` needs
right multiplication by `γ` to permute the `Xᵢ` up to multiplication by `H` **on the left** —
that is, the `Xᵢ` must represent **right** cosets `HXᵢ`.

Transposition exchanges the two: if `HδH = ⊔ᵢ (σᵢδ)H` then `HδH = ⊔ᵢ H(δᵀσᵢᵀ)`, because
transposition is an anti-automorphism preserving `SL₂(ℤ)` and fixing every double coset. So the
representative used here is `(σᵢδ)ᵀ`, which is `transposeRep`.

The transpose is an artefact of which handedness Mathlib's `DecompQuotient` supplies, not of the
mathematics. Shimura decomposes `Γ₁αΓ₂ = ⊔ᵥ Γ₁aᵥ` — the group on the **left** — so his slash,
being a right action, permutes those representatives directly and no transpose ever appears.

⚠ Conventions: `gH` is a left coset and `Hg` a right one, as in Mathlib and in
`LeftCosetModule/Basic.lean`. AINTLIB's `HeckeAction.lean` uses the opposite labels for the
same objects; the mathematics is identical, the words are not.

Transposition is available as the anti-involution of `GLn/TransposeAntiInvolution.lean`, the
same one that proves the Hecke ring commutative; this file only needs that it preserves
`SL_n(ℤ)` and `Δ`.

## Positive determinants throughout

Every representative lies in `Δ = posDetInt 2`, so its determinant is positive, and that is what
makes the sum `ℂ`-linear: on the positive branch the slash action's conjugation `σ` is trivial
and scalars commute past it (`ModularForm.rat_smul_slash_of_det_pos`). Over a general
`GL(2, ℚ)`-element the twist is complex conjugation and linearity would fail.

## Main definitions

* `HeckeRing.GL2.transposeRep`: the transposed representative `(σᵢ δ)ᵀ`.
* `HeckeRing.GL2.heckeSlashSum`: the choice-dependent sum `∑ᵢ f ∣[k] (σᵢ δ)ᵀ`.

## Main results

* `HeckeRing.GL2.transposeRep_def`, `HeckeRing.GL2.heckeSlashSum_def` and
  `HeckeRing.GL2.heckeSlashSum_apply`: the characteristic equations, which are the interface
  since neither definition is `@[expose]`. The last two are the function-level and pointwise
  forms of the same equation.
* `HeckeRing.GL2.det_transposeRep_pos`: the representatives have positive determinant.
* `HeckeRing.GL2.heckeSlashSum_add`, `heckeSlashSum_zero`, `heckeSlashSum_smul`: `ℂ`-linearity.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck): `transposeRep`,
its `heckeSlash` (renamed `heckeSlashSum` here, since it is not yet an action) and that
definition's additivity, zero and scalar lemmas. Restated
against TauCeti's `SLnZ`/`posDetInt` Hecke pair and `transposeGLEquiv` rather than AINTLIB's
`GL_pair`/`GL_transposeEquiv`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4 *Action of double cosets on automorphic forms*: equation (3.4.1) defines the operator
  `f ∣[Γ₁ α Γ₂]ₖ` as the sum below, and Proposition 3.37 is the statement that it maps
  automorphic forms to automorphic forms — the invariance this file stops short of.
-/

public section

open Matrix UpperHalfPlane DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable (k : ℤ) (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))

/-- The transposed left-coset representative `(σᵢ δ)ᵀ = δᵀ σᵢᵀ`, where `δ` is the chosen
representative of the double coset `D` and `σᵢ` runs over its left-coset decomposition. The
transpose turns it into a representative of a right coset `H(σᵢ δ)ᵀ`, which is what a right
action needs. -/
noncomputable def transposeRep (i : DecompQuotient (SLnZ 2) (SLnZ 2) (D.out : GL (Fin 2) ℚ)) :
    GL (Fin 2) ℚ :=
  (transposeGLEquiv 2 ((i.out : GL (Fin 2) ℚ) * (D.out : GL (Fin 2) ℚ))).unop

-- `transposeRep` and `heckeSlashSum` are not `@[expose]`, so a module downstream of this one cannot
-- unfold either body. Their characteristic equations below are therefore the interface, not a
-- restatement of something already visible; `transposeRep_def` is written `(rfl)` in the style of
-- `ModularForms/Basic.lean`, which opts out of exporting the definitional equality itself.

/-- Defining equation for `transposeRep`: the transpose of `σᵢ δ`. Since `transposeRep` is not
`@[expose]`, a downstream module rewrites with this instead of unfolding the body. -/
lemma transposeRep_def (i : DecompQuotient (SLnZ 2) (SLnZ 2) (D.out : GL (Fin 2) ℚ)) :
    transposeRep D i =
      (transposeGLEquiv 2 ((i.out : GL (Fin 2) ℚ) * (D.out : GL (Fin 2) ℚ))).unop := (rfl)

/-- Each representative lies in `Δ`. -/
lemma transposeRep_mem_posDetInt (i : DecompQuotient (SLnZ 2) (SLnZ 2) (D.out : GL (Fin 2) ℚ)) :
    transposeRep D i ∈ posDetInt 2 :=
  transposeRep_def D i ▸
    transposeGLEquiv_mem_posDetInt 2 (mul_mem (SLnZ_le_posDetInt 2 i.out.2) D.out.2)

/-- The representatives have positive determinant — the `0 < det` half of
`transposeRep_mem_posDetInt`, in the shape `ModularForm.rat_smul_slash_of_det_pos` consumes. -/
lemma det_transposeRep_pos (i : DecompQuotient (SLnZ 2) (SLnZ 2) (D.out : GL (Fin 2) ℚ)) :
    0 < (transposeRep D i : Matrix (Fin 2) (Fin 2) ℚ).det :=
  ((mem_posDetInt_iff 2).mp (transposeRep_mem_posDetInt D i)).2

/-- **The slash sum over a chosen decomposition of a double coset**:
`∑ᵢ f ∣[k] (σᵢ δ)ᵀ`, over the transposed representatives of the left-coset decomposition of
`HδH` (Shimura's `f ∣[Γ₁ α Γ₂]ₖ`, §3.4 (3.4.1), up to the `det` normalising factor).

⚠ This depends on the chosen representatives `D.out` and `i.out`, and on a general
`f : ℍ → ℂ` the value changes with them — see the module docstring. Slash-invariance of `f` is
*sufficient* to make it independent of the choices, and so an action; that is a separate
theorem. Whether it is also necessary is not claimed here — a particular `f` and `D` could be
independent by cancellation. Do not read this definition as "the Hecke operator" until the
sufficiency theorem is available. -/
noncomputable def heckeSlashSum (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : DecompQuotient (SLnZ 2) (SLnZ 2) (D.out : GL (Fin 2) ℚ), f ∣[k] transposeRep D i

/-- Defining equation for `heckeSlashSum` at the level of functions. Since `heckeSlashSum` is
not `@[expose]`, a downstream module rewrites with this instead of unfolding the body; the
pointwise `heckeSlashSum_apply` below is the companion for arguments that work at a point. -/
lemma heckeSlashSum_def (f : ℍ → ℂ) : heckeSlashSum k D f =
    ∑ i : DecompQuotient (SLnZ 2) (SLnZ 2) (D.out : GL (Fin 2) ℚ), f ∣[k] transposeRep D i := (rfl)

/-- The pointwise value of the slash sum: the sum of the slashed values. This is the equation
the reindexing proof of Prop 3.37 works from. -/
lemma heckeSlashSum_apply (f : ℍ → ℂ) (τ : ℍ) : heckeSlashSum k D f τ =
    ∑ i : DecompQuotient (SLnZ 2) (SLnZ 2) (D.out : GL (Fin 2) ℚ), (f ∣[k] transposeRep D i) τ :=
  Finset.sum_apply ..

/-- The slash sum is additive in `f`. -/
@[simp]
lemma heckeSlashSum_add (f g : ℍ → ℂ) : heckeSlashSum k D (f + g) =
    heckeSlashSum k D f + heckeSlashSum k D g := by
  simp [heckeSlashSum, Finset.sum_add_distrib]

/-- The slash sum kills the zero function. -/
@[simp]
lemma heckeSlashSum_zero : heckeSlashSum k D 0 = 0 := by
  rw [heckeSlashSum]
  exact Finset.sum_eq_zero fun i _ ↦ SlashAction.zero_slash k (transposeRep D i)

/-- **The slash sum is homogeneous in `f`**: a scalar acting on `ℂ` through the scalar tower
passes out of the sum. With `heckeSlashSum_add`, at `α := ℂ`, this gives `ℂ`-linearity. -/
@[simp]
lemma heckeSlashSum_smul {α : Type*} [DistribSMul α ℂ] [IsScalarTower α ℂ ℂ] (c : α) (f : ℍ → ℂ) :
    heckeSlashSum k D (c • f) = c • heckeSlashSum k D f := by
  rw [heckeSlashSum, heckeSlashSum]
  -- each representative has positive determinant, so the slash carries no `σ` twist: the
  -- scalar leaves the summands one at a time, and only then comes out of the sum as a whole
  exact (Finset.sum_congr rfl fun i _ ↦ ModularForm.rat_smul_slash_of_det_pos k
    (det_transposeRep_pos D i) f c).trans Finset.smul_sum.symm

end HeckeRing.GL2
