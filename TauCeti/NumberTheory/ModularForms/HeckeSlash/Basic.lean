/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.Basic
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# The slash sum over a double-coset decomposition

A Hecke operator acts on a modular form by slashing it against representatives of the double
coset and summing. This file defines that sum. It is unconditionally *additive* in `f` and kills
`0`; homogeneity — and so `ℂ`-linearity — additionally needs the representatives to have positive
determinant, because the scalar passes through the slash only on that branch.

## Which cosets the representatives run over

Shimura decomposes `Γ₁ δ Γ₂ = ⊔ᵥ Γ₁ aᵥ` — the group on the **left** — and sets
`f ∣[Γ₁ δ Γ₂]ₖ = ∑ᵥ f ∣[k] aᵥ` (§3.4, (3.4.1)). That handedness is what a *right* action needs:
right multiplication by `γ ∈ Γ₂` permutes the right cosets `Γ₁ aᵥ` among themselves, which is the
proof of his Proposition 3.37, and the invariance that makes the sum independent of the chosen
representatives is invariance of `f` under `Γ₁`.

Mathlib's `DoubleCoset.DecompQuotient Γ₁ Γ₂ δ` indexes the *left* cosets `σᵢ δ Γ₂` instead. The
right cosets are indexed by the mirror quotient `DecompQuotient Γ₂ Γ₁ δ⁻¹ = Γ₂ ⧸ (Γ₂ ∩ δ⁻¹Γ₁δ)`:
`Γ₁ δ τ = Γ₁ δ τ'` exactly when `δ τ' τ⁻¹ δ⁻¹ ∈ Γ₁`, that is when `τ` and `τ'` have the same class
there. The representative attached to a class `v` is `δ · (τᵥ)⁻¹`, the inverse appearing because
`Γ₂ ⧸ (Γ₂ ∩ δ⁻¹Γ₁δ)` is a quotient by *left* cosets while `Γ₁ δ τ` is constant along right ones;
`v ↦ γ⁻¹ • v` is then the permutation right multiplication by `γ` induces. That these
representatives do run over the right cosets, each exactly once, is
`DoubleCoset.doubleCoset_eq_iUnion_rightCosets` together with
`DoubleCoset.op_mul_out_inv_smul_injective` (`HeckeRing/Basic.lean`).

⚠ **It is not yet an action, and on a general `f : ℍ → ℂ` it is not even well defined.**
`heckeSlashSum` is a sum over *chosen* representatives — `D.out` for the double coset and `v.out`
for each of its right cosets — and on an arbitrary function the choice changes the answer. A
different representative of the same right coset is `γ₁ · (δ τᵥ⁻¹)` for some `γ₁ ∈ Γ₁`, and
`f ∣[k] (γ₁ x) = (f ∣[k] γ₁) ∣[k] x`, so the summand moves unless the slash by `γ₁` is trivial on
`f`. Even the identity double coset can therefore send a raw `f` to `f ∣[k] γ₁` rather than to `f`.
What repairs it is slash-invariance of `f` under `Γ₁`, and that is `HeckeSlash/Reindex.lean`;
`HeckeSlash/Invariance.lean` then turns it into invariance of the sum under `Γ₂`.

⚠ Conventions: `gH` is a left coset and `Hg` a right one, as in Mathlib and in
`LeftCosetModule/Basic.lean`. AINTLIB's `HeckeAction.lean` uses the opposite labels for the same
objects; the mathematics is identical, the words are not.

## An arbitrary triple, and what each declaration actually needs

The declarations are stated over an arbitrary triple `HeckeCoset Δ Γ₁ Γ₂` rather than the
level-one pair `(posDetInt 2, SLnZ 2, SLnZ 2)`, and each carries only what it uses. Nothing is
asked of `Δ` at all beyond containing the chosen `δ`. In particular no group here has to be
stable under transposition, which is what confines the *left*-coset indexing to level one and is
why this file does not use it: `!![1, 1; 0, 1] ∈ Γ₁(N)` for every `N` while its transpose lies in
`Γ₁(N)` only when `N = 1`.

* `rightCosetRep` and its characteristic equation need only the group law.
* The **sum** and its additivity and vanishing on `0` need only that the index type is finite,
  so they take `[Finite (DecompQuotient Γ₂ Γ₁ δ⁻¹)]` directly — the proposition, not the
  data-bearing `Fintype`, since no chosen enumeration is used; the `Fintype` that `∑` needs is
  installed once as a local instance. A Hecke triple supplies that finiteness
  (`IsHeckeTriple.commensurable_conjAct_inv_left`, `HeckeRing/Basic.lean`) and is strictly
  stronger — it also demands commensurability and that `Δ` commensurate `Γ₁`, none of which the
  sum uses.
* Positivity of the determinant enters exactly once, in **homogeneity**: on the positive branch
  the slash action's conjugation `σ` is trivial and scalars commute past it
  (`ModularForm.rat_smul_slash_of_det_pos`), whereas over a general `GL(2, ℚ)`-element the twist
  is complex conjugation and linearity would fail. So `rightCosetRep_mem_posDetInt`,
  `det_rightCosetRep_pos` and `heckeSlashSum_smul` — and only those — mention determinants, and
  each asks for the weakest form it can. `rightCosetRep_mem_posDetInt` concludes a `posDetInt`
  membership and so needs integrality. `det_rightCosetRep_pos` concludes a statement about
  determinants alone, so it asks only `Γ₂ ≤ GLPos (Fin 2) ℚ` and `δ ∈ GLPos (Fin 2) ℚ`.
  `heckeSlashSum_smul` asks less still: not a condition on the factors but
  `∀ v, 0 < det (rightCosetRep D v)`, since a product can be positive with neither factor
  positive and a factorwise hypothesis would exclude those cases. `det_rightCosetRep_pos` is how
  callers supply it. Neither `Γ₁` nor the rest of `Δ` is constrained anywhere.

## Main definitions

* `HeckeRing.GL2.rightCosetRep`: the representative `δ τᵥ⁻¹` of the `v`-th right coset.
* `HeckeRing.GL2.heckeSlashSum`: the choice-dependent sum `∑ᵥ f ∣[k] (δ τᵥ⁻¹)`.

## Main results

* `HeckeRing.GL2.rightCosetRep_def`, `HeckeRing.GL2.heckeSlashSum_def` and
  `HeckeRing.GL2.heckeSlashSum_apply`: the characteristic equations, which are the interface
  since neither definition is `@[expose]`. The last two are the function-level and pointwise
  forms of the same equation.
* `HeckeRing.GL2.det_rightCosetRep_pos`: the representatives have positive determinant, given
  `Γ₂ ≤ GLPos (Fin 2) ℚ` and `δ ∈ GLPos (Fin 2) ℚ`.
* `HeckeRing.GL2.heckeSlashSum_add` and `heckeSlashSum_zero`: additivity and vanishing on `0`,
  with no hypothesis beyond finiteness of the index type.
* `HeckeRing.GL2.heckeSlashSum_smul`: homogeneity, which additionally needs each representative
  to have positive determinant — the hypothesis is that, not the factorwise condition, since a
  product can be positive with neither factor positive. `det_rightCosetRep_pos` supplies it.
  Together with `heckeSlashSum_add` this gives `ℂ`-linearity.

## Provenance

The definition and its additivity, zero and scalar lemmas correspond to `heckeSlash` and its
algebraic API in the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck). No code is
transcribed: AINTLIB indexes the sum by Mathlib's left-coset `DecompQuotient` and repairs the
handedness with a transpose, a device that works only where every group in sight is stable under
transposition — level one. The sum below runs over Shimura's own right-coset index instead, so it
is stated over an arbitrary triple, with no transpose anywhere.

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

variable (k : ℤ) {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ Γ₁ Γ₂)

/-- The representative `δ τᵥ⁻¹` of the `v`-th right coset `Γ₁ aᵥ` in the decomposition
`Γ₁ δ Γ₂ = ⊔ᵥ Γ₁ aᵥ`, where `δ` is the chosen representative of the double coset `D` and `τᵥ`
runs over the chosen representatives of `Γ₂ ⧸ (Γ₂ ∩ δ⁻¹Γ₁δ)`.

The inverse is what converts the *left*-coset quotient Mathlib supplies into the right-coset
index the decomposition needs; see "Which cosets the representatives run over" in the module
docstring. -/
noncomputable def rightCosetRep (v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹) :
    GL (Fin 2) ℚ :=
  (D.out : GL (Fin 2) ℚ) * ((v.out : GL (Fin 2) ℚ))⁻¹

-- `rightCosetRep` and `heckeSlashSum` are not `@[expose]`, so a module downstream of this one
-- cannot unfold either body. Their characteristic equations below are therefore the interface,
-- not a restatement of something already visible; `rightCosetRep_def` is written `(rfl)` in the
-- style of `ModularForms/Basic.lean`, which opts out of exporting the definitional equality.

/-- Defining equation for `rightCosetRep`. Since `rightCosetRep` is not `@[expose]`, a
downstream module rewrites with this instead of unfolding the body. -/
lemma rightCosetRep_def (v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹) :
    rightCosetRep D v = (D.out : GL (Fin 2) ℚ) * ((v.out : GL (Fin 2) ℚ))⁻¹ := (rfl)

/-- Each representative lies in `posDetInt 2` when `δ` does and `Γ₂` does. Only `Γ₂` and the
chosen `δ` are constrained: nothing is asked of `Γ₁`, and nothing of `Δ` beyond containing `δ`.
The hypothesis is used at `τᵥ⁻¹`, which lies in `Γ₂` because `Γ₂` is a group. -/
lemma rightCosetRep_mem_posDetInt (hΓ₂ : Γ₂.toSubmonoid ≤ posDetInt 2)
    (hD : (D.out : GL (Fin 2) ℚ) ∈ posDetInt 2)
    (v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹) : rightCosetRep D v ∈ posDetInt 2 := by
  have hv : ((v.out : GL (Fin 2) ℚ))⁻¹ ∈ Γ₂ := inv_mem v.out.2
  exact rightCosetRep_def D v ▸ mul_mem hD (hΓ₂ hv)

/-- The representatives have positive determinant, in the shape
`ModularForm.rat_smul_slash_of_det_pos` consumes.

This asks only for positivity, not for the integrality `posDetInt 2` also carries: the conclusion
is about determinants alone, and `det (δ τᵥ⁻¹) = det δ · det τᵥ⁻¹`. A `posDetInt` hypothesis is
converted by `posDetInt_le_glpos`.

Factorwise positivity is *sufficient*, not necessary — a product can be positive with neither
factor positive — so `heckeSlashSum_smul` takes the positivity of each representative directly
and this lemma is the convenient way to supply it. -/
lemma det_rightCosetRep_pos (hΓ₂ : Γ₂ ≤ Matrix.GLPos (Fin 2) ℚ)
    (hD : (D.out : GL (Fin 2) ℚ) ∈ Matrix.GLPos (Fin 2) ℚ)
    (v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹) :
    0 < (rightCosetRep D v : Matrix (Fin 2) (Fin 2) ℚ).det := by
  have hv : ((v.out : GL (Fin 2) ℚ))⁻¹ ∈ Γ₂ := inv_mem v.out.2
  have h := mul_mem hD (hΓ₂ hv)
  rw [rightCosetRep_def]
  simpa using h

-- From here on the sum needs its index type to be finite, and that is *all* it needs: a Hecke
-- triple supplies this finiteness (`HeckeRing/Basic.lean`) but is strictly stronger, so it is
-- assumed directly. It is introduced here rather than `omit`ted from the four declarations
-- above, which do without it.
--
-- The assumption is the *proposition* `Finite`, not the data-bearing `Fintype`: the sum needs no
-- chosen enumeration, only that one exists. The `Fintype` the `∑` notation requires is then
-- installed once, as a local instance, so every statement below is written against a single
-- instance and none has to carry a `letI`. Everything here is already `noncomputable`.
variable [Finite (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)]

/-- The enumeration `∑` needs, obtained from the `Finite` assumption by choice. It is `local`
and `noncomputable`: the sum below does not depend on which enumeration is chosen, so no
declaration in this file should carry one as data. -/
noncomputable local instance : Fintype (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹) :=
  Fintype.ofFinite _

/-- **The slash sum over a chosen decomposition of a double coset**: `∑ᵥ f ∣[k] (δ τᵥ⁻¹)`, over
the representatives of the decomposition of `Γ₁ δ Γ₂` into right cosets `Γ₁ aᵥ`. Up to the `det`
normalising factor already built into the slash action, this is Shimura's `f ∣[Γ₁ δ Γ₂]ₖ`
(§3.4, (3.4.1)).

⚠ This depends on the chosen representatives `D.out` and `v.out`, and on a general
`f : ℍ → ℂ` the value changes with them — see the module docstring. Invariance of `f` under
`Γ₁` is *sufficient* to make it independent of those choices (`slash_rightCosetRep_of_mem`,
`HeckeSlash/Reindex.lean`); whether it is also necessary is not claimed here, since a particular
`f` and `D` could be independent by cancellation.

⚠ Choice-independence is not the same as being an action, and this docstring does not claim the
latter. What right multiplication gives is invariance of the *output* under `Γ₂`, which is the
same group as the input's only on a diagonal triple. -/
noncomputable def heckeSlashSum (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹, f ∣[k] rightCosetRep D v

/-- Defining equation for `heckeSlashSum` at the level of functions. Since `heckeSlashSum` is
not `@[expose]`, a downstream module rewrites with this instead of unfolding the body; the
pointwise `heckeSlashSum_apply` below is the companion for arguments that work at a point. -/
lemma heckeSlashSum_def (f : ℍ → ℂ) : heckeSlashSum k D f =
    ∑ v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹, f ∣[k] rightCosetRep D v := (rfl)

/-- The pointwise value of the slash sum: the sum of the slashed values. This is the equation
the reindexing proof of Prop 3.37 works from. -/
lemma heckeSlashSum_apply (f : ℍ → ℂ) (τ : ℍ) : heckeSlashSum k D f τ =
    ∑ v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹, (f ∣[k] rightCosetRep D v) τ :=
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
  exact Finset.sum_eq_zero fun v _ ↦ SlashAction.zero_slash k (rightCosetRep D v)

/-- **The slash sum is homogeneous in `f`**: a scalar acting on `ℂ` through the scalar tower
passes out of the sum. With `heckeSlashSum_add`, at `α := ℂ`, this gives `ℂ`-linearity.

Unlike additivity, this needs each representative to have positive determinant, because the
scalar passes through the slash only on that branch. That is asked for directly rather than
factorwise: `det (δ τᵥ⁻¹) > 0` is what the proof uses, and a product can be positive with neither
factor positive, so hypotheses on `Γ₂` and `δ` separately would exclude cases the theorem covers.
`det_rightCosetRep_pos` is the convenient sufficient condition. -/
@[simp]
lemma heckeSlashSum_smul
    (hpos : ∀ v, 0 < (rightCosetRep D v : Matrix (Fin 2) (Fin 2) ℚ).det)
    {α : Type*} [DistribSMul α ℂ] [IsScalarTower α ℂ ℂ] (c : α) (f : ℍ → ℂ) :
    heckeSlashSum k D (c • f) = c • heckeSlashSum k D f := by
  rw [heckeSlashSum, heckeSlashSum]
  -- each representative has positive determinant, so the slash carries no `σ` twist: the
  -- scalar leaves the summands one at a time, and only then comes out of the sum as a whole
  exact (Finset.sum_congr rfl fun v _ ↦ ModularForm.rat_smul_slash_of_det_pos k
    (hpos v) f c).trans Finset.smul_sum.symm

end HeckeRing.GL2
