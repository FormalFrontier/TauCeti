/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# When the discriminant bound is an equality: integral bases

The effective discriminant bound `|d_K| ≤ |disc b|`
(`TauCeti.NumberField.abs_discr_le_of_basis_isIntegral`) holds for *every* `ℚ`-basis `b` of a
number field `K` consisting of algebraic integers, and is strict exactly when `b` fails to
generate the whole ring of integers: writing `m` for the index of the `ℤ`-span of `b` in
`𝒪_K`, one has `disc b = m² · d_K`. The roadmap's Layer-1 discriminant target records the
inequality; this file supplies the complementary **equality** half, the case `m = 1`.

Concretely, if `b` is (the image in `K` of) a `ℤ`-basis of `𝒪_K` — an *integral basis* — then

`disc b = d_K` (exactly, over `ℚ`),

so the upper bound is attained. This is what makes the bound usable as an evaluator: once a
`ℤ`-basis of `𝒪_K` is exhibited, computing its trace-form discriminant computes `d_K` on the
nose. It is exactly the step behind the roadmap's `ℚ(i)` worked example, where `{1, i}` is a
`ℤ`-basis of the Gaussian integers and `disc {1, i} = -4` gives `d_{ℚ(i)} = -4`.

## Main results

* `TauCeti.NumberField.discr_eq_of_integralBasis`: for a `ℤ`-basis `c` of `𝒪_K`, the rational
  discriminant of its image in `K` equals `d_K`.
* `TauCeti.NumberField.discr_eq_of_basis_isIntegral_of_span_eq_top`: the same, phrased for a
  `ℚ`-basis `b` of algebraic integers whose `ℤ`-span (inside `𝒪_K`) is everything.
* `TauCeti.NumberField.abs_discr_eq_of_basis_isIntegral_of_span_eq_top`: the matching
  `|d_K| = |disc b|`, the equality companion of `abs_discr_le_of_basis_isIntegral`.
* `TauCeti.NumberField.discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int`: the consumer
  form that turns an evaluated integer basis discriminant into `d_K` exactly, with
  `TauCeti.NumberField.natAbs_discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int` its
  `natAbs` corollary.

## Provenance

No formal code is vendored. The equality is assembled from Mathlib's
`Algebra.discr_localizationLocalization` and `NumberField.discr_eq_discr`; the `ℚ`-basis form
constructs the `ℤ`-basis of `𝒪_K` from the spanning hypothesis. It is the exact-attainment
companion of the migrated Layer-1 bound `TauCeti.NumberField.abs_discr_le_of_basis_isIntegral`,
whose source attribution (kim-em/erdos-unit-distance) is in
`TauCeti/NumberTheory/EffectiveBounds/Discriminant/Basic.lean`.
-/

public section

open Module
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **An integral basis attains the discriminant bound.** For a `ℤ`-basis `c` of the ring of
integers `𝒪_K`, the rational discriminant of the induced `ℚ`-basis of `K` is exactly the field
discriminant `d_K`. -/
theorem discr_eq_of_integralBasis (c : Basis ι ℤ (𝓞 K)) :
    Algebra.discr ℚ (fun i => algebraMap (𝓞 K) K (c i)) = (NumberField.discr K : ℚ) := by
  have h : (fun i => algebraMap (𝓞 K) K (c i)) =
      ⇑(c.localizationLocalization ℚ (nonZeroDivisors ℤ) K) :=
    funext fun i => (c.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) K i).symm
  rw [h, Algebra.discr_localizationLocalization, NumberField.discr_eq_discr]
  simp

/-- **The discriminant bound is an equality for a spanning integral basis.** If `b` is a
`ℚ`-basis of `K` consisting of algebraic integers whose `ℤ`-span inside `𝒪_K` is all of `𝒪_K`,
then `disc b = d_K` exactly (over `ℚ`). -/
theorem discr_eq_of_basis_isIntegral_of_span_eq_top
    (b : Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (hspan : Submodule.span ℤ (Set.range fun i => (⟨b i, hb i⟩ : 𝓞 K)) = ⊤) :
    Algebra.discr ℚ (b : ι → K) = (NumberField.discr K : ℚ) := by
  set v : ι → 𝓞 K := fun i => ⟨b i, hb i⟩ with hv
  -- The `𝒪_K`-valued family is `ℤ`-linearly independent: it maps to the `ℚ`-basis `b` under the
  -- (injective, `ℤ`-linear) inclusion `𝒪_K → K`.
  have hli : LinearIndependent ℤ v := by
    have hb' : LinearIndependent ℤ (b : ι → K) :=
      LinearIndependent.restrict_scalars' ℤ b.linearIndependent
    have hcomp :
        ⇑(IsScalarTower.toAlgHom ℤ (𝓞 K) K).toLinearMap ∘ v = (b : ι → K) := by
      funext i
      -- `v i` is `⟨b i, hb i⟩`, so the inclusion `𝒪_K → K` returns `b i` by definition; the
      -- pre-bump `simp [hv]` no longer closes this.
      rfl
    rw [← hcomp] at hb'
    exact hb'.of_comp _
  -- Package it as a `ℤ`-basis of `𝒪_K`, whose image in `K` is `b`.
  let c : Basis ι ℤ (𝓞 K) := Basis.mk hli hspan.ge
  have hc : (fun i => algebraMap (𝓞 K) K (c i)) = (b : ι → K) := by
    funext i
    have hi : c i = v i := Basis.mk_apply hli hspan.ge i
    rw [hi]
    -- as above, `algebraMap (𝓞 K) K ⟨b i, hb i⟩` is `b i` by definition.
    rfl
  have := discr_eq_of_integralBasis c
  rwa [hc] at this

/-- **The equality companion of the effective discriminant bound.** For a `ℚ`-basis of algebraic
integers that generates `𝒪_K`, the effective bound `|d_K| ≤ |disc b|` is an equality. -/
theorem abs_discr_eq_of_basis_isIntegral_of_span_eq_top
    (b : Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (hspan : Submodule.span ℤ (Set.range fun i => (⟨b i, hb i⟩ : 𝓞 K)) = ⊤) :
    |(NumberField.discr K : ℚ)| = |Algebra.discr ℚ (b : ι → K)| := by
  rw [discr_eq_of_basis_isIntegral_of_span_eq_top b hb hspan]

/-- **Evaluating the discriminant through a spanning integral basis.** If the discriminant of a
generating basis of algebraic integers computes to an integer `d`, then `d_K = d` exactly. This is
the consumer form used to read off `d_K` from a concrete trace-form computation, as in the
roadmap's `ℚ(i)` example (`disc {1, i} = -4`, whence `d_{ℚ(i)} = -4`). -/
theorem discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int
    (b : Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (hspan : Submodule.span ℤ (Set.range fun i => (⟨b i, hb i⟩ : 𝓞 K)) = ⊤)
    {d : ℤ} (hd : Algebra.discr ℚ (b : ι → K) = (d : ℚ)) :
    NumberField.discr K = d := by
  have h : (NumberField.discr K : ℚ) = (d : ℚ) :=
    (discr_eq_of_basis_isIntegral_of_span_eq_top b hb hspan).symm.trans hd
  exact_mod_cast h

/-- **The absolute value of the discriminant from a spanning integral basis.** The `natAbs`
corollary of `discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int`, reading off `|d_K|`
from an evaluated integer basis discriminant (in the `ℚ(i)` example, `(d_{ℚ(i)}).natAbs = 4`). -/
theorem natAbs_discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int
    (b : Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (hspan : Submodule.span ℤ (Set.range fun i => (⟨b i, hb i⟩ : 𝓞 K)) = ⊤)
    {d : ℤ} (hd : Algebra.discr ℚ (b : ι → K) = (d : ℚ)) :
    (NumberField.discr K).natAbs = d.natAbs := by
  rw [discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int b hb hspan hd]

end TauCeti.NumberField
