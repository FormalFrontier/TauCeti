/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.NebentypusChar
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma0

/-!
# The nebentypus-twisted slash sum over a double coset of `Γ₀(N)`

`HeckeSlash/Basic.lean` sums `f ∣[k] aᵥ` over representatives of the right cosets a double coset
decomposes into, with no weights at all, and `HeckeSlash/Gamma0.lean` instantiates that at
`Γ₀(N)`. That instantiation stops short of the character on purpose: `Γ₀(N)` is where the
nebentypus lives, so there is a second, weighted sum to be had, and this file is it. Each summand
is multiplied by `delta0NebentypusChar χ` of its own representative, which `Δ₀(N)` contains.

## Which way the character goes

The weight is the character itself, not its inverse, and that is forced by the convention
`Delta0UpperUnit` was defined with rather than chosen here. `Delta0UpperUnit` reads off the
*upper-left* unit, so on `Γ₀(N)` it is the inverse of the lower-right unit `Gamma0Map` records
(`Delta0UpperUnit_mapGL`: `ad ≡ 1` there), and `delta0NebentypusChar_mapGL` carries that inverse
through `χ`. Classically the twisted operator divides by the nebentypus; composing the two
inversions, dividing by `χ ∘ Gamma0Map` is multiplying by `delta0NebentypusChar χ`, so the
inverse appears nowhere in the sum below. Reading the weight as the nebentypus extended along
`Gamma0Map` and adding an inverse to compensate would negate the twist twice over.

⚠ The pay-off of the weighting is *not* proved here. What makes the twisted sum the useful one
is that it is well defined on, and preserves, the character space `modFormCharSpace k χ` — the
weights cancel the eigenvalue `χ` that `mem_modFormCharSpace_iff_nebentypus` records, which the
unweighted `heckeSlashSum` cannot do. Like `heckeSlashSum` before it, what is established below
is only the definition and its linearity in `f`; every statement here holds for an arbitrary
`f : ℍ → ℂ`, and none of them mentions a character space.

## Main definitions

* `HeckeRing.GL2.nebentypusWeight`: the weight `delta0NebentypusChar χ aᵥ` a summand carries.
* `HeckeRing.GL2.twistedHeckeSlashSum`: the weighted sum
  `∑ᵥ delta0NebentypusChar χ aᵥ • (f ∣[k] aᵥ)`.
* `HeckeRing.GL2.twistedHeckeSlashSumEnd`: that sum bundled as a `ℂ`-linear endomorphism of
  `ℍ → ℂ`, the form downstream constructions consume.

## Main results

* `HeckeRing.GL2.twistedHeckeSlashSum_add`, `HeckeRing.GL2.twistedHeckeSlashSum_zero`,
  `HeckeRing.GL2.twistedHeckeSlashSum_smul`: the twisted sum is `ℂ`-linear in `f`. Unlike the
  unweighted sum, homogeneity needs no positivity hypothesis from the caller: the
  representatives lie in `Δ₀(N)`, whose determinants are positive.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5 (Hecke operators with nebentypus).
* Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck),
  [`HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`](https://github.com/CBirkbeck/AINTLIB) at
  commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, declarations `deltaRepGen`,
  `delta0NebentypusWeight`, `twistedHeckeSlashGen`, `twistedHeckeSlashGen_add` and
  `twistedHeckeSlashGen_smul`. The source sums over adjugated representatives indexed by its own
  quotient and carries an explicit inverse on each weight; here the representatives are
  `HeckeSlash/Basic.lean`'s `rightCosetRep`, and the inverse is absent for the reason above.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

-- `[NeZero N]` is introduced further down, immediately before the first declaration that needs
-- it: the weight of a single representative does not ask `N` to be nonzero. `Gamma0/Basic.lean`
-- splits its own file at the same point and for the same reason. The two facts about the
-- representative itself that the weight rests on — `rightCosetRep_mem_Delta0` and
-- `det_rightCosetRep_pos_of_delta0` — carry no character data and live in `HeckeSlash/Gamma0.lean`.
variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
  (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))
  (v : DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
    (D.out : GL (Fin 2) ℚ)⁻¹)

/-- **The weight a summand carries**: the twisting character `delta0NebentypusChar χ` evaluated
on the summand's own representative. Naming it keeps `rightCosetRep_mem_Delta0` out of every
statement downstream, since the character is a homomorphism on the submonoid and so needs the
membership proof as data. -/
noncomputable def nebentypusWeight : ℂˣ :=
  delta0NebentypusChar N χ ⟨rightCosetRep D v, rightCosetRep_mem_Delta0 D v⟩

/-- Defining equation for `nebentypusWeight`. Since the definition sits in a `public section`
without `@[expose]`, a downstream module rewrites with this instead of unfolding the body. -/
lemma nebentypusWeight_def : nebentypusWeight χ D v =
    delta0NebentypusChar N χ ⟨rightCosetRep D v, rightCosetRep_mem_Delta0 D v⟩ := (rfl)

-- From here on the sum needs its index type to be finite, and `[NeZero N]` is what buys that:
-- it is the hypothesis the `Γ₀(N)` Hecke-triple instance of `Gamma0/Basic.lean` carries, and the
-- finiteness of the right-coset index comes with the triple.
variable [NeZero N]

/-- The enumeration `∑` needs, obtained from the ambient `Finite` instance by choice. As in
`HeckeSlash/Basic.lean` it is `local` and `noncomputable`: nothing below depends on which
enumeration is chosen, so no declaration should carry one as data. -/
noncomputable local instance :
    Fintype (DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      (D.out : GL (Fin 2) ℚ)⁻¹) :=
  Fintype.ofFinite _

/-- **The nebentypus-twisted slash sum over a double coset of `Γ₀(N)`**:
`∑ᵥ delta0NebentypusChar χ aᵥ • (f ∣[k] aᵥ)` over the same representatives `aᵥ = δ τᵥ⁻¹` that
the unweighted `heckeSlashSum` runs over, each summand weighted by the twisting character of its
own representative.

⚠ Like `heckeSlashSum`, the *definition* depends on the chosen representatives `D.out` and
`v.out`, and on a general `f : ℍ → ℂ` the value changes with them; the weights are attached to
the representatives, not to the cosets. What repairs that is the twisted invariance of `f`, in
the same way `Γ₁`-invariance repairs the unweighted sum, and it is not proved here. -/
noncomputable def twistedHeckeSlashSum (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ v : DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
    (D.out : GL (Fin 2) ℚ)⁻¹, (nebentypusWeight χ D v : ℂ) • (f ∣[k] rightCosetRep D v)

/-- Defining equation for `twistedHeckeSlashSum` at the level of functions. Since the definition
is not `@[expose]`, a downstream module rewrites with this instead of unfolding the body; the
pointwise `twistedHeckeSlashSum_apply` below is the companion for arguments that work at a
point. -/
lemma twistedHeckeSlashSum_def (f : ℍ → ℂ) : twistedHeckeSlashSum k χ D f =
    ∑ v : DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      (D.out : GL (Fin 2) ℚ)⁻¹, (nebentypusWeight χ D v : ℂ) • (f ∣[k] rightCosetRep D v) := (rfl)

/-- The pointwise value of the twisted slash sum: the weights scale the slashed values one by
one, so the scalar sits inside the sum and outside the evaluation. -/
lemma twistedHeckeSlashSum_apply (f : ℍ → ℂ) (τ : ℍ) : twistedHeckeSlashSum k χ D f τ =
    ∑ v : DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      (D.out : GL (Fin 2) ℚ)⁻¹, (nebentypusWeight χ D v : ℂ) • (f ∣[k] rightCosetRep D v) τ := by
  simp [twistedHeckeSlashSum]

/-- The twisted slash sum is additive in `f`. -/
@[simp]
lemma twistedHeckeSlashSum_add (f g : ℍ → ℂ) : twistedHeckeSlashSum k χ D (f + g) =
    twistedHeckeSlashSum k χ D f + twistedHeckeSlashSum k χ D g := by
  simp [twistedHeckeSlashSum, smul_add, Finset.sum_add_distrib]

/-- The twisted slash sum kills the zero function. -/
@[simp]
lemma twistedHeckeSlashSum_zero : twistedHeckeSlashSum k χ D 0 = 0 := by
  rw [twistedHeckeSlashSum]
  exact Finset.sum_eq_zero fun v _ ↦ by rw [SlashAction.zero_slash k (rightCosetRep D v), smul_zero]

/-- **The twisted slash sum is homogeneous in `f`.** With `twistedHeckeSlashSum_add` this gives
`ℂ`-linearity.

The positivity the scalar needs to pass through the slash is `det_rightCosetRep_pos_of_delta0`,
which holds outright at this level, so no hypothesis is asked of the caller.

Stated for a complex scalar only, where `heckeSlashSum_smul` admits any `α` acting on `ℂ`
through the scalar tower. The weights here are complex, so such an `α`-scalar would additionally
have to commute past them — `SMulCommClass ℂ α ℂ` does not follow from `DistribSMul α ℂ` plus
`IsScalarTower α ℂ ℂ` — and `ℂ` is the field the character space is a module over, so nothing
downstream asks for more. -/
@[simp]
lemma twistedHeckeSlashSum_smul (c : ℂ) (f : ℍ → ℂ) :
    twistedHeckeSlashSum k χ D (c • f) = c • twistedHeckeSlashSum k χ D f := by
  rw [twistedHeckeSlashSum, twistedHeckeSlashSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [ModularForm.rat_smul_slash_of_det_pos k (det_rightCosetRep_pos_of_delta0 D v) f c, smul_comm]

/-- **The twisted slash sum as a `ℂ`-linear endomorphism of `ℍ → ℂ`.** Bundling it as a
`Module.End ℂ` is what lets a downstream construction consume the operator directly, instead of
re-bundling this map and re-proving its linearity; the two fields are exactly
`twistedHeckeSlashSum_add` and `twistedHeckeSlashSum_smul`.

⚠ This is an endomorphism of *all* functions `ℍ → ℂ`, not of the character space
`modFormCharSpace k χ`. That the twisted sum is well defined on, and preserves, that subspace is
the pay-off of the weighting, and — as everywhere in this file — it is not proved here. -/
noncomputable def twistedHeckeSlashSumEnd : Module.End ℂ (ℍ → ℂ) where
  toFun := twistedHeckeSlashSum k χ D
  map_add' := twistedHeckeSlashSum_add k χ D
  map_smul' c f := twistedHeckeSlashSum_smul k χ D c f

/-- The endomorphism is `twistedHeckeSlashSum` on underlying functions. This characterises it
directly, without exposing the bundling. -/
@[simp] lemma coe_twistedHeckeSlashSumEnd :
    ⇑(twistedHeckeSlashSumEnd k χ D) = twistedHeckeSlashSum k χ D := (rfl)

end HeckeRing.GL2

end
