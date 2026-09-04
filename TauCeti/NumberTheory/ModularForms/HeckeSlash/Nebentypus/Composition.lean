/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Composition
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CharRing
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Independence

/-!
# The composite of two nebentypus-twisted slash sums

`HeckeSlash/Composition.lean` computes the composite of two *unweighted* slash sums, first over the
representatives they are defined with and then over free families, and collapses it onto a single
double coset. This file is the weighted counterpart of that development, up to and including the
operator statement: for a single pair of double cosets whose product set is a third, the twisted
operators of `D₁` and `D₂` compose to the operator of `D₃` on the character space. It then reads
that operator statement at the ring level, on basis elements, through the extension of
`Nebentypus/CharRing.lean`.

⚠ That is a *generator-level* statement, and it is **not** the multiplicativity
`HeckeSlash/Nebentypus/Ring.lean` records as missing. That gap is about
`twistedHeckeSlashRingLinearMap : 𝕋 … →ₗ[ℤ] Module.End ℂ (ℍ → ℂ)`, over arbitrary elements of the
Hecke ring and on all of `ℍ → ℂ`; this file proves only the single-double-coset case, only on
`functionCharSpace k χ`, and only under the per-triple hypotheses `hD₃` and `hinj₃`. That map is
untouched here and remains merely `ℤ`-linear. As in the untwisted file, the general
multiplicity-weighted composite `∑_D m(D₁, D₂; D) · T_D` — and with it the ring homomorphism
`𝕋 → Module.End` — is not proved here. Its two counting ingredients are now available:
`DoubleCoset.card_pairs_mem_rightCoset_eq_multiplicity` is the left/right handedness
reconciliation that `DoubleCoset.multiplicity` requires, and
`DoubleCoset.card_pairs_mem_rightCoset_congr` the count that each right coset of a fixed `D` is
hit by the same number of pairs. What is missing is the assembly, together with the twisted
weights it has to carry.

## Why the weights multiply, and why that is the whole point

`delta0NebentypusChar N χ` is a `MonoidHom` on `Δ₀(N)`, so the weight of a product of
representatives is the product of their weights. The composite of the two twisted sums is
therefore a sum over *products* `a_v b_w` weighted by the character of that product — exactly the
shape a single twisted sum over a third double coset has, which is what makes the collapse
possible. Changing representatives changes the weights attached to them, so that collapse needs
genuine representative-independence; that is `Nebentypus/Independence.lean`, and this file consumes
it.

## Where the positivity hypothesis comes from

Unlike the unweighted statements, the weighted ones carry `0 < det x`: the weight has to pass
through the slash by `x`, which is `ModularForm.rat_smul_slash_of_det_pos`. No caller is
inconvenienced — over the chosen representatives it is `det_rightCosetRep_pos_of_delta0`, and over
a free family it follows from the `Δ₀(N)` membership those statements already require.

## Why the operator lives on the character space

`twistedHeckeSlashSumEnd` is an endomorphism of *all* of `ℍ → ℂ`, and on that carrier the
multiplicativity below is simply false: the underlying identity needs `f` to be a `χ`-eigenfunction.
`functionCharSpace` is an invariant subspace, by `twistedHeckeSlashSum_mem_functionCharSpace`, so
the operator restricts to it — and there the operators do multiply. This mirrors the untwisted
development, which states its operator-level results on `ModularForm`/`CuspForm` for the same
reason: that is the carrier on which the hypothesis comes for free.

## Main definitions

This file introduces no definitions; the extension it reads the composition theorem through,
`twistedHeckeSlashRingCharLinearMap`, is defined in `Nebentypus/CharRing.lean`.

## Main results

* `HeckeRing.GL2.twistedHeckeSlashSum_slash`: slashing a twisted sum multiplies the
  representatives on the right, the weights riding along unchanged.
* `HeckeRing.GL2.twistedHeckeSlashSum_twistedHeckeSlashSum`: the composite of two twisted sums, as
  a double sum over products of representatives weighted by the character of the product.
* `HeckeRing.GL2.twistedHeckeSlashSum_twistedHeckeSlashSum_eq_sum_of_rightCosets`: the same
  composite over *any* families of representatives of the right cosets.
* `HeckeRing.GL2.twistedHeckeSlashSum_twistedHeckeSlashSum_eq_twistedHeckeSlashSum`: the collapse
  onto a single twisted sum, when the product set is one double coset and the products meet each
  of its right cosets once.
* `HeckeRing.GL2.twistedHeckeSlashSumCharEnd_mul_of_doubleCoset_eq_mul`: the pay-off — the twisted
  Hecke operators multiply.
* `HeckeRing.GL2.twistedHeckeSlashRingCharLinearMap_mul_single_single`: the ring-level reading of
  that pay-off — a **conditional anti-multiplicativity identity on basis elements**. Under the
  same collapse and injectivity hypotheses, the image of `single D₁ 1 * single D₂ 1` is the
  composite of the images *in the opposite order*. It is not a multiplicative action of the Hecke
  ring: basis elements only, under those hypotheses, and no ring homomorphism follows.

## Provenance

`twistedHeckeSlashRingCharLinearMap_mul_single_single` is adapted from the same project's
`twistedHeckeSumFunction_mul` (line 917), with two departures: the source proves multiplicativity
for arbitrary ring elements, reaching it through its own fibre-counting chain (lines 601-801,
which this repository does not carry), so what is stated here is the basis-element form the
generator-level theorem above supports, with the collapse hypotheses explicit; and the statement
shape follows `main`'s own untwisted
`heckeSlashGamma1RingModularFormLinearMap_mul_single_single` (`HeckeSlash/Composition.lean`).

The weight-multiplication that `twistedHeckeSlashSum_twistedHeckeSlashSum` turns on is the content
of `delta0NebentypusWeight_mul_eq_tripleDelta` (line 478) in the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean`, Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`). It is not
ported: with `Delta0UpperUnit` a `MonoidHom` — and hence `delta0NebentypusChar` one too — it is
`map_mul`, so it appears inline in the proof rather than as a declaration. That is the same
substitution which removed the source's `delta0UpperUnit_mul` and `delta0IntegralMatrix_mul` from
the invariance rung.

`twistedHeckeSlashSum_slash` has no counterpart in the source to adapt: it is the weighted
analogue of this repository's own `heckeSlashSum_slash`. AINTLIB reaches the same effect through
`twistedHeckeSlashGen_slash_distrib` (`:399`), which sits inside the adjugate-and-correction block
that the campaign routes around because this repository's substrate supersedes it.

`twistedHeckeSlashSumCharEnd_mul_of_doubleCoset_eq_mul` is the source's payoff
`twistedHeckeSlashGen_comp` (`:801`) — the source's `twistedHeckeSlashGen` is this repository's
`twistedHeckeSlashSum`. One hypothesis is deliberately **not** reproduced: the source assumes the
two Hecke-ring generators commute, because it states the payoff at ring level where their product
order is ambiguous. Stated at operator level the order is fixed by the statement — `Module.End`
multiplies by composition, so `D₁` acts first — exactly as the untwisted
`heckeSlashGamma1ModularFormEnd_mul_of_doubleCoset_eq_mul` does, and the hypothesis has nothing
left to do.

⚠ Not adapted, so that the source line numbers are not read as a wider claim:
`twisted_weighted_slash_product_eq` (`:494`) is a per-pair step that carries a summand into a third
double coset under an assumed twisted invariance of `f`; the route here goes through
representative-independence instead. The source's fibre block (`:629`, `:661`, `:710`) is not
adapted either — that bookkeeping is already on main, untwisted and more general, in
`HeckeSlash/Composition.lean` with the `HeckeRing/Multiplicity` module.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4: the displayed computation preceding Proposition 3.37 is the composite below.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm Pointwise HeckeCosetModule

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) [NeZero N]

-- The enumeration `∑` needs. `HeckeSlash/Composition.lean` does exactly this for the unweighted
-- sums, and it is what `Basic.lean`'s own `local instance` resolves to, so the `∑`s here and the
-- ones `twistedHeckeSlashSum_def` unfolds to are the same term. Declaring a bespoke instance
-- instead would need one per section, and the second would be auto-named with an underscore.
attribute [local instance] Fintype.ofFinite

section Chosen

variable (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

/-- **Slashing a twisted slash sum multiplies the representatives on the right**, the weights
riding along unchanged. The weighted counterpart of `heckeSlashSum_slash`, which needs no
hypothesis at all; here `0 < det x` is what lets each weight pass through the slash by `x`. -/
theorem twistedHeckeSlashSum_slash (f : ℍ → ℂ) {x : GL (Fin 2) ℚ}
    (hx : 0 < (x : Matrix (Fin 2) (Fin 2) ℚ).det) :
    twistedHeckeSlashSum k χ D f ∣[k] x =
      ∑ v, (nebentypusWeight χ D v : ℂ) • (f ∣[k] (rightCosetRep D v * x)) := by
  rw [twistedHeckeSlashSum_def, SlashAction.sum_slash]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [ModularForm.rat_smul_slash_of_det_pos k hx _ _,
    ← SlashAction.slash_mul k (rightCosetRep D v) x f]

end Chosen

section Composite

variable (D₁ D₂ : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

/-- **The composite of two twisted slash sums**, over the representatives they are defined with,
for an arbitrary `f : ℍ → ℂ`.

The weight on the summand at `(v, w)` is the character of the *product* `a_v b_w`, because
`delta0NebentypusChar` is a `MonoidHom` and the two weights therefore multiply. That is what makes
this a candidate for collapsing onto a single twisted sum over a third double coset. That collapse
needs twisted representative-independence, so it is not available at this point in the file; it is
`twistedHeckeSlashSum_twistedHeckeSlashSum_eq_twistedHeckeSlashSum` in the `Free` section below. -/
theorem twistedHeckeSlashSum_twistedHeckeSlashSum (f : ℍ → ℂ) :
    twistedHeckeSlashSum k χ D₂ (twistedHeckeSlashSum k χ D₁ f) =
      ∑ v, ∑ w, (delta0NebentypusChar N χ
          ⟨rightCosetRep D₁ v * rightCosetRep D₂ w,
            mul_mem (rightCosetRep_mem_Delta0 D₁ v) (rightCosetRep_mem_Delta0 D₂ w)⟩ : ℂ) •
        (f ∣[k] (rightCosetRep D₁ v * rightCosetRep D₂ w)) := by
  rw [twistedHeckeSlashSum_def k χ D₂, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [twistedHeckeSlashSum_slash k χ D₁ f (det_rightCosetRep_pos_of_delta0 D₂ w),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  -- The two weights multiply because `delta0NebentypusChar` is a `MonoidHom` on `Δ₀(N)`, and
  -- `map_mul` needs its argument as a product of bundled elements rather than the single bundled
  -- product the statement carries. `MulMemClass.mk_mul_mk` is the submonoid API for that step; it
  -- holds by `rfl`, but naming it keeps the proof independent of how `Δ₀(N)`'s multiplication is
  -- built, which an inline `rfl` here would silently depend on.
  rw [smul_smul, nebentypusWeight_def, nebentypusWeight_def, ← MulMemClass.mk_mul_mk,
    map_mul, Units.val_mul, mul_comm]

end Composite

section Free

variable (D₁ D₂ : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))
  {ι κ : Type*}
  (a : ι → GL (Fin 2) ℚ) (b : κ → GL (Fin 2) ℚ)
  (hcover₁ : doubleCoset (D₁.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
    ((Gamma0 N).map (mapGL ℚ)) =
    ⋃ i, MulOpposite.op (a i) • (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) :
      Set (GL (Fin 2) ℚ)))
  (hinj₁ : Function.Injective fun i ↦ MulOpposite.op (a i) •
    (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)))
  (hcover₂ : doubleCoset (D₂.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
    ((Gamma0 N).map (mapGL ℚ)) =
    ⋃ j, MulOpposite.op (b j) • (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) :
      Set (GL (Fin 2) ℚ)))
  (hinj₂ : Function.Injective fun j ↦ MulOpposite.op (b j) •
    (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)))

include hcover₁ hinj₁ hcover₂ hinj₂ in
/-- **The multiplicativity of the twisted slash sum**, over any families of representatives. For a
`χ`-eigenfunction `f` and families `(aᵢ)`, `(bⱼ)` of representatives of the right cosets of the two
double cosets,

`twistedHeckeSlashSum k χ D₂ (twistedHeckeSlashSum k χ D₁ f) = ∑_{i,j} χ'(aᵢ bⱼ) • (f ∣[k] aᵢ bⱼ)`,

writing `χ'` for `delta0NebentypusChar N χ`: the summand at `(i, j)` is weighted by the character of
the *product*.

The weighted counterpart of `heckeSlashSum_heckeSlashSum_eq_sum_of_rightCosets`, and the free-family
form of `twistedHeckeSlashSum_twistedHeckeSlashSum` above. The eigenfunction property is used twice,
exactly as invariance is there: once to evaluate the inner sum on `(aᵢ)`, and once — through
`twistedHeckeSlashSum_mem_functionCharSpace` — to know the inner sum is itself a `χ`-eigenfunction,
which is what lets the outer sum be evaluated on `(bⱼ)`.

The weights multiply because `delta0NebentypusChar` is a `MonoidHom`, and `ℂ` is commutative, so the
two factors combine into the character of the product regardless of the order they are met in. -/
theorem twistedHeckeSlashSum_twistedHeckeSlashSum_eq_sum_of_rightCosets [Fintype ι] [Fintype κ]
    (f : ℍ → ℂ)
    (hf : f ∈ functionCharSpace k χ) :
    twistedHeckeSlashSum k χ D₂ (twistedHeckeSlashSum k χ D₁ f) =
      ∑ i, ∑ j, (delta0NebentypusChar N χ ⟨a i * b j,
          mul_mem (mem_Delta0_of_cover D₁ hcover₁ i)
            (mem_Delta0_of_cover D₂ hcover₂ j)⟩ : ℂ) • (f ∣[k] (a i * b j)) := by
  rw [twistedHeckeSlashSum_eq_sum_of_rightCosets k χ D₂ b hcover₂ hinj₂ _
      (twistedHeckeSlashSum_mem_functionCharSpace k χ D₁ f hf), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [twistedHeckeSlashSum_eq_sum_of_rightCosets k χ D₁ a hcover₁ hinj₁ f hf,
    SlashAction.sum_slash, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ModularForm.rat_smul_slash_of_det_pos k
      (posDetInt_le_glpos 2 (Delta0_le_posDetInt N (mem_Delta0_of_cover D₂ hcover₂ j))) _ _,
    ← SlashAction.slash_mul k (a i) (b j) f, smul_smul, ← MulMemClass.mk_mul_mk, map_mul,
    Units.val_mul, mul_comm]

variable [Finite ι] [Finite κ]
  (D₃ : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

include hcover₁ hinj₁ hcover₂ hinj₂ in
/-- **The composite of two twisted slash sums is the twisted slash sum of a single double coset**,
when the product set is that coset and the products `aᵢ bⱼ` meet each of its right cosets exactly
once.

This is the collapse, for a `χ`-eigenfunction `f` — the identity is false without `hf`, as the
module docstring records. The weighted counterpart of
`heckeSlashSum_heckeSlashSum_eq_heckeSlashSum`, and its two hypotheses play the same roles: `hD₃`
says the product set is the single coset `D₃`, and `hinj₃` says the products have no right-coset
collisions. This does not identify `hinj₃` with the left-representative count used by
`DoubleCoset.multiplicity`. The covering half that
`twistedHeckeSlashSum_eq_sum_of_rightCosets` would otherwise need is automatic, by
`doubleCoset_mul_doubleCoset_eq_iUnion_rightCosets`.

The products lie in `Δ₀(N)` because each factor does and `Δ₀(N)` is a submonoid, which is what lets
the twisting character be applied to them. -/
theorem twistedHeckeSlashSum_twistedHeckeSlashSum_eq_twistedHeckeSlashSum
    (hD₃ : doubleCoset (D₃.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) =
      doubleCoset (D₁.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
          ((Gamma0 N).map (mapGL ℚ)) *
        doubleCoset (D₂.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
          ((Gamma0 N).map (mapGL ℚ)))
    (hinj₃ : Function.Injective fun p : ι × κ ↦ MulOpposite.op (a p.1 * b p.2) •
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)))
    (f : ℍ → ℂ) (hf : f ∈ functionCharSpace k χ) :
    twistedHeckeSlashSum k χ D₂ (twistedHeckeSlashSum k χ D₁ f) =
      twistedHeckeSlashSum k χ D₃ f := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
  rw [twistedHeckeSlashSum_eq_sum_of_rightCosets k χ D₃ (fun p : ι × κ ↦ a p.1 * b p.2)
      (hD₃.trans (doubleCoset_mul_doubleCoset_eq_iUnion_rightCosets a b hcover₁ hcover₂))
      hinj₃ f hf,
    twistedHeckeSlashSum_twistedHeckeSlashSum_eq_sum_of_rightCosets k χ D₁ D₂ a b
      hcover₁ hinj₁ hcover₂ hinj₂ f hf,
    Fintype.sum_prod_type]

include hcover₁ hinj₁ hcover₂ hinj₂ in
/-- **The twisted Hecke operators multiply.** On the character space, and when the product set is
the single double coset `D₃` with no right-coset collisions among the products, the composite of
the operators of `D₁` and `D₂` is the operator of `D₃`.

This is the generator-level input that a multiplicativity proof for
`twistedHeckeSlashRingLinearMap` would consume; it does not itself close that gap, which concerns
arbitrary Hecke-ring elements on all of `ℍ → ℂ`. It is the weighted counterpart of
`heckeSlashGamma1ModularFormEnd_mul_of_doubleCoset_eq_mul`, and it is stated on the character space
for the same reason that one is stated on `ModularForm`: that is the carrier on which the
hypothesis the underlying identity needs — here `f ∈ functionCharSpace`, there `Γ₁`-invariance —
comes for free.

As there, `Module.End` multiplies by composition, so `D₁` acts first on the right-hand side of the
underlying identity; that is the order recorded here. The source states this with a hypothesis that
the two Hecke-ring generators commute; no such hypothesis is needed once the order is fixed by the
statement. -/
theorem twistedHeckeSlashSumCharEnd_mul_of_doubleCoset_eq_mul
    (hD₃ : doubleCoset (D₃.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) =
      doubleCoset (D₁.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
          ((Gamma0 N).map (mapGL ℚ)) *
        doubleCoset (D₂.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
          ((Gamma0 N).map (mapGL ℚ)))
    (hinj₃ : Function.Injective fun p : ι × κ ↦ MulOpposite.op (a p.1 * b p.2) •
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ))) :
    twistedHeckeSlashSumCharEnd k χ D₂ * twistedHeckeSlashSumCharEnd k χ D₁ =
      twistedHeckeSlashSumCharEnd k χ D₃ := by
  ext f x
  have := congrFun (twistedHeckeSlashSum_twistedHeckeSlashSum_eq_twistedHeckeSlashSum k χ D₁ D₂
    a b hcover₁ hinj₁ hcover₂ hinj₂ D₃ hD₃ hinj₃ f f.2) x
  simpa [Module.End.mul_apply] using this

include hcover₁ hinj₁ hcover₂ hinj₂ in
/-- **A conditional anti-multiplicativity identity on basis elements.** When the product of the two
double cosets is again a single double coset with no right-coset collisions, the image of
`single D₁ 1 * single D₂ 1` is the composite of the images in the opposite order. Stated for basis
elements only, under those hypotheses; this is not a multiplicative action of the Hecke ring, and
no ring homomorphism follows from it.

The ring-level reading of `twistedHeckeSlashSumCharEnd_mul_of_doubleCoset_eq_mul` above: the two
criteria line up, one on each side, with `HeckeCosetModule.mul_single_single_of_mulMap_eq`
supplying the product in the Hecke ring and the composition theorem supplying it in `Module.End`.

`Module.End` multiplies by composition and the slash acts on the right, so the basis element `D₁`
of the *left* factor is the operator applied *first* — the map is an anti-homomorphism on these
elements, matching `heckeSlashGamma1RingModularFormLinearMap_mul_single_single` for the untwisted
`Γ₁(N)` operators. -/
theorem twistedHeckeSlashRingCharLinearMap_mul_single_single
    (hmulMap : ∀ p, HeckeCoset.mulMap ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) D₁.rep D₂.rep p = D₃)
    (hmul : multiplicity ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) (D₁.rep : GL (Fin 2) ℚ) (D₂.rep : GL (Fin 2) ℚ)
      (D₃.rep : GL (Fin 2) ℚ) ≤ 1)
    (hD₃ : doubleCoset (D₃.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) =
      doubleCoset (D₁.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
          ((Gamma0 N).map (mapGL ℚ)) *
        doubleCoset (D₂.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
          ((Gamma0 N).map (mapGL ℚ)))
    (hinj₃ : Function.Injective fun p : ι × κ ↦ MulOpposite.op (a p.1 * b p.2) •
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ))) :
    twistedHeckeSlashRingCharLinearMap k χ
        (HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1) =
      twistedHeckeSlashRingCharLinearMap k χ (HeckeCosetModule.single ℤ D₂ 1) *
        twistedHeckeSlashRingCharLinearMap k χ (HeckeCosetModule.single ℤ D₁ 1) := by
  have hprod : HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1
      = HeckeCosetModule.single ℤ D₃ 1 :=
    HeckeCosetModule.mul_single_single_of_mulMap_eq ℤ D₁ D₂ D₃ hmulMap hmul
  rw [hprod, twistedHeckeSlashRingCharLinearMap_single, twistedHeckeSlashRingCharLinearMap_single,
    twistedHeckeSlashRingCharLinearMap_single, one_smul, one_smul, one_smul]
  exact (twistedHeckeSlashSumCharEnd_mul_of_doubleCoset_eq_mul k χ D₁ D₂ a b
    hcover₁ hinj₁ hcover₂ hinj₂ D₃ hD₃ hinj₃).symm

end Free

end HeckeRing.GL2

end
