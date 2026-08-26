/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma1

/-!
# Composing the slash sums of two double cosets

`HeckeSlash/Basic.lean` attaches to a double coset `Γ₁ δ Γ₂ = ⊔ᵥ Γ₁ aᵥ` the slash sum
`f ∣[Γ₁ δ Γ₂]ₖ = ∑ᵥ f ∣[k] aᵥ`, and `HeckeSlash/Invariance.lean` shows the result is
`Γ₂`-invariant, so a second double coset `Γ₂ δ₂ Γ₃` may be applied to it. This file computes that
composite: it is the double sum over the products of the two families of representatives,

`(f ∣[Γ₁ δ₁ Γ₂]ₖ) ∣[Γ₂ δ₂ Γ₃]ₖ = ∑_{i, j} f ∣[k] (aᵢ bⱼ)`,

which is the multiplicative half of Shimura's §3.4 and the engine behind his Proposition 3.37.
`HeckeSlash/Ring.lean` and `HeckeSlash/CuspRing.lean` both record that its absence is what
confines the action of the abstract Hecke ring on `M_k(Γ₁(N))` and `S_k(Γ₁(N))` to a `ℤ`-linear
map rather than a ring homomorphism.

## The two statements, and what each costs

The identity above is proved twice, because two different things are being asserted.

*With the chosen representatives* (`heckeSlashSum_heckeSlashSum`) it is pure bookkeeping and
needs no hypothesis on `f` at all: slashing distributes over a finite sum
(`SlashAction.sum_slash`) and `f ∣[k] (a b) = (f ∣[k] a) ∣[k] b` is `SlashAction.slash_mul`.

*With arbitrary representatives* (`heckeSlashSum_heckeSlashSum_eq_sum_of_rightCosets`) it needs
`f` to be `Γ₁`-invariant, twice over: once so that the inner sum may be read off the family
`(aᵢ)` (`heckeSlashSum_eq_sum_of_rightCosets`), and once more because the *outer* sum is read
off `(bⱼ)`, which requires the inner sum to be `Γ₂`-invariant — that is
`heckeSlashSum_slash_invariant`, and it is the only place the two flanking groups have to be
matched.

Which right cosets the products `aᵢ bⱼ` run over is a set-level question with no slash action in
it, so it is answered where the rest of the double-coset vocabulary lives: they cover the
**product set** `Γ₁ δ₁ Γ₂ · Γ₂ δ₂ Γ₃`, by
`DoubleCoset.doubleCoset_mul_doubleCoset_eq_iUnion_rightCosets` (`HeckeRing/Basic.lean`). They do
so with repetition, which is why the criterion below has to be told separately that the cosets
are distinct. These right-coset collision counts are not identified here with
`DoubleCoset.multiplicity`, which is defined using left-coset representatives.

## What this does and does not give

Putting these together gives the criterion `heckeSlashSum_heckeSlashSum_eq_heckeSlashSum`:
if the product set is a *single* double coset `Γ₁ δ₃ Γ₃` and the pairs `(i, j)` do meet each of
its right cosets exactly once, then the composite operator is the operator of `Γ₁ δ₃ Γ₃`. At
`Γ₁ = Γ₂ = Γ₃ = Γ₁(N)` this is `heckeSlashGamma1ModularFormEnd_mul_of_doubleCoset_eq_mul` and
its cusp-form companion. The criterion is formally analogous to the ring-side
single-basis-element criterion `HeckeCosetModule.mul_single_single_of_mulMap_eq`, but no
identification with that criterion is made here.

⚠ The general multiplicity-weighted statement — the composite as `∑_D m(D₁, D₂; D) · T_D`, and
with it the ring homomorphism `𝕋 → Module.End` — is **not** proved here. It needs, beyond this
file, the count that each right coset of a fixed `D` is hit by the same number of pairs, and a
reconciliation of handedness: `DoubleCoset.multiplicity` counts pairs of *left*-coset
representatives while the slash sum runs over right cosets.

## Main results

* `HeckeRing.GL2.heckeSlashSum_slash`: slashing a slash sum by `x` multiplies each representative
  by `x` on the right.
* `HeckeRing.GL2.heckeSlashSum_heckeSlashSum`: the composite of two slash sums, over the chosen
  representatives, with no hypothesis on `f`.
* `HeckeRing.GL2.heckeSlashSum_heckeSlashSum_eq_sum_of_rightCosets`: **the multiplicativity of
  the slash sum**, over arbitrary representatives, for a `Γ₁`-invariant `f`.
* `HeckeRing.GL2.heckeSlashSum_heckeSlashSum_eq_heckeSlashSum`: the composite is the slash sum of
  a third double coset, when the product set is that coset and the pairs are in bijection with
  its right cosets.
* `HeckeRing.GL2.heckeSlashGamma1ModularFormEnd_mul_of_doubleCoset_eq_mul` and
  `HeckeRing.GL2.heckeSlashGamma1CuspFormEnd_mul_of_doubleCoset_eq_mul`: the same criterion for
  the Hecke operators of level `Γ₁(N)`, as an equation between endomorphisms.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4: (3.4.1) defines `f ∣[Γ₁ α Γ₂]ₖ`, and the displayed computation preceding Proposition 3.37
  is the composite below.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable (k : ℤ) {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ Γ₃ : Subgroup (GL (Fin 2) ℚ)}

attribute [local instance] Fintype.ofFinite

section Chosen

variable (D : HeckeCoset Δ Γ₁ Γ₂) [Finite (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)]

/-- **Slashing a slash sum multiplies the representatives on the right.** No hypothesis on `f` is
needed: the slash action is additive in the function and `f ∣[k] (a x) = (f ∣[k] a) ∣[k] x`. -/
theorem heckeSlashSum_slash (f : ℍ → ℂ) (x : GL (Fin 2) ℚ) :
    heckeSlashSum k D f ∣[k] x = ∑ v, f ∣[k] (rightCosetRep D v * x) := by
  rw [heckeSlashSum_def, SlashAction.sum_slash]
  exact Finset.sum_congr rfl fun v _ ↦ (SlashAction.slash_mul k (rightCosetRep D v) x f).symm

end Chosen

section Composite

variable (D₁ : HeckeCoset Δ Γ₁ Γ₂) (D₂ : HeckeCoset Δ Γ₂ Γ₃)
  [Finite (DecompQuotient Γ₂ Γ₁ (D₁.out : GL (Fin 2) ℚ)⁻¹)]
  [Finite (DecompQuotient Γ₃ Γ₂ (D₂.out : GL (Fin 2) ℚ)⁻¹)]

/-- **The composite of two slash sums, over the representatives they are defined with.** The
statement holds for an arbitrary `f : ℍ → ℂ`; it is the choice-dependent form of the identity,
and `heckeSlashSum_heckeSlashSum_eq_sum_of_rightCosets` is the statement that matters. -/
theorem heckeSlashSum_heckeSlashSum (f : ℍ → ℂ) :
    heckeSlashSum k D₂ (heckeSlashSum k D₁ f) =
      ∑ v, ∑ w, f ∣[k] (rightCosetRep D₁ v * rightCosetRep D₂ w) := by
  rw [heckeSlashSum_def k D₂, Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ ↦ heckeSlashSum_slash k D₁ f (rightCosetRep D₂ w)

end Composite

section Free

variable (D₁ : HeckeCoset Δ Γ₁ Γ₂) (D₂ : HeckeCoset Δ Γ₂ Γ₃)
  [Finite (DecompQuotient Γ₂ Γ₁ (D₁.out : GL (Fin 2) ℚ)⁻¹)]
  [Finite (DecompQuotient Γ₃ Γ₂ (D₂.out : GL (Fin 2) ℚ)⁻¹)]
  {ι κ : Type*} (a : ι → GL (Fin 2) ℚ) (b : κ → GL (Fin 2) ℚ)
  (hcover₁ : doubleCoset (D₁.out : GL (Fin 2) ℚ) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₂ =
    ⋃ i, MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)))
  (hinj₁ : Function.Injective fun i ↦ MulOpposite.op (a i) • (Γ₁ : Set (GL (Fin 2) ℚ)))
  (hcover₂ : doubleCoset (D₂.out : GL (Fin 2) ℚ) (Γ₂ : Set (GL (Fin 2) ℚ)) Γ₃ =
    ⋃ j, MulOpposite.op (b j) • (Γ₂ : Set (GL (Fin 2) ℚ)))
  (hinj₂ : Function.Injective fun j ↦ MulOpposite.op (b j) • (Γ₂ : Set (GL (Fin 2) ℚ)))

include hcover₁ hinj₁ hcover₂ hinj₂ in
/-- **The multiplicativity of the slash sum.** For a `Γ₁`-invariant `f`, and any families
`(aᵢ)`, `(bⱼ)` of representatives of the right cosets of `Γ₁ δ₁ Γ₂` and of `Γ₂ δ₂ Γ₃`,

`(f ∣[Γ₁ δ₁ Γ₂]ₖ) ∣[Γ₂ δ₂ Γ₃]ₖ = ∑_{i, j} f ∣[k] (aᵢ bⱼ)`.

This is the identity Shimura computes in §3.4 on the way to Proposition 3.37, and the engine the
ring homomorphism from the abstract Hecke ring is missing.

Invariance is used twice: once to evaluate the inner slash sum on the family `(aᵢ)`, and once —
through `heckeSlashSum_slash_invariant` — to know that the inner sum is `Γ₂`-invariant, which is
what lets the outer one be evaluated on `(bⱼ)`. -/
theorem heckeSlashSum_heckeSlashSum_eq_sum_of_rightCosets [Fintype ι] [Fintype κ] (f : ℍ → ℂ)
    (hf : ∀ γ ∈ Γ₁, f ∣[k] γ = f) :
    heckeSlashSum k D₂ (heckeSlashSum k D₁ f) = ∑ i, ∑ j, f ∣[k] (a i * b j) := by
  rw [heckeSlashSum_eq_sum_of_rightCosets k D₂ b hcover₂ hinj₂ _
      (fun γ hγ ↦ heckeSlashSum_slash_invariant k D₁ f hf hγ), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [heckeSlashSum_eq_sum_of_rightCosets k D₁ a hcover₁ hinj₁ f hf, SlashAction.sum_slash]
  exact Finset.sum_congr rfl fun i _ ↦ (SlashAction.slash_mul k (a i) (b j) f).symm

variable [Finite ι] [Finite κ] (D₃ : HeckeCoset Δ Γ₁ Γ₃)
  [Finite (DecompQuotient Γ₃ Γ₁ (D₃.out : GL (Fin 2) ℚ)⁻¹)]

include hcover₁ hinj₁ hcover₂ hinj₂ in
/-- **The composite is the operator of a single double coset**, when the product set
`Γ₁ δ₁ Γ₂ · Γ₂ δ₂ Γ₃` is that coset and the products `aᵢ bⱼ` meet each of its right cosets
exactly once.

The two hypotheses are formally analogous to those of
`HeckeCosetModule.mul_single_single_of_mulMap_eq`: `hD₃` says that the product set is the single
coset `D₃`, while `hinj₃` says that the products have no right-coset collisions. This does not
identify `hinj₃` with the left-representative count used by `DoubleCoset.multiplicity`. The
covering half of the hypothesis `heckeSlashSum_eq_sum_of_rightCosets` would otherwise need is
automatic, by `doubleCoset_mul_doubleCoset_eq_iUnion_rightCosets`. -/
theorem heckeSlashSum_heckeSlashSum_eq_heckeSlashSum
    (hD₃ : doubleCoset (D₃.out : GL (Fin 2) ℚ) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₃ =
      doubleCoset (D₁.out : GL (Fin 2) ℚ) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₂ *
        doubleCoset (D₂.out : GL (Fin 2) ℚ) (Γ₂ : Set (GL (Fin 2) ℚ)) Γ₃)
    (hinj₃ : Function.Injective
      fun p : ι × κ ↦ MulOpposite.op (a p.1 * b p.2) • (Γ₁ : Set (GL (Fin 2) ℚ)))
    (f : ℍ → ℂ) (hf : ∀ γ ∈ Γ₁, f ∣[k] γ = f) :
    heckeSlashSum k D₂ (heckeSlashSum k D₁ f) = heckeSlashSum k D₃ f := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
  rw [heckeSlashSum_eq_sum_of_rightCosets k D₃ (fun p : ι × κ ↦ a p.1 * b p.2)
      (hD₃.trans (doubleCoset_mul_doubleCoset_eq_iUnion_rightCosets a b hcover₁ hcover₂))
      hinj₃ f hf,
    heckeSlashSum_heckeSlashSum_eq_sum_of_rightCosets k D₁ D₂ a b hcover₁ hinj₁ hcover₂ hinj₂ f hf,
    Fintype.sum_prod_type]

end Free

section Gamma1

variable {N : ℕ} [NeZero N]
  (D₁ D₂ D₃ : HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)))
  {ι κ : Type*} [Finite ι] [Finite κ] (a : ι → GL (Fin 2) ℚ) (b : κ → GL (Fin 2) ℚ)
  (hcover₁ : doubleCoset (D₁.out : GL (Fin 2) ℚ) ((Gamma1 N).map (mapGL ℚ) :
      Set (GL (Fin 2) ℚ)) ((Gamma1 N).map (mapGL ℚ)) =
    ⋃ i, MulOpposite.op (a i) • ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
  (hinj₁ : Function.Injective
    fun i ↦ MulOpposite.op (a i) • ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
  (hcover₂ : doubleCoset (D₂.out : GL (Fin 2) ℚ) ((Gamma1 N).map (mapGL ℚ) :
      Set (GL (Fin 2) ℚ)) ((Gamma1 N).map (mapGL ℚ)) =
    ⋃ j, MulOpposite.op (b j) • ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
  (hinj₂ : Function.Injective
    fun j ↦ MulOpposite.op (b j) • ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
  (hD₃ : doubleCoset (D₃.out : GL (Fin 2) ℚ) ((Gamma1 N).map (mapGL ℚ) :
      Set (GL (Fin 2) ℚ)) ((Gamma1 N).map (mapGL ℚ)) =
    doubleCoset (D₁.out : GL (Fin 2) ℚ) ((Gamma1 N).map (mapGL ℚ) :
        Set (GL (Fin 2) ℚ)) ((Gamma1 N).map (mapGL ℚ)) *
      doubleCoset (D₂.out : GL (Fin 2) ℚ) ((Gamma1 N).map (mapGL ℚ) :
        Set (GL (Fin 2) ℚ)) ((Gamma1 N).map (mapGL ℚ)))
  (hinj₃ : Function.Injective fun p : ι × κ ↦
    MulOpposite.op (a p.1 * b p.2) • ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))

include hcover₁ hinj₁ hcover₂ hinj₂ hD₃ hinj₃

/-- **The Hecke operators of level `Γ₁(N)` multiply**, when the product set is the single double
coset `D₃` and the products of the chosen right-coset representatives have no collisions.

`Module.End` multiplies by composition, so `D₁` acts first on the right-hand side of the
underlying identity `(f ∣ D₁) ∣ D₂ = f ∣ D₃`; that is the order recorded here. -/
theorem heckeSlashGamma1ModularFormEnd_mul_of_doubleCoset_eq_mul :
    heckeSlashGamma1ModularFormEnd k D₂ * heckeSlashGamma1ModularFormEnd k D₁ =
      heckeSlashGamma1ModularFormEnd k D₃ := by
  ext f τ
  have hf : ∀ γ ∈ (Gamma1 N).map (mapGL ℚ), ⇑f ∣[k] γ = ⇑f := fun _ hγ ↦
    ModularForm.slash_eq_of_mem_map_mapGL
      (fun γ' hγ' ↦ SlashInvariantFormClass.slash_action_eq f γ' hγ') hγ
  have := heckeSlashSum_heckeSlashSum_eq_heckeSlashSum k D₁ D₂ a b hcover₁ hinj₁ hcover₂ hinj₂
    D₃ hD₃ hinj₃ ⇑f hf
  simpa [coe_heckeSlashGamma1ModularFormEnd] using congrFun this τ

/-- **The Hecke operators of level `Γ₁(N)` multiply on cusp forms**, when the product set is the
single double coset `D₃` and the products of the chosen right-coset representatives have no
collisions. -/
theorem heckeSlashGamma1CuspFormEnd_mul_of_doubleCoset_eq_mul :
    heckeSlashGamma1CuspFormEnd k D₂ * heckeSlashGamma1CuspFormEnd k D₁ =
      heckeSlashGamma1CuspFormEnd k D₃ := by
  ext f τ
  have hf : ∀ γ ∈ (Gamma1 N).map (mapGL ℚ), ⇑f ∣[k] γ = ⇑f := fun _ hγ ↦
    ModularForm.slash_eq_of_mem_map_mapGL
      (fun γ' hγ' ↦ SlashInvariantFormClass.slash_action_eq f γ' hγ') hγ
  have := heckeSlashSum_heckeSlashSum_eq_heckeSlashSum k D₁ D₂ a b hcover₁ hinj₁ hcover₂ hinj₂
    D₃ hD₃ hinj₃ ⇑f hf
  simpa [coe_heckeSlashGamma1CuspFormEnd] using congrFun this τ

end Gamma1

end HeckeRing.GL2

end
