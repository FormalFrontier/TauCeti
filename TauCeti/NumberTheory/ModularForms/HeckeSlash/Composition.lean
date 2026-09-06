/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.Multiplicity.Handedness
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.CuspRing
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Ring

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
are distinct. How often each right coset is met is counted by
`DoubleCoset.card_pairs_mem_rightCoset_eq_multiplicity`, which identifies that count with
`DoubleCoset.multiplicity`. Since the multiplicity counts *left*-coset representatives, the
identification inverts all three arguments and exchanges the two factors; the group-theoretic
content of it is a statement about the group alone, proved with the multiplicity API itself.

## What this does and does not give

Putting these together gives the criterion `heckeSlashSum_heckeSlashSum_eq_heckeSlashSum`:
if the product set is a *single* double coset `Γ₁ δ₃ Γ₃` and the pairs `(i, j)` do meet each of
its right cosets exactly once, then the composite operator is the operator of `Γ₁ δ₃ Γ₃`. At
`Γ₁ = Γ₂ = Γ₃ = Γ₁(N)` this is `heckeSlashGamma1ModularFormEnd_mul_of_doubleCoset_eq_mul` and
its cusp-form companion. The criterion is formally analogous to the ring-side
single-basis-element criterion `HeckeCosetModule.mul_single_single_of_mulMap_eq`, and the two
are identified here: `heckeSlashGamma1RingModularFormLinearMap_mul_single_single` and its
cusp-form companion apply both criteria at once, so the ring product of two basis elements maps
to the composite of their operators.

The general multiplicity-weighted statement — the composite as `∑_D m(D₁, D₂; D) · T_D` — is
`heckeSlashSum_heckeSlashSum_eq_sum_nsmul`, in the last section below. It partitions the pairs
`(v, w)` by the double coset their product lies in, which is what `pairCoset` names; the double
cosets met are the image of the finite type of pairs under that map, so no finiteness beyond
that of the two index types is needed. Its two counting ingredients are
`DoubleCoset.card_pairs_mem_rightCoset_eq_multiplicity`, which reconciles the handedness by
identifying the right-coset collision count with the multiplicity, and
`DoubleCoset.card_pairs_mem_rightCoset_congr`, which supplies the uniformity: each right coset
of a fixed `D` is met by the same number of pairs.

⚠ The ring homomorphism `𝕋 → Module.End` is still not built here, and the remaining gap is
wider than a change of notation. `HeckeCosetModule.structureConstants` weights `D` by
`DoubleCoset.multiplicity Γ₁ Γ₂ Γ₃ δ₁ δ₂ δ₃`, whereas the sum below weights it by
`DoubleCoset.multiplicity Γ₃ Γ₂ Γ₁ δ₂⁻¹ δ₁⁻¹ δ₃⁻¹` — the factors exchanged and all three
arguments inverted, which is what the right-coset indexing of a slash sum forces. **These are
not equal**, and no symmetry of `multiplicity` identifies them: the two counts run over
`Γ ⧸ (Γ ∩ gΓ'g⁻¹)` and `Γ ⧸ (Γ ∩ g⁻¹Γ'g)`, the two degrees of a double coset, and those
differ in general. Closing the gap needs an anti-involution rather than a rewriting of
coefficients; `HeckeRing/GLn/TransposeAntiInvolution.lean` supplies one at level `SLₙ(ℤ)`, and
it is what makes the Hecke ring commutative there (Shimura's Proposition 3.8).

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
* `HeckeRing.GL2.heckeSlashGamma1RingModularFormLinearMap_mul_single_single` and
  `HeckeRing.GL2.heckeSlashGamma1CuspRingLinearMap_mul_single_single`: the ring-level reading of
  those two — the Hecke ring acts multiplicatively on basis elements whose product is a single
  double coset. The map is an *anti*-homomorphism there, since `Module.End` composes.
* `HeckeRing.GL2.pairCoset`: the double coset `Γ₁ (aᵥ b_w) Γ₃` that a pair of right-coset
  representatives lands in — the map the double sum is fibred over.
* `HeckeRing.GL2.pairCoset_eq_iff`: a pair lies in the fibre over `D` exactly when the product
  of its two representatives lies in `D`'s double coset.
* `HeckeRing.GL2.card_pairs_pairCoset_rightCoset_eq_multiplicity`: each right coset of a double
  coset `D` is met by `m(D₁, D₂; D)` of the pairs, whichever right coset of `D` is chosen.
* `HeckeRing.GL2.heckeSlashSum_heckeSlashSum_eq_sum_nsmul`: **the multiplicity-weighted
  composite**, `(f ∣[Γ₁ δ₁ Γ₂]ₖ) ∣[Γ₂ δ₂ Γ₃]ₖ = ∑_D m(D₁, D₂; D) • (f ∣[Γ₁ δ₃ Γ₃]ₖ)`, for a
  `Γ₁`-invariant `f`.
* `HeckeRing.GL2.heckeSlashGamma1ModularFormEnd_mul_of_doubleCoset_eq_mul` and
  `HeckeRing.GL2.heckeSlashGamma1CuspFormEnd_mul_of_doubleCoset_eq_mul`: the same criterion for
  the Hecke operators of level `Γ₁(N)`, as an equation between endomorphisms.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4: (3.4.1) defines `f ∣[Γ₁ α Γ₂]ₖ`, and the displayed computation preceding Proposition 3.37
  is the composite below.

## Provenance

`heckeSlashSum_heckeSlashSum_eq_sum_nsmul` and its fibre argument follow the corresponding
result in the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0),
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
`LeanModularForms/HeckeRIngs/GL2/HeckeActionGeneral.lean`: `heckeSlash_gen_comp_sum_eq` and
`heckeSlash_gen_fiber_sum`. That version is stated for a single `HeckePair P` (so
`Γ₁ = Γ₂ = Γ₃`), indexed by *left* cosets through the adjugate anti-involution its
`HeckePairAction` supplies, and weighted by `Finsupp.sum` over Hecke-ring structure constants.
The version here is at a general Hecke triple, right-coset indexed as `heckeSlashSum` is, needs
no anti-involution or determinant hypothesis, and takes its coefficient from
`DoubleCoset.multiplicity`.
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
coset `D₃`, while `hinj₃` says that the products have no right-coset collisions. `hinj₃` is
left as the bare injectivity it is used as; the collision count it rules out is identified with
`DoubleCoset.multiplicity` by `DoubleCoset.card_pairs_mem_rightCoset_eq_multiplicity`. The
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

section Assembly

variable [IsHeckeTriple Δ Γ₁ Γ₂] [IsHeckeTriple Δ Γ₂ Γ₃]
  (D₁ : HeckeCoset Δ Γ₁ Γ₂) (D₂ : HeckeCoset Δ Γ₂ Γ₃)

/-- **The product `aᵥ b_w` of a right-coset representative of `D₁` and one of `D₂`, as an element
of `Δ`.** Each factor lies in the double coset of an element of `Δ`, hence in `Δ` itself by
`IsHeckeTriple.mem_of_mem_doubleCoset`, and a submonoid is closed under multiplication.

Membership in `Δ` is the point of the definition: it is what lets the product name an element of
`HeckeCoset Δ Γ₁ Γ₃`, which is how the double sum below is partitioned. -/
private noncomputable def pairRep (p : DecompQuotient Γ₂ Γ₁ (D₁.out : GL (Fin 2) ℚ)⁻¹ ×
    DecompQuotient Γ₃ Γ₂ (D₂.out : GL (Fin 2) ℚ)⁻¹) : Δ :=
  ⟨rightCosetRep D₁ p.1 * rightCosetRep D₂ p.2, mul_mem
    (IsHeckeTriple.mem_of_mem_doubleCoset (D₁.out).2 (rightCosetRep_mem_doubleCoset D₁ p.1))
    (IsHeckeTriple.mem_of_mem_doubleCoset (D₂.out).2 (rightCosetRep_mem_doubleCoset D₂ p.2))⟩

/-- The underlying matrix of `pairRep` is the product of the two right-coset
representatives. -/
private lemma coe_pairRep (p : DecompQuotient Γ₂ Γ₁ (D₁.out : GL (Fin 2) ℚ)⁻¹ ×
    DecompQuotient Γ₃ Γ₂ (D₂.out : GL (Fin 2) ℚ)⁻¹) :
    (pairRep D₁ D₂ p : GL (Fin 2) ℚ) = rightCosetRep D₁ p.1 * rightCosetRep D₂ p.2 := (rfl)

/-- **The double coset `Γ₁ (aᵥ b_w) Γ₃` a pair of representatives lands in.** This is the map the
double sum of `heckeSlashSum_heckeSlashSum` is fibred over. -/
noncomputable def pairCoset (p : DecompQuotient Γ₂ Γ₁ (D₁.out : GL (Fin 2) ℚ)⁻¹ ×
    DecompQuotient Γ₃ Γ₂ (D₂.out : GL (Fin 2) ℚ)⁻¹) : HeckeCoset Δ Γ₁ Γ₃ :=
  HeckeCoset.mk Γ₁ Γ₃ (pairRep D₁ D₂ p)

/-- `pairCoset` is the double coset of `pairRep`; `pairCoset_eq_iff` characterises it by
membership. -/
private lemma pairCoset_def (p : DecompQuotient Γ₂ Γ₁ (D₁.out : GL (Fin 2) ℚ)⁻¹ ×
    DecompQuotient Γ₃ Γ₂ (D₂.out : GL (Fin 2) ℚ)⁻¹) :
    pairCoset D₁ D₂ p = HeckeCoset.mk Γ₁ Γ₃ (pairRep D₁ D₂ p) := (rfl)

variable {D₁ D₂}
variable {D : HeckeCoset Δ Γ₁ Γ₃} {p : DecompQuotient Γ₂ Γ₁ (D₁.out : GL (Fin 2) ℚ)⁻¹ ×
  DecompQuotient Γ₃ Γ₂ (D₂.out : GL (Fin 2) ℚ)⁻¹}

/-- **`pairCoset` is characterised by membership**: a pair lies in the fibre over `D` exactly
when the product of its two representatives lies in the double coset of `D`. -/
@[simp] lemma pairCoset_eq_iff : pairCoset D₁ D₂ p = D ↔
    rightCosetRep D₁ p.1 * rightCosetRep D₂ p.2 ∈
      doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₃ := by
  constructor
  · intro h
    have hD := HeckeCoset.eq_iff.mp
      ((pairCoset_def D₁ D₂ p).symm.trans (h.trans (HeckeCoset.mk_rep D).symm))
    rw [HeckeCoset.rep_def, coe_pairRep] at hD
    exact hD ▸ mem_doubleCoset_self Γ₁ Γ₃ _
  · intro h
    rw [pairCoset_def, ← HeckeCoset.mk_rep D]
    refine HeckeCoset.eq_iff.mpr ?_
    rw [HeckeCoset.rep_def, coe_pairRep]
    exact doubleCoset_eq_of_mem h

/-- A pair whose product lies in one right coset `Γ₁ x` of a double coset is in the fibre of
`pairCoset` over that double coset: a right coset is contained in the double coset it
generates, and `x` generates `D`. -/
private lemma pairCoset_eq_of_mem_rightCoset {x : GL (Fin 2) ℚ}
    (hx : x ∈ doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₃)
    (hp : rightCosetRep D₁ p.1 * rightCosetRep D₂ p.2 ∈
      MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ))) :
    pairCoset D₁ D₂ p = D := by
  refine pairCoset_eq_iff.mpr ?_
  rw [← doubleCoset_eq_of_mem hx]
  exact mem_doubleCoset.mpr ⟨_, (mem_rightCoset_iff x).mp hp, 1, one_mem _, by group⟩

/-- **Each right coset of a double coset `D` is met by Shimura's multiplicity `m(D₁, D₂; D)`
many pairs**, whichever `x ∈ D` names that right coset: among the pairs lying over `D`, the
number whose product spans the right coset `Γ₁ x` does not depend on `x`. -/
lemma card_pairs_pairCoset_rightCoset_eq_multiplicity {x : GL (Fin 2) ℚ}
    (hx : x ∈ doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₃) :
    Nat.card {i : {q // pairCoset D₁ D₂ q = D} //
        MulOpposite.op (rightCosetRep D₁ i.1.1 * rightCosetRep D₂ i.1.2) •
            (Γ₁ : Set (GL (Fin 2) ℚ)) = MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ))} =
      DoubleCoset.multiplicity Γ₃ Γ₂ Γ₁ (D₂.out : GL (Fin 2) ℚ)⁻¹ (D₁.out : GL (Fin 2) ℚ)⁻¹
        (D.out : GL (Fin 2) ℚ)⁻¹ := by
  have hiff (y : GL (Fin 2) ℚ) :
      (MulOpposite.op y • (Γ₁ : Set (GL (Fin 2) ℚ)) =
          MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ))) ↔
        y ∈ MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ)) := by
    rw [rightCoset_eq_iff, mem_rightCoset_iff]
    exact ⟨fun h ↦ by simpa using inv_mem h, fun h ↦ by simpa using inv_mem h⟩
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtype (p := fun q ↦ pairCoset D₁ D₂ q = D)
      (q := fun q ↦ MulOpposite.op (rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2) •
        (Γ₁ : Set (GL (Fin 2) ℚ)) = MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ)))
      fun {q} hq ↦ pairCoset_eq_of_mem_rightCoset hx ((hiff _).mp hq)),
    ← card_pairs_mem_rightCoset_eq_multiplicity Γ₁ Γ₂ Γ₃ (D₁.out : GL (Fin 2) ℚ)
      (D₂.out : GL (Fin 2) ℚ) (D.out : GL (Fin 2) ℚ)]
  simp only [hiff, rightCosetRep_def, Set.coe_ofPred]
  exact card_pairs_mem_rightCoset_congr Γ₁ Γ₂ Γ₃ (D₁.out : GL (Fin 2) ℚ)
    (D₂.out : GL (Fin 2) ℚ) hx

variable (D₁ D₂)

open Classical in
/-- **The multiplicity-weighted composite**, and with it the general form of the composition law.
For a `Γ₁`-invariant `f`, the composite of the two slash sums is the sum, over the double cosets
met by the products `aᵥ b_w`, of Shimura's multiplicity times the slash sum of that coset:

`(f ∣[Γ₁ δ₁ Γ₂]ₖ) ∣[Γ₂ δ₂ Γ₃]ₖ = ∑_D m(D₁, D₂; D) • (f ∣[Γ₁ δ₃ Γ₃]ₖ)`.

`heckeSlashSum_heckeSlashSum_eq_heckeSlashSum` is the special case where the products meet a
single double coset and meet each of its right cosets exactly once.

This is a composition formula for the slash action, not yet the Hecke-ring homomorphism. Its
coefficient is `DoubleCoset.multiplicity Γ₃ Γ₂ Γ₁ δ₂⁻¹ δ₁⁻¹ δ₃⁻¹`, with the factors exchanged
and all three arguments inverted relative to `HeckeCosetModule.structureConstants`; as the
module docstring records, the two are not equal, and comparing them needs an anti-involution.

No finiteness is assumed beyond the two input Hecke triples. The double cosets met are the
image of a finite type under `pairCoset`, and the finiteness of each output coset's own
decomposition quotient — which `heckeSlashSum k D f` sums over — comes from the composite
triple `IsHeckeTriple Δ Γ₁ Γ₃`, which `IsHeckeTriple.trans` derives from the two given ones. -/
theorem heckeSlashSum_heckeSlashSum_eq_sum_nsmul
    (f : ℍ → ℂ) (hf : ∀ γ ∈ Γ₁, f ∣[k] γ = f) :
    letI : IsHeckeTriple Δ Γ₁ Γ₃ := IsHeckeTriple.trans (H₂ := Γ₂)
    heckeSlashSum k D₂ (heckeSlashSum k D₁ f) =
      ∑ D ∈ Finset.univ.image (pairCoset D₁ D₂),
        DoubleCoset.multiplicity Γ₃ Γ₂ Γ₁ (D₂.out : GL (Fin 2) ℚ)⁻¹ (D₁.out : GL (Fin 2) ℚ)⁻¹
          (D.out : GL (Fin 2) ℚ)⁻¹ • heckeSlashSum k D f := by
  -- the same composite triple the statement derives; `IsHeckeTriple.trans` cannot be an
  -- instance, since `Γ₂` does not occur in `IsHeckeTriple Δ Γ₁ Γ₃`, so it is named at both
  -- points rather than found by synthesis
  let _ : IsHeckeTriple Δ Γ₁ Γ₃ := IsHeckeTriple.trans (H₂ := Γ₂)
  rw [heckeSlashSum_heckeSlashSum, ← Fintype.sum_prod_type',
    ← Finset.sum_fiberwise_of_maps_to (g := pairCoset D₁ D₂)
      (fun p _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ p))]
  refine Finset.sum_congr rfl fun D _ ↦ ?_
  rw [Finset.sum_subtype (p := fun q ↦ pairCoset D₁ D₂ q = D)
    (Finset.univ.filter fun q ↦ pairCoset D₁ D₂ q = D) (fun q ↦ by simp)
    fun q ↦ f ∣[k] (rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2)]
  exact sum_slash_eq_nsmul_heckeSlashSum k D _ _ (fun i ↦ pairCoset_eq_iff.mp i.2)
    (fun _ hx ↦ card_pairs_pairCoset_rightCoset_eq_multiplicity hx) f hf

end Assembly

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

/-- **The Hecke ring acts multiplicatively on modular forms, where the product of two double
cosets is again a single double coset.** The modular-form half of the pair; see
`heckeSlashGamma1CuspRingLinearMap_mul_single_single` for cusp forms.

The two are parallel rather than one specialising the other: the operators live in
`Module.End ℂ (ModularForm ..)` and `Module.End ℂ (CuspForm ..)` respectively, so neither
equation transports to the other, and each is proved from its own composition theorem. -/
theorem heckeSlashGamma1RingModularFormLinearMap_mul_single_single
    (hmulMap : ∀ p, HeckeCoset.mulMap ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ)) D₁.rep D₂.rep p = D₃)
    (hmul : multiplicity ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
      (D₁.rep : GL (Fin 2) ℚ) (D₂.rep : GL (Fin 2) ℚ) (D₃.rep : GL (Fin 2) ℚ) ≤ 1) :
    heckeSlashGamma1RingModularFormLinearMap k
        (HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1) =
      heckeSlashGamma1RingModularFormLinearMap k (HeckeCosetModule.single ℤ D₂ 1) *
        heckeSlashGamma1RingModularFormLinearMap k (HeckeCosetModule.single ℤ D₁ 1) := by
  have hprod : HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1
      = HeckeCosetModule.single ℤ D₃ 1 :=
    HeckeCosetModule.mul_single_single_of_mulMap_eq ℤ D₁ D₂ D₃ hmulMap hmul
  rw [hprod, heckeSlashGamma1RingModularFormLinearMap_single,
    heckeSlashGamma1RingModularFormLinearMap_single,
    heckeSlashGamma1RingModularFormLinearMap_single, one_smul, one_smul, one_smul]
  exact (heckeSlashGamma1ModularFormEnd_mul_of_doubleCoset_eq_mul k D₁ D₂ D₃ a b
    hcover₁ hinj₁ hcover₂ hinj₂ hD₃ hinj₃).symm

/-- **The Hecke ring acts multiplicatively on cusp forms, where the product of two double cosets
is again a single double coset.** This is the ring-level reading of
`heckeSlashGamma1CuspFormEnd_mul_of_doubleCoset_eq_mul`: the two criteria line up, one on each
side, with `mul_single_single_of_mulMap_eq` supplying the product in the Hecke ring and the
composition theorem supplying it in `Module.End`.

Note the order. `Module.End` multiplies by composition and the slash acts on the right, so the
basis element `D₁` of the *left* factor becomes the operator applied *first*: the map is an
anti-homomorphism on these elements, not a homomorphism.

Full multiplicativity (Shimura, Proposition 3.37) is not available — it needs the structure
constants of a product that spreads over several double cosets with multiplicity, whereas both
criteria used here assume the product collapses to the single coset `D₃`. This lemma is the part
that is provable from what is on hand. -/
theorem heckeSlashGamma1CuspRingLinearMap_mul_single_single
    (hmulMap : ∀ p, HeckeCoset.mulMap ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ)) D₁.rep D₂.rep p = D₃)
    (hmul : multiplicity ((Gamma1 N).map (mapGL ℚ))
      ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
      (D₁.rep : GL (Fin 2) ℚ) (D₂.rep : GL (Fin 2) ℚ) (D₃.rep : GL (Fin 2) ℚ) ≤ 1) :
    heckeSlashGamma1CuspRingLinearMap k
        (HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1) =
      heckeSlashGamma1CuspRingLinearMap k (HeckeCosetModule.single ℤ D₂ 1) *
        heckeSlashGamma1CuspRingLinearMap k (HeckeCosetModule.single ℤ D₁ 1) := by
  have hprod : HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1
      = HeckeCosetModule.single ℤ D₃ 1 :=
    HeckeCosetModule.mul_single_single_of_mulMap_eq ℤ D₁ D₂ D₃ hmulMap hmul
  rw [hprod, heckeSlashGamma1CuspRingLinearMap_single,
    heckeSlashGamma1CuspRingLinearMap_single, heckeSlashGamma1CuspRingLinearMap_single,
    one_smul, one_smul, one_smul]
  exact (heckeSlashGamma1CuspFormEnd_mul_of_doubleCoset_eq_mul k D₁ D₂ D₃ a b
    hcover₁ hinj₁ hcover₂ hinj₂ hD₃ hinj₃).symm

end Gamma1

end HeckeRing.GL2

end
