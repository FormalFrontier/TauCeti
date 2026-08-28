/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PurelyInseparable.Exponent

/-!
# Embedding a purely inseparable extension into a field with enough roots

Let `M / K` be a purely inseparable extension of exponent at most `n`, so that
`x ↦ x ^ (p ^ n)` is a ring homomorphism `M →+* K` (`IsPurelyInseparable.iterateFrobenius`). If a
field `K'` over `K` contains `p ^ n`-th roots of the images of a generating set of `M`, then `M`
embeds into `K'` over `K`: the embedding is `ψ⁻¹ ∘ φ` for `φ` the Frobenius of `M` into `K` and
`ψ` the (injective) Frobenius of `K'`. Mathlib provides this embedding only into perfect fields
(`IsPurelyInseparable.instNonemptyAlgHomOfPerfectField`); the target that
normalization-finiteness needs, `k'(X_1, …, X_r)`, is not perfect.

The companion existence statement produces, for finitely many elements of a field, a finite
extension containing `n`-th roots of all of them.

## Main results

* `TauCeti.exists_finiteDimensional_forall_exists_pow_eq`: a finite extension of `F`
  containing `n`-th roots of finitely many given elements of `F`.
* `TauCeti.IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq`: the embedding of a
  purely inseparable extension of bounded exponent into any field over `K` containing
  `p ^ n`-th roots of the Frobenius images of a generating set.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`. The mathematics is the field-theoretic half of
the "some details omitted" sentence of Stacks 10.161.13 (tag 032O): there is a finite purely
inseparable `L' / K` and `q = p ^ e` with `L ⊂ L'(x^{1/q})`.
-/

public section

universe u

namespace TauCeti

/-- Source: Stacks, Lemma 10.161.13 (tag 032O), proof: "There exists a finite purely inseparable
field extension `L′/K` and `q = p^e` such that `L ⊂ L′(x^{1/q})`; some details omitted" — the
extension `L'`. For finitely many elements `s` of a field `F` and `0 < n`, there is a finite
extension `E` of `F` in which every `c ∈ s` has an `n`-th root (adjoin roots inside an algebraic
closure). Both conjuncts concern the same witness `E`, which is why they are bundled. -/
theorem exists_finiteDimensional_forall_exists_pow_eq (F : Type u) [Field F] (s : Finset F)
    {n : ℕ} (hn : 0 < n) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E),
      FiniteDimensional F E ∧ ∀ c ∈ s, ∃ d : E, d ^ n = algebraMap F E c := by
  classical
  -- pick an `n`-th root of each `c` inside an algebraic closure, then adjoin the finitely many
  have hroot : ∀ c : F, ∃ d : AlgebraicClosure F,
      d ^ n = algebraMap F (AlgebraicClosure F) c := fun c ↦ IsAlgClosed.exists_pow_nat_eq _ hn
  choose d hd using hroot
  have hTfin : (d '' (s : Set F)).Finite := s.finite_toSet.image d
  have : Finite (d '' (s : Set F)) := hTfin
  refine ⟨IntermediateField.adjoin F (d '' (s : Set F)), inferInstance, inferInstance,
    IntermediateField.finiteDimensional_adjoin (fun x _ ↦ Algebra.IsIntegral.isIntegral x),
    fun c hc ↦ ⟨⟨d c, IntermediateField.subset_adjoin F _ ⟨c, hc, rfl⟩⟩, ?_⟩⟩
  ext
  push_cast
  exact hd c

/-- Source: Stacks, Lemma 10.161.13 (tag 032O), proof: "`L ⊂ L′(x^{1/q})`; some details omitted"
— the embedding. Let `M / K` be purely inseparable of exponent at most `n`, with Frobenius
`φ = IsPurelyInseparable.iterateFrobenius K M p hn : M →+* K`, and let `s` generate `M` over
`K`. If every `φ x` for `x ∈ s` has a `p ^ n`-th root in a field `K'` over `K`, then `M` embeds
into `K'` over `K`. -/
theorem IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq (K M : Type*) [Field K]
    [Field M] [Algebra K M] [IsPurelyInseparable.HasExponent K M] (p : ℕ) [ExpChar K p] {n : ℕ}
    (hn : IsPurelyInseparable.exponent K M ≤ n) (K' : Type*) [Field K'] [Algebra K K']
    {s : Set M} (hs : IntermediateField.adjoin K s = ⊤)
    (h : ∀ x ∈ s, ∃ y : K',
      y ^ p ^ n = algebraMap K K' (IsPurelyInseparable.iterateFrobenius K M p hn x)) :
    Nonempty (M →ₐ[K] K') := by
  classical
  -- B2.0: `K'` inherits the exponential characteristic from `K`
  have : ExpChar K' p := expChar_of_injective_algebraMap (algebraMap K K').injective p
  set φ := IsPurelyInseparable.iterateFrobenius K M p hn with hφ
  set ψ := iterateFrobenius K' p n with hψ
  set θ : M →+* K' := (algebraMap K K').comp φ with hθ
  have hψ_apply : ∀ y : K', ψ y = y ^ p ^ n := fun _ ↦ rfl
  -- The single computation both the `K`-algebra law (B2.2) and the `K`-linearity of the
  -- assembled embedding (B2.6) rest on: on the image of `K`, `θ` and `ψ` agree.
  have hKθ : ∀ a : K, θ (algebraMap K M a) = ψ (algebraMap K K' a) := fun a ↦ by
    rw [hθ, RingHom.comp_apply, hφ, IsPurelyInseparable.iterateFrobenius_algebraMap, hψ_apply,
      map_pow]
  -- B2.2: the good set contains the image of `K`
  have hKmem : ∀ a : K, algebraMap K M a ∈ Subfield.comap θ ψ.fieldRange := fun a ↦
    RingHom.mem_fieldRange.mpr ⟨algebraMap K K' a, (hKθ a).symm⟩
  -- B2.1 + B2.4: promote the good set and show it is everything
  set G : IntermediateField K M :=
    (Subfield.comap θ ψ.fieldRange).toIntermediateField hKmem with hG
  have hsG : s ⊆ (G : Set M) := by
    intro x hx
    obtain ⟨y, hy⟩ := h x hx
    exact RingHom.mem_fieldRange.mpr ⟨y, by rw [hψ_apply, hy]; rfl⟩
  have hGtop : G = ⊤ := by
    rw [eq_top_iff, ← hs]
    exact IntermediateField.adjoin_le_iff.mpr hsG
  have hgood : ∀ x : M, θ x ∈ ψ.fieldRange := by
    intro x
    have hx : x ∈ G := by rw [hGtop]; exact IntermediateField.mem_top
    exact hx
  -- B2.6: invert `ψ` on its range. The range equivalence is taken at the RING level: `ψ` is only
  -- `K`-semilinear (along Frobenius), so no `K`-algebra equivalence is available here.
  -- name the ring map first: stating its defining property separately keeps the `AlgHom`
  -- structure's coercion out of the `commutes'` goal
  let σ : M →+* K' :=
    (ψ.rangeRestrictFieldEquiv.symm.toRingHom).comp (θ.codRestrict ψ.fieldRange hgood)
  have hσ : ∀ x : M, ψ (σ x) = θ x := fun x ↦
    RingHom.rangeRestrictFieldEquiv_apply_symm_apply ψ _
  -- `K`-linearity is forced by injectivity of `ψ`, not proved separately
  exact ⟨{ toRingHom := σ
           commutes' := fun a ↦ ψ.injective ((hσ _).trans (hKθ a)) }⟩

end TauCeti
