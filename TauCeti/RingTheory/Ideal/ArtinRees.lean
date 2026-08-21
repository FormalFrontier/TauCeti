/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Filtration

/-!
# Lifting through a surjection with control on the `I`-adic filtration

Mathlib's Artin–Rees lemma, `Ideal.exists_pow_inf_eq_pow_smul`, compares the `I`-adic filtration
of a module with the filtration it induces on a submodule. This file draws the lifting consequence
that the adic theory uses.

Fix a submodule `N` of a finite module `M` over a noetherian ring. Then **one shift `k₀` serves
every surjection onto `N` and every depth at once**: for any module `P` and any surjection
`φ : P →ₗ[R] N`, an element of `N` lying `k₀` steps deeper than `m` in the *ambient* filtration
of `M` is the image under `φ` of something at depth `m` in `P`.

The order of quantifiers is the content. `k₀` comes from `Ideal.exists_pow_inf_eq_pow_smul`,
which mentions only `I` and `N`, so it is bound outside `P` and `φ`; a statement giving a
constant only after the surjection is fixed would be strictly weaker and would not compose.

The shift is what makes the statement useful and what makes it non-trivial. Membership in
`I ^ n • ⊤` is measured in `M`, while a lift is constrained by the filtration `N` inherits, and
those two differ; Artin–Rees is exactly the input that bounds the discrepancy by a constant
independent of `n`. Without the shift the statement is false in general.

Nothing here is topological or adic-space-specific — it is filtration algebra over an arbitrary
commutative noetherian ring — so it sits beside Mathlib's own Artin–Rees material rather than in
the Huber development that consumes it.

## Main results

* `TauCeti.ArtinRees.exists_controlled_lift`: there is a shift depending only on `I` and the
  submodule — quantified before the surjection — for which every surjection onto that submodule
  admits lifts with control on the `I`-adic filtration.

## Provenance

Adapted from AINTLIB's `ArtinRees.controlled_lift`, branch `dev/adic-spaces`, commit `37bbdaeb`,
Apache-2.0, Chris Birkbeck, `projects/AdicSpaces/Adic spaces/ArtinReesConvergence.lean`, whose
reference is given there as Wedhorn Lemma 8.31. Note that the TauCeti roadmap assigns that
number to a different statement — `A⟨X⟩` faithfully flat over `A`, in
`AdicSpaces/README.md` — so the citation below is the source's own attribution, not a
roadmap node. Two generalisations:

* the source fixes the ambient module to `Fin l → R` and the source of the surjection to
  `Fin k → R`, presenting the map as `∑ j, c j • s j` for a chosen spanning family; here the
  ambient module, the source and the map are arbitrary, since the proof uses only surjectivity.
  The source's `surjMap` and its two lemmas are consequently dropped — that map is Mathlib's
  `Fintype.linearCombination`, and the image computation is `Submodule.map_smul''` composed with
  `Submodule.map_top`;
* the source takes the Artin–Rees conclusion as a hypothesis `hAR` together with the constant
  `k₀`; here both come from `Ideal.exists_pow_inf_eq_pow_smul`, so no caller has to supply them.

One declaration is not ported: the source's `pi_smul_top_component`, which has no consumer.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.31.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/ArtinReesConvergence.lean`.
-/

public section

namespace TauCeti.ArtinRees

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **Artin–Rees controlled lift.** For an ideal `I` and a submodule `N` of a finite module over a
noetherian ring there is a shift `k₀` — depending on `I` and `N` alone, so independent of both
the depth and the surjection — such that for every surjection `φ` onto `N`, every `v : N` whose
image in `M` lies in `I ^ (m + k₀) • ⊤` has a `φ`-preimage in `I ^ m • ⊤`. -/
theorem exists_controlled_lift [IsNoetherianRing R] [Module.Finite R M] (I : Ideal R)
    (N : Submodule R M) :
    ∃ k₀ : ℕ, ∀ {P : Type*} [AddCommGroup P] [Module R P] (φ : P →ₗ[R] N),
      Function.Surjective φ → ∀ (m : ℕ) (v : N),
        (v : M) ∈ (I ^ (m + k₀) • ⊤ : Submodule R M) →
          ∃ c ∈ (I ^ m • ⊤ : Submodule R P), φ c = v := by
  obtain ⟨k₀, hAR⟩ := I.exists_pow_inf_eq_pow_smul N
  refine ⟨k₀, fun {P} _ _ φ hφ m v hv ↦ ?_⟩
  -- Artin–Rees turns ambient depth `m + k₀` into depth `m` for the filtration induced on `N`
  have hv_inf : (v : M) ∈ I ^ (m + k₀) • ⊤ ⊓ N := ⟨hv, v.prop⟩
  rw [hAR (m + k₀) (Nat.le_add_left k₀ m), Nat.add_sub_cancel] at hv_inf
  have hv_smul_N : (v : M) ∈ I ^ m • N := (Submodule.smul_mono le_rfl inf_le_right) hv_inf
  have hv_top : v ∈ (I ^ m • ⊤ : Submodule R N) :=
    (Submodule.mem_smul_top_iff (I ^ m) N v).mpr hv_smul_N
  -- a surjection carries `I ^ m • ⊤` onto `I ^ m • ⊤`, so the lift can be taken at depth `m`
  have hmap : (I ^ m • ⊤ : Submodule R P).map φ = (I ^ m • ⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hφ]
  rw [← hmap] at hv_top
  exact Submodule.mem_map.mp hv_top

end TauCeti.ArtinRees

end
