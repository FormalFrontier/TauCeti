/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Integrability
public import TauCeti.Algebra.Lie.Sl2.WeightString
public import TauCeti.Algebra.Lie.Submodule.LocallyFinite

public section

/-!
# An irreducible highest weight module of dominant integral weight is integrable

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, let `H` be a splitting Cartan subalgebra, let `b` be a base of its root system
and let `M` be an irreducible `L`-module carrying a highest weight vector `v` of weight `lam`.
This file proves that when `lam` is integral along a simple root `αᵢ` the module `M` is
**integrable** in that direction:

* both root vectors of `αᵢ` act **locally nilpotently** on the whole of `M`, and
* every vector of `M` lies in a **finitely generated** subspace stable under the `sl₂` triple of
  `αᵢ`, so that `M` is a locally finite module over that triple.

Integrability is the property that turns the weight cone `lam - Q⁺` of
`TauCeti/Algebra/Lie/HighestWeight/Module.lean` into a *finite* set: only for an integrable module
is the set of weights stable under the Weyl group, and it is that stability, together with the
cone, which bounds the weights and eventually makes `L(lam)` finite-dimensional.

## The argument

Both statements have the same shape. The condition in question — being annihilated by a power of a
fixed element, or lying in a finitely generated subspace stable under a fixed set of elements —
holds on a Lie submodule of `M`, by `TauCeti/Algebra/Lie/Submodule/LocallyFinite.lean`; an
irreducible module is therefore either everywhere or nowhere in that condition, and the highest
weight vector settles which.

* For a **positive** root vector `e` nothing is needed beyond the definition of a highest weight
  vector: `e` annihilates `v` outright. The relevant Lie submodule contains `v`, hence is `⊤`.
* For the **simple lowering** vector `fᵢ` the input is the integrability relation of
  `TauCeti/Algebra/Lie/HighestWeight/Integrability.lean`: in an irreducible highest weight module
  `fᵢ^{n + 1} v = 0`, where `n = lam (αᵢ^∨)`.
* Local finiteness uses finite-dimensionality of `L` and the explicit stable weight-string
  submodule `TauCeti.weightStringSubmodule`; the integrability relation truncates its generating
  string to `v, fᵢ v, …, fᵢ^n v`, so its underlying submodule is finitely generated.

The local-nilpotence results also need `ad` of the root vector to be nilpotent, which is Mathlib's
`LieAlgebra.isNilpotent_ad_of_mem_rootSpace`: a root vector moves the root spaces of `L` by a
nonzero root, and `L` has only finitely many. The local-finiteness result does not use this
hypothesis.

## Main results

* `TauCeti.exists_pow_toEnd_eq_zero_of_mem_posRoots`: every positive root vector acts locally
  nilpotently on an irreducible highest weight module.
* `TauCeti.exists_pow_toEnd_eq_zero_of_mem_rootSpace_neg`: so does every lowering vector of a
  simple root along which the highest weight is integral, and
  `TauCeti.exists_pow_toEnd_eq_zero_of_mem_rootSpace_neg_of_isDominantIntegral` reads that off
  dominance.
* `TauCeti.locallyFiniteSubmodule_eq_top_of_isSl2Triple`: **integrability**, that every vector of
  the module lies in a finitely generated subspace stable under the `sl₂` triple of such a simple
  root.

## References

This is the local-nilpotence half of the "maximal integrable quotient and local nilpotence"
milestone of Layer 4, "the classification of finite-dimensional irreducibles", of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §21.2.
* V. G. Kac, *Infinite Dimensional Lie Algebras*, 3rd ed., §3.6.
-/

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  {b : (IsKilling.rootSystem H).Base} {lam : Dual K H} {v : M}

/-! ### Local nilpotence of the root vectors -/

/-- **A positive root vector acts locally nilpotently.** On an irreducible module carrying a
highest weight vector, every element of a positive root space is annihilated on every vector by
one of its powers.

The positive root spaces annihilate the highest weight vector itself, and `ad` of a root vector is
nilpotent, so the locally nilpotent vectors form a nonzero Lie submodule. -/
theorem exists_pow_toEnd_eq_zero_of_mem_posRoots [LieModule.IsIrreducible K L M]
    (hv : IsHighestWeightVector b lam v) {i : H.root}
    (hi : i ∈ posRoots (IsKilling.rootSystem H) b)
    {e : L} (he : e ∈ rootSpace H ((i : Weight K H L) : H → K)) (m : M) :
    ∃ k : ℕ, ((toEnd K L M e) ^ k) m = 0 := by
  have hα : (i : Weight K H L).IsNonZero := H.isNonZero_coe_root i
  have had : IsNilpotent (ad K L e) :=
    LieAlgebra.isNilpotent_ad_of_mem_rootSpace H (χ := ⇑(i : Weight K H L)) hα he
  refine exists_pow_toEnd_eq_zero_of_isIrreducible
    (Module.End.isNilpotent_iff_of_finite.mp had) hv.ne_zero (k₀ := 1) ?_ m
  rw [pow_one]
  exact hv.lie_eq_zero_of_mem_rootSpace hi he

/-- **The lowering vector of a simple root acts locally nilpotently.** If the highest weight `lam`
of an irreducible highest weight module takes the natural value `n` on the coroot of a simple root
`αᵢ`, then every element of the `-αᵢ` root space is annihilated on every vector by one of its
powers.

The integrability relation `TauCeti.pow_toEnd_eq_zero_of_isHighestWeightVector_of_isIrreducible`
makes `fᵢ^{n + 1}` annihilate the highest weight vector, and the locally nilpotent vectors form a
Lie submodule. -/
theorem exists_pow_toEnd_eq_zero_of_mem_rootSpace_neg [LieModule.IsIrreducible K L M]
    (hv : IsHighestWeightVector b lam v) {i : H.root} (hi : i ∈ b.support) {n : ℕ}
    (hn : lam ((IsKilling.rootSystem H).coroot i) = (n : K))
    {f : L} (hf : f ∈ rootSpace H ((-(i : Weight K H L) : Weight K H L) : H → K)) (m : M) :
    ∃ k : ℕ, ((toEnd K L M f) ^ k) m = 0 := by
  have hα : (i : Weight K H L).IsNonZero := H.isNonZero_coe_root i
  have had : IsNilpotent (ad K L f) :=
    LieAlgebra.isNilpotent_ad_of_mem_rootSpace H (χ := ⇑(-(i : Weight K H L))) hα.neg hf
  exact exists_pow_toEnd_eq_zero_of_isIrreducible
    (Module.End.isNilpotent_iff_of_finite.mp had) hv.ne_zero
    (pow_toEnd_eq_zero_of_isHighestWeightVector_of_isIrreducible hv hi hn hf) m

/-- **Local nilpotence of a lowering vector, from dominance.** A dominant integral highest weight
is integral along every simple root, so each simple lowering vector acts locally nilpotently on an
irreducible highest weight module of that weight. The positive-root half is
`TauCeti.exists_pow_toEnd_eq_zero_of_mem_posRoots`. -/
theorem exists_pow_toEnd_eq_zero_of_mem_rootSpace_neg_of_isDominantIntegral
    [LieModule.IsIrreducible K L M]
    (hv : IsHighestWeightVector b lam v) (hlam : IsDominantIntegral b lam) {i : H.root}
    (hi : i ∈ b.support)
    {f : L} (hf : f ∈ rootSpace H ((-(i : Weight K H L) : Weight K H L) : H → K)) (m : M) :
    ∃ k : ℕ, ((toEnd K L M f) ^ k) m = 0 := by
  obtain ⟨n, hn⟩ := isDominantIntegral_iff.mp hlam i hi
  exact exists_pow_toEnd_eq_zero_of_mem_rootSpace_neg hv hi hn hf m

/-! ### Local finiteness over the `sl₂` triple of a simple root -/

/-- **Integrability of an irreducible highest weight module along a simple root.** Let `M` be
irreducible with a highest weight vector `v` of weight `lam`, let `αᵢ` be a simple root and suppose
`lam (αᵢ^∨) = n` is a natural number. Then `M` is a locally finite module over the `sl₂` triple of
`αᵢ`: every vector lies in a finitely generated subspace stable under that triple.

The witness for `v` itself is the span of `v, fᵢ v, …, fᵢ^n v`: the ladder lemmas of Mathlib's
`Sl2.lean` keep `hᵢ` and `eᵢ` inside it, and `fᵢ` walks along it and off its end into `0`, by the
integrability relation. Local finiteness holds on a Lie submodule, so irreducibility spreads it
from `v` to all of `M`. -/
theorem locallyFiniteSubmodule_eq_top_of_isSl2Triple [LieModule.IsIrreducible K L M]
    (hv : IsHighestWeightVector b lam v) {i : H.root} (hi : i ∈ b.support) {n : ℕ}
    (hn : lam ((IsKilling.rootSystem H).coroot i) = (n : K)) {h₀ e₀ f₀ : L}
    (t : IsSl2Triple h₀ e₀ f₀) (he₀ : e₀ ∈ rootSpace H ((i : Weight K H L) : H → K))
    (hf₀ : f₀ ∈ rootSpace H ((-(i : Weight K H L) : Weight K H L) : H → K)) :
    locallyFiniteSubmodule K M (t.toLieSubalgebra K : Set L) = ⊤ := by
  have hα : (i : Weight K H L).IsNonZero := H.isNonZero_coe_root i
  have hipos := support_subset_posRoots (IsKilling.rootSystem H) b hi
  -- the generating vector is a primitive vector of eigenvalue `n` for the triple of `αᵢ`
  have hP : t.HasPrimitiveVectorWith v (n : K) :=
    { ne_zero := hv.ne_zero
      lie_h := by
        rw [t.h_eq_coroot hα he₀ hf₀, ← hn, IsKilling.rootSystem_coroot_apply]
        exact hv.lie_eq_smul _
      lie_e := hv.lie_eq_zero_of_mem_rootSpace hipos he₀ }
  have hzero : ((toEnd K L M f₀) ^ (n + 1)) v = 0 :=
    pow_toEnd_eq_zero_of_isHighestWeightVector_of_isIrreducible hv hi hn hf₀
  -- Reuse the stable weight-string submodule; `hzero` truncates its generators to a finite set.
  set N₀ : Submodule K M := (weightStringSubmodule hP).toSubmodule with hN₀
  have hspan : N₀ =
      Submodule.span K (Set.range fun k : Fin (n + 1) => ((toEnd K L M f₀) ^ (k : ℕ)) v) := by
    rw [hN₀, weightStringSubmodule_toSubmodule]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨k, rfl⟩
      by_cases hk : k < n + 1
      · exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
      · have hkzero := Module.End.pow_map_zero_of_le (Nat.le_of_not_gt hk) hzero
        dsimp only
        rw [hkzero]
        exact Submodule.zero_mem _
    · rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨(k : ℕ), rfl⟩
  have hfgN₀ : N₀.FG := hspan.symm ▸ Submodule.fg_span (Set.finite_range _)
  have hst : ∀ x ∈ (t.toLieSubalgebra K : Set L), ∀ u ∈ N₀, ⁅x, u⁆ ∈ N₀ := by
    intro x hx u hu
    rw [hN₀] at hu ⊢
    exact (weightStringSubmodule hP).lie_mem (x := ⟨x, hx⟩) hu
  -- irreducibility spreads local finiteness from `v` to all of `M`
  have hvN₀ : v ∈ N₀ := by
    rw [hN₀]
    exact mem_weightStringSubmodule hP
  exact locallyFiniteSubmodule_eq_top_of_isIrreducible hfgN₀ hst hv.ne_zero hvN₀

end TauCeti
