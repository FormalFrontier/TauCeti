/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import Mathlib.Algebra.Lie.Basis.Base

/-!
# Serre systems in a split semisimple Lie algebra

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra, and let `b` be a base of the root
system of `(L, H)`. Choosing an `sl₂` triple `(αⱼ∨, eⱼ, fⱼ)` for each simple root `αⱼ` produces a
*Serre system* in the sense of `TauCeti.IsSerreSystem`: the three families satisfy exactly the
relators of the Serre presentation of the Cartan matrix of `b`.

Four of the six relations are immediate from the choice of `sl₂` triples together with the fact
that `αᵢ - αⱼ` is never a root for distinct simple roots. The two higher relations

```text
(ad eᵢ) ^ (1 - ⟨αⱼ, αᵢ∨⟩) eⱼ = 0
```

are the content here. They come from the `αᵢ`-root string through `αⱼ`: since `αⱼ - αᵢ` is not a
root, that string has no lower part, so `⟨αⱼ, αᵢ∨⟩` is minus the length of its upper part, and one
step past the top of the string the root space vanishes.

Together with `TauCeti.serreLift` this presents `L` as a quotient of the Serre algebra of its own
Cartan matrix, `TauCeti.exists_surjective_serreLift_of_base`. The corresponding statement for
Mathlib's bundled `LieAlgebra.Basis` needs none of the hypotheses above and is proved by
`sl₂`-strings instead, in `TauCeti/Algebra/Lie/Presentation/Serre/Basis.lean`.

Note that the Cartan matrix is transposed on the way: `TauCeti.IsSerreSystem` follows Serre's
convention `⁅Hᵢ, Eⱼ⁆ = CMᵢⱼ Eⱼ`, whereas `RootPairing.Base.cartanMatrix i j` is `⟨αᵢ, αⱼ∨⟩`.

## Main results

* `TauCeti.chainBotCoeff_eq_zero_of_rootSpace_sub_eq_bot`: a root string has no lower part as soon
  as one step down from its base is not a root.
* `TauCeti.ad_pow_lie_eq_zero_of_rootSpace_sub_eq_bot`: the higher Serre relation for a pair of
  root vectors whose difference of roots is not a root.
* `TauCeti.rootSpace_sub_eq_bot_of_base`: the difference of two distinct simple roots is not a
  root.
* `TauCeti.isSerreSystem_coroot`: simple-root `sl₂` triples form a Serre system for the transposed
  Cartan matrix of the base.
* `TauCeti.exists_isSerreSystem_of_base`: such a Serre system exists, and its raising and lowering
  families generate `L`.
* `TauCeti.exists_surjective_serreLift_of_base`: `L` is a quotient of the Serre algebra of its
  Cartan matrix, by a homomorphism sending `Hᵢ` to the simple coroot `αᵢ∨`.

## References

* [J.P. Serre, *Complex Semisimple Lie Algebras*][serre1965], chapter VI
* [J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972], §18.1

## Roadmap

The Serre presentation is the explicit carrier of the split semisimple Lie algebra whose Chevalley
basis and Kostant `ℤ`-form build the Chevalley--Demazure group scheme, Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, consumed in turn by milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`. `TauCeti.IsSerreSystem` had no consumer outside the
presentation itself; this file supplies the one that matters there, namely that the split
semisimple Lie algebras the construction is about really are Serre systems for their Cartan
matrices.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule LieSubalgebra Module RootPairing Set
open scoped Matrix

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-! ## The higher Serre relation from a root string -/

/-- If `β - α` is not a root then the `α`-root string through `β` has no lower part. -/
theorem chainBotCoeff_eq_zero_of_rootSpace_sub_eq_bot {α β : Weight K H L} (hα : α.IsNonZero)
    (hsub : rootSpace H (⇑β - ⇑α) = ⊥) :
    chainBotCoeff (⇑α) β = 0 := by
  by_contra hne
  refine (rootSpace_zsmul_add_ne_bot_iff α β hα (-1)).2 ⟨by omega, by omega⟩ ?_
  rw [neg_one_zsmul, neg_add_eq_sub]
  exact hsub

/-- **The higher Serre relation.** If `x` and `y` are root vectors for roots `α` and `β` whose
difference `β - α` is not a root, and `n = ⟨β, α∨⟩`, then `ad x` kills `⁅x, y⁆` after `-n` further
steps: one step past the top of the `α`-root string through `β`. -/
theorem ad_pow_lie_eq_zero_of_rootSpace_sub_eq_bot {α β : Weight K H L} (hα : α.IsNonZero)
    (hsub : rootSpace H (⇑β - ⇑α) = ⊥) {n : ℤ} (hn : (n : K) = β (coroot α))
    {x y : L} (hx : x ∈ rootSpace H (⇑α)) (hy : y ∈ rootSpace H (⇑β)) :
    ((ad K L x) ^ (-n).toNat) ⁅x, y⁆ = 0 := by
  have hbot := chainBotCoeff_eq_zero_of_rootSpace_sub_eq_bot hα hsub
  have hcast : ((n : ℤ) : K) = (((chainBotCoeff (⇑α) β : ℤ) - chainTopCoeff (⇑α) β : ℤ) : K) :=
    hn.trans (apply_coroot_eq_cast α β)
  have hn' : n = (chainBotCoeff (⇑α) β : ℤ) - chainTopCoeff (⇑α) β := by exact_mod_cast hcast
  have hexp : (-n).toNat = chainTopCoeff (⇑α) β + 1 - 1 := by omega
  have hmem := toEnd_pow_apply_mem hx hy (chainTopCoeff (⇑α) β + 1)
  rw [genWeightSpace_chainTopCoeff_add_one_nsmul_add (⇑α) β hα] at hmem
  have hzero : ((toEnd K L L x) ^ (chainTopCoeff (⇑α) β + 1)) y = 0 := by
    simpa using hmem
  have hadt : ((ad K L) x : Module.End K L) = toEnd K L L x := by
    ext z
    simp
  rw [hexp, Nat.add_sub_cancel, hadt]
  rw [pow_succ] at hzero
  simpa [Module.End.mul_apply] using hzero

/-! ## Simple roots -/

/-- The difference of two distinct simple roots is not a root. -/
theorem rootSpace_sub_eq_bot_of_base (b : (rootSystem H).Base) {i j : ↥b.support} (hij : i ≠ j) :
    rootSpace H (⇑((i : H.root) : Weight K H L) - ⇑((j : H.root) : Weight K H L)) = ⊥ := by
  by_contra hbot
  have hχ0 : ⇑((i : H.root) : Weight K H L) - ⇑((j : H.root) : Weight K H L) ≠ 0 := by
    rw [sub_ne_zero]
    intro hc
    exact hij (Subtype.ext (Subtype.ext (LieModule.Weight.ext (congrFun hc))))
  have hsub := b.sub_notMem_range_root i.property j.property
  simp only [rootSystem_root_apply, mem_range, Subtype.exists, not_exists] at hsub
  refine hsub ⟨_, hbot⟩ ?_ (LinearMap.ext fun x ↦ by simp)
  simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun hc ↦ hχ0 hc

/-- The corresponding entry of the Cartan matrix of the base is the pairing of two simple roots. -/
theorem cartanMatrix_eq_apply_coroot (b : (rootSystem H).Base) (i j : ↥b.support) :
    ((b.cartanMatrix j i : ℤ) : K) =
      ((j : H.root) : Weight K H L) (coroot ((i : H.root) : Weight K H L)) := by
  have h := (rootSystem H).algebraMap_pairingIn ℤ (j : H.root) (i : H.root)
  rw [rootSystem_pairing_apply, algebraMap_int_eq] at h
  simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using h

/-! ## Serre systems from simple-root `sl₂` triples -/

/-- **`sl₂` triples for the simple roots of a base form a Serre system.** The relevant Cartan
matrix is the transpose of `RootPairing.Base.cartanMatrix`, because `TauCeti.IsSerreSystem`
follows Serre's convention `⁅Hᵢ, Eⱼ⁆ = CMᵢⱼ Eⱼ`. -/
theorem isSerreSystem_coroot (b : (rootSystem H).Base) {e f : ↥b.support → L}
    (hsl2 : ∀ i : ↥b.support, IsSl2Triple (((rootSystem H).coroot i : H) : L) (e i) (f i))
    (he : ∀ i : ↥b.support, e i ∈ rootSpace H (⇑((i : H.root) : Weight K H L)))
    (hf : ∀ i : ↥b.support, f i ∈ rootSpace H (-⇑((i : H.root) : Weight K H L))) :
    IsSerreSystem K b.cartanMatrixᵀ (fun i ↦ (((rootSystem H).coroot i : H) : L)) e f where
  lie_H_H i j := by
    simp [← LieSubalgebra.coe_bracket, trivial_lie_zero]
  lie_E_F_self i := (hsl2 i).lie_e_f
  lie_E_F_of_ne i j hij := by
    have hmem : ⁅e i, f j⁆ ∈ rootSpace H
        (⇑((i : H.root) : Weight K H L) - ⇑((j : H.root) : Weight K H L)) := by
      rw [sub_eq_add_neg]
      exact mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L _ _ (he i) (hf j)
    simpa [rootSpace_sub_eq_bot_of_base b hij] using hmem
  lie_H_E i j := by
    rw [Matrix.transpose_apply, ← LieSubalgebra.coe_bracket_of_module,
      lie_eq_smul_of_mem_rootSpace (he j), ← Int.cast_smul_eq_zsmul K,
      cartanMatrix_eq_apply_coroot b i j, rootSystem_coroot_apply]
  lie_H_F i j := by
    rw [Matrix.transpose_apply, ← LieSubalgebra.coe_bracket_of_module,
      lie_eq_smul_of_mem_rootSpace (hf j), ← Int.cast_smul_eq_zsmul K,
      cartanMatrix_eq_apply_coroot b i j, rootSystem_coroot_apply, Pi.neg_apply, neg_smul]
  ad_pow_lie_E_E i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    have hn : ((b.cartanMatrixᵀ i j : ℤ) : K) =
        ((j : H.root) : Weight K H L) (coroot ((i : H.root) : Weight K H L)) := by
      rw [Matrix.transpose_apply]
      exact cartanMatrix_eq_apply_coroot b i j
    exact ad_pow_lie_eq_zero_of_rootSpace_sub_eq_bot (H.isNonZero_coe_root _)
      (rootSpace_sub_eq_bot_of_base b hij.symm) hn (he i) (he j)
  ad_pow_lie_F_F i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    have hx : f i ∈ rootSpace H (⇑(-((i : H.root) : Weight K H L))) := by
      rw [Weight.coe_neg]; exact hf i
    have hy : f j ∈ rootSpace H (⇑(-((j : H.root) : Weight K H L))) := by
      rw [Weight.coe_neg]; exact hf j
    have hsub : rootSpace H
        (⇑(-((j : H.root) : Weight K H L)) - ⇑(-((i : H.root) : Weight K H L))) = ⊥ := by
      rw [Weight.coe_neg, Weight.coe_neg, neg_sub_neg]
      exact rootSpace_sub_eq_bot_of_base b hij
    have hn : ((b.cartanMatrixᵀ i j : ℤ) : K) =
        (-((j : H.root) : Weight K H L)) (coroot (-((i : H.root) : Weight K H L))) := by
      rw [coroot_neg, Weight.coe_neg, Pi.neg_apply, map_neg, neg_neg, Matrix.transpose_apply]
      exact cartanMatrix_eq_apply_coroot b i j
    exact ad_pow_lie_eq_zero_of_rootSpace_sub_eq_bot
      (Weight.isNonZero_neg.2 (H.isNonZero_coe_root _)) hsub hn hx hy

/-- **A split semisimple Lie algebra carries a Serre system for its Cartan matrix**, whose
raising and lowering families generate it. -/
theorem exists_isSerreSystem_of_base (b : (rootSystem H).Base) :
    ∃ e f : ↥b.support → L,
      IsSerreSystem K b.cartanMatrixᵀ (fun i ↦ (((rootSystem H).coroot i : H) : L)) e f ∧
        lieSpan K L (range e ∪ range f) = ⊤ := by
  have nonZero (i : ↥b.support) : ((i : H.root) : Weight K H L).IsNonZero :=
    H.isNonZero_coe_root _
  choose h e f hsl2 he hf using fun i ↦ exists_isSl2Triple_of_weight_isNonZero (nonZero i)
  have hh (i : ↥b.support) : h i = (((rootSystem H).coroot i : H) : L) := by
    rw [rootSystem_coroot_apply]
    exact (hsl2 i).h_eq_coroot (nonZero i) (he i) (hf i)
  simp_rw [hh] at hsl2
  refine ⟨e, f, isSerreSystem_coroot b hsl2 he hf, ?_⟩
  refine lieSpan_range_union_eq_top_of_mem_rootSpace b e f (fun i ↦ ?_) (fun i ↦ ?_) fun i ↦ ?_
  · simpa [rootSystem_coroot_apply] using hsl2 i
  · simpa using he i
  · simpa using hf i

open scoped Classical in
/-- **A split semisimple Lie algebra is a quotient of the Serre algebra of its Cartan matrix**,
by a homomorphism sending the generator `Hᵢ` to the simple coroot `αᵢ∨`. -/
theorem exists_surjective_serreLift_of_base (b : (rootSystem H).Base) :
    ∃ φ : Matrix.ToLieAlgebra K b.cartanMatrixᵀ →ₗ⁅K⁆ L, Function.Surjective φ ∧
      ∀ i, φ (serreH K b.cartanMatrixᵀ i) = (((rootSystem H).coroot i : H) : L) := by
  obtain ⟨e, f, hS, hspan⟩ := exists_isSerreSystem_of_base b
  exact ⟨serreLift hS, serreLift_surjective hS hspan, fun i ↦ serreLift_serreH hS i⟩

end TauCeti
