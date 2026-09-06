/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Dual
public import TauCeti.Algebra.Lie.HighestWeight.FiniteDimensional
public import TauCeti.Algebra.Lie.HighestWeight.Irreducible
public import TauCeti.Algebra.Lie.HighestWeight.LowestWeight
public import TauCeti.Algebra.Lie.HighestWeight.Verma
public import TauCeti.Algebra.Lie.Weights.Diagonalizable

/-!
# Self-duality of a finite-dimensional irreducible highest weight module

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a Cartan subalgebra and `b` a base of its root
system, and let `M` be a finite-dimensional irreducible `L`-module with a highest weight vector of
weight `lam`. This file identifies the highest weight of the dual module `M*` and reads off the
self-duality criterion:

`M` carries a nonzero invariant bilinear form ↔ `M ≃ M*` ↔ `-(w₀ • lam) = lam`,

with `w₀` the longest element of the Weyl group.

## The highest weight of the dual

`TauCeti/Algebra/Lie/HighestWeight/LowestWeight.lean` identifies `w₀ • lam` as the lowest weight of
`M`: nothing lies below it, so subtracting a positive root from it leaves the weight support
(`TauCeti.genWeightSpace_longestElement_smul_sub_root_eq_bot`).

A functional that vanishes on every weight space except the lowest one is then a highest weight
vector of `M*` of weight `-(w₀ • lam)`. Its weight is read off the decomposition of `M` into
weight spaces, and a positive root space kills it because raising a weight into `w₀ • lam` would
have to start below `w₀ • lam`, where `M` is zero.

## The criterion

`M*` is irreducible (`TauCeti.LieModule.isIrreducible_dual`), so the classification of irreducible
highest weight modules by their weight turns the existence of an equivalence `M ≃ M*` into the
equation `-(w₀ • lam) = lam`; and a nonzero invariant bilinear form on `M` is exactly a nonzero
morphism `M → M*`, which by Schur's lemma is an equivalence.

## The criterion at `L(lam)`

At the named carrier `L(lam)` the criterion needs more than dominance of `lam`. A form of it
assuming dominance alone would entail `M(lam) ≠ 0` for every dominant integral `lam` with
`-(w₀ • lam) = lam`, since for such a `lam` it produces a nonzero bilinear form on `L(lam)`, and
the zero module carries none. That nonvanishing is the freeness half of
Poincaré--Birkhoff--Witt, isolated as the hypothesis `vermaGenerator b lam ≠ 0` in
`TauCeti/Algebra/Lie/HighestWeight/Verma.lean`, so the specialization below carries it
explicitly.

## Main results

* `TauCeti.exists_isHighestWeightVector_dual`: **the dual module has a highest weight vector of
  weight `-(w₀ • lam)`.**
* `TauCeti.nonempty_lieModuleEquiv_dual_iff` and
  `TauCeti.exists_ne_zero_lieInvariant_iff_neg_longestElement_smul_eq`: **the self-duality
  criterion**, in its module and its bilinear-form form.
* `TauCeti.exists_ne_zero_lieInvariant_irreducibleQuotient_iff_of_vermaGenerator_ne_zero`: the
  same criterion at the named carrier `L(lam)`, under the Poincaré--Birkhoff--Witt nonvanishing
  hypothesis `vermaGenerator b lam ≠ 0`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §21.6.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre VIII, §7.5.
-/

public section

namespace TauCeti

open LieAlgebra Module _root_.LieModule

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {b : (IsKilling.rootSystem H).Base} {lam : Dual K H}

variable [IsAlgClosed K]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] {v : M}
  [_root_.LieModule.IsIrreducible K L M]

/-! ### The highest weight vector of the dual -/

variable [FiniteDimensional K M]

/-- **The dual of an irreducible highest weight module has a highest weight vector of weight
`-(w₀ • lam)`.** A functional vanishing on every weight space but the lowest one has weight
`-(w₀ • lam)` because the weight spaces are honest eigenspaces, and a positive root space kills it
because it raises the lowest weight space out of the weight support. -/
theorem exists_isHighestWeightVector_dual (hv : IsHighestWeightVector b lam v) :
    ∃ f : Dual K M,
      IsHighestWeightVector b (-(longestElement (IsKilling.rootSystem H) b • lam)) f := by
  have hlam : IsDominantIntegral b lam := hv.isDominantIntegral
  set w₀ := longestElement (IsKilling.rootSystem H) b
  set mu : Dual K H := w₀ • lam
  -- the lowest weight space is nonzero
  have hmu_ne : genWeightSpace M ⇑mu ≠ ⊥ :=
    genWeightSpace_weylGroup_smul_ne_bot hv hlam w₀ hv.genWeightSpace_ne_bot
  -- the span of the other weight spaces is a proper submodule
  set N : LieSubmodule K H M := genWeightSpaceSpan H M {chi | chi ≠ ⇑mu}
  have hdisj : Disjoint (genWeightSpace M ⇑mu) N :=
    disjoint_genWeightSpace_genWeightSpaceSpan_ne H M mu
  have hNtop : N ≠ ⊤ := fun h => hmu_ne (by simpa [h] using hdisj)
  have hlt : N.toSubmodule < ⊤ := by
    rw [lt_top_iff_ne_top]
    simpa using hNtop
  obtain ⟨f, hf0, hfN⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hfN' : ∀ m ∈ N, f m = 0 := by
    intro m hm
    have hmem : f m ∈ N.toSubmodule.map f := Submodule.mem_map_of_mem hm
    rw [hfN] at hmem
    simpa using hmem
  -- `f` kills every weight space other than the lowest one
  have hkill : ∀ chi : H → K, chi ≠ ⇑mu → ∀ m ∈ genWeightSpace M chi, f m = 0 :=
    fun _ hchi _ hm => hfN' _ (genWeightSpace_le_genWeightSpaceSpan hchi hm)
  refine ⟨f, isHighestWeightVector_of_forall_rootSpace hf0 (fun x => ?_) (fun alpha ha x hx => ?_)⟩
  · -- the Cartan subalgebra acts through `-mu`
    refine sub_eq_zero.mp (eq_zero_of_forall_genWeightSpace (L := H) fun chi m hm => ?_)
    have hlie : ⁅(x : L), m⁆ = chi x • m := mem_genWeightSpace_iff_forall_lie_eq_smul.mp hm x
    rcases eq_or_ne chi ⇑mu with rfl | hchi
    · simp [Module.Dual.lie_apply, hlie]
    · simp [Module.Dual.lie_apply, hlie, hkill chi hchi m hm]
  · -- a positive root space kills `f`
    refine eq_zero_of_forall_genWeightSpace (L := H) fun chi m hm => ?_
    rw [Module.Dual.lie_apply, neg_eq_zero]
    rcases eq_or_ne ((alpha : H → K) + chi) ⇑mu with hsum | hsum
    · -- the raised weight is the lowest one, so `m` lives below it and is zero
      have hchi : chi = ⇑mu - (alpha : H → K) := eq_sub_of_add_eq' hsum
      rw [hchi] at hm
      rw [genWeightSpace_longestElement_smul_sub_root_eq_bot hv hlam ha] at hm
      rw [(_root_.LieSubmodule.mem_bot _).mp hm]
      simp
    · exact hkill _ hsum _ (lie_mem_genWeightSpace_of_mem_genWeightSpace hx hm)

/-! ### The self-duality criterion -/

/-- **A finite-dimensional irreducible module is self-dual exactly when `-(w₀ • lam) = lam`.** The
dual is irreducible with highest weight `-(w₀ • lam)`, and irreducible highest weight modules are
classified by their weight. -/
theorem nonempty_lieModuleEquiv_dual_iff (hv : IsHighestWeightVector b lam v) :
    Nonempty (M ≃ₗ⁅K,L⁆ Dual K M) ↔
      -(longestElement (IsKilling.rootSystem H) b • lam) = lam := by
  obtain ⟨f, hf⟩ := exists_isHighestWeightVector_dual hv
  have _i := TauCeti.LieModule.isIrreducible_dual (K := K) (L := L) (M := M)
  exact (nonempty_lieModuleEquiv_iff_eq_of_isHighestWeightVector hv hf).trans eq_comm

/-- **The self-duality criterion in its invariant-form shape.** A finite-dimensional irreducible
module with highest weight `lam` carries a nonzero invariant bilinear form exactly when
`-(w₀ • lam) = lam`.

`TauCeti.IsDominantIntegral.neg_longestElement_smul` records the pointwise reading of `w₀` behind
this: whenever `lam` is dominant integral, so is `-(w₀ • lam)`, that is, `w₀ • lam` lands in the
negative of the dominant integral weights. -/
theorem exists_ne_zero_lieInvariant_iff_neg_longestElement_smul_eq
    (hv : IsHighestWeightVector b lam v) :
    (∃ Φ : LinearMap.BilinForm K M, Φ ≠ 0 ∧ Φ.lieInvariant L) ↔
      -(longestElement (IsKilling.rootSystem H) b • lam) = lam :=
  TauCeti.LieModule.exists_ne_zero_lieInvariant_iff_nonempty_lieModuleEquiv_dual.trans
    (nonempty_lieModuleEquiv_dual_iff hv)

/-- **The self-duality criterion at the named carrier `L(lam)`.** For dominant integral `lam` with
`M(lam) ≠ 0`, the module `L(lam)` carries a nonzero invariant bilinear form exactly when
`-(w₀ • lam) = lam`.

The nonvanishing `vermaGenerator b lam ≠ 0` is the isolated Poincaré--Birkhoff--Witt input of
`TauCeti/Algebra/Lie/HighestWeight/Verma.lean`, which `TauCeti.isIrreducible_irreducibleQuotient`
already takes; a caller holding a highest weight vector of weight `lam` in any module obtains it
from `TauCeti.vermaGenerator_ne_zero_of_isHighestWeightVector`. It cannot be dropped: without it
`L(lam)` may be the zero module, which carries no nonzero bilinear form however `lam` sits. Given
it, dominance makes `L(lam)` finite-dimensional
(`TauCeti.finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral`), so no
finite-dimensionality hypothesis is needed. -/
theorem exists_ne_zero_lieInvariant_irreducibleQuotient_iff_of_vermaGenerator_ne_zero
    (hlam : IsDominantIntegral b lam) (hne : vermaGenerator b lam ≠ 0) :
    (∃ Φ : LinearMap.BilinForm K (irreducibleQuotient b lam), Φ ≠ 0 ∧ Φ.lieInvariant L) ↔
      -(longestElement (IsKilling.rootSystem H) b • lam) = lam := by
  have _i := isIrreducible_irreducibleQuotient b lam hne
  have hgen := isHighestWeightVector_irreducibleQuotientGenerator b lam hne
  have _j := finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral hgen hlam
  exact exists_ne_zero_lieInvariant_iff_neg_longestElement_smul_eq hgen

end TauCeti
