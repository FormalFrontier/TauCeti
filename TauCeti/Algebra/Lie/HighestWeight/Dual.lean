/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Dual
public import TauCeti.Algebra.Lie.HighestWeight.FiniteDimensional
public import TauCeti.Algebra.Lie.HighestWeight.Irreducible
public import TauCeti.Algebra.Lie.HighestWeight.Verma
public import TauCeti.Algebra.Lie.Weights.Diagonalizable
public import TauCeti.LinearAlgebra.RootSystem.Opposition

public section

/-!
# Self-duality of a finite-dimensional irreducible highest weight module

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a Cartan subalgebra and `b` a base of its root
system, and let `M` be a finite-dimensional irreducible `L`-module with a highest weight vector of
weight `lam`. This file identifies the highest weight of the dual module `M*` and reads off the
self-duality criterion:

`M` carries a nonzero invariant bilinear form ↔ `M ≃ M*` ↔ `-(w₀ • lam) = lam`,

with `w₀` the longest element of the Weyl group.

## The lowest weight

The weights of `M` are stable under the Weyl group and lie below `lam`
(`TauCeti.sub_weylGroup_smul_mem_posRootCone_of_genWeightSpace_ne_bot_of_isHighestWeightVector`),
so applying `w₀` — which carries the positive root cone to its negative
(`TauCeti.neg_longestElement_smul_mem_posRootCone`) — shows that every weight of `M` lies *above*
`w₀ • lam` (`TauCeti.sub_longestElement_smul_mem_posRootCone_of_genWeightSpace_ne_bot`). So
`w₀ • lam` is the lowest weight: subtracting a positive root from it leaves the weight support.

A functional that vanishes on every weight space except the lowest one is then a highest weight
vector of `M*` of weight `-(w₀ • lam)`. Its weight is read off the honest weight-space
decomposition of Layer 2, and a positive root space kills it because raising a weight into
`w₀ • lam` would have to start below `w₀ • lam`, where `M` is zero.

## The criterion

`M*` is irreducible (`TauCeti.LieModule.isIrreducible_dual`), so the classification of irreducible
highest weight modules by their weight turns the existence of an equivalence `M ≃ M*` into the
equation `-(w₀ • lam) = lam`; and a nonzero invariant bilinear form on `M` is exactly a nonzero
morphism `M → M*`, which by Schur's lemma is an equivalence.

## Main results

* `TauCeti.IsDominantIntegral.neg_longestElement_smul`: `-(w₀ • lam)` is dominant integral when
  `lam` is, by the opposition involution of the base.
* `TauCeti.sub_longestElement_smul_mem_posRootCone_of_genWeightSpace_ne_bot`: **`w₀ • lam` is the
  lowest weight**, and `TauCeti.genWeightSpace_longestElement_smul_sub_root_eq_bot` is the form the
  construction of the dual highest weight vector consumes.
* `TauCeti.exists_isHighestWeightVector_dual`: **the dual module has a highest weight vector of
  weight `-(w₀ • lam)`.**
* `TauCeti.nonempty_lieModuleEquiv_dual_iff` and
  `TauCeti.exists_ne_zero_lieInvariant_iff_neg_longestElement_smul_eq`: **the self-duality
  criterion**, in its module and its bilinear-form form.
* `TauCeti.exists_ne_zero_lieInvariant_irreducibleQuotient_iff_of_vermaGenerator_ne_zero`: the
  same criterion at the named carrier `L(lam)`, conditional on the currently missing PBW
  nonvanishing input.

## References

This file supplies the carrier-independent self-duality theorem required by the "self-duality of
`L(λ)`" coverage target `exists_invariantForm_iff_neg_longest_smul_eq` of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/Suggested.lean`. The roadmap's Layer 6
records that target as the interface the Frobenius-Schur indicator of
`TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md` consumes. The pinned statement
phrases `w₀` as "a Weyl element carrying the dominant cone to its negative" so as not to import a
length function; `TauCeti.longestElement` is that element, so it is used directly here.

This does not close the pinned target, which asks for the criterion at `L(lam)` from dominance
alone. That form entails `M(lam) ≠ 0` for every dominant integral `lam`, since for `lam` with
`-(w₀ • lam) = lam` it produces a nonzero bilinear form on `L(lam)`, and the zero module carries
none. The nonvanishing is the freeness half of Poincaré--Birkhoff--Witt, isolated as a hypothesis in
`TauCeti/Algebra/Lie/HighestWeight/Verma.lean` and assigned to the roadmap's separate Layer 3 PBW
work. The conditional named-carrier specialization below makes that missing input explicit.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §21.6.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre VIII, §7.5.
-/

namespace TauCeti

open LieAlgebra Module _root_.LieModule

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {b : (IsKilling.rootSystem H).Base} {lam : Dual K H}

/-! ### Dominance of the opposite weight -/

/-- **The opposite of a dominant integral weight is dominant integral.** The opposition involution
`i ↦ -w₀ i` permutes the simple roots (`TauCeti.opposition_mem_support`), and the value of
`-(w₀ • lam)` on the coroot of `αᵢ` is the value of `lam` on the coroot of the opposite simple
root. -/
theorem IsDominantIntegral.neg_longestElement_smul (hlam : IsDominantIntegral b lam) :
    IsDominantIntegral b (-(longestElement (IsKilling.rootSystem H) b • lam)) := by
  -- The root system of `H` pairs a weight with a coroot by evaluation, so its `coroot'` is
  -- evaluation at the coroot; this is the boundary between the two coroot interfaces.
  have hcoroot' : ∀ (j : H.root) (x : Dual K H),
      (IsKilling.rootSystem H).coroot' j x = x ((IsKilling.rootSystem H).coroot j) :=
    fun _ _ => by rw [LinearMap.flip_apply, IsKilling.rootSystem_toLinearMap_apply]
  refine isDominantIntegral_iff.mpr fun i hi => ?_
  obtain ⟨n, hn⟩ :=
    isDominantIntegral_iff.mp hlam _ (opposition_mem_support (IsKilling.rootSystem H) b hi)
  refine ⟨n, ?_⟩
  have h := coroot'_opposition (IsKilling.rootSystem H) b i lam
  rw [hcoroot', hcoroot', hn] at h
  rw [LinearMap.neg_apply, h]

/-! ### The lowest weight -/

variable [IsAlgClosed K]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] {v : M}
  [_root_.LieModule.IsIrreducible K L M]

/-- **`w₀ • lam` is the lowest weight of an irreducible highest weight module.** Every weight lies
above it, in the sense that their difference is a nonnegative combination of the simple roots.

The weights of `M` are stable under the Weyl group and lie below `lam`; applying `w₀`, which
negates the positive root cone, reverses the inequality. -/
theorem sub_longestElement_smul_mem_posRootCone_of_genWeightSpace_ne_bot
    (hv : IsHighestWeightVector b lam v) (hlam : IsDominantIntegral b lam) {chi : Dual K H}
    (hchi : genWeightSpace M ⇑chi ≠ ⊥) :
    chi - longestElement (IsKilling.rootSystem H) b • lam
      ∈ posRootCone (IsKilling.rootSystem H) b := by
  have h := sub_weylGroup_smul_mem_posRootCone_of_genWeightSpace_ne_bot_of_isHighestWeightVector
    hv hlam (longestElement (IsKilling.rootSystem H) b) hchi
  have h2 := neg_longestElement_smul_mem_posRootCone h
  rwa [smul_sub, smul_smul_longestElement, neg_sub] at h2

omit [IsAlgClosed K] [_root_.LieModule.IsIrreducible K L M] in
/-- The weight underlying the difference of a weight and a root is the pointwise difference. -/
private theorem coe_sub_root_rootSystem (x : Dual K H) (i : H.root) :
    ⇑(x - (IsKilling.rootSystem H).root i) = ⇑x - (i : H → K) :=
  rfl

/-- **Nothing lies below the lowest weight.** Subtracting a positive root from `w₀ • lam` leaves
the weight support of `M`: the positive root cone is pointed, so a weight below the lowest one
would give a positive root whose negative is again in the cone. -/
theorem genWeightSpace_longestElement_smul_sub_root_eq_bot
    (hv : IsHighestWeightVector b lam v) (hlam : IsDominantIntegral b lam) {i : H.root}
    (hi : i ∈ posRoots (IsKilling.rootSystem H) b) :
    genWeightSpace M (⇑(longestElement (IsKilling.rootSystem H) b • lam) - (i : H → K)) = ⊥ := by
  by_contra hne
  rw [← coe_sub_root_rootSystem] at hne
  have h := sub_longestElement_smul_mem_posRootCone_of_genWeightSpace_ne_bot hv hlam hne
  rw [sub_sub_cancel_left] at h
  exact root_add_ne_zero_of_mem_posRoots_of_mem_posRootCone (IsKilling.rootSystem H) b hi h
    (add_neg_cancel _)

/-! ### The highest weight vector of the dual -/

variable [FiniteDimensional K M]

omit [CharZero K] [IsKilling K L] [FiniteDimensional K L] [IsTriangularizable K H L]
  [_root_.LieModule.IsIrreducible K L M] in
/-- A linear functional vanishing on every weight space is zero: the weight spaces span. -/
private theorem eq_zero_of_forall_genWeightSpace {g : Dual K M}
    (hg : ∀ chi : H → K, ∀ m ∈ genWeightSpace M chi, g m = 0) : g = 0 := by
  refine LinearMap.ker_eq_top.mp (top_le_iff.mp ?_)
  rw [← _root_.LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top K H M)]
  exact iSup_le fun chi m hm => hg chi m hm

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
    refine sub_eq_zero.mp (eq_zero_of_forall_genWeightSpace (H := H) fun chi m hm => ?_)
    have hlie : ⁅(x : L), m⁆ = chi x • m := mem_genWeightSpace_iff_forall_lie_eq_smul.mp hm x
    rcases eq_or_ne chi ⇑mu with rfl | hchi
    · simp [Module.Dual.lie_apply, hlie]
    · simp [Module.Dual.lie_apply, hlie, hkill chi hchi m hm]
  · -- a positive root space kills `f`
    refine eq_zero_of_forall_genWeightSpace (H := H) fun chi m hm => ?_
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

The roadmap pins the criterion against "a Weyl element carrying the dominant cone to its negative";
`TauCeti.IsDominantIntegral.neg_longestElement_smul` says that `w₀` is such an element, so the two
readings agree. -/
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
