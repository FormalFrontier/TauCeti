/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Dual
public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import Mathlib.LinearAlgebra.RootSystem.Base

public section

/-!
# Scaffolding shared by the pinned simply connected root data

Layer 6 of the root-systems roadmap pins one integral root datum per valid Dynkin type, each on the
lattices `Fin n → ℤ` with the dot product as pairing, and each carrying a base whose support is the
image of an injective *simple index* map `e` naming the simple roots in Bourbaki order. This file
holds the part of that construction which carries no information about the type: only the per-type
files, such as `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A` and
`...SimplyConnectedRootDatum.D.Basic`, supply the mathematics of their own root system.

## Main definitions

* `TauCeti.simpleSupport`: the support of a pinned base, the image of a simple index map.

## Main results

* `TauCeti.hasCartanType_of_pairing_eq`: a base supported on a simple index map has Cartan type `t`
  as soon as the pairings of the simple roots are the entries of the standard Cartan matrix of `t`.
* `TauCeti.corootSpan_eq_top_of_coroot_eq_single`: the coroots span the cocharacter lattice as soon
  as the simple coroots are the standard basis. This is the simply connected lattice condition.
* `TauCeti.sum_smul_mem_or_neg_mem_closure`: a combination of a family with coefficients of one
  sign lies in the additive closure of the family, or its negative does. This is the shape in which
  the two membership axioms of `RootPairing.Base` are met.
* `TauCeti.sub_mem_of_consecutive_sub_mem`: a difference of two members of a family telescopes into
  any additive submonoid containing the consecutive differences between them.
* `TauCeti.sub_mem_closure_of_le`: a difference of two members of a family telescopes into the
  additive closure of the consecutive differences. This is the shape in which those same axioms are
  met by the pinned data written in a coordinate potential.

Every pinned datum of Layer 6 pairs its two lattices by the dot product, which is a perfect pairing
by `TauCeti.dotProductBilin_isPerfPair` in `TauCeti/LinearAlgebra/Matrix/Dual.lean`. The symmetry
and reflection preservation of the quadratic form carried by the Cartan matrix are supplied by
`TauCeti.vecMul_dotProduct_comm` and `TauCeti.reflect_vecMul_dotProduct_self` in
`TauCeti/LinearAlgebra/Matrix/Gram.lean`.
-/

namespace TauCeti

open Function Set

/-! ## The support of a pinned base -/

section SimpleSupport

variable {ι κ : Type*} [Fintype κ] {e : κ → ι} (he : Injective e)

/-- The support of a pinned base: the image of the simple index map `e`, which names the simple
roots among all root indices. -/
def simpleSupport : Finset ι :=
  Finset.univ.map ⟨e, he⟩

theorem mem_simpleSupport {k : ι} : k ∈ simpleSupport he ↔ ∃ i, e i = k := by
  simp [simpleSupport]

theorem coe_simpleSupport : (simpleSupport he : Set ι) = range e := by
  simp [simpleSupport]

/-- A family indexed by the root indices is determined on a pinned support by its values at the
simple indices. -/
theorem image_simpleSupport {M : Type*} (f : ι → M) :
    f '' (simpleSupport he : Set ι) = range (f ∘ e) := by
  rw [coe_simpleSupport, range_comp]

/-- Linear independence of the simple members of a family is linear independence on the pinned
support, the form in which `RootPairing.Base` asks for it. -/
theorem linearIndepOn_simpleSupport {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (f : ι → M) (h : LinearIndependent R (f ∘ e)) : LinearIndepOn R f (simpleSupport he) := by
  rw [coe_simpleSupport]
  exact (linearIndepOn_range_iff he f).mpr h

end SimpleSupport

section SimpleSupportFin

variable {n N : ℕ} {e : Fin n → Fin N}

/-- **A pinned support numbered in order is an initial segment.** When the simple index map sends
`i` to the root index `i`, membership in the support is the bound `k < n` on the index. -/
theorem mem_simpleSupport_iff_lt (he : Injective e) (h : ∀ i, ((e i : Fin N) : ℕ) = i)
    {k : Fin N} : k ∈ simpleSupport he ↔ (k : ℕ) < n := by
  rw [mem_simpleSupport]
  refine ⟨?_, fun hk => ⟨⟨k, hk⟩, Fin.ext (h ⟨k, hk⟩)⟩⟩
  rintro ⟨i, rfl⟩
  rw [h i]
  exact i.isLt

end SimpleSupportFin


/-! ## Combinations with coefficients of one sign -/

section Closure

variable {κ M : Type*} [Fintype κ] [AddCommGroup M] (v : κ → M)

theorem sum_smul_mem_closure (c : κ → ℤ) (hc : ∀ i, 0 ≤ c i) :
    (∑ i, c i • v i) ∈ AddSubmonoid.closure (range v) := by
  refine AddSubmonoid.sum_mem _ fun i _ => ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (hc i)
  rw [hm, natCast_zsmul]
  exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (mem_range_self i)) m

/-- A combination of a family whose coefficients all have the same sign lies in the additive
closure of the family, or its negative does. Both membership axioms of `RootPairing.Base` are met
in this shape. -/
theorem sum_smul_mem_or_neg_mem_closure (c : κ → ℤ) (hc : (∀ i, 0 ≤ c i) ∨ (∀ i, c i ≤ 0)) :
    (∑ i, c i • v i) ∈ AddSubmonoid.closure (range v) ∨
      -(∑ i, c i • v i) ∈ AddSubmonoid.closure (range v) := by
  rcases hc with h | h
  · exact Or.inl (sum_smul_mem_closure v c h)
  · refine Or.inr ?_
    rw [← Finset.sum_neg_distrib]
    simp only [← neg_smul]
    exact sum_smul_mem_closure v (fun i => -c i) fun i => neg_nonneg.mpr (h i)

/-- A difference `f a - f b` telescopes into any additive submonoid containing all the consecutive
differences `f k - f (k + 1)` for `a ≤ k < b`. -/
theorem sub_mem_of_consecutive_sub_mem (S : AddSubmonoid M) (f : ℕ → M) {a b : ℕ} (hab : a ≤ b)
    (h : ∀ k, a ≤ k → k < b → f k - f (k + 1) ∈ S) : f a - f b ∈ S := by
  have key := Finset.sum_Ico_sub (fun k => -f k) hab
  simp only [neg_sub_neg] at key
  rw [← key]
  exact sum_mem fun k hk => h k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2

/-- **Telescoping into the closure of the consecutive differences.** A difference `f a - f b` with
`a ≤ b ≤ n` lies in the additive submonoid generated by the `n` differences `f i - f (i + 1)`. A
pinned datum whose roots or coroots are differences of a coordinate potential meets the membership
axioms of `RootPairing.Base` in this shape. -/
theorem sub_mem_closure_of_le {n : ℕ} (f : ℕ → M) {a b : ℕ} (hb : b ≤ n) (hab : a ≤ b) :
    f a - f b ∈ AddSubmonoid.closure (range fun i : Fin n => f (i : ℕ) - f ((i : ℕ) + 1)) := by
  refine sub_mem_of_consecutive_sub_mem _ _ hab fun i _ hib => AddSubmonoid.subset_closure ?_
  exact ⟨⟨i, lt_of_lt_of_le hib hb⟩, rfl⟩

end Closure

/-! ## Recognizing the pinned data -/

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **A pinned base has the Cartan type its simple pairings display.** The Cartan matrix of a base
supported on a simple index map is read off the pairings of the simple roots, so a base whose
simple pairings are the entries of the standard Cartan matrix of `t` has Cartan type `t`. -/
theorem hasCartanType_of_pairing_eq [FaithfulSMul ℤ R] {P : RootPairing ι R M N}
    [P.IsCrystallographic] {b : P.Base} {t : DynkinType} {e : Fin t.rank → ι} (he : Injective e)
    (hb : b.support = simpleSupport he)
    (h : ∀ i j, P.pairing (e i) (e j) = algebraMap ℤ R (t.cartanMatrix i j)) :
    HasCartanType P b t := by
  have hmem : ∀ i, e i ∈ b.support := fun i => hb ▸ (mem_simpleSupport he).mpr ⟨i, rfl⟩
  have hbij : Bijective fun i : Fin t.rank => (⟨e i, hmem i⟩ : b.support) := by
    constructor
    · exact fun i j hij => he (congrArg Subtype.val hij)
    · rintro ⟨k, hk⟩
      obtain ⟨i, rfl⟩ := (mem_simpleSupport he).mp (hb ▸ hk)
      exact ⟨i, rfl⟩
  set q := (Equiv.ofBijective _ hbij).symm with hq
  refine (hasCartanType_iff b t).mpr ⟨q, fun i j => ?_⟩
  have hval : ∀ x : b.support, (x : ι) = e (q x) := fun x =>
    congrArg Subtype.val (Equiv.apply_symm_apply (Equiv.ofBijective _ hbij) x).symm
  rw [← (FaithfulSMul.algebraMap_injective ℤ R).eq_iff,
    RootPairing.Base.algebraMap_cartanMatrixIn_apply, hval i, hval j, h]

/-- **The coroots span the cocharacter lattice when the simple coroots are the standard basis.**
For the pinned data of Layer 6 this is the simply connected lattice condition. -/
theorem corootSpan_eq_top_of_coroot_eq_single {κ : Type*} [Finite κ] [DecidableEq κ]
    {P : RootPairing ι R M (κ → R)} {e : κ → ι} (h : ∀ i, P.coroot (e i) = Pi.single i 1) :
    P.corootSpan R = ⊤ := by
  refine top_unique ?_
  rw [← (Pi.basisFun R κ).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨e i, by rw [h i]; simp⟩

end RootPairing

end TauCeti
