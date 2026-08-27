/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.OrderOfVanishing.Basic
-- Proof-only: `QuotSMulTop` supplies the transport used to prove `length_quotient_lsmul_congr`;
-- no statement in this file mentions it.
import Mathlib.RingTheory.QuotSMulTop

/-!
# General facts about the length of a module

Mathlib defines `Module.length R M` as the Krull dimension of the lattice of submodules and
proves that it is additive in short exact sequences. This file adds the facts about it that a
length-counting argument needs but Mathlib does not yet have: monotonicity in the submodule
quotiented by, additivity along a filtration, the length of an image, the fact that finitely
generated submodules already see the whole length, and the length of `I ⧸ aI` for an ideal `I`.

The finite-generation reduction is the load-bearing one. `Module.length` is a supremum over
strictly increasing chains, and any *finite* chain — in particular any one witnessing a finite
lower bound on the length — is realised inside a finitely generated submodule, spanned by one
element taken from each of its steps. So a uniform bound on finitely generated submodules is a
bound on the module.

Multiplication by a ring element `a` on a module `M` is written throughout as
`LinearMap.range (LinearMap.lsmul A M a)`, which is the submodule `aM`. Mathlib spells the same
submodule pointwise, as `a • ⊤`, and quotients by it in `QuotSMulTop`. `TauCeti.map_lsmul_eq_smul`
is the single bridge between the two readings: `TauCeti.range_lsmul_eq_smul_top` and hence
`TauCeti.length_quotient_lsmul_congr` are derived from it, so that Mathlib's `QuotSMulTop` API
applies to the quotients appearing here without any further appeal to defeq.

## Main results

* `TauCeti.length_quotient_anti`: `M ⧸ Q` is no longer than `M ⧸ P` when `P ≤ Q`.
* `TauCeti.length_quotient_eq_length_map_add_length_quotient_sup`: additivity along a filtration.
* `TauCeti.length_map_mkQ`: the length of the image of `N` in `M ⧸ P`.
* `TauCeti.length_le_of_forall_fg`: a bound on all finitely generated submodules bounds the
  length.
* `TauCeti.map_lsmul_eq_smul` and `TauCeti.range_lsmul_eq_smul_top`: `aN` and `aM` as Mathlib's
  pointwise `a • N` and `a • ⊤`.
* `TauCeti.comap_subtype_map_lsmul`: `aN` computed inside `N` agrees with `aN` computed in the
  ambient module.
* `TauCeti.length_quotient_lsmul_congr`: the length of `M ⧸ aM` is a linear-equivalence invariant.
* `TauCeti.length_quotient_lsmul_le_of_forall_fg`: the finite-generation reduction for `M ⧸ aM`.
* `TauCeti.isFiniteLength_quotient_of_nonZeroDivisor_mem`: `A ⧸ I` has finite length when `I`
  contains a non-zero-divisor.
* `TauCeti.length_quotient_lsmul_ideal_eq_ord`: `length (I ⧸ aI) = Ring.ord A a` for an ideal `I`
  with `A ⧸ I` of finite length.
-/

public section

namespace TauCeti

section Ring

variable {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]

/-- Quotienting by a larger submodule cannot increase length. -/
theorem length_quotient_anti {P Q : Submodule A M} (h : P ≤ Q) :
    Module.length A (M ⧸ Q) ≤ Module.length A (M ⧸ P) := by
  rw [Module.length_quotient, Module.length_quotient]
  exact Order.coheight_anti h

/-- **Filtration additivity.** The image of `N` in `M ⧸ P` and the further quotient
`M ⧸ (P ⊔ N)` account between them for the whole of `M ⧸ P`. -/
theorem length_quotient_eq_length_map_add_length_quotient_sup (N P : Submodule A M) :
    Module.length A (M ⧸ P) = Module.length A (N.map P.mkQ) + Module.length A (M ⧸ (P ⊔ N)) := by
  rw [← (Submodule.quotientQuotientEquivQuotientSup P N).length_eq]
  exact Module.length_eq_add_of_exact (N.map P.mkQ).subtype (N.map P.mkQ).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)

/-- The image of `N` in `M ⧸ P` has the length of `N ⧸ (N ⊓ P)`, for any `P`; in particular no
`P ≤ N` is needed. -/
theorem length_map_mkQ (N P : Submodule A M) :
    Module.length A (N.map P.mkQ) = Module.length A (↥N ⧸ Submodule.comap N.subtype P) := by
  have hker : LinearMap.ker (P.mkQ ∘ₗ N.subtype) = Submodule.comap N.subtype P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hran : LinearMap.range (P.mkQ ∘ₗ N.subtype) = N.map P.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hran, ← hker]
  exact ((LinearMap.quotKerEquivRange (P.mkQ ∘ₗ N.subtype)).length_eq).symm

/-- **Length is detected by finitely generated submodules.** -/
theorem length_le_of_forall_fg {c : ℕ∞} (h : ∀ N : Submodule A M, N.FG → Module.length A N ≤ c) :
    Module.length A M ≤ c := by
  rcases eq_or_ne c ⊤ with rfl | hc
  · exact le_top
  lift c to ℕ using hc
  by_contra hlt
  rw [not_le] at hlt
  -- A chain one step longer than `c` exists in the submodule lattice.
  have hstep : ((c + 1 : ℕ) : ℕ∞) ≤ Module.length A M := by
    exact_mod_cast Order.add_one_le_of_lt hlt
  have hkd : ((c + 1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (Submodule A M) := by
    rw [← Module.coe_length]; exact_mod_cast hstep
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hkd
  -- Pick a witness for each strict step, and span them: the chain survives inside that span.
  have hx : ∀ i : Fin l.length, ∃ x : M, x ∈ l i.succ ∧ x ∉ l i.castSucc := fun i =>
    SetLike.exists_of_lt (l.strictMono (Fin.castSucc_lt_succ : i.castSucc < i.succ))
  choose x hx1 hx2 using hx
  set N : Submodule A M := Submodule.span A (Set.range x) with hN
  have hxN : ∀ i, x i ∈ N := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hmono : StrictMono (fun i => Submodule.comap N.subtype (l i)) :=
    Fin.strictMono_iff_lt_succ.mpr fun i => by
      refine lt_of_le_of_ne (Submodule.comap_mono
        (l.strictMono (Fin.castSucc_lt_succ : i.castSucc < i.succ)).le) ?_
      intro hEq
      refine hx2 i ?_
      have hmem : (⟨x i, hxN i⟩ : N) ∈ Submodule.comap N.subtype (l i.castSucc) := by
        rw [hEq]; exact hx1 i
      simpa using hmem
  have hq : ((l.length : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (Submodule A N) :=
    Order.LTSeries.length_le_krullDim
      (LTSeries.mk l.length (fun i => Submodule.comap N.subtype (l i)) hmono)
  rw [← Module.coe_length, hl] at hq
  have hfin := h N (Submodule.fg_span (Set.finite_range x))
  have habs : ((c + 1 : ℕ) : ℕ∞) ≤ ((c : ℕ) : ℕ∞) := le_trans (by exact_mod_cast hq) hfin
  have : c + 1 ≤ c := by exact_mod_cast habs
  omega

end Ring

section CommSemiring

open scoped Pointwise

variable {A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M]

/-- `aN`, written as the image of the submodule `N` under multiplication by `a`, is the pointwise
scalar multiple `a • N`. This is the only bridge between the two readings of `aN`; the rest of
this file meets Mathlib's pointwise API through it. -/
theorem map_lsmul_eq_smul (N : Submodule A M) (a : A) :
    N.map (LinearMap.lsmul A M a) = a • N := by
  rw [Submodule.pointwise_smul_def]
  exact congrArg (fun f : M →ₗ[A] M => Submodule.map f N) (LinearMap.ext fun _ => rfl)

/-- `aM`, written as the range of multiplication by `a`, is the pointwise scalar multiple
`a • ⊤` that Mathlib's `QuotSMulTop` quotients by. -/
theorem range_lsmul_eq_smul_top (a : A) :
    LinearMap.range (LinearMap.lsmul A M a) = a • (⊤ : Submodule A M) := by
  rw [← map_lsmul_eq_smul, Submodule.map_top]

/-- For a submodule `N`, the elements of `N` lying in `aN` computed in the ambient module are
exactly the elements of `aN` computed in `N`. -/
@[simp]
theorem comap_subtype_map_lsmul (N : Submodule A M) (a : A) :
    Submodule.comap N.subtype (N.map (LinearMap.lsmul A M a))
      = LinearMap.range (LinearMap.lsmul A ↥N a) := by
  ext y
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.mem_map,
    LinearMap.mem_range, LinearMap.lsmul_apply]
  constructor
  · rintro ⟨z, hz, hzy⟩
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  · rintro ⟨z, rfl⟩
    exact ⟨(z : M), z.2, rfl⟩

end CommSemiring

section CommRing

open scoped Pointwise

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- The length of `M ⧸ aM` depends on `M` only through its linear equivalence class.

This proves nothing that Mathlib does not: it is `QuotSMulTop.congr` read through
`range_lsmul_eq_smul_top`, and exists only so that the change of spelling is not repeated at each
call site. It is stated forward-only, because rewriting back out of a `QuotSMulTop`-shaped goal is
not type-correct — the `AddCommGroup` instance on the quotient depends on the submodule being
rewritten. -/
theorem length_quotient_lsmul_congr {N : Type*} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N)
    (a : A) :
    Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M a))
      = Module.length A (N ⧸ LinearMap.range (LinearMap.lsmul A N a)) := by
  rw [range_lsmul_eq_smul_top, range_lsmul_eq_smul_top]
  exact (QuotSMulTop.congr a e).length_eq

/-- **Reduction of the length of `M ⧸ aM` to finitely generated submodules.** -/
theorem length_quotient_lsmul_le_of_forall_fg {a : A} {c : ℕ∞} (h : ∀ N : Submodule A M, N.FG →
      Module.length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N a)) ≤ c) :
    Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M a)) ≤ c := by
  set P : Submodule A M := LinearMap.range (LinearMap.lsmul A M a)
  refine length_le_of_forall_fg fun Q hQ => ?_
  -- A finitely generated submodule of `M ⧸ aM` is the image of a finitely generated `N ≤ M`.
  obtain ⟨s, hs⟩ := hQ
  choose g hg using Submodule.mkQ_surjective P
  set N : Submodule A M := Submodule.span A (g '' (s : Set (M ⧸ P))) with hN
  have hNfg : N.FG := Submodule.fg_span (s.finite_toSet.image _)
  have hQeq : Q = N.map P.mkQ := by
    rw [hN, Submodule.map_span, ← hs, ← Set.image_comp]
    congr 1
    simp [hg]
  have hle : LinearMap.range (LinearMap.lsmul A ↥N a) ≤ Submodule.comap N.subtype P := by
    rintro y ⟨z, rfl⟩
    exact ⟨(z : M), rfl⟩
  calc Module.length A ↥Q = Module.length A ↥(N.map P.mkQ) := by rw [hQeq]
    _ = Module.length A (↥N ⧸ Submodule.comap N.subtype P) := length_map_mkQ N P
    _ ≤ Module.length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N a)) :=
        length_quotient_anti hle
    _ ≤ c := h N hNfg

/-- In a Noetherian ring of Krull dimension at most one, the quotient by an ideal containing a
non-zero-divisor has finite length. -/
theorem isFiniteLength_quotient_of_nonZeroDivisor_mem [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    (I : Ideal A) {x : A} (hxI : x ∈ I) (hx : x ∈ nonZeroDivisors A) :
    IsFiniteLength A (A ⧸ I) := by
  have hle : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hxI
  exact (isFiniteLength_quotient_span_singleton A hx).of_surjective
    (f := Submodule.factor hle) (Submodule.factor_surjective hle)

/-- **The length of `I ⧸ aI` for an ideal `I`.** For an ideal `I` with `A ⧸ I` of finite length
and a non-zero-divisor `a`, `length (I ⧸ aI)` is the order of vanishing `Ring.ord A a`, which is
by definition `length (A ⧸ aA)`.

Both sides are read off `length (A ⧸ aI)`, which splits in two ways. Mathlib's exact sequence
`A ⧸ I ↪ A ⧸ aI ↠ A ⧸ aA` — multiplication by `a`, then quotienting further, from
`Ideal.exact_mulQuot_quotOfMul` — splits it as `length (A ⧸ I) + length (A ⧸ aA)`, while the
filtration `aI ≤ I ≤ A` splits it as `length (I ⧸ aI) + length (A ⧸ I)`. Cancelling the common
term, finite by hypothesis, leaves the claim. -/
theorem length_quotient_lsmul_ideal_eq_ord (I : Ideal A) (hI : IsFiniteLength A (A ⧸ I)) (a : A)
    (ha : a ∈ nonZeroDivisors A) :
    Module.length A (↥I ⧸ LinearMap.range (LinearMap.lsmul A ↥I a)) = Ring.ord A a := by
  have hord : Ring.ord A a = Module.length A (A ⧸ Ideal.span {a}) := rfl
  have hfin : Module.length A (A ⧸ I) ≠ ⊤ := Module.length_ne_top_iff.mpr hI
  have hexact : Module.length A (A ⧸ Submodule.map (LinearMap.lsmul A A a) I)
      = Module.length A (A ⧸ I) + Module.length A (A ⧸ Ideal.span {a}) := by
    rw [map_lsmul_eq_smul]
    exact Module.length_eq_add_of_exact (Ideal.mulQuot a I) (Ideal.quotOfMul a I)
      (Ideal.mulQuot_injective I ha) (Ideal.quotOfMul_surjective I)
      (Ideal.exact_mulQuot_quotOfMul I)
  -- The filtration `aI ≤ I ≤ A` splits the same length the other way.
  have hleI : Submodule.map (LinearMap.lsmul A A a) I ⊔ I = I := by
    refine sup_eq_right.mpr ?_
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    simpa [LinearMap.lsmul_apply] using I.smul_mem a hx
  have hfilt := length_quotient_eq_length_map_add_length_quotient_sup I
    (Submodule.map (LinearMap.lsmul A A a) I)
  rw [hleI, length_map_mkQ, comap_subtype_map_lsmul, hexact] at hfilt
  rw [hord]
  exact (WithTop.add_left_cancel hfin (hfilt.trans (add_comm _ _))).symm

end CommRing

end TauCeti
