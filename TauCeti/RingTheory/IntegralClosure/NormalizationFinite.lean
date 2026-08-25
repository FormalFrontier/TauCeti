/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Proof-only: the dual space appears in the private induction helpers, not in any statement.
import Mathlib.LinearAlgebra.Dual.Lemmas
-- Proof-only: fractional ideals appear in the private rank-one helper, not in any statement.
import Mathlib.RingTheory.FractionalIdeal.Operations
public import TauCeti.RingTheory.Length

/-!
# Krull–Akizuki: an integral closure that is Noetherian without separability

Let `A` be a Noetherian domain of Krull dimension at most one, let `K` be its fraction field and
let `L` be a finite extension of `K`. This file proves that any integral closure of `A` in `L` is
a Noetherian ring. No separability of `L / K` is assumed, and the integral closure is *not* claimed
to be a finite `A`-module — it need not be.

The engine is a length bound. Write `aM` for the image of multiplication by `a` on a module `M`,
which is `LinearMap.range (LinearMap.lsmul A M a)`. For a finite-dimensional `K`-vector space `V`,
an arbitrary `A`-submodule `M ≤ V` and a nonzero `a : A`,

```text
length_A (M ⧸ aM) ≤ dim_K V * ord_A a,
```

where `ord_A a = length_A (A ⧸ aA)` is Mathlib's `Ring.ord`. The right-hand side is finite because
the quotient by a nonzero principal ideal of a one-dimensional Noetherian domain has finite length.
Applied to `M` the integral closure sitting inside `V = L`, this makes `C ⧸ aC` a Noetherian
`A`-module, which is enough to finitely generate every ideal of `C`.

## Main results

* `TauCeti.length_quotient_lsmul_le_finrank_mul_ord`: the Krull–Akizuki length bound displayed
  above.
* `TauCeti.isFiniteLength_quotient_lsmul`: the finiteness that bound delivers.
* `TauCeti.IsIntegralClosure.isNoetherianRing`: **Krull–Akizuki**, for any integral closure `C` of
  `A` in `L`.
* `TauCeti.integralClosure.isNoetherianRing`: the same for Mathlib's `integralClosure A L`.

The general facts about `Module.length` that the bound rests on — additivity along a filtration,
the reduction of a length bound to finitely generated submodules, and the rank-one computation
`length (I ⧸ aI) = ord_A a` for an ideal `I` — are in `TauCeti/RingTheory/Length.lean`.

## Proof outline

The bound is proved by induction on `n ≥ dim_K U` for a `K`-subspace `U` containing `M`, with `M`
finitely generated (`length_quotient_lsmul_le_mul_ord_of_finrank_le`);
`TauCeti.length_quotient_lsmul_le_of_forall_fg` then removes the finite generation. The inductive
step runs on a projection built from a functional supplied by Mathlib's
`Module.Projective.exists_dual_eq_one`; `ker_id_sub_smulRight` and `finrank_ker_inf_add_one` are
the rest of that construction, isolated. Filtration additivity splits `length (M ⧸ aM)` into the
part supported on `N = M ⊓ K ∙ x` and the part seen by the projection `e`. The first is bounded by
`length_quotient_lsmul_le_ord_of_le_span_singleton`, which clears denominators to reach the
rank-one case in `Length.lean`; the second is `length (e M ⧸ a e M)`, and `e M` lies one dimension
lower.

## Design

`Ring.KrullDimLE 1` is used rather than `Ring.DimensionLEOne`; both predicates live in the pinned
Mathlib, and `Ring.krullDimLE_one_iff_of_noZeroDivisors` unfolds the former into exactly the
latter's content over a domain, so a caller holding either one can supply the other.

Multiplication by `a` is written as `LinearMap.range (LinearMap.lsmul A M a)` throughout rather
than as a pointwise scalar action on submodules. That keeps every statement inside the plain
`Submodule` API, and the compatibility of the two readings is confined to `Length.lean`, where
`TauCeti.map_lsmul_eq_smul` is the single bridge.

Krull–Akizuki is stated for an abstract `C` with `[IsIntegralClosure C A L]`, following Mathlib's
convention for `IsIntegralClosure.isNoetherianRing`, with the `integralClosure A L` form derived
from it. The roadmap consumer needs the abstract form: its intermediate ring is a `Subring` of a
function field known to be an integral closure, not Mathlib's literal `integralClosure` subalgebra.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), which names
`RingTheory/IntegralClosure/NormalizationFinite` among the three supports of D. Angdinata's
isogeny development. The file
`TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/IntermediateRing/Dedekind.lean` records the
missing piece precisely: its Dedekind conclusion carries a separability hypothesis only because
every Mathlib route to Noetherianity of an integral closure sits under the section variable
`[Algebra.IsSeparable K L]` declared at `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`
line 147. This file lands the Noetherian half of that module and removes that obstruction;
finiteness of the normalization (the Nagata/N-2 half) is separate and is not proved here.

This is original mathematics for the project, not a port. The pinned Mathlib has no Krull–Akizuki
and no `IsNagata` / `IsJapanese` / `IsExcellent`. AINTLIB (`github.com/CBirkbeck/AINTLIB`,
Apache-2.0), at the revision the roadmap pins for its HasseWeil project
(`dev/hasse-weil @ 513e83879e2f`), states the result only in the separable case and obtains it
from Mathlib — `HasseWeil/Curves/NormConormIntegralClosure.lean:88` (`instDedekindB`) and
`HasseWeil/Curves/RamificationFinite.lean:90` — so it supplies nothing reusable here.
The argument follows the classical one (Matsumura, *Commutative Ring Theory*, Theorem 11.7).
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

/-! ### The dimension-dropping projection

The two lemmas of this section are the inductive step's tool: the projection defined by a
functional normalised at `x`, and the dimension that projection removes. The functional itself
comes from Mathlib's `Module.Projective.exists_dual_eq_one`.
-/

section Projection

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If `φ x = 1` then `id - φ(·) • x` kills exactly the line through `x`. -/
private theorem ker_id_sub_smulRight (φ : Module.Dual K V) {x : V} (hφx : φ x = 1) :
    LinearMap.ker (LinearMap.id - LinearMap.smulRight φ x) = K ∙ x := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, sub_eq_zero, Submodule.mem_span_singleton]
  exact ⟨fun h => ⟨φ y, h.symm⟩, by rintro ⟨c, rfl⟩; simp [hφx]⟩

/-- Cutting a subspace containing `x` by the kernel of a functional normalised at `x` removes
exactly one dimension. -/
private theorem finrank_ker_inf_add_one [Module.Finite K V] (φ : Module.Dual K V) {x : V}
    (hφx : φ x = 1) {U : Submodule K V} (hxU : x ∈ U) :
    Module.finrank K ↥(LinearMap.ker φ ⊓ U) + 1 = Module.finrank K ↥U := by
  have hne : φ.domRestrict U ≠ 0 := fun h => by
    have hx : (φ.domRestrict U) ⟨x, hxU⟩ = 0 := by rw [h]; rfl
    rw [LinearMap.domRestrict_apply] at hx
    simp [hφx] at hx
  have hker : LinearMap.ker (φ.domRestrict U)
      = Submodule.comap U.subtype (LinearMap.ker φ ⊓ U) := by
    rw [LinearMap.ker_domRestrict, Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  have hfin := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rwa [hker, (Submodule.comapSubtypeEquivOfLe
    (inf_le_right : LinearMap.ker φ ⊓ U ≤ U)).finrank_eq] at hfin

end Projection

/-! ### The induced map on a linear image -/

section Kernel

variable {A : Type*} [CommRing A]

/-- The kernel of the map `M → eM ⧸ a·eM` induced by a linear endomorphism `e` is
`aM ⊔ (M ⊓ ker e)`. -/
private theorem ker_mkQ_comp_codRestrict {V : Type*} [AddCommGroup V] [Module A V]
    (e : V →ₗ[A] V) (M : Submodule A V) (a : A) :
    LinearMap.ker ((LinearMap.range (LinearMap.lsmul A ↥(M.map e) a)).mkQ ∘ₗ
        LinearMap.codRestrict (M.map e) (e ∘ₗ M.subtype) (fun y => Submodule.mem_map_of_mem y.2))
      = LinearMap.range (LinearMap.lsmul A ↥M a) ⊔ Submodule.comap M.subtype (LinearMap.ker e) := by
  set g : ↥M →ₗ[A] ↥(M.map e) :=
    LinearMap.codRestrict (M.map e) (e ∘ₗ M.subtype) (fun y => Submodule.mem_map_of_mem y.2)
  refine le_antisymm (fun y hy => ?_) (sup_le ?_ ?_)
  · -- `e y ∈ a·eM` means `e y = e (a v)` for some `v ∈ M`, so `y - a v` lies in `M ⊓ ker e`.
    have hgy : g y ∈ LinearMap.range (LinearMap.lsmul A ↥(M.map e) a) := by
      rwa [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨w, hw⟩ := hgy
    obtain ⟨v, hv, hvw⟩ := w.2
    have hgyv : e ((y : ↥M) : V) = a • ((w : ↥(M.map e)) : V) := by
      have hval := congrArg (fun t : ↥(M.map e) => (t : V)) hw
      simpa [g] using hval.symm
    have hkey : e (((y : ↥M) : V) - a • v) = 0 := by
      rw [map_sub, map_smul, hvw, hgyv, sub_self]
    have hmemM : ((y : ↥M) : V) - a • v ∈ M := M.sub_mem y.2 (M.smul_mem a hv)
    have hdec : y = a • (⟨v, hv⟩ : ↥M) + ⟨((y : ↥M) : V) - a • v, hmemM⟩ := by
      ext; simp
    rw [hdec]
    exact Submodule.add_mem_sup ⟨⟨v, hv⟩, rfl⟩ hkey
  · rintro _ ⟨z, rfl⟩
    have hgz : g (LinearMap.lsmul A ↥M a z) = LinearMap.lsmul A ↥(M.map e) a (g z) := by
      simp [g, LinearMap.lsmul_apply, map_smul]
    rw [LinearMap.mem_ker, LinearMap.comp_apply, hgz, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨g z, rfl⟩
  · intro z hz
    have hez : e ((z : ↥M) : V) = 0 := LinearMap.mem_ker.mp (Submodule.mem_comap.mp hz)
    have hgz : g z = 0 := Subtype.ext hez
    rw [LinearMap.mem_ker, LinearMap.comp_apply, hgz, map_zero]

end Kernel

/-! ### The rank-one case over the fraction field -/

section Domain

variable {A : Type*} [CommRing A] [IsDomain A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- **The rank-one case for a finitely generated `A`-submodule of the fraction field.** For
`J ≤ K` finitely generated over `A` and `a ≠ 0`, `length (J ⧸ aJ) ≤ ord_A a`.

Such a `J` is a fractional ideal, and multiplying by its denominator identifies it with the
integral ideal `J.num`, where `length_quotient_lsmul_ideal_eq_ord` gives the corresponding
*equality*. The conclusion here is an inequality only because `J = ⊥` is allowed, and there both
sides need not agree. -/
private theorem length_quotient_lsmul_fractionRing_le_ord [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] (J : Submodule A K) (hJ : J.FG) (a : A) (ha : a ≠ 0) :
    Module.length A (↥J ⧸ LinearMap.range (LinearMap.lsmul A ↥J a)) ≤ Ring.ord A a := by
  rcases eq_or_ne J ⊥ with rfl | hJ0
  · refine le_trans (le_of_eq ?_) zero_le
    refine Module.length_eq_zero_iff.mpr ⟨fun p q => ?_⟩
    obtain ⟨p', rfl⟩ := Submodule.mkQ_surjective _ p
    obtain ⟨q', rfl⟩ := Submodule.mkQ_surjective _ q
    rw [Subsingleton.elim p' q']
  -- A finitely generated submodule of `K` is a fractional ideal.
  set I : FractionalIdeal A⁰ K := ⟨J, FractionalIdeal.isFractional_of_fg hJ⟩
  have hIJ : (I : Submodule A K) = J := rfl
  have hInum : I.num ≠ ⊥ := by
    intro hnum
    refine hJ0 ?_
    rw [← hIJ, FractionalIdeal.num_eq_zero_iff.mp hnum]
    simp
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hInum
  -- Multiplication by the denominator carries it onto the integral ideal `I.num`.
  rw [← hIJ, length_quotient_lsmul_congr (FractionalIdeal.equivNumOfIsLocalization I) a]
  exact le_of_eq (length_quotient_lsmul_ideal_eq_ord I.num
    (isFiniteLength_quotient_of_nonZeroDivisor_mem I.num hyI
      (mem_nonZeroDivisors_of_ne_zero hy0))
    a (mem_nonZeroDivisors_of_ne_zero ha))

/-! ### The rank induction -/

variable {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

/-- A finitely generated `A`-submodule of a `K`-line obeys the rank-one bound: a functional
normalised at a spanning vector embeds it in `K`. -/
private theorem length_quotient_lsmul_le_ord_of_le_span_singleton [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] (a : A) (ha : a ≠ 0) {x : V} (N : Submodule A V)
    (hN : N ≤ (K ∙ x).restrictScalars A) (hfg : N.FG) :
    Module.length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N a)) ≤ Ring.ord A a := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have hN0 : N = ⊥ := by
      refine le_bot_iff.mp fun y hy => ?_
      have hy' := hN hy
      rw [Submodule.restrictScalars_mem, Submodule.span_zero_singleton, Submodule.mem_bot] at hy'
      simpa using hy'
    subst hN0
    simp
  obtain ⟨φ, hφx⟩ := Module.Projective.exists_dual_eq_one K hx0
  set ι : ↥N →ₗ[A] K := (φ.restrictScalars A) ∘ₗ N.subtype with hιdef
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hzx : (z : V) ∈ K ∙ x := by
      rw [← Submodule.restrictScalars_mem (S := A)]; exact hN z.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzx
    have hz' : φ (z : V) = 0 := by simpa [hιdef] using hz
    rw [← hc, map_smul, hφx, smul_eq_mul, mul_one] at hz'
    exact Subtype.ext (by rw [← hc, hz', zero_smul]; simp)
  have hJfg : (LinearMap.range ι).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.finite_def.mp (Module.Finite.iff_fg.mpr hfg)).map ι
  rw [length_quotient_lsmul_congr (LinearEquiv.ofInjective ι hιinj) a]
  exact length_quotient_lsmul_fractionRing_le_ord _ hJfg a ha

/-- **The Krull–Akizuki length bound for a finitely generated submodule**, relative to any bound
`n` on the dimension of a `K`-subspace containing it. -/
private theorem length_quotient_lsmul_le_mul_ord_of_finrank_le [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [Module.Finite K V] (a : A) (ha : a ≠ 0) (n : ℕ) (U : Submodule K V)
    (hU : Module.finrank K U ≤ n) (M : Submodule A V) (hM : M ≤ U.restrictScalars A) (hfg : M.FG) :
    Module.length A (↥M ⧸ LinearMap.range (LinearMap.lsmul A ↥M a)) ≤ n * Ring.ord A a := by
  induction n generalizing U M with
  | zero =>
      have hU0 : U = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU)
      have hM0 : M = ⊥ := by
        refine le_bot_iff.mp fun y hy => ?_
        have hyU := hM hy
        rw [hU0] at hyU
        simpa using hyU
      subst hM0
      simp
  | succ n ih =>
      rcases eq_or_ne M ⊥ with rfl | hM0
      · simp
      -- Phase 1: build the projection `e` killing the line `K ∙ x` through some `0 ≠ x ∈ M`.
      obtain ⟨x, hxM, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM0
      obtain ⟨φ, hφx⟩ := Module.Projective.exists_dual_eq_one K hx0
      set e : V →ₗ[K] V := LinearMap.id - LinearMap.smulRight φ x with hedef
      have hkere : LinearMap.ker e = K ∙ x := ker_id_sub_smulRight φ hφx
      set eA : V →ₗ[A] V := e.restrictScalars A with heAdef
      have hkereA : LinearMap.ker eA = (K ∙ x).restrictScalars A := by
        rw [heAdef, LinearMap.ker_restrictScalars, hkere]
      have hxU : x ∈ U := hM hxM
      have hrkU' : Module.finrank K ↥(LinearMap.ker φ ⊓ U) ≤ n := by
        have := finrank_ker_inf_add_one φ hφx hxU
        omega
      -- Phase 2: split `length (M ⧸ aM)` along `N = M ⊓ K ∙ x`.
      set P : Submodule A ↥M := LinearMap.range (LinearMap.lsmul A ↥M a)
      set N : Submodule A ↥M := Submodule.comap M.subtype ((K ∙ x).restrictScalars A) with hNdef
      have : Module.Finite A ↥M := Module.Finite.iff_fg.mpr hfg
      have hNfg : N.FG := IsNoetherian.noetherian N
      -- Phase 3: `N` lives on the line `K ∙ x`, so the rank-one bound applies to it.
      have hterm1 : Module.length A (N.map P.mkQ) ≤ Ring.ord A a := by
        rw [length_map_mkQ]
        calc Module.length A (↥N ⧸ Submodule.comap N.subtype P)
            ≤ Module.length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N a)) := by
              refine length_quotient_anti ?_
              rintro y ⟨z, rfl⟩
              exact ⟨(z : ↥M), rfl⟩
          _ = Module.length A (↥(N.map M.subtype) ⧸
                LinearMap.range (LinearMap.lsmul A ↥(N.map M.subtype) a)) :=
              length_quotient_lsmul_congr
                (Submodule.equivMapOfInjective M.subtype (Submodule.subtype_injective M) N) a
          _ ≤ Ring.ord A a :=
              length_quotient_lsmul_le_ord_of_le_span_singleton a ha _
                (by rw [hNdef]; exact Submodule.map_comap_le _ _) (hNfg.map _)
      -- Phase 4: the rest is `e M ⧸ a·e M`, one dimension lower, so the hypothesis applies.
      set M' : Submodule A V := M.map eA
      have hM'U : M' ≤ (LinearMap.ker φ ⊓ U).restrictScalars A := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨by simp [heAdef, hedef, hφx], by
          simpa [heAdef, hedef] using U.sub_mem (hM hy) (U.smul_mem _ hxU)⟩
      set Q : Submodule A ↥M' := LinearMap.range (LinearMap.lsmul A ↥M' a)
      set g : ↥M →ₗ[A] ↥M' :=
        LinearMap.codRestrict M' (eA ∘ₗ M.subtype) (fun y => Submodule.mem_map_of_mem y.2)
      have hgsurj : Function.Surjective g := by
        rintro ⟨_, y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      have hker : LinearMap.ker (Q.mkQ ∘ₗ g) = P ⊔ N := by
        rw [ker_mkQ_comp_codRestrict eA M a, hkereA]
      have hterm2 : Module.length A (↥M ⧸ (P ⊔ N)) ≤ n * Ring.ord A a := by
        rw [← hker, (LinearMap.quotKerEquivOfSurjective (Q.mkQ ∘ₗ g)
          ((Submodule.mkQ_surjective Q).comp hgsurj)).length_eq]
        exact ih (LinearMap.ker φ ⊓ U) hrkU' M' hM'U (hfg.map eA)
      rw [length_quotient_eq_length_map_add_length_quotient_sup N P]
      calc Module.length A (N.map P.mkQ) + Module.length A (↥M ⧸ (P ⊔ N))
          ≤ Ring.ord A a + n * Ring.ord A a := add_le_add hterm1 hterm2
        _ = (n + 1 : ℕ) * Ring.ord A a := by push_cast; rw [add_mul, one_mul, add_comm]

/-- **Krull–Akizuki's length bound.** For any `A`-submodule `M` of a finite-dimensional
`K`-vector space `V` — finitely generated or not — and any nonzero `a : A`,
`length (M ⧸ aM) ≤ dim_K V * ord_A a`. -/
theorem length_quotient_lsmul_le_finrank_mul_ord [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Module.Finite K V] (M : Submodule A V) (a : A) (ha : a ≠ 0) :
    Module.length A (↥M ⧸ LinearMap.range (LinearMap.lsmul A ↥M a))
      ≤ Module.finrank K V * Ring.ord A a := by
  refine length_quotient_lsmul_le_of_forall_fg fun N hN => ?_
  rw [length_quotient_lsmul_congr
    (Submodule.equivMapOfInjective M.subtype (Submodule.subtype_injective M) N) a]
  exact length_quotient_lsmul_le_mul_ord_of_finrank_le a ha (Module.finrank K V)
    (⊤ : Submodule K V) (le_of_eq (finrank_top K V)) (N.map M.subtype)
    (fun _ _ => Submodule.mem_top) (hN.map _)

/-- **Krull–Akizuki's finiteness.** Under the hypotheses of the length bound, `M ⧸ aM` has finite
length; equivalently it is both Noetherian and Artinian over `A`. -/
theorem isFiniteLength_quotient_lsmul [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Module.Finite K V] (M : Submodule A V) (a : A) (ha : a ≠ 0) :
    IsFiniteLength A (↥M ⧸ LinearMap.range (LinearMap.lsmul A ↥M a)) :=
  Module.length_ne_top_iff.mp (ne_top_of_le_ne_top
    (WithTop.mul_ne_top (ENat.natCast_ne_top _)
      (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha)))
    (length_quotient_lsmul_le_finrank_mul_ord (K := K) M a ha))

end Domain

/-! ### Krull–Akizuki -/

section Lifting

variable {A : Type*} [CommRing A]

/-- If the image of `a` lies in the ideal `𝔟` of an `A`-algebra `B` and `B ⧸ aB` is Noetherian as
an `A`-module, then `𝔟` is finitely generated as a `B`-ideal.

The `A`-submodule `aB` is the `B`-ideal generated by the image of `a`, so `B ⧸ aB` is Noetherian
over `B` as well; `𝔟` then sits in an extension of its finitely generated image in `B ⧸ aB` by the
principal ideal `aB`. -/
private theorem fg_of_isNoetherian_quotient_lsmul {B : Type*} [CommRing B] [Algebra A B] (a : A)
    (𝔟 : Ideal B) (ha : algebraMap A B a ∈ 𝔟)
    (h : IsNoetherian A (B ⧸ LinearMap.range (LinearMap.lsmul A B a))) : 𝔟.FG := by
  set Q : Ideal B := Ideal.span {algebraMap A B a} with hQdef
  have hPQ : LinearMap.range (LinearMap.lsmul A B a) = Q.restrictScalars A := by
    ext y
    simp [hQdef, Ideal.mem_span_singleton', Algebra.smul_def, eq_comm, mul_comm]
  rw [hPQ] at h
  have : IsNoetherian B (B ⧸ Q) :=
    isNoetherian_of_tower A (isNoetherian_of_linearEquiv
      (Submodule.Quotient.restrictScalarsEquiv A Q))
  refine Submodule.fg_of_fg_map_of_fg_inf_ker Q.mkQ (IsNoetherian.noetherian _) ?_
  rw [Submodule.ker_mkQ, inf_eq_right.2 ((Ideal.span_singleton_le_iff_mem _).2 ha)]
  exact Submodule.fg_span_singleton _

end Lifting

section IntegralClosure

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
variable {L : Type*} [Field L] [Algebra A L]

/-- **Krull–Akizuki.** An integral closure `C` of a Noetherian domain of Krull dimension at most
one in a finite extension `L` of its fraction field is a Noetherian ring. No separability of `L`
over the fraction field is assumed, and `C` need not be a finite `A`-module. -/
theorem IsIntegralClosure.isNoetherianRing (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L] [Module.Finite K L] (C : Type*) [CommRing C] [Algebra A C]
    [Algebra C L] [IsScalarTower A C L] [IsIntegralClosure C A L] :
    IsNoetherianRing C := by
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  have : IsDomain C := Function.Injective.isDomain (algebraMap C L)
    (IsIntegralClosure.algebraMap_injective C A L)
  rw [isNoetherianRing_iff_ideal_fg]
  intro 𝔟
  rcases eq_or_ne 𝔟 ⊥ with rfl | h0
  · exact Submodule.fg_bot
  -- A nonzero ideal of an integral extension meets the base ring in a nonzero element.
  obtain ⟨a, ha𝔟, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.IsIntegral.comap_ne_bot (A := C) A h0)
  -- `C` is an `A`-submodule of `L`, so the length bound makes `C ⧸ aC` a Noetherian `A`-module.
  have hinj : Function.Injective ((Algebra.linearMap C L).restrictScalars A) :=
    IsIntegralClosure.algebraMap_injective C A L
  have hlen : Module.length A (C ⧸ LinearMap.range (LinearMap.lsmul A C a)) ≠ ⊤ := by
    rw [length_quotient_lsmul_congr (LinearEquiv.ofInjective _ hinj) a]
    exact Module.length_ne_top_iff.mpr (isFiniteLength_quotient_lsmul (K := K) _ a ha0)
  exact fg_of_isNoetherian_quotient_lsmul a 𝔟 ha𝔟
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hlen)).1

/-- **Krull–Akizuki for Mathlib's `integralClosure`.** The specialisation of
`TauCeti.IsIntegralClosure.isNoetherianRing` to the integral closure of `A` in `L` as a
subalgebra. -/
theorem integralClosure.isNoetherianRing (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L] [Module.Finite K L] :
    IsNoetherianRing (integralClosure A L) :=
  _root_.TauCeti.IsIntegralClosure.isNoetherianRing (A := A) (L := L) K (integralClosure A L)

end IntegralClosure

end TauCeti
