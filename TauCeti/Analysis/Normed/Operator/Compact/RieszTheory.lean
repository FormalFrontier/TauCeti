/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Operator.Compact.Eigenspace

/-!
# Riesz theory for compact perturbations of the identity

Let `K` be a compact operator on a Banach space `X` and write `A = 1 - K`. This file proves the
three finiteness facts that make `A` a Fredholm operator: its kernel is finite dimensional, its
range is closed, and its cokernel is finite dimensional. Together they are the operator-theoretic
half of the Riesz--Schauder theory, and they are what upgrades Mathlib's spectral Fredholm
alternative for compact operators to a statement about Fredholm operators.

Compactness enters the three arguments in different forms: the kernel argument uses the existing
finite-dimensional eigenspace theorem, the range argument extracts a convergent subsequence with
`TauCeti.IsCompactOperator.exists_subseq_tendsto`, and the cokernel argument uses the separation
consequence `TauCeti.IsCompactOperator.exists_dist_lt_of_norm_le`.

* The kernel is the `1`-eigenspace of `K`, already known to be finite dimensional.
* For the range, split off a closed complement `M` of `ker A`, which exists because `ker A` is
  finite dimensional. On `M` the operator `A` is bounded below: otherwise a sequence in a fixed
  norm shell with `A xₙ → 0` would, along a subsequence on which `K` converges, converge to a
  nonzero element of `ker A ⊓ M`. A bounded-below map on a complete space has closed range.
* For the cokernel, run the classical Riesz argument on the decreasing chain of ranges
  `range A ⊇ range A² ⊇ ⋯`. Each `Aⁿ` is again `1` minus a compact operator, so each of these
  ranges is closed, and Riesz's lemma would otherwise produce a separated bounded sequence. Once
  the chain stabilises at `p`, every `x` splits as an element of `ker A ^ (p + 1)` plus an element
  of `range A ^ (p + 1) ≤ range A`, so `ker A ^ (p + 1)` surjects onto the cokernel.

## Main declarations

* `TauCeti.IsCompactOperator.exists_pos_mul_norm_le_of_disjoint_ker`: `1 - K` is bounded below on
  any closed subspace meeting its kernel trivially.
* `TauCeti.IsCompactOperator.finiteDimensional_ker_one_sub`: `ker (1 - K)` is finite dimensional.
* `TauCeti.IsCompactOperator.isClosed_range_one_sub`: `range (1 - K)` is closed.
* `TauCeti.IsCompactOperator.isCompactOperator_one_sub_pow`: `1 - (1 - K) ^ n` is compact, so
  every power of `1 - K` is again a compact perturbation of the identity.
* `TauCeti.IsCompactOperator.finiteDimensional_quotient_range_one_sub`: `X ⧸ range (1 - K)` is
  finite dimensional.

The argument is the classical Riesz theory of compact operators; see, for example, Conway,
*A Course in Functional Analysis*, Chapter VI, Section 5, or Rudin, *Functional Analysis*,
Chapter 4. It supplies the compact-perturbation half of the Fredholm package asked for in Lane F0
of the analytic Heegaard Floer roadmap.
-/

public section

namespace TauCeti

open Filter Module
open scoped Topology

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {K : X →L[𝕜] X}

/-- The kernel of `1 - K` is the `1`-eigenspace of `K`. -/
@[simp]
theorem ker_one_sub (K : X →L[𝕜] X) :
    LinearMap.ker (1 - (K : X →ₗ[𝕜] X)) = End.eigenspace (K : X →ₗ[𝕜] X) 1 := by
  ext x
  rw [LinearMap.mem_ker, End.mem_eigenspace_iff]
  rw [LinearMap.sub_apply, Module.End.one_apply, one_smul, sub_eq_zero]
  exact eq_comm

namespace IsCompactOperator

/-- **A bounded sequence whose `(1 - K)`-images vanish in the limit has a subsequence converging
to a point of `ker (1 - K)`.** The bound `R` on the sequence is arbitrary. -/
private theorem exists_subseq_tendsto_mem_ker (hK : IsCompactOperator K) {R : ℝ} {v : ℕ → X}
    (hvle : ∀ n, ‖v n‖ ≤ R)
    (hAtendsto : Tendsto (fun n => (1 - K : X →L[𝕜] X) (v n)) atTop (𝓝 0)) :
    ∃ (y : X) (ψ : ℕ → ℕ), StrictMono ψ ∧ Tendsto (fun k => v (ψ k)) atTop (𝓝 y) ∧
      y ∈ LinearMap.ker ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) := by
  obtain ⟨y, ψ, hψ, hψy⟩ := exists_subseq_tendsto hK hvle
  have hvsub : Tendsto (fun k => v (ψ k)) atTop (𝓝 y) := by
    -- `v = (1 - K) v + K v`, and both summands converge along the subsequence.
    have hsum : ∀ k, (1 - K : X →L[𝕜] X) (v (ψ k)) + K (v (ψ k)) = v (ψ k) := by
      intro k
      rw [sub_apply, one_apply_eq_self]
      abel
    have hlim : Tendsto (fun k => (1 - K : X →L[𝕜] X) (v (ψ k)) + K (v (ψ k))) atTop
        (𝓝 (0 + y)) := (hAtendsto.comp hψ.tendsto_atTop).add hψy
    rw [zero_add] at hlim
    exact Filter.Tendsto.congr hsum hlim
  have h1 : Tendsto (fun k => (1 - K : X →L[𝕜] X) (v (ψ k))) atTop
      (𝓝 ((1 - K : X →L[𝕜] X) y)) :=
    (((1 : X →L[𝕜] X) - K).continuous.tendsto y).comp hvsub
  have h0 : Tendsto (fun k => (1 - K : X →L[𝕜] X) (v (ψ k))) atTop (𝓝 0) :=
    hAtendsto.comp hψ.tendsto_atTop
  exact ⟨y, ψ, hψ, hvsub, LinearMap.mem_ker.mpr (tendsto_nhds_unique h1 h0)⟩

/-- On a closed subspace `M` meeting `ker (1 - K)` only in `0`, the operator `1 - K` is bounded
below.

Were it not, a sequence of vectors in a fixed norm shell whose images tend to `0` would, along a
subsequence on which `K` converges, converge to a nonzero vector of `ker (1 - K) ⊓ M`. -/
theorem exists_pos_mul_norm_le_of_disjoint_ker (hK : IsCompactOperator K) {M : Submodule 𝕜 X}
    (hM : IsClosed (M : Set X))
    (hdisj : Disjoint (LinearMap.ker ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X)) M) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ M, c * ‖x‖ ≤ ‖(1 - K : X →L[𝕜] X) x‖ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hcpos : (0 : ℝ) < ‖c‖ := one_pos.trans hc
  choose u huM hu using fun n : ℕ => hcon (1 / (n + 1) : ℝ) (by positivity)
  have hune : ∀ n, u n ≠ 0 := by
    intro n hn
    have h := hu n
    rw [hn] at h
    simp at h
  choose d hd0 hdlt hdge hdaux using fun n => rescale_to_shell hc one_pos (hune n)
  clear hdaux
  set v : ℕ → X := fun n => d n • u n with hv
  have hvM : ∀ n, v n ∈ M := fun n => M.smul_mem _ (huM n)
  have hvle : ∀ n, ‖v n‖ ≤ 1 := fun n => (hdlt n).le
  have hvge : ∀ n, ‖c‖⁻¹ ≤ ‖v n‖ := by
    intro n
    simpa [one_div] using hdge n
  have hAv : ∀ n, ‖(1 - K : X →L[𝕜] X) (v n)‖ ≤ 1 / (n + 1) := by
    intro n
    have hdn : (0 : ℝ) ≤ ‖d n‖ := norm_nonneg _
    have hstep : (1 : ℝ) / (n + 1) * ‖v n‖ ≤ 1 / (n + 1) := by
      have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
      simpa using mul_le_mul_of_nonneg_left (hvle n) hpos.le
    calc ‖(1 - K : X →L[𝕜] X) (v n)‖
        = ‖d n‖ * ‖(1 - K : X →L[𝕜] X) (u n)‖ := by simp [hv, norm_smul]
      _ ≤ ‖d n‖ * (1 / (n + 1) * ‖u n‖) := mul_le_mul_of_nonneg_left (hu n).le hdn
      _ = 1 / (n + 1) * ‖v n‖ := by rw [hv]; simp only [norm_smul]; ring
      _ ≤ 1 / (n + 1) := hstep
  have hAtendsto : Tendsto (fun n => (1 - K : X →L[𝕜] X) (v n)) atTop (𝓝 0) :=
    squeeze_zero_norm hAv tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨y, ψ, -, hvsub, hyker⟩ := exists_subseq_tendsto_mem_ker hK hvle hAtendsto
  have hyM : y ∈ M := hM.mem_of_tendsto hvsub (Eventually.of_forall fun k => hvM (ψ k))
  have hy0 : y = 0 := by simpa using hdisj.le_bot ⟨hyker, hyM⟩
  have hyge : ‖c‖⁻¹ ≤ ‖y‖ := ge_of_tendsto' hvsub.norm fun k => hvge (ψ k)
  rw [hy0, norm_zero] at hyge
  exact absurd hyge (not_le.mpr (by positivity))

/-- Every power of a compact perturbation of the identity is again a compact perturbation of the
identity. -/
theorem isCompactOperator_one_sub_pow (hK : IsCompactOperator K) (n : ℕ) :
    IsCompactOperator ⇑((1 : X →L[𝕜] X) - (1 - K) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, sub_self]
    simpa using isCompactOperator_zero (M₁ := X) (M₂ := X)
  | succ n ih =>
    have key : (1 : X →L[𝕜] X) - (1 - K) ^ (n + 1)
        = ((1 : X →L[𝕜] X) - (1 - K) ^ n) + (1 - K) ^ n * K := by
      rw [pow_succ, mul_sub, mul_one]
      abel
    rw [key]
    simpa using ih.add (by simpa using hK.clm_comp ((1 - K : X →L[𝕜] X) ^ n))

section Chain

/-- Riesz's lemma in the form used below: a proper closed subspace `P` of a subspace `Q` contains
a vector of `Q` of controlled norm at distance at least `1` from `P`. -/
private theorem exists_riesz {P Q : Submodule 𝕜 X} (hPQ : P ≤ Q) (hP : IsClosed (P : Set X))
    (hne : P ≠ Q) {c : 𝕜} (hc : 1 < ‖c‖) :
    ∃ x ∈ Q, ‖x‖ ≤ ‖c‖ + 1 ∧ ∀ y ∈ P, 1 ≤ ‖x - y‖ := by
  have h₁ : IsClosed ((P.comap Q.subtype : Submodule 𝕜 Q) : Set Q) :=
    hP.preimage continuous_subtype_val
  have h₂ : ∃ x : Q, x ∉ P.comap Q.subtype := by
    obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hPQ hne)
    exact ⟨⟨x, hxQ⟩, by simpa using hxP⟩
  obtain ⟨x₀, hx₀norm, hx₀⟩ := riesz_lemma_of_norm_lt hc (R := ‖c‖ + 1) (by linarith) h₁ h₂
  refine ⟨(x₀ : X), x₀.2, hx₀norm, fun y hy => ?_⟩
  simpa using hx₀ ⟨y, hPQ hy⟩ (by simpa using hy)

/-- A decreasing chain of closed subspaces stable under `1 - K`, in the sense that `1 - K` carries
the `n`-th one into the `(n + 1)`-st, cannot be strictly decreasing: Riesz's lemma would otherwise
produce a bounded sequence whose images under `K` stay `1` apart. -/
private theorem exists_eq_succ_of_chain (hK : IsCompactOperator K) {V : ℕ → Submodule 𝕜 X}
    (hmono : ∀ n, V (n + 1) ≤ V n) (hclosed : ∀ n, IsClosed ((V n : Set X)))
    (hstep : ∀ n, ∀ x ∈ V n, x - K x ∈ V (n + 1)) :
    ∃ p, V (p + 1) = V p := by
  by_contra hcon
  push Not at hcon
  have hanti : ∀ {m n : ℕ}, m ≤ n → V n ≤ V m := by
    intro m n h
    induction h with
    | refl => exact le_rfl
    | step h ih => exact (hmono _).trans ih
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  choose f hfmem hfnorm hfsep using fun n =>
    exists_riesz (hmono n) (hclosed (n + 1)) (hcon n) hc
  have key : ∀ m n : ℕ, m < n → 1 ≤ ‖K (f m) - K (f n)‖ := by
    intro m n hmn
    have hy : (f m - K (f m)) + f n - (f n - K (f n)) ∈ V (m + 1) := by
      refine Submodule.sub_mem _ (Submodule.add_mem _ (hstep m _ (hfmem m)) ?_) ?_
      · exact hanti hmn (hfmem n)
      · exact hanti (Nat.succ_le_succ hmn.le) (hstep n _ (hfmem n))
    have hrw : K (f m) - K (f n) = f m - ((f m - K (f m)) + f n - (f n - K (f n))) := by abel
    rw [hrw]
    exact hfsep m _ hy
  obtain ⟨m, n, hmn, hlt⟩ := exists_dist_lt_of_norm_le hK hfnorm one_pos
  rw [dist_eq_norm] at hlt
  rcases lt_or_gt_of_ne hmn with h | h
  · exact absurd hlt (not_lt.mpr (key m n h))
  · rw [norm_sub_rev] at hlt
    exact absurd hlt (not_lt.mpr (key n m h))

end Chain

variable [CompleteSpace 𝕜]

/-- The kernel of a compact perturbation of the identity is finite dimensional. -/
theorem finiteDimensional_ker_one_sub (hK : IsCompactOperator K) :
    FiniteDimensional 𝕜 (LinearMap.ker ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X)) := by
  rw [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one,
    TauCeti.ker_one_sub]
  exact finiteDimensional_eigenspace hK one_ne_zero

variable [IsRCLikeNormedField 𝕜] [CompleteSpace X]

/-- The range of a compact perturbation of the identity is closed. -/
theorem isClosed_range_one_sub (hK : IsCompactOperator K) :
    IsClosed (LinearMap.range ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) : Set X) := by
  have hfin : FiniteDimensional 𝕜 (LinearMap.ker ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X)) :=
    finiteDimensional_ker_one_sub hK
  obtain ⟨M, hMclosed, hMcompl⟩ :=
    (Submodule.ClosedComplemented.of_finiteDimensional
      (LinearMap.ker ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X))).exists_isClosed_isCompl
  obtain ⟨c, hcpos, hc⟩ := exists_pos_mul_norm_le_of_disjoint_ker hK hMclosed hMcompl.disjoint
  -- Every value of `1 - K` is already attained on `M`.
  have hrange : (LinearMap.range ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) : Set X)
      = Set.range ((1 - K : X →L[𝕜] X).comp M.subtypeL) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hx : x ∈ LinearMap.ker ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) ⊔ M := by
        rw [hMcompl.sup_eq_top]; trivial
      obtain ⟨n, hn, m, hm, hnm⟩ := Submodule.mem_sup.mp hx
      refine ⟨⟨m, hm⟩, ?_⟩
      have hn0 : (1 - K : X →L[𝕜] X) n = 0 := hn
      simp only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL,
        Submodule.subtype_apply, ContinuousLinearMap.coe_coe]
      rw [← hnm, map_add, hn0, zero_add]
    · rintro ⟨m, rfl⟩
      exact ⟨(m : X), rfl⟩
  have hMcomplete : CompleteSpace M := hMclosed.completeSpace_coe
  have hcinv : (0 : ℝ) ≤ c⁻¹ := by positivity
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹)
      ((1 - K : X →L[𝕜] X).comp M.subtypeL) := by
    refine AddMonoidHomClass.antilipschitz_of_bound _ fun m => ?_
    have hm := hc (m : X) m.2
    have h2 : ‖(m : X)‖ ≤ c⁻¹ * ‖(1 - K : X →L[𝕜] X) (m : X)‖ := by
      have h3 := mul_le_mul_of_nonneg_left hm hcinv
      rwa [← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul] at h3
    simpa [Real.coe_toNNReal _ hcinv] using h2
  rw [hrange]
  exact hanti.isClosed_range ((1 - K : X →L[𝕜] X).comp M.subtypeL).uniformContinuous

/-- The cokernel of a compact perturbation of the identity is finite dimensional. -/
theorem finiteDimensional_quotient_range_one_sub (hK : IsCompactOperator K) :
    FiniteDimensional 𝕜 (X ⧸ LinearMap.range ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X)) := by
  set A : X →L[𝕜] X := 1 - K with hA
  set V : ℕ → Submodule 𝕜 X :=
    fun n => LinearMap.range ((A ^ n : X →L[𝕜] X) : X →ₗ[𝕜] X) with hV
  have hVmem : ∀ (n : ℕ) (x : X), x ∈ V n ↔ ∃ z, (A ^ n) z = x := by
    intro n x
    simp only [hV, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  have hVsucc : ∀ n, ∀ x ∈ V n, A x ∈ V (n + 1) := by
    intro n x hx
    obtain ⟨z, rfl⟩ := (hVmem n x).mp hx
    exact (hVmem (n + 1) _).mpr ⟨z, by rw [pow_succ']; rfl⟩
  have hVmono : ∀ n, V (n + 1) ≤ V n := by
    intro n x hx
    obtain ⟨z, rfl⟩ := (hVmem _ _).mp hx
    exact (hVmem n _).mpr ⟨A z, by rw [pow_succ]; rfl⟩
  have hVmap : ∀ n, V (n + 1) = Submodule.map (A : X →ₗ[𝕜] X) (V n) := by
    intro n
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨z, rfl⟩ := (hVmem _ _).mp hx
      exact ⟨(A ^ n) z, (hVmem n _).mpr ⟨z, rfl⟩, by rw [pow_succ']; rfl⟩
    · obtain ⟨w, hw, rfl⟩ := hx
      exact hVsucc n w hw
  have hVclosed : ∀ n, IsClosed ((V n : Set X)) := by
    intro n
    have h := isClosed_range_one_sub (isCompactOperator_one_sub_pow hK n)
    rw [sub_sub_cancel, ← hA] at h
    rw [hV]
    exact h
  obtain ⟨p, hp⟩ := exists_eq_succ_of_chain hK hVmono hVclosed (by
    intro n x hx
    have : x - K x = A x := rfl
    rw [this]
    exact hVsucc n x hx)
  -- The chain of ranges is constant from `p` on.
  have hstab : ∀ n, p ≤ n → V (n + 1) = V n := by
    intro n hn
    induction n with
    | zero => rw [Nat.le_zero.mp hn] at hp; exact hp
    | succ n ih =>
      rcases Nat.lt_or_ge p (n + 1) with h | h
      · have hih := ih (Nat.lt_succ_iff.mp h)
        calc V (n + 1 + 1) = Submodule.map (A : X →ₗ[𝕜] X) (V (n + 1)) := hVmap (n + 1)
          _ = Submodule.map (A : X →ₗ[𝕜] X) (V n) := by rw [hih]
          _ = V (n + 1) := (hVmap n).symm
      · rw [Nat.le_antisymm hn h] at hp; exact hp
  have hconst : ∀ n, V (p + n) = V p := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [← Nat.add_assoc, hstab (p + n) (Nat.le_add_right p n)]; exact ih
  have hV2 : V (p + 1 + (p + 1)) = V (p + 1) := by
    have h1 : p + 1 + (p + 1) = p + (p + 2) := by omega
    rw [h1, hconst, hp]
  -- The kernel of `A ^ (p + 1)` surjects onto the cokernel of `A`.
  have hkerfin : FiniteDimensional 𝕜
      (LinearMap.ker ((A ^ (p + 1) : X →L[𝕜] X) : X →ₗ[𝕜] X)) := by
    have h := finiteDimensional_ker_one_sub (isCompactOperator_one_sub_pow hK (p + 1))
    rw [sub_sub_cancel, ← hA] at h
    exact h
  refine FiniteDimensional.of_surjective
    ((LinearMap.range (A : X →ₗ[𝕜] X)).mkQ.comp
      (LinearMap.ker ((A ^ (p + 1) : X →L[𝕜] X) : X →ₗ[𝕜] X)).subtype) ?_
  intro ξ
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ ξ
  have hx : (A ^ (p + 1)) x ∈ V (p + 1 + (p + 1)) := by
    rw [hV2]
    exact (hVmem _ _).mpr ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := (hVmem _ _).mp hx
  have hcomp : ∀ (m n : ℕ) (w : X), (A ^ (m + n)) w = (A ^ m) ((A ^ n) w) := by
    intro m n w
    rw [pow_add]
    rfl
  have hzz : (A ^ (p + 1)) ((A ^ (p + 1)) z) = (A ^ (p + 1)) x := by
    rw [← hcomp]
    exact hz
  refine ⟨⟨x - (A ^ (p + 1)) z, ?_⟩, ?_⟩
  · rw [LinearMap.mem_ker]
    have hzz' :
        ((A ^ (p + 1) : X →L[𝕜] X) : X →ₗ[𝕜] X) ((A ^ (p + 1)) z) =
          ((A ^ (p + 1) : X →L[𝕜] X) : X →ₗ[𝕜] X) x := by
      simpa only [ContinuousLinearMap.coe_coe] using hzz
    rw [map_sub, hzz', sub_self]
  · have hmem : (A ^ (p + 1)) z ∈ LinearMap.range (A : X →ₗ[𝕜] X) :=
      ⟨(A ^ p) z, by rw [pow_succ']; rfl⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    simpa using neg_mem hmem

end IsCompactOperator

end TauCeti

end
