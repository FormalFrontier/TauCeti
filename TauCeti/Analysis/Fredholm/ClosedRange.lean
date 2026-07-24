/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.Fredholm.Basic

/-!
# Closed range from a finite-dimensional cokernel

For the nonlinear-analysis substrate of the analytic Heegaard Floer roadmap (Lane F0, "Fredholm
operators and index theory"), this file proves that the closed-range hypothesis in the definition
of a Fredholm operator is *automatic* between Banach spaces once the cokernel is finite
dimensional.

Concretely, a continuous linear map `T : E →L[𝕜] F` between complete normed spaces whose cokernel
`F ⧸ range T` is finite dimensional already has closed range. The proof is a clean application of
the Banach open mapping theorem: choosing a finite-dimensional algebraic complement `N` of
`range T`, the auxiliary map `Φ(x, n) = T x + n` from `E × N` is a continuous linear surjection
between Banach spaces, hence a quotient map. Its preimage `Φ ⁻¹' range T = E × {0}` is closed, and
a quotient map carries the closed-set characterization that a set is closed exactly when its
preimage is, so `range T` is closed.

This upgrades the Fredholm predicate of `TauCeti.Analysis.Fredholm.Basic`: over Banach spaces a
Fredholm operator is *exactly* a continuous linear map with finite-dimensional kernel and cokernel,
the closed-range condition following for free. Downstream this lets Sard–Smale and transversality
arguments certify Fredholmness of a linearization from the two defect spaces alone, without a
separate closed-range check.

## Main declarations

* `TauCeti.ContinuousLinearMap.isClosed_range_of_finiteDimensional_coker`: a continuous linear map
  between Banach spaces with finite-dimensional cokernel has closed range.
* `TauCeti.IsFredholm.of_finiteDimensional_ker_coker`: over Banach spaces, finite-dimensional
  kernel and cokernel suffice for Fredholmness.
* `TauCeti.isFredholm_iff_finiteDimensional_ker_coker`: over Banach spaces, the Fredholm predicate
  is equivalent to finite dimensionality of the kernel and cokernel.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix
A.1, where a Fredholm operator has finite-dimensional kernel and cokernel; the closed-range
condition is noted there to be automatic between Banach spaces.
-/

public section

namespace TauCeti

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace ContinuousLinearMap

/-- A continuous linear map between Banach spaces whose cokernel `F ⧸ range T` is finite
dimensional has closed range.

Closedness of the range is therefore not an independent hypothesis in the Banach setting: it is
forced by finite dimensionality of the cokernel. The proof runs the Banach open mapping theorem on
the surjection `Φ(x, n) = T x + n` from `E × N`, where `N` is a finite-dimensional algebraic
complement of `range T`. -/
theorem isClosed_range_of_finiteDimensional_coker (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F))] :
    IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F) := by
  set R := LinearMap.range (T : E →ₗ[𝕜] F) with hR
  -- A finite-dimensional algebraic complement `N` of `range T`.
  obtain ⟨N, hN⟩ := R.exists_isCompl
  haveI : FiniteDimensional 𝕜 N := (Submodule.quotientEquivOfIsCompl R N hN).finiteDimensional
  haveI : CompleteSpace N := FiniteDimensional.complete 𝕜 N
  -- The auxiliary map `Φ(x, n) = T x + n`, the coproduct of `T` and the inclusion of `N`,
  -- continuous linear from the Banach space `E × N`.
  set Φ : (E × N) →L[𝕜] F := T.coprod N.subtypeL with hΦdef
  have hΦ : ∀ p : E × N, Φ p = T p.1 + (p.2 : F) := fun p => by simp [hΦdef]
  -- `Φ` is surjective: every `y : F` lies in `R ⊔ N = ⊤`, so `y = T x + n` for some
  -- `x : E` and `n ∈ N`, and `Φ (x, ⟨n, _⟩) = y`.
  have hsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨r, hr, n, hn, rfl⟩ :=
      Submodule.mem_sup.mp (hN.sup_eq_top ▸ Submodule.mem_top : y ∈ R ⊔ N)
    obtain ⟨x, rfl⟩ := hr
    exact ⟨(x, ⟨n, hn⟩), by simp [hΦ]⟩
  -- The preimage of `range T` under `Φ` is the closed subset `{p | p.2 = 0}`.
  have hpre : Φ ⁻¹' (R : Set F) = {p : E × N | p.2 = 0} := by
    ext p
    simp only [Set.mem_preimage, SetLike.mem_coe, hΦ, Set.mem_setOf_eq]
    have hTp : T p.1 ∈ R := by
      rw [hR, ← ContinuousLinearMap.coe_coe]; exact LinearMap.mem_range_self _ p.1
    constructor
    · intro hmem
      have hb : (p.2 : F) ∈ R := by simpa using R.sub_mem hmem hTp
      have hbot : (p.2 : F) ∈ R ⊓ N := ⟨hb, p.2.2⟩
      rw [hN.inf_eq_bot] at hbot
      exact Submodule.coe_eq_zero.mp (by simpa using hbot)
    · intro h
      rw [h]
      simpa using hTp
  have hclosed : IsClosed (Φ ⁻¹' (R : Set F)) := by
    rw [hpre]; exact isClosed_eq continuous_snd continuous_const
  exact (Φ.isQuotientMap hsurj).isClosed_preimage.mp hclosed

end ContinuousLinearMap

/-- Over Banach spaces, a continuous linear map with finite-dimensional kernel and cokernel is
Fredholm: the closed-range condition is automatic.

This is the Banach-space form of the Fredholm criterion, complementing the direct constructor of
`TauCeti.IsFredholm` by removing the closed-range obligation. -/
theorem IsFredholm.of_finiteDimensional_ker_coker (T : E →L[𝕜] F)
    (hker : FiniteDimensional 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)))
    (hcoker : FiniteDimensional 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F))) :
    IsFredholm T where
  finiteDimensional_ker := hker
  isClosed_range := by
    haveI := hcoker
    exact ContinuousLinearMap.isClosed_range_of_finiteDimensional_coker T
  finiteDimensional_coker := hcoker

/-- Over Banach spaces the Fredholm predicate is equivalent to finite dimensionality of the kernel
and cokernel; closedness of the range is not an independent condition. -/
theorem isFredholm_iff_finiteDimensional_ker_coker (T : E →L[𝕜] F) :
    IsFredholm T ↔
      FiniteDimensional 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)) ∧
        FiniteDimensional 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) :=
  ⟨fun h => ⟨h.finiteDimensional_ker, h.finiteDimensional_coker⟩,
    fun h => .of_finiteDimensional_ker_coker T h.1 h.2⟩

end TauCeti
