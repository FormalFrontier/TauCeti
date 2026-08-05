/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Basic
public import TauCeti.Analysis.SpecialFunctions.Hermite.Orthogonality
public import TauCeti.Probability.Distributions.Gaussian.Basic
public import TauCeti.RingTheory.Polynomial.Hermite.Real

/-!
# The Hermite polynomials as a Hilbert basis of `L²(γ)`

Roadmap milestone **A3′**: the measure-side one-dimensional Gaussian Hermite basis. Where
`TauCeti.hermiteHilbertBasis` puts the Gaussian envelope inside the *function* (`ψₙ` in `L²(ℝ)`),
this puts it in the *measure*: `Hₙ/√(n!)` is an orthonormal basis of `L²(γ)` for the standard
Gaussian `γ = gaussianReal 0 1`.

That is the form multivariate Gaussian `L²` and chaos expansions consume, and it is the input
`piHilbertBasis` needs for the multidimensional basis of Part D.

## Main statements

* `TauCeti.integral_hermite_mul_hermite_mul_gaussianPDFReal` — the orthogonality relation against
  the standard Gaussian density, with normalization `cₙ = n!`.
* `TauCeti.integrable_exp_mul_abs_gaussianPDFReal` — the standard Gaussian density has every
  exponential moment finite, the hypothesis
  `TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot` needs.
* `TauCeti.gaussianHermiteHilbertBasis` — milestone A3′ itself.
* `TauCeti.coeFn_gaussianHermiteHilbertBasis` — the anti-vacuity pin: the basis vectors really are
  `Hₙ/√(n!)`, not merely *some* orthonormal basis.
* `TauCeti.sqrt_gaussianPDFReal_mul_hermiteℝ_div_sqrt_factorial` — the `√w`-envelope of a basis
  vector is `2^{-1/4}·ψₙ(x/√2)`, identifying this basis with the function-side
  `TauCeti.hermiteHilbertBasis` through `TauCeti.weightL2Isometry`.
* `TauCeti.sqrt_gaussianPDFReal_smul_gaussianHermiteHilbertBasis` — that envelope computed on the
  public basis vector itself, a.e. against `volume`.
* `TauCeti.weightL2Isometry_gaussianHermiteHilbertBasis` — the same identification at the
  `TauCeti.weightL2Isometry` level: the image of the `n`-th basis vector is `2^{-1/4} • ψₙ(·/√2)`.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial Real ProbabilityTheory

/-- **Orthogonality against the standard Gaussian density.**
`∫ Hₘ Hₙ dγ = δₘₙ · n!`. This is the density-side reading of the Gaussian-measure orthogonality
milestone `TauCeti.integral_hermite_mul_hermite_gaussianReal`: `∫ · ∂γ` unfolds to `∫ pdf • ·`, so
the two differ only by the order of the factors. -/
theorem integral_hermite_mul_hermite_mul_gaussianPDFReal (m n : ℕ) :
    (∫ x : ℝ, aeval x (hermite m) * aeval x (hermite n) * gaussianPDFReal 0 1 x)
      = if m = n then (n.factorial : ℝ) else 0 := by
  rw [← integral_hermite_mul_hermite_gaussianReal m n,
    integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  simp only [smul_eq_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-! ## The weighted-measure input data

`TauCeti.hermiteℝ` and its `eval`/`degree` lemmas live in
`TauCeti/RingTheory/Polynomial/Hermite/Real.lean`: they mention no measure and no Gaussian, and
keeping them here would strand them below the function-side files that use the same cast. -/

/-- **Finite exponential moments of the standard Gaussian.** For every rate `a`, `e^{a|x|}` is
integrable against `γ`.

Both one-sided exponentials are already integrable against a Gaussian
(`ProbabilityTheory.integrable_exp_mul_gaussianReal`, which is the mgf being everywhere finite), and
`ProbabilityTheory.integrable_exp_mul_abs` folds the rates `a` and `-a` into the two-sided
`e^{a|x|}`. Transporting along `ProbabilityTheory.gaussianReal_of_var_ne_zero` then puts it in the
with-density form the completeness theorem takes; the `ENNReal.ofReal ∘ gaussianPDFReal` spelling
of the density is definitionally the `gaussianPDF` that lemma produces. -/
theorem integrable_exp_mul_abs_gaussianPDFReal (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|))
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) := by
  rw [← gaussianPDF_def, ← gaussianReal_of_var_ne_zero 0 one_ne_zero]
  exact integrable_exp_mul_abs (X := fun x : ℝ => x) (t := a)
    (integrable_exp_mul_gaussianReal a) (integrable_exp_mul_gaussianReal (-a))

/-- The exponential-moment hypothesis in the existential form the completeness theorem takes. -/
theorem exp_moment_gaussianPDFReal :
    ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|))
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) :=
  ⟨1, one_pos, integrable_exp_mul_abs_gaussianPDFReal 1⟩

section Basis

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The `MemLp` obligation for the Hermite family against the standard Gaussian density. This is
the generic `TauCeti.memLp_two_bareNormalized` at `p = hermiteℝ`, `c n = n!`; the only content
specific to this family is `exp_moment_gaussianPDFReal`. -/
private theorem memLp_hermiteℝ_normalized (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜)
        ((hermiteℝ n).eval x / Real.sqrt ((n.factorial : ℝ)))) 2
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) :=
  memLp_two_bareNormalized (𝕜 := 𝕜) exp_moment_gaussianPDFReal hermiteℝ
    (fun n => (n.factorial : ℝ)) n

/-- The basis in the weighted-measure form the machinery produces; `gaussianHermiteHilbertBasis`
is this transported along `ProbabilityTheory.gaussianReal_of_var_ne_zero`. -/
private noncomputable def gaussianHermiteHilbertBasisAux :
    HilbertBasis ℕ 𝕜
      (Lp 𝕜 2 (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x))) :=
  hilbertBasisOfWeightedMeasure (𝕜 := 𝕜) (fun n x => (hermiteℝ n).eval x)
    (fun x => gaussianPDFReal 0 1 x) (fun n => (n.factorial : ℝ))
    (Filter.Eventually.of_forall fun x => gaussianPDFReal_nonneg 0 1 x) (by fun_prop)
    (fun n => Nat.cast_pos.mpr n.factorial_pos)
    (fun m n => by
      simpa only [eval_hermiteℝ] using integral_hermite_mul_hermite_mul_gaussianPDFReal m n)
    (memLp_hermiteℝ_normalized 𝕜)
    (orthogonal_span_range_bareNormalizedLp_eq_bot (𝕜 := 𝕜) hermiteℝ
      (fun x => gaussianPDFReal 0 1 x)
      (fun n => (n.factorial : ℝ)) degree_hermiteℝ (fun n => Nat.cast_pos.mpr n.factorial_pos)
      exp_moment_gaussianPDFReal (memLp_hermiteℝ_normalized 𝕜))

/-- Transporting a basis along an equality of measures does not change its vectors: the `cast` is
along `Lp 𝕜 2 μ = Lp 𝕜 2 ν`, so it acts as the identity on representatives. -/
private theorem coe_cast_hilbertBasis {μ ν : Measure ℝ} (h : μ = ν)
    (hty : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 μ) = HilbertBasis ℕ 𝕜 (Lp 𝕜 2 ν))
    (b : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 μ)) (n : ℕ) {g : ℝ → 𝕜} (hb : ⇑(b n) =ᵐ[μ] g) :
    ⇑((cast hty b) n) =ᵐ[ν] g := by
  subst h
  rw [cast_eq]
  exact hb

/-- Transporting an `L²` element along an equality of measures does not move its representative:
the `cast` is along `↥(Lp 𝕜 2 μ) = ↥(Lp 𝕜 2 ν)`, so it is the identity on functions. -/
private theorem coeFn_cast_lp {μ ν : Measure ℝ} (h : μ = ν) (f : Lp 𝕜 2 μ) (x : ℝ) :
    ((cast (congrArg (fun m : Measure ℝ => (Lp 𝕜 2 m : Type _)) h) f : Lp 𝕜 2 ν) : ℝ → 𝕜) x
      = (f : ℝ → 𝕜) x := by
  subst h
  rfl

/-- **Roadmap A3′: the Hermite polynomials are a Hilbert basis of `L²(γ)`.** Orthonormality comes
from the orthogonality relation against the Gaussian density and completeness from moment
determinacy (`TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`), applied to the exact-degree
family `Hₙ`.
Where `TauCeti.hermiteHilbertBasis` carries the Gaussian in the function, this carries it in the
measure — the form multivariate `L²(γ^ι)` and chaos expansions consume. -/
noncomputable def gaussianHermiteHilbertBasis :
    HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (gaussianReal 0 1)) :=
  cast (by rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, gaussianPDF_def])
    (gaussianHermiteHilbertBasisAux 𝕜)

/-- **The basis vectors are the normalized Hermite polynomials.** Without this the construction
would only exhibit *some* Hilbert basis of `L²(γ)`; here each vector is pinned to `Hₙ/√(n!)`, which
is what downstream chaos-coordinate computations need. -/
theorem coeFn_gaussianHermiteHilbertBasis (n : ℕ) :
    ⇑(gaussianHermiteHilbertBasis 𝕜 n) =ᵐ[gaussianReal 0 1]
      fun x => (algebraMap ℝ 𝕜) (aeval x (hermite n) / Real.sqrt ((n.factorial : ℝ))) := by
  have hcoe : ⇑(gaussianHermiteHilbertBasisAux 𝕜)
      = bareNormalizedLp (𝕜 := 𝕜) (fun n x => (hermiteℝ n).eval x)
        (fun x => gaussianPDFReal 0 1 x) (fun n => (n.factorial : ℝ))
        (memLp_hermiteℝ_normalized 𝕜) :=
    coe_hilbertBasisOfWeightedMeasure _ _ _ _ _ _ _ _ _
  have haux : ⇑(gaussianHermiteHilbertBasisAux 𝕜 n)
      =ᵐ[volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)]
        fun x => (algebraMap ℝ 𝕜) (aeval x (hermite n) / Real.sqrt ((n.factorial : ℝ))) := by
    rw [hcoe]
    filter_upwards [coeFn_bareNormalizedLp (𝕜 := 𝕜) (fun n x => (hermiteℝ n).eval x)
      (fun x => gaussianPDFReal 0 1 x) (fun n => (n.factorial : ℝ))
      (memLp_hermiteℝ_normalized 𝕜) n] with x hx
    rw [hx, eval_hermiteℝ]
  rw [gaussianHermiteHilbertBasis]
  have hγ : (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x))
      = (gaussianReal 0 1 : Measure ℝ) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, gaussianPDF_def]
  exact coe_cast_hilbertBasis 𝕜 hγ _ _ n haux

/-- **The Gaussian envelope carries `Hₙ/√(n!)` to a dilated Hermite function.**
`√(γ-density x) · Hₙ(x)/√(n!) = 2^{-1/4} · ψₙ(x/√2)`, with `2^{-1/4}` written as `(√√2)⁻¹` to stay
inside `Real.sqrt`.

Multiplication by `√w` is exactly `TauCeti.weightL2Isometry`, so this is the pointwise
characterization of that isometry's image on `TauCeti.gaussianHermiteHilbertBasis`: it pins the
measure-side basis of `L²(γ)` to the function-side basis `TauCeti.hermiteHilbertBasis` of `L²(ℝ)`,
up to the dilation `x ↦ x/√2` and that normalization. Without it a consumer moving between the two
normalizations has to redo the dilation and normalization bookkeeping. -/
theorem sqrt_gaussianPDFReal_mul_hermiteℝ_div_sqrt_factorial (n : ℕ) (x : ℝ) :
    Real.sqrt (gaussianPDFReal 0 1 x) * ((hermiteℝ n).eval x / Real.sqrt (n.factorial : ℝ))
      = (Real.sqrt (Real.sqrt 2))⁻¹ * hermiteFunction n (x / Real.sqrt 2) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  -- The dilation cancels inside the Hermite polynomial, and halves the exponent.
  have harg : x / Real.sqrt 2 * Real.sqrt 2 = x := div_mul_cancel₀ x (ne_of_gt h2)
  have hsq : (x / Real.sqrt 2) ^ 2 / 2 = x ^ 2 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  -- `√` of the Gaussian density: the exponent halves again, `e^{-x²/2} = (e^{-x²/4})²`.
  have hhalf : Real.exp (-(x ^ 2 / 4)) * Real.exp (-(x ^ 2 / 4)) = Real.exp (-(x ^ 2 / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdens : Real.sqrt (gaussianPDFReal 0 1 x)
      = (Real.sqrt (Real.sqrt (2 * π)))⁻¹ * Real.exp (-(x ^ 2 / 4)) := by
    rw [gaussianPDFReal_zero_one, Real.sqrt_mul (by positivity), Real.sqrt_inv]
    congr 1
    rw [← hhalf]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  -- Both normalizations factor through `√√π`, which is what makes the two constants agree.
  have hsplit1 : Real.sqrt (Real.sqrt (2 * π))
      = Real.sqrt (Real.sqrt 2) * Real.sqrt (Real.sqrt π) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (Real.sqrt_nonneg 2)]
  have hsplit2 : Real.sqrt ((n.factorial : ℝ) * Real.sqrt π)
      = Real.sqrt (n.factorial : ℝ) * Real.sqrt (Real.sqrt π) :=
    Real.sqrt_mul hfac.le _
  have hne2 : Real.sqrt (Real.sqrt 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h2)
  have hnepi : Real.sqrt (Real.sqrt π) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr Real.pi_pos))
  have hnefac : Real.sqrt (n.factorial : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hfac)
  rw [hdens, eval_hermiteℝ, hermiteFunction_def, harg, hsq, hsplit1, hsplit2]
  field_simp

/-- **The Gaussian envelope of the basis is the dilated Hermite function family.** Scaling the
`n`-th basis vector of `L²(γ)` by `√(γ-density)` gives `2^{-1/4} • ψₙ(·/√2)`.

Stated a.e. against `volume`, the measure that envelope lives on, and in terms of the public
`gaussianHermiteHilbertBasis` rather than its weighted-measure preimage. The pointwise content is
`TauCeti.sqrt_gaussianPDFReal_mul_hermiteℝ_div_sqrt_factorial`; the only work here is moving the
basis representative from `γ`-a.e. to `volume`-a.e., which is legitimate because the Gaussian
density never vanishes.

`√w`-scaling is the forward map of `TauCeti.weightL2Isometry`, so this is the pointwise content of
`TauCeti.weightL2Isometry_gaussianHermiteHilbertBasis` below, which states the same fact at the
isometry level. -/
theorem sqrt_gaussianPDFReal_smul_gaussianHermiteHilbertBasis (n : ℕ) :
    (fun x : ℝ => Real.sqrt (gaussianPDFReal 0 1 x)
        • (gaussianHermiteHilbertBasis 𝕜 n : ℝ → 𝕜) x)
      =ᵐ[volume] fun x : ℝ => (Real.sqrt (Real.sqrt 2))⁻¹
        • (algebraMap ℝ 𝕜) (hermiteFunction n (x / Real.sqrt 2)) := by
  -- `w > 0` makes `volume` absolutely continuous with respect to `γ = w·volume`, so the
  -- `γ`-a.e. representative of the basis vector is also a `volume`-a.e. one.
  have hac : (volume : Measure ℝ) ≪ (gaussianReal 0 1 : Measure ℝ) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
    exact withDensity_absolutelyContinuous' (by fun_prop)
      (Filter.Eventually.of_forall fun x => (gaussianPDF_pos 0 one_ne_zero x).ne')
  filter_upwards [(coeFn_gaussianHermiteHilbertBasis 𝕜 n).filter_mono hac.ae_le] with x hx
  rw [hx, ← eval_hermiteℝ, Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul,
    sqrt_gaussianPDFReal_mul_hermiteℝ_div_sqrt_factorial n x]

/-- **The `weightL2Isometry`-image of the Gaussian Hermite basis is the dilated Hermite function
family.** The `n`-th vector goes to `2^{-1/4} • ψₙ(·/√2)`, pinning the measure-side basis of `L²(γ)`
to the function-side basis `TauCeti.hermiteHilbertBasis` of `L²(ℝ)` up to that dilation and
normalization.

`TauCeti.weightL2Isometry` has `L²(volume.withDensity …)` as its domain, whereas
`TauCeti.gaussianHermiteHilbertBasis` lives in the propositionally equal `L²(γ)`, so the basis
vector is transported along that equality of measures before the isometry is applied. The weight is
the fixed function `gaussianPDFReal 0 1`, whose positivity and measurability are supplied here
rather than left to the caller; by proof irrelevance this still applies to
`TauCeti.weightL2Isometry` built from any other proofs of those two side conditions. -/
theorem weightL2Isometry_gaussianHermiteHilbertBasis (n : ℕ) :
    weightL2Isometry volume (fun x : ℝ => gaussianPDFReal 0 1 x)
        (Filter.Eventually.of_forall fun x => gaussianPDFReal_pos 0 1 x one_ne_zero) (by fun_prop)
        (cast (congrArg (fun m : Measure ℝ => (Lp 𝕜 2 m : Type _))
          (by rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, gaussianPDF_def]))
          (gaussianHermiteHilbertBasis 𝕜 n))
      =ᵐ[volume] fun x : ℝ => (Real.sqrt (Real.sqrt 2))⁻¹
        • (algebraMap ℝ 𝕜) (hermiteFunction n (x / Real.sqrt 2)) := by
  -- The isometry is multiplication by `√w`, and the transport does not move representatives.
  refine (weightL2Isometry_apply (𝕜 := 𝕜) volume (fun x : ℝ => gaussianPDFReal 0 1 x)
    _ _ _).trans ?_
  have hγ : (gaussianReal 0 1 : Measure ℝ)
      = volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, gaussianPDF_def]
  refine Filter.EventuallyEq.trans ?_ (sqrt_gaussianPDFReal_smul_gaussianHermiteHilbertBasis 𝕜 n)
  exact Filter.Eventually.of_forall fun x => by
    simp only [coeFn_cast_lp 𝕜 hγ (gaussianHermiteHilbertBasis 𝕜 n) x]

end Basis

end TauCeti
