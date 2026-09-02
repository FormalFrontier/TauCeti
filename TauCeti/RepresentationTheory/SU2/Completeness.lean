/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import TauCeti.RepresentationTheory.SU2.ConjugacyClasses
public import TauCeti.RepresentationTheory.SU2.SymmetricPower

/-!
# The characters of the symmetric powers span the class functions of `SU(2)`

`TauCeti/RepresentationTheory/SU2/Weyl/Orthogonality.lean` proves that the characters `χ_d` of the
symmetric powers `Symᵈ(ℂ²)` are *orthonormal* against the Weyl density. This file proves the
complementary statement, that nothing else is needed: the `ℂ`-linear span of the `χ_d` is
**uniformly dense in the continuous class functions of `SU(2)`**, and its closure is exactly the
space of continuous class functions.

## The route

The engine is a closed form for the character. `TauCeti.SU2.character_symPower_torusHom_zpow`
computes `χ_d` on the maximal torus as the weight string `∑_{i ≤ d} z^{2i-d}`, and multiplying that
string by `z + z⁻¹ = tr (diag (z, z⁻¹))` telescopes to `χ_{d+1} + χ_{d-1}`. Since both sides are
class functions and every element of `SU(2)` is conjugate into the torus, this recursion holds on
all of `SU(2)` (`TauCeti.SU2.trace_mul_character_symPower`). It is the Chebyshev recursion, so with
the two base cases `χ_0 = 1` and `χ_1 = tr` it gives

`χ_d = U_d (tr / 2)`  (`TauCeti.SU2.character_symPower_eq_chebyshevU_eval`)

for the Chebyshev polynomial `Polynomial.Chebyshev.U` of the second kind. Two things follow at
once: each `χ_d` is *continuous*, being a polynomial in the trace; and, running the recursion the
other way, every *power* of the trace lies in the span of the `χ_d`
(`TauCeti.SU2.pow_symPowerCharacter_one_mem_characterSpan`), so by linearity that span is exactly
the polynomial functions of the trace.

Density is then Weierstrass approximation on the interval `[-2, 2]` of traces. Every element of
`SU(2)` is conjugate to `diag (e^{iθ}, e^{-iθ})` for an angle `θ` of the Weyl chamber `[0, π]`
(`TauCeti.SU2.exists_isConj_torusExp_mem_Icc`), where the trace is `2 cos θ`; since `arccos`
inverts `cos` on that chamber, the continuous function `t ↦ f (diag (e^{i arccos (t/2)}, …))` on
`[-2, 2]` takes at the trace of `g` the value `f g`. Approximating its real and imaginary parts by
real polynomials and substituting the trace therefore approximates `f` uniformly by elements of
the span.

## Main definitions

* `TauCeti.SU2.symPowerCharacter`: the character of `Symᵈ(ℂ²)` bundled as a continuous function.
* `TauCeti.SU2.characterSpan`: the `ℂ`-linear span of those characters inside `C(SU(2), ℂ)`.

## Main results

* `TauCeti.SU2.trace_mul_character_symPower`: the Chebyshev recursion
  `tr · χ_{d+1} = χ_{d+2} + χ_d`, the character shadow of the Clebsch-Gordan decomposition of
  `Sym¹ ⊗ Sym^{d+1}`.
* `TauCeti.SU2.character_symPower_eq_chebyshevU_eval`: `χ_d = U_d (tr / 2)`.
* `TauCeti.SU2.continuous_character_symPower`: the characters are continuous.
* `TauCeti.SU2.pow_symPowerCharacter_one_mem_characterSpan`: every power of the trace lies in the
  span of the characters.
* `TauCeti.SU2.exists_mem_characterSpan_norm_sub_lt`: **uniform density.** Every continuous class
  function on `SU(2)` is within any `ε > 0` of an element of the span.
* `TauCeti.SU2.mem_topologicalClosure_characterSpan_iff`: the closure of the span is **exactly**
  the continuous class functions.

## References

This is the completeness half of the "the `{χ_n}` are an orthonormal basis of the class functions
of `SU(2)`" item of the `SU(2)` engine case of
`TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md`; orthonormality is
`TauCeti.SU2.character_symPower_orthonormal_torusExp`. It is the analytic input to the remaining
item of that engine case, that the `Symᵈ(ℂ²)` exhaust the finite-dimensional irreducibles, which
is *not* proved here: that deduction additionally needs the symmetric powers as continuous unitary
representations, so that the character orthogonality of
`TauCeti/RepresentationTheory/Compact/Character/Basic.lean` applies to them.

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 3.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, §5.
-/

public section

open Matrix Polynomial

namespace TauCeti

namespace SU2

/-! ### The Chebyshev recursion for the characters -/

/-- Multiplying the weight string of `Symᵈ⁺¹(ℂ²)` by `z + z⁻¹` telescopes: the two shifted copies
of the string `∑_{i ≤ d+1} z^{2i-d-1}` overlap in all but one term each, and the leftover terms are
exactly the ends of the strings of `Symᵈ⁺²(ℂ²)` and `Symᵈ(ℂ²)`. -/
private theorem trace_mul_character_symPower_torusHom (d : ℕ) (z : Circle) :
    Matrix.trace ((torusHom z : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
        * (symPower (d + 1)).character (torusHom z)
      = (symPower (d + 2)).character (torusHom z) + (symPower d).character (torusHom z) := by
  have hz : (z : ℂ) ≠ 0 := z.coe_ne_zero
  have hstep : ∀ i : ℕ, ((z : ℂ) + ((z : ℂ))⁻¹) * (z : ℂ) ^ (2 * (i : ℤ) - ((d : ℤ) + 1))
      = (z : ℂ) ^ (2 * (i : ℤ) - (d : ℤ)) + (z : ℂ) ^ (2 * (i : ℤ) - ((d : ℤ) + 2)) := by
    intro i
    have hsucc : 2 * (i : ℤ) - (d : ℤ) = (2 * (i : ℤ) - ((d : ℤ) + 1)) + 1 := by ring
    have hpred : 2 * (i : ℤ) - ((d : ℤ) + 2) = (2 * (i : ℤ) - ((d : ℤ) + 1)) - 1 := by ring
    rw [hsucc, hpred, zpow_add_one₀ hz, zpow_sub_one₀ hz]
    field_simp
  rw [coe_torusHom, trace_torusMatrix, character_symPower_torusHom_zpow,
    character_symPower_torusHom_zpow, character_symPower_torusHom_zpow]
  push_cast
  rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib,
    Finset.sum_range_succ (fun i : ℕ => (z : ℂ) ^ (2 * (i : ℤ) - (d : ℤ))) (d + 1),
    Finset.sum_range_succ (fun i : ℕ => (z : ℂ) ^ (2 * (i : ℤ) - ((d : ℤ) + 2))) (d + 2)]
  push_cast
  -- the two leftover exponents, the top of the string of `Symᵈ⁺²(ℂ²)` twice over
  have hlast : 2 * ((d : ℤ) + 1) - (d : ℤ) = (d : ℤ) + 2 := by ring
  have hlast' : 2 * ((d : ℤ) + 2) - ((d : ℤ) + 2) = (d : ℤ) + 2 := by ring
  rw [hlast, hlast']
  ring

/-- **The Chebyshev recursion for the characters of `SU(2)`:**
`tr · χ_{d+1} = χ_{d+2} + χ_d`.

On the level of representations this is the Clebsch-Gordan decomposition
`Sym¹(ℂ²) ⊗ Sym^{d+1}(ℂ²) ≅ Sym^{d+2}(ℂ²) ⊕ Symᵈ(ℂ²)`, read on characters; only the character
identity is proved here, by telescoping the weight strings on the maximal torus and extending to
`SU(2)` by conjugation invariance. -/
theorem trace_mul_character_symPower (d : ℕ) (g : SU2) :
    Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) * (symPower (d + 1)).character g
      = (symPower (d + 2)).character g + (symPower d).character g := by
  have h : (fun g : SU2 => Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)
        * (symPower (d + 1)).character g)
      = fun g : SU2 => (symPower (d + 2)).character g + (symPower d).character g := by
    refine eq_of_conjInvariant_of_eqOn_torus (fun u g => ?_) (fun u g => ?_) fun x hx => ?_
    · rw [(trace_eq_of_isConj (isConj_iff.mpr ⟨u, rfl⟩)).symm, Representation.char_conj]
    · rw [Representation.char_conj, Representation.char_conj]
    · obtain ⟨z, rfl⟩ := mem_torus_iff_exists_torusHom.mp hx
      exact trace_mul_character_symPower_torusHom d z
  exact congrFun h g

/-- **`Sym⁰(ℂ²)` is the trivial representation:** its character is constantly `1`. -/
@[simp]
theorem character_symPower_zero (g : SU2) : (symPower 0).character g = 1 := by
  have h : (fun g : SU2 => (symPower 0).character g) = fun _ : SU2 => (1 : ℂ) := by
    refine eq_of_conjInvariant_of_eqOn_torus (fun u g => Representation.char_conj _ g u)
      (fun _ _ => rfl) fun x hx => ?_
    obtain ⟨z, rfl⟩ := mem_torus_iff_exists_torusHom.mp hx
    simp [character_symPower_torusHom]
  exact congrFun h g

/-- **`Sym¹(ℂ²)` is the standard representation:** its character is the trace. -/
@[simp]
theorem character_symPower_one_eq_trace (g : SU2) :
    (symPower 1).character g = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h : (fun g : SU2 => (symPower 1).character g)
      = fun g : SU2 => Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) := by
    refine eq_of_conjInvariant_of_eqOn_torus (fun u g => Representation.char_conj _ g u)
      (fun u g => (trace_eq_of_isConj (isConj_iff.mpr ⟨u, rfl⟩)).symm) fun x hx => ?_
    obtain ⟨z, rfl⟩ := mem_torus_iff_exists_torusHom.mp hx
    rw [character_symPower_torusHom_zpow, coe_torusHom, trace_torusMatrix,
      Finset.sum_range_succ, Finset.sum_range_one]
    push_cast
    rw [_root_.zpow_neg_one, zpow_one]
    ring
  exact congrFun h g

/-- **The character of `Symᵈ(ℂ²)` is the Chebyshev polynomial of half the trace:**
`χ_d (g) = U_d (tr g / 2)`, for `Polynomial.Chebyshev.U` the Chebyshev polynomial of the second
kind. On the maximal torus this is the classical `U_d (cos θ) = sin ((d+1) θ) / sin θ`, and off it
the statement is meaningful because the trace is a complete conjugacy invariant of `SU(2)`. -/
theorem character_symPower_eq_chebyshevU_eval (d : ℕ) (g : SU2) :
    (symPower d).character g
      = (Chebyshev.U ℂ d).eval (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) / 2) := by
  induction d using Nat.twoStepInduction with
  | zero => simp [character_symPower_zero]
  | one => simp [character_symPower_one_eq_trace, Chebyshev.U_one]; ring
  | more n ihn ihn1 =>
    have hrec := trace_mul_character_symPower n g
    have hU : (Chebyshev.U ℂ ((n : ℤ) + 2))
        = 2 * X * Chebyshev.U ℂ ((n : ℤ) + 1) - Chebyshev.U ℂ (n : ℤ) :=
      Chebyshev.U_add_two ℂ (n : ℤ)
    have hcast : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have hcast1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [hcast, hU, ← hcast1]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    rw [← ihn, ← ihn1]
    linear_combination -hrec

/-! ### The characters as continuous functions -/

/-- The trace is continuous on `SU(2)`, the topology being induced from the matrices. -/
private theorem continuous_trace :
    Continuous fun g : SU2 => Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) :=
  Continuous.matrix_trace continuous_subtype_val

/-- **The character of `Symᵈ(ℂ²)` is continuous**, being a polynomial in the trace. -/
theorem continuous_character_symPower (d : ℕ) :
    Continuous fun g : SU2 => (symPower d).character g := by
  have h : (fun g : SU2 => (symPower d).character g)
      = fun g : SU2 => (Chebyshev.U ℂ d).eval (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) / 2) :=
    funext (character_symPower_eq_chebyshevU_eval d)
  rw [h]
  exact (Chebyshev.U ℂ d).continuous.comp (continuous_trace.div_const 2)

/-- The character of `Symᵈ(ℂ²)`, bundled as a continuous function on `SU(2)`. This is the form in
which the characters generate a subspace of `C(SU(2), ℂ)`; the unbundled statements are about
`(TauCeti.SU2.symPower d).character`. -/
noncomputable def symPowerCharacter (d : ℕ) : C(SU2, ℂ) :=
  ⟨fun g => (symPower d).character g, continuous_character_symPower d⟩

@[simp]
theorem symPowerCharacter_apply (d : ℕ) (g : SU2) :
    symPowerCharacter d g = (symPower d).character g := (rfl)

@[simp]
theorem symPowerCharacter_zero : symPowerCharacter 0 = 1 :=
  ContinuousMap.ext fun g => character_symPower_zero g

/-! ### The span of the characters -/

/-- The `ℂ`-linear span of the characters of the symmetric powers `Symᵈ(ℂ²)` inside the continuous
complex-valued functions on `SU(2)`. -/
noncomputable def characterSpan : Submodule ℂ C(SU2, ℂ) :=
  Submodule.span ℂ (Set.range symPowerCharacter)

theorem symPowerCharacter_mem_characterSpan (d : ℕ) :
    symPowerCharacter d ∈ characterSpan :=
  Submodule.subset_span ⟨d, rfl⟩

/-- The span of the characters is contained in a subspace exactly when every character is: the
characteristic property of `TauCeti.SU2.characterSpan` as a span. -/
theorem characterSpan_le_iff {p : Submodule ℂ C(SU2, ℂ)} :
    characterSpan ≤ p ↔ ∀ d : ℕ, symPowerCharacter d ∈ p := by
  rw [characterSpan, Submodule.span_le, Set.range_subset_iff]
  rfl

/-- Multiplying a character by the trace stays in the span of the characters: the Chebyshev
recursion `TauCeti.SU2.trace_mul_character_symPower` expresses the product as a sum of two
characters. -/
private theorem symPowerCharacter_one_mul_symPowerCharacter_mem (d : ℕ) :
    symPowerCharacter 1 * symPowerCharacter d ∈ characterSpan := by
  match d with
  | 0 =>
    rw [symPowerCharacter_zero, mul_one]
    exact symPowerCharacter_mem_characterSpan 1
  | (e + 1) =>
    have : symPowerCharacter 1 * symPowerCharacter (e + 1)
        = symPowerCharacter (e + 2) + symPowerCharacter e := by
      refine ContinuousMap.ext fun g => ?_
      simpa [character_symPower_one_eq_trace] using trace_mul_character_symPower e g
    rw [this]
    exact Submodule.add_mem _ (symPowerCharacter_mem_characterSpan _)
      (symPowerCharacter_mem_characterSpan _)

private theorem symPowerCharacter_one_mul_mem {f : C(SU2, ℂ)} (hf : f ∈ characterSpan) :
    symPowerCharacter 1 * f ∈ characterSpan := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    exact symPowerCharacter_one_mul_symPowerCharacter_mem d
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa [mul_smul_comm] using Submodule.smul_mem _ a hx

/-- **Every power of the trace lies in the span of the characters.** The first character is the
trace (`TauCeti.SU2.character_symPower_one_eq_trace`), so with linearity this says that every
polynomial function of the trace is a linear combination of the characters; the reverse inclusion
is `TauCeti.SU2.character_symPower_eq_chebyshevU_eval`, which writes each character as a
polynomial in the trace. -/
theorem pow_symPowerCharacter_one_mem_characterSpan (n : ℕ) :
    symPowerCharacter 1 ^ n ∈ characterSpan := by
  induction n with
  | zero => simpa [← symPowerCharacter_zero] using symPowerCharacter_mem_characterSpan 0
  | succ n ih => rw [pow_succ']; exact symPowerCharacter_one_mul_mem ih

/-- A real polynomial in the trace, as an element of the span of the characters: the polynomial
evaluated at the first character `χ_1 = tr` in the `ℝ`-algebra `C(SU(2), ℂ)`. -/
private noncomputable def polyTrace (p : Polynomial ℝ) : C(SU2, ℂ) :=
  aeval (symPowerCharacter 1) p

private theorem polyTrace_mem_characterSpan (p : Polynomial ℝ) :
    polyTrace p ∈ characterSpan := by
  rw [polyTrace, aeval_eq_sum_range]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_of_tower_mem _ _ (pow_symPowerCharacter_one_mem_characterSpan i)

private theorem polyTrace_apply (p : Polynomial ℝ) {g : SU2} {t : ℝ}
    (ht : Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) = (t : ℂ)) :
    polyTrace p g = ((p.eval t : ℝ) : ℂ) := by
  rw [polyTrace, aeval_eq_sum_range, p.eval_eq_sum_range]
  push_cast
  simp [ContinuousMap.sum_apply, ht, Complex.real_smul]

/-! ### Uniform density in the class functions -/

/-- **The characters of the symmetric powers span a uniformly dense subspace of the continuous
class functions of `SU(2)`:** a continuous conjugation-invariant function is within any `ε > 0`,
in the supremum norm, of a linear combination of the `χ_d`.

The class function is read on the Weyl chamber `[0, π]`, where `θ ↦ 2 cos θ` parametrises the
traces `[-2, 2]`; Weierstrass approximation on that interval, applied to the real and imaginary
parts, produces the linear combination through
`TauCeti.SU2.pow_symPowerCharacter_one_mem_characterSpan`. -/
theorem exists_mem_characterSpan_norm_sub_lt {f : C(SU2, ℂ)}
    (hf : ∀ u g : SU2, f (u * g * u⁻¹) = f g) {ε : ℝ} (hε : 0 < ε) :
    ∃ h ∈ characterSpan, ‖f - h‖ < ε := by
  -- the class function read as a function of the trace, through the Weyl chamber
  set F : ℝ → ℂ := fun t => f (torusExp (Real.arccos (t / 2))) with hF
  have hFc : Continuous F :=
    f.continuous.comp (continuous_torusExp.comp
      (Real.continuous_arccos.comp (continuous_id.div_const 2)))
  obtain ⟨p₁, hp₁⟩ := exists_polynomial_near_of_continuousOn (-2) 2 (fun t => (F t).re)
    (Complex.continuous_re.comp hFc).continuousOn (ε / 3) (by positivity)
  obtain ⟨p₂, hp₂⟩ := exists_polynomial_near_of_continuousOn (-2) 2 (fun t => (F t).im)
    (Complex.continuous_im.comp hFc).continuousOn (ε / 3) (by positivity)
  refine ⟨polyTrace p₁ + Complex.I • polyTrace p₂,
    Submodule.add_mem _ (polyTrace_mem_characterSpan p₁)
      (Submodule.smul_mem _ _ (polyTrace_mem_characterSpan p₂)), ?_⟩
  refine (ContinuousMap.norm_lt_iff _ hε).mpr fun g => ?_
  -- the conjugacy class of `g` meets the Weyl chamber
  obtain ⟨θ, hθ, hconj⟩ := exists_isConj_torusExp_mem_Icc g
  obtain ⟨u, hu⟩ := isConj_iff.mp hconj
  have harc : Real.arccos (2 * Real.cos θ / 2) = θ := by
    have hhalf : (2 : ℝ) * Real.cos θ / 2 = Real.cos θ := by ring
    rw [hhalf, Real.arccos_cos hθ.1 hθ.2]
  have hfg : f g = F (2 * Real.cos θ) := by
    rw [hF]
    simp only [harc]
    rw [← hu, hf]
  have htr : Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) = ((2 * Real.cos θ : ℝ) : ℂ) := by
    rw [trace_eq_of_isConj hconj, trace_torusExp]
    push_cast
    ring
  have hmem : (2 * Real.cos θ) ∈ Set.Icc (-2 : ℝ) 2 := by
    constructor <;> nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have h₁ := hp₁ _ hmem
  have h₂ := hp₂ _ hmem
  -- the value of the approximant at `g`
  have hval : (polyTrace p₁ + Complex.I • polyTrace p₂) g
      = ((p₁.eval (2 * Real.cos θ) : ℝ) : ℂ)
        + Complex.I * ((p₂.eval (2 * Real.cos θ) : ℝ) : ℂ) := by
    simp [polyTrace_apply p₁ htr, polyTrace_apply p₂ htr]
  rw [ContinuousMap.sub_apply, hfg, hval]
  have hsplit : F (2 * Real.cos θ)
        - (((p₁.eval (2 * Real.cos θ) : ℝ) : ℂ)
          + Complex.I * ((p₂.eval (2 * Real.cos θ) : ℝ) : ℂ))
      = ((((F (2 * Real.cos θ)).re - p₁.eval (2 * Real.cos θ) : ℝ)) : ℂ)
        + Complex.I * ((((F (2 * Real.cos θ)).im - p₂.eval (2 * Real.cos θ) : ℝ)) : ℂ) := by
    push_cast
    linear_combination -Complex.re_add_im (F (2 * Real.cos θ))
  have h₁' : |(F (2 * Real.cos θ)).re - p₁.eval (2 * Real.cos θ)| < ε / 3 := by
    rw [abs_sub_comm]; exact h₁
  have h₂' : |(F (2 * Real.cos θ)).im - p₂.eval (2 * Real.cos θ)| < ε / 3 := by
    rw [abs_sub_comm]; exact h₂
  rw [hsplit]
  calc ‖((((F (2 * Real.cos θ)).re - p₁.eval (2 * Real.cos θ) : ℝ)) : ℂ)
          + Complex.I * ((((F (2 * Real.cos θ)).im - p₂.eval (2 * Real.cos θ) : ℝ)) : ℂ)‖
      ≤ |(F (2 * Real.cos θ)).re - p₁.eval (2 * Real.cos θ)|
        + |(F (2 * Real.cos θ)).im - p₂.eval (2 * Real.cos θ)| := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ < ε := by linarith

/-- **The closure of the span of the characters is exactly the continuous class functions of
`SU(2)`.** Membership of the closure is uniform approximability by linear combinations of the
`χ_d`, so this says that the characters of the symmetric powers are a *complete* orthonormal system
for the class functions, the companion of the orthonormality
`TauCeti.SU2.character_symPower_orthonormal_torusExp`. -/
theorem mem_topologicalClosure_characterSpan_iff {f : C(SU2, ℂ)} :
    f ∈ characterSpan.topologicalClosure ↔ ∀ u g : SU2, f (u * g * u⁻¹) = f g := by
  constructor
  · intro hf u g
    have hspan : Set.EqOn (fun h : C(SU2, ℂ) => h (u * g * u⁻¹)) (fun h : C(SU2, ℂ) => h g)
        (characterSpan : Set C(SU2, ℂ)) := by
      intro h hh
      induction hh using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨d, rfl⟩ := hx
        exact Representation.char_conj _ g u
      | zero => rfl
      | add x y _ _ hx hy => simpa using congrArg₂ (· + ·) hx hy
      | smul a x _ hx => simpa using congrArg (a * ·) hx
    refine hspan.closure (continuous_eval_const _) (continuous_eval_const _) ?_
    rwa [← Submodule.topologicalClosure_coe]
  · intro hf
    have hclosure : f ∈ closure (characterSpan : Set C(SU2, ℂ)) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨h, hh, hlt⟩ := exists_mem_characterSpan_norm_sub_lt hf hε
      exact ⟨h, hh, by rwa [dist_eq_norm]⟩
    rwa [← Submodule.topologicalClosure_coe] at hclosure

end SU2

end TauCeti
