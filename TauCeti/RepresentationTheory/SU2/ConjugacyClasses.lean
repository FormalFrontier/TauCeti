/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SU2.TorusConjugacy

/-!
# The conjugacy classes of `SU(2)` are classified by the trace

Two elements of `SU(2)` are conjugate exactly when they have the same trace
(`TauCeti.SU2.isConj_iff_trace_eq`), and the traces that occur are exactly the real numbers of
absolute value at most `2`. So the conjugacy classes of `SU(2)` are parametrised by an angle
`θ ∈ [0, π]`, through `θ ↦ diag (e^{iθ}, e^{-iθ})`, whose trace is `2 cos θ`.

This assembles two halves that are already available. Every element of `SU(2)` is conjugate into
the maximal torus `T` (`TauCeti.SU2.exists_conj_mem_torus`), and each conjugacy class meets `T` in
exactly one Weyl orbit `{z, z⁻¹}` (`TauCeti.SU2.isConj_torusHom_iff` of
`TauCeti/RepresentationTheory/SU2/TorusConjugacy.lean`); here `z + z⁻¹ = tr (diag (z, z⁻¹))` is
the invariant that separates those orbits. Cutting each orbit down to a single representative
makes `[0, π]` a set of representatives for the conjugacy classes: every element of `SU(2)` is
conjugate to `diag (e^{iθ}, e^{-iθ})` for exactly one `θ` in it
(`TauCeti.SU2.exists_isConj_torusExp_mem_Icc` and
`TauCeti.SU2.eq_of_mem_Icc_of_isConj_torusExp`). Note that the angle has to be read modulo `2π`
for this to be the Weyl action alone: `θ ↦ -θ` by itself does not move `θ = 5` into `[0, π]`.
This is the Weyl chamber that the Weyl integration formula for `SU(2)` integrates over.

The immediate use is for class functions. A conjugation-invariant function on `SU(2)` factors
through the trace (`TauCeti.SU2.eq_of_conjInvariant_of_trace_eq`), and two of them that agree on
the chamber `[0, π]` are equal (`TauCeti.SU2.eq_of_conjInvariant_of_eqOn_torusExp_Icc`). The
latter sharpens `TauCeti.SU2.eq_of_conjInvariant_of_eqOn_torus`, which reduces a class function to
the whole torus but does not say how much of the torus is needed. The consequence for characters
is drawn in `TauCeti/RepresentationTheory/SU2/Character.lean`.

## Main results

* `TauCeti.SU2.isConj_iff_trace_eq`: two elements of `SU(2)` are conjugate if and only if they
  have the same trace.
* `TauCeti.SU2.isConj_torusExp_iff_cos_eq`: on the maximal torus that criterion reads as the
  equality of the cosines of the angles, the cosine being the invariant of the Weyl action on
  angles read modulo `2π`.
* `TauCeti.SU2.norm_trace_le_two` and `TauCeti.SU2.exists_trace_torusExp_eq_ofReal`: together with
  `TauCeti.SU2.isSelfAdjoint_trace`, the traces of elements of `SU(2)` are exactly the real
  numbers of absolute value at most `2`.
* `TauCeti.SU2.exists_isConj_torusExp_mem_Icc` and
  `TauCeti.SU2.eq_of_mem_Icc_of_isConj_torusExp`: every element of `SU(2)` is conjugate to
  `diag (e^{iθ}, e^{-iθ})` for exactly one `θ ∈ [0, π]`, so the Weyl chamber `[0, π]` is a set of
  representatives for the conjugacy classes.
* `TauCeti.SU2.eq_of_conjInvariant_of_trace_eq`,
  `TauCeti.SU2.exists_mem_Icc_eq_torusExp_of_conjInvariant` and
  `TauCeti.SU2.eq_of_conjInvariant_of_eqOn_torusExp_Icc`: a class function on `SU(2)` is a
  function of the trace, is computed at every element by its value at an angle of the Weyl
  chamber, and is determined by its values there.

## References

This serves the engine case of
`TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md`, "Engine case: `SU(2)` and the
maximal torus", whose torus-conjugacy step asks for the identification of the class functions of
`SU(2)` with the `W`-invariant functions on the maximal torus.

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 18.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I.
-/

public section

namespace TauCeti

namespace SU2

/-! ### The traces that occur -/

/-- **The trace of an element of `SU(2)` has absolute value at most `2`**: it is `2 cos θ` for
the angle of any torus element it is conjugate to. -/
theorem norm_trace_le_two (g : SU2) : ‖Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 := by
  obtain ⟨θ, hθ⟩ := exists_isConj_torusExp g
  rw [trace_eq_of_isConj hθ, trace_torusExp]
  simp only [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  linarith [Real.abs_cos_le_one θ]

/-- **Every real number of absolute value at most `2` is the trace of an element of `SU(2)`**,
realized on the maximal torus by the angle `arccos (t / 2)`, which lies in the Weyl chamber
`[0, π]`. With `TauCeti.SU2.isConj_iff_trace_eq` and `TauCeti.SU2.isSelfAdjoint_trace` this
identifies the set of conjugacy classes of `SU(2)` with the interval `[-2, 2]`, and it inverts
`θ ↦ 2 cos θ` on the chamber. -/
theorem exists_trace_torusExp_eq_ofReal {t : ℝ} (ht : |t| ≤ 2) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      Matrix.trace ((torusExp θ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = (t : ℂ) := by
  obtain ⟨hlb, hub⟩ := abs_le.mp ht
  refine ⟨Real.arccos (t / 2), ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, ?_⟩
  rw [trace_torusExp, Real.cos_arccos (by linarith) (by linarith)]
  push_cast
  ring

/-! ### The trace as a complete conjugacy invariant -/

/-- **The conjugacy classes of `SU(2)` are classified by the trace:** two elements of `SU(2)` are
conjugate if and only if they have the same trace. Conjugation always preserves the trace
(`TauCeti.SU2.trace_eq_of_isConj`); the content is the converse, which conjugates both elements
into the maximal torus (`TauCeti.SU2.exists_isConj_torusHom`) and separates the Weyl orbits there
by the invariant `z + z⁻¹ = tr (diag (z, z⁻¹))`
(`TauCeti.SU2.eq_or_eq_inv_of_trace_torusMatrix_eq` and
`TauCeti.SU2.isConj_torusHom_iff`). -/
theorem isConj_iff_trace_eq {g h : SU2} :
    IsConj g h ↔ Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨trace_eq_of_isConj, fun htr => ?_⟩
  obtain ⟨z, hz⟩ := exists_isConj_torusHom g
  obtain ⟨w, hw⟩ := exists_isConj_torusHom h
  have hg := trace_eq_of_isConj hz
  have hh := trace_eq_of_isConj hw
  rw [coe_torusHom] at hg hh
  refine hz.trans (IsConj.trans (isConj_torusHom_iff.mpr ?_) hw.symm)
  exact eq_or_eq_inv_of_trace_torusMatrix_eq (by rw [← hg, ← hh]; exact htr.symm)

/-! ### Conjugacy on the maximal torus -/

/-- Two torus elements are conjugate in `SU(2)` exactly when their angles have the same cosine:
the Weyl group acts on the angle by negation, and, on angles read modulo `2π`, the cosine is
precisely the invariant of that action — equal cosines say exactly that `φ ≡ ±θ (mod 2π)`, which
negation alone on `ℝ` does not. This is `TauCeti.SU2.isConj_iff_trace_eq` in the angle
parametrisation of the maximal torus, with the trace evaluated by
`TauCeti.SU2.trace_torusExp`. -/
theorem isConj_torusExp_iff_cos_eq {θ φ : ℝ} :
    IsConj (torusExp θ) (torusExp φ) ↔ Real.cos φ = Real.cos θ := by
  rw [isConj_iff_trace_eq, trace_torusExp, trace_torusExp]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  exact_mod_cast (mul_left_cancel₀ (a := (2 : ℂ)) (by norm_num) h).symm

/-! ### The Weyl chamber `[0, π]` as a set of representatives -/

/-- Every element of `SU(2)` is conjugate to `diag (e^{iθ}, e^{-iθ})` for some angle `θ` in the
Weyl chamber `[0, π]`: the angle produced by torus conjugacy is folded into the chamber by
`arccos ∘ cos`, which changes it only by the Weyl reflection `θ ↦ -θ` and a whole number of full
turns. -/
theorem exists_isConj_torusExp_mem_Icc (g : SU2) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi, IsConj g (torusExp θ) := by
  obtain ⟨φ, hφ⟩ := exists_isConj_torusExp g
  refine ⟨Real.arccos (Real.cos φ), ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, ?_⟩
  exact hφ.trans (isConj_torusExp_iff_cos_eq.mpr
    (Real.cos_arccos (Real.neg_one_le_cos φ) (Real.cos_le_one φ)))

/-- The Weyl chamber `[0, π]` contains **at most** one angle from each conjugacy class: distinct
angles there give non-conjugate torus elements, because the cosine is injective on `[0, π]`.
With `TauCeti.SU2.exists_isConj_torusExp_mem_Icc` this says that each conjugacy class of `SU(2)`
contains `diag (e^{iθ}, e^{-iθ})` for exactly one `θ ∈ [0, π]`; equivalently, `[0, π]` is a strict
fundamental domain for the Weyl reflection `θ ↦ -θ` acting on the angles read modulo `2π`. -/
theorem eq_of_mem_Icc_of_isConj_torusExp {θ φ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi)
    (hφ : φ ∈ Set.Icc (0 : ℝ) Real.pi) (h : IsConj (torusExp θ) (torusExp φ)) : θ = φ :=
  Real.injOn_cos hθ hφ (isConj_torusExp_iff_cos_eq.mp h).symm

/-! ### Class functions are functions of the trace -/

/-- **A class function on `SU(2)` factors through the trace:** a conjugation-invariant function
takes the same value at any two elements of the same trace. -/
theorem eq_of_conjInvariant_of_trace_eq {α : Type*} {f : SU2 → α}
    (hf : ∀ u g : SU2, f (u * g * u⁻¹) = f g) {g h : SU2}
    (htr : Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ)) : f g = f h := by
  obtain ⟨u, hu⟩ := isConj_iff.mp (isConj_iff_trace_eq.mpr htr)
  rw [← hu, hf]

/-- **A class function on `SU(2)` is computed on the Weyl chamber:** a conjugation-invariant
function takes at any element the value it takes at `diag (e^{iθ}, e^{-iθ})` for some angle
`θ ∈ [0, π]`, that element being conjugate to it
(`TauCeti.SU2.exists_isConj_torusExp_mem_Icc`). -/
theorem exists_mem_Icc_eq_torusExp_of_conjInvariant {α : Type*} {f : SU2 → α}
    (hf : ∀ u g : SU2, f (u * g * u⁻¹) = f g) (g : SU2) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi, f g = f (torusExp θ) := by
  obtain ⟨θ, hθ, hconj⟩ := exists_isConj_torusExp_mem_Icc g
  obtain ⟨u, hu⟩ := isConj_iff.mp hconj
  exact ⟨θ, hθ, by rw [← hu, hf]⟩

/-- **A class function on `SU(2)` is determined by its values on the Weyl chamber:** two
conjugation-invariant functions that agree at `diag (e^{iθ}, e^{-iθ})` for every `θ ∈ [0, π]` are
equal. This sharpens `TauCeti.SU2.eq_of_conjInvariant_of_eqOn_torus`, which asks for agreement on
the whole maximal torus, to the Weyl chamber, which by
`TauCeti.SU2.exists_isConj_torusExp_mem_Icc` already meets every conjugacy class. -/
theorem eq_of_conjInvariant_of_eqOn_torusExp_Icc {α : Type*} {f₁ f₂ : SU2 → α}
    (h₁ : ∀ u g : SU2, f₁ (u * g * u⁻¹) = f₁ g) (h₂ : ∀ u g : SU2, f₂ (u * g * u⁻¹) = f₂ g)
    (h : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, f₁ (torusExp θ) = f₂ (torusExp θ)) : f₁ = f₂ := by
  funext g
  obtain ⟨θ, hθ, hconj⟩ := exists_isConj_torusExp_mem_Icc g
  obtain ⟨u, hu⟩ := isConj_iff.mp hconj
  rw [← h₁ u g, ← h₂ u g, hu, h θ hθ]

end SU2

end TauCeti
