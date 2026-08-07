/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
the maximal torus `T` (`TauCeti.SU2.exists_conj_mem_torus`) and the Weyl group of `SU(2)`, of order
two, acts on `T` by inversion (`TauCeti.SU2.isConj_inv_of_mem_torus`); conversely, conjugating a
torus element back into `T` can only return it or its inverse
(`TauCeti.SU2.eq_or_eq_inv_of_conj_torusHom`). Hence each conjugacy class meets `T` in exactly one
Weyl orbit `{z, z⁻¹}` (`TauCeti.SU2.isConj_torusHom_iff`), and `z + z⁻¹ = tr (diag (z, z⁻¹))` is
the invariant that separates those orbits. Cutting each orbit down to a single representative is
what makes `[0, π]` a strict fundamental domain for the Weyl action on angles
(`TauCeti.SU2.exists_isConj_torusExp_mem_Icc` and
`TauCeti.SU2.angle_eq_of_isConj_torusExp_of_mem_Icc`): it is the Weyl chamber that the Weyl
integration formula for `SU(2)` integrates over.

The immediate use is for class functions. A conjugation-invariant function on `SU(2)` factors
through the trace (`TauCeti.SU2.eq_of_conjInvariant_of_trace_eq`). This sharpens
`TauCeti.SU2.eq_of_conjInvariant_of_eqOn_torus`, which reduces a class function to the torus but
does not say how much of the torus is needed. The consequence for characters is drawn in
`TauCeti/RepresentationTheory/SU2/Character.lean`.

## Main results

* `TauCeti.SU2.isConj_iff_trace_eq`: two elements of `SU(2)` are conjugate if and only if they
  have the same trace.
* `TauCeti.SU2.isConj_torusHom_iff`: two torus elements are conjugate in `SU(2)` exactly when they
  are equal or inverse, so each conjugacy class meets the torus in a single Weyl orbit.
* `TauCeti.SU2.conj_trace`, `TauCeti.SU2.norm_trace_le_two` and
  `TauCeti.SU2.exists_trace_eq_ofReal`: the traces of elements of `SU(2)` are exactly the real
  numbers of absolute value at most `2`.
* `TauCeti.SU2.exists_isConj_torusExp_mem_Icc` and
  `TauCeti.SU2.angle_eq_of_isConj_torusExp_of_mem_Icc`: `[0, π]` is a strict fundamental domain,
  every element of `SU(2)` being conjugate to `diag (e^{iθ}, e^{-iθ})` for exactly one `θ` in it.
* `TauCeti.SU2.eq_of_conjInvariant_of_trace_eq`: a class function on `SU(2)` is a function of the
  trace.

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

/-! ### The trace of an element of `SU(2)` -/

/-- **The trace of an element of `SU(2)` is real.** Taking traces in
`TauCeti.SU2.coe_add_star`, `g + g* = (tr g) • 1`, gives `tr g + conj (tr g)` on the left and
`2 tr g` on the right. -/
theorem conj_trace (g : SU2) :
    (starRingEnd ℂ) (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ))
      = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h := congrArg Matrix.trace (coe_add_star g)
  simp only [Matrix.trace_add, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, Nat.cast_ofNat] at h
  rw [starRingEnd_apply]
  linear_combination h

/-- Conjugate elements of `SU(2)` have the same trace. -/
theorem trace_eq_of_isConj {g h : SU2} (hgh : IsConj g h) :
    Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨u, rfl⟩ := isConj_iff.mp hgh
  simp only [Submonoid.coe_mul]
  rw [Matrix.trace_mul_cycle, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
    Matrix.one_mul]

/-- The trace of the torus element `diag (e^{iθ}, e^{-iθ})` is `2 cos θ`. This is not a `simp`
lemma: `TauCeti.SU2.coe_torusExp` already rewrites the underlying matrix to a diagonal one, so its
left-hand side is not in simp-normal form. -/
theorem trace_coe_torusExp (θ : ℝ) :
    Matrix.trace ((torusExp θ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = 2 * (Real.cos θ : ℂ) := by
  rw [torusExp_def, coe_torusHom, trace_torusMatrix, Circle.coe_exp, ← Complex.exp_neg,
    Complex.ofReal_cos, Complex.two_cos, neg_mul]

/-- **The trace of an element of `SU(2)` has absolute value at most `2`**: it is `2 cos θ` for
the angle of any torus element it is conjugate to. -/
theorem norm_trace_le_two (g : SU2) : ‖Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 := by
  obtain ⟨θ, hθ⟩ := exists_isConj_torusExp g
  rw [trace_eq_of_isConj hθ, trace_coe_torusExp]
  simp only [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  linarith [Real.abs_cos_le_one θ]

/-- **Every real number of absolute value at most `2` is the trace of an element of `SU(2)`**,
realized on the maximal torus by the angle `arccos (t / 2)`. With
`TauCeti.SU2.isConj_iff_trace_eq` and `TauCeti.SU2.conj_trace` this identifies the set of
conjugacy classes of `SU(2)` with the interval `[-2, 2]`. -/
theorem exists_trace_eq_ofReal {t : ℝ} (ht : |t| ≤ 2) :
    ∃ g : SU2, Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) = (t : ℂ) := by
  obtain ⟨hlb, hub⟩ := abs_le.mp ht
  refine ⟨torusExp (Real.arccos (t / 2)), ?_⟩
  rw [trace_coe_torusExp, Real.cos_arccos (by linarith) (by linarith)]
  push_cast
  ring

/-! ### Conjugacy on the maximal torus -/

/-- **Each conjugacy class of `SU(2)` meets the maximal torus in exactly one Weyl orbit:** two
torus elements are conjugate in `SU(2)` precisely when they are equal or inverse. The forward
direction is `TauCeti.SU2.eq_or_eq_inv_of_conj_torusHom` and the backward direction is the Weyl
reflection `TauCeti.SU2.isConj_inv_of_mem_torus`. -/
theorem isConj_torusHom_iff {z w : Circle} :
    IsConj (torusHom z) (torusHom w) ↔ w = z ∨ w = z⁻¹ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := isConj_iff.mp h
    exact eq_or_eq_inv_of_conj_torusHom hu
  · rintro (rfl | rfl)
    · exact IsConj.refl _
    · rw [map_inv]
      exact isConj_inv_of_mem_torus (torusHom_mem_torus z)

/-- Reading off the angles from an equality of traces on the torus: the factor `2` in
`tr (diag (e^{iθ}, e^{-iθ})) = 2 cos θ` cancels, and the cosines are real. -/
private theorem cos_eq_of_trace_torusExp_eq {θ φ : ℝ}
    (h : Matrix.trace ((torusExp θ : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace ((torusExp φ : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) :
    Real.cos φ = Real.cos θ := by
  rw [trace_coe_torusExp, trace_coe_torusExp] at h
  have hc := mul_left_cancel₀ (a := (2 : ℂ)) (by norm_num) h
  exact_mod_cast hc.symm

/-- Two torus elements are conjugate in `SU(2)` exactly when their angles have the same cosine:
the Weyl group acts on the angle by negation, and the cosine is precisely the invariant of that
action. -/
theorem isConj_torusExp_iff {θ φ : ℝ} :
    IsConj (torusExp θ) (torusExp φ) ↔ Real.cos φ = Real.cos θ := by
  refine ⟨fun h => cos_eq_of_trace_torusExp_eq (trace_eq_of_isConj h), fun h => ?_⟩
  rw [torusExp_def, torusExp_def]
  refine isConj_torusHom_iff.mpr (eq_or_eq_inv_of_trace_torusMatrix_eq ?_)
  have hφ := trace_coe_torusExp φ
  have hθ := trace_coe_torusExp θ
  rw [torusExp_def, coe_torusHom] at hφ hθ
  rw [hφ, hθ, h]

/-! ### The trace as a complete conjugacy invariant -/

/-- **The conjugacy classes of `SU(2)` are classified by the trace:** two elements of `SU(2)` are
conjugate if and only if they have the same trace. Conjugation always preserves the trace; the
content is the converse, which conjugates both elements into the maximal torus and applies the
Weyl-orbit description `TauCeti.SU2.isConj_torusExp_iff`. -/
theorem isConj_iff_trace_eq {g h : SU2} :
    IsConj g h ↔ Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨trace_eq_of_isConj, fun htr => ?_⟩
  obtain ⟨θ, hθ⟩ := exists_isConj_torusExp g
  obtain ⟨φ, hφ⟩ := exists_isConj_torusExp h
  refine hθ.trans (IsConj.trans ?_ hφ.symm)
  refine isConj_torusExp_iff.mpr (cos_eq_of_trace_torusExp_eq ?_)
  rw [← trace_eq_of_isConj hθ, ← trace_eq_of_isConj hφ]
  exact htr

/-! ### The Weyl chamber `[0, π]` as a strict fundamental domain -/

/-- Every element of `SU(2)` is conjugate to `diag (e^{iθ}, e^{-iθ})` for some angle `θ` in the
Weyl chamber `[0, π]`: the angle produced by torus conjugacy is folded into the chamber by
`arccos ∘ cos`, which changes it only by the Weyl reflection `θ ↦ -θ` and a full turn. -/
theorem exists_isConj_torusExp_mem_Icc (g : SU2) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi, IsConj g (torusExp θ) := by
  obtain ⟨φ, hφ⟩ := exists_isConj_torusExp g
  refine ⟨Real.arccos (Real.cos φ), ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, ?_⟩
  exact hφ.trans (isConj_torusExp_iff.mpr
    (Real.cos_arccos (Real.neg_one_le_cos φ) (Real.cos_le_one φ)))

/-- The Weyl chamber `[0, π]` contains **at most** one angle from each conjugacy class: distinct
angles there give non-conjugate torus elements, because the cosine is injective on `[0, π]`.
With `TauCeti.SU2.exists_isConj_torusExp_mem_Icc` this says `[0, π]` is a *strict* fundamental
domain for the Weyl action on the angles of the maximal torus. -/
theorem angle_eq_of_isConj_torusExp_of_mem_Icc {θ φ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi)
    (hφ : φ ∈ Set.Icc (0 : ℝ) Real.pi) (h : IsConj (torusExp θ) (torusExp φ)) : θ = φ :=
  Real.injOn_cos hθ hφ (isConj_torusExp_iff.mp h).symm

/-! ### Class functions are functions of the trace -/

/-- **A class function on `SU(2)` factors through the trace:** a conjugation-invariant function
takes the same value at any two elements of the same trace. -/
theorem eq_of_conjInvariant_of_trace_eq {α : Type*} {f : SU2 → α}
    (hf : ∀ u g : SU2, f (u * g * u⁻¹) = f g) {g h : SU2}
    (htr : Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ)) : f g = f h := by
  obtain ⟨u, hu⟩ := isConj_iff.mp (isConj_iff_trace_eq.mpr htr)
  rw [← hu, hf]

end SU2

end TauCeti
