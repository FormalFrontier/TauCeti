/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula

/-!
# Riemann's theorem and the genus

For a divisor `D` of an algebraic function field `F / k`, the quantity `deg D - ℓ(D)` is bounded
above by a constant depending only on `F / k`.  The **genus** of `F / k` is the supremum

`g := sup {deg D + 1 - ℓ(D) | D a divisor}`,

truncated to `ℕ`.  Over an exact constant field the truncation changes nothing and `g` really is
the maximum, attained at some divisor; over a non-exact one it is a junk value (see
`TauCeti.genus`).  Unwinding the supremum gives **Riemann's theorem** `ℓ(D) ≥ deg D + 1 - g`,
valid over any constant field; over an exact constant field there is moreover equality as soon
as `deg D` is large.  This file is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed.,
Proposition 1.4.14 through Definition 1.5.1.

The boundedness argument is the only substantial one.  Fix a transcendental `x`, let `B = (x)_∞`
be its pole divisor, so that `deg B = [F : k(x)] = n` by the product formula, and let `C` be an
effective divisor dominating the pole divisors of a `k(x)`-basis `u₁, …, uₙ` of `F`.  The
`n (l + 1)` functions `uᵢ xʲ` with `j ≤ l` are `k`-linearly independent and lie in `L(l B + C)`,
so `ℓ(l B + C) ≥ n (l + 1)`, whence `deg (l B) - ℓ(l B) ≤ deg C - n` uniformly in `l`.  Every
divisor is linearly equivalent to one below some `l B`, and both `deg` and `ℓ` are
linear-equivalence invariants, so the same bound holds for every divisor.

## Main definitions

* `TauCeti.genus`: the genus `g` of `F / k` (Definition 1.4.15), as a natural number.  It is
  finite for a function field by Proposition 1.4.14, and truncation to `ℕ` is harmless when the
  constant field is exact.
* `TauCeti.Divisor.indexOfSpecialty`: the index of specialty `i(D) = ℓ(D) - deg D - 1 + g`
  (Definition 1.5.1).

## Main results

* `TauCeti.Divisor.bddAbove_range_degree_sub_dim`: **Proposition 1.4.14** — `deg D - ℓ(D)` is
  bounded above.  This is what makes the genus well-defined.
* `TauCeti.Divisor.degree_add_one_sub_genus_le_dim`: **Riemann's theorem** (Theorem 1.4.17),
  `ℓ(D) ≥ deg D + 1 - g`, over an arbitrary constant field.
* `TauCeti.exists_degree_add_one_sub_dim_eq_genus`: the genus is attained (Corollary 1.4.16).
* `TauCeti.exists_forall_dim_eq_degree_add_one_sub_genus`: **Theorem 1.4.17**, second half —
  equality holds in Riemann's theorem once `deg D` is large enough.
* `TauCeti.Divisor.indexOfSpecialty_nonneg` and
  `TauCeti.exists_forall_indexOfSpecialty_eq_zero`: the index of specialty is nonnegative, and
  vanishes in large degree.

Only the statements that mention the *value* of the maximum need the constant field to be exact;
the bound of Proposition 1.4.14 and Riemann's inequality itself hold with no hypothesis on `k`
beyond `IsFunctionField k F`.

## Provenance

The mathematics is Stichtenoth's and the Lean development is independent, as in
`TauCeti.FieldTheory.FunctionField.Place.Zeros`.  The roadmap's coordination section records
that `vaca22/riemann-roch-function-fields` (Guanghao Li, Apache-2.0) carries a complete
function-field Riemann–Roch by the same Stichtenoth route, and that this roadmap specifies the
mathematics rather than that code; no code is copied or adapted from it here.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.4 and Definition 1.5.1.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### The uniform bound on `deg D - ℓ(D)` -/

/-- The ladder underlying Stichtenoth's proof of Proposition 1.4.14: a divisor `B` of some positive
degree `n` and an effective divisor `C` such that `ℓ(l B + C) ≥ n (l + 1)` for every `l`. -/
private theorem exists_growth_ladder (hF : IsFunctionField k F) :
    ∃ (B C : Divisor k F) (n : ℕ), 0 < n ∧ Divisor.degree B = n ∧ 0 ≤ C ∧
      ∀ l : ℕ, n * (l + 1) ≤ Divisor.dim (l • B + C) := by
  classical
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  have hfin : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  have hx0 : x ≠ 0 := by rintro rfl; exact hx isAlgebraic_zero
  obtain ⟨n, hnrank⟩ : ∃ n : ℕ, Module.finrank k⟮x⟯ F = n := ⟨_, rfl⟩
  have hn : 0 < n := hnrank ▸ Module.finrank_pos
  obtain ⟨u⟩ : Nonempty (Module.Basis (Fin n) k⟮x⟯ F) :=
    ⟨Module.finBasisOfFinrankEq k⟮x⟯ F hnrank⟩
  obtain ⟨c, hcval⟩ : ∃ w : Fin n → Fˣ, ∀ i, (w i : F) = u i :=
    ⟨fun i ↦ Units.mk0 (u i) (u.ne_zero i), fun _ ↦ rfl⟩
  refine ⟨Divisor.poles hF (Units.mk0 x hx0), ∑ i : Fin n, Divisor.poles hF (c i), n, hn,
    ?_, ?_, ?_⟩
  · have h := Divisor.degree_poles hF (Units.mk0 x hx0) hx
    rwa [Units.val_mk0, hnrank] at h
  · exact Finset.sum_nonneg fun i _ ↦
      WeilDivisor.isEffective_iff_zero_le.mp (Divisor.isEffective_poles hF (c i))
  · intro l
    have hC : ∀ i, Divisor.poles hF (c i) ≤ ∑ j : Fin n, Divisor.poles hF (c j) :=
      fun i ↦ Finset.single_le_sum
        (f := fun j : Fin n ↦ Divisor.poles hF (c j))
        (fun j _ ↦ WeilDivisor.isEffective_iff_zero_le.mp (Divisor.isEffective_poles hF (c j)))
        (Finset.mem_univ i)
    have hli : LinearIndependent k⟮x⟯ fun i ↦ (c i : F) := by
      have hfun : (fun i ↦ (c i : F)) = ⇑u := funext hcval
      rw [hfun]
      exact u.linearIndependent
    have hgrowth :=
      Divisor.card_mul_succ_le_dim_nsmul_poles_add hF (Units.mk0 x hx0) hx c hli hC l
    simpa using hgrowth

/-- If `L(E - A)` is nonzero, then `ℓ(E) - deg E ≤ ℓ(A) - deg A`. -/
private theorem dim_sub_degree_le_of_riemannRochSpace_ne_bot (hF : IsFunctionField k F)
    {A E : Divisor k F} (h : riemannRochSpace (E - A) ≠ ⊥) :
    (Divisor.dim E : ℤ) - Divisor.degree E ≤ Divisor.dim A - Divisor.degree A := by
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).mp h
  have hzmem : (0 : Divisor k F) ≤ Divisor.principal hF (Units.mk0 z hz0) + (E - A) :=
    (mem_riemannRochSpace_units_iff hF (z := Units.mk0 z hz0)).mp hz
  have hAle : A - Divisor.principal hF (Units.mk0 z hz0) ≤ E := by
    refine sub_le_iff_le_add'.mpr (sub_nonneg.mp ?_)
    rw [add_sub_assoc]
    exact hzmem
  have hstep := Divisor.dim_le_dim_add_degree_sub hF hAle
  rw [Divisor.dim_sub_principal hF (Units.mk0 z hz0) A, Divisor.degree_sub,
    Divisor.degree_principal, sub_zero] at hstep
  linarith

/-- **Stichtenoth, Proposition 1.4.14**: over all divisors of an algebraic function field the
quantity `deg D - ℓ(D)` is bounded above.  This finiteness is what makes the genus well-defined;
no hypothesis on the constant field is needed. -/
theorem Divisor.bddAbove_range_degree_sub_dim (hF : IsFunctionField k F) :
    BddAbove (Set.range fun D : Divisor k F ↦ Divisor.degree D - (Divisor.dim D : ℤ)) := by
  obtain ⟨B, C, n, hn, hdegB, hC, hladder⟩ := exists_growth_ladder hF
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hdeg : ∀ l : ℕ, Divisor.degree (l • B) = (l : ℤ) * n := fun l ↦ by
    rw [map_nsmul, hdegB, nsmul_eq_mul]
  -- `ℓ(l • B)` grows at least as fast as `n (l + 1) - deg C`.
  have hlow : ∀ l : ℕ, (n : ℤ) * (l + 1) - Divisor.degree C ≤ Divisor.dim (l • B) := by
    intro l
    have hmono := Divisor.dim_le_dim_add_degree_sub hF
      (le_add_of_nonneg_right hC : l • B ≤ l • B + C)
    have hgrow : ((n : ℤ) * (l + 1)) ≤ (Divisor.dim (l • B + C) : ℤ) := by
      exact_mod_cast hladder l
    rw [Divisor.degree_add, hdeg l] at hmono
    linarith
  refine ⟨Divisor.degree C - n, ?_⟩
  rintro _ ⟨A, rfl⟩
  -- Choose `l` large enough that `L(l • B - A⁺)` is nonzero.
  obtain ⟨l, hlge⟩ : ∃ l : ℕ, Divisor.degree C + Divisor.degree A⁺ ≤ (l : ℤ) :=
    ⟨(Divisor.degree C + Divisor.degree A⁺).toNat, Int.self_le_toNat _⟩
  have hposA : (0 : Divisor k F) ≤ A⁺ :=
    WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_posPart A)
  have hdrop := Divisor.dim_le_dim_add_degree_sub hF (sub_le_self (l • B) hposA)
  rw [Divisor.degree_sub, hdeg l] at hdrop
  have hbig : (l : ℤ) + 1 ≤ (n : ℤ) * (l + 1) :=
    le_mul_of_one_le_left (by positivity) hn'
  have hpos : 1 ≤ Divisor.dim (l • B - A⁺) := by
    have h : (1 : ℤ) ≤ Divisor.dim (l • B - A⁺) := by linarith [hlow l]
    exact_mod_cast h
  -- Move `A` below `l • B` by a linear equivalence, and compare there.
  have hne : riemannRochSpace (l • B - A) ≠ ⊥ :=
    (Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF _).mp
      (hpos.trans (Divisor.dim_mono hF (sub_le_sub_left (le_posPart A) (l • B))))
  have hfinal := dim_sub_degree_le_of_riemannRochSpace_ne_bot hF hne
  rw [hdeg l] at hfinal
  linarith [hlow l]

/-! ### The genus -/

variable (k F) in
/-- **The genus of an algebraic function field** (Stichtenoth, Definition 1.4.15):
`g = sup {deg D + 1 - ℓ(D)}` after truncation to natural numbers.  When `IsFunctionField k F`,
`TauCeti.Divisor.bddAbove_range_degree_sub_dim` makes this supremum finite; without that hypothesis,
an unbounded range gives the junk value `0`.

The value is truncated to `ℕ`.  Over an exact constant field this loses nothing, because `D = 0`
already gives `deg 0 + 1 - ℓ(0) = 0`; see `TauCeti.exists_degree_add_one_sub_dim_eq_genus`.  Over a
non-exact constant field the truncation is a junk value: for `ℝ ⊆ ℂ(x)` the true maximum is `-1`,
because every `ℝ`-degree and every `ℝ`-dimension is twice its `ℂ`-counterpart. -/
noncomputable def genus : ℕ :=
  sSup (Set.range fun D : Divisor k F ↦ (Divisor.degree D + 1 - Divisor.dim D).toNat)

/-- The set of values whose supremum defines the genus is bounded above. -/
private theorem bddAbove_range_genusValue (hF : IsFunctionField k F) :
    BddAbove (Set.range fun D : Divisor k F ↦ (Divisor.degree D + 1 - Divisor.dim D).toNat) := by
  obtain ⟨γ, hγ⟩ := Divisor.bddAbove_range_degree_sub_dim hF
  refine ⟨(γ + 1).toNat, ?_⟩
  rintro _ ⟨D, rfl⟩
  have h : Divisor.degree D - (Divisor.dim D : ℤ) ≤ γ := hγ ⟨D, rfl⟩
  have hbound : (Divisor.degree D + 1 - (Divisor.dim D : ℤ)).toNat ≤ (γ + 1).toNat := by omega
  exact hbound

/-- The least-upper-bound half of the universal property defining the genus. -/
theorem genus_le {c : ℕ}
    (h : ∀ D : Divisor k F, Divisor.degree D + 1 - Divisor.dim D ≤ (c : ℤ)) :
    genus k F ≤ c := by
  rw [genus]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨D, rfl⟩
  exact Int.toNat_le.mpr (h D)

/-- **Riemann's theorem** (Stichtenoth, Theorem 1.4.17), in the form that unwinds the definition
of the genus: `deg D + 1 - ℓ(D) ≤ g` for every divisor `D`. -/
theorem Divisor.degree_add_one_sub_dim_le_genus (hF : IsFunctionField k F) (D : Divisor k F) :
    Divisor.degree D + 1 - Divisor.dim D ≤ (genus k F : ℤ) := by
  refine Int.self_le_toNat _ |>.trans ?_
  exact_mod_cast le_csSup (bddAbove_range_genusValue hF) (Set.mem_range_self D)

/-- **Riemann's theorem** (Stichtenoth, Theorem 1.4.17): `ℓ(D) ≥ deg D + 1 - g`.  No hypothesis on
the constant field is needed for the inequality. -/
theorem Divisor.degree_add_one_sub_genus_le_dim (hF : IsFunctionField k F) (D : Divisor k F) :
    Divisor.degree D + 1 - (genus k F : ℤ) ≤ Divisor.dim D := by
  have h := Divisor.degree_add_one_sub_dim_le_genus hF D
  linarith

/-- **Stichtenoth, Corollary 1.4.16**: over an exact constant field the maximum defining the genus
is attained, so `g ≥ 0` is the honest bound rather than an artefact of truncation. -/
theorem exists_degree_add_one_sub_dim_eq_genus (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) :
    ∃ D : Divisor k F, Divisor.degree D + 1 - Divisor.dim D = (genus k F : ℤ) := by
  rcases Nat.eq_zero_or_pos (genus k F) with hg | hg
  · refine ⟨0, ?_⟩
    rw [Divisor.degree_zero, Divisor.dim_zero_of_isIntegrallyClosedIn hF hex, hg]
    norm_num
  · have hmem : genus k F ∈ Set.range fun D : Divisor k F ↦
        (Divisor.degree D + 1 - Divisor.dim D).toNat :=
      Nat.sSup_mem (Set.range_nonempty _) (bddAbove_range_genusValue hF)
    obtain ⟨D, hD⟩ := hmem
    have hD' : (Divisor.degree D + 1 - (Divisor.dim D : ℤ)).toNat = genus k F := hD
    exact ⟨D, by omega⟩

/-- **Stichtenoth, Theorem 1.4.17**, second half: equality holds in Riemann's theorem for every
divisor of sufficiently large degree. -/
theorem exists_forall_dim_eq_degree_add_one_sub_genus (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) :
    ∃ c : ℤ, ∀ D : Divisor k F, c ≤ Divisor.degree D →
      (Divisor.dim D : ℤ) = Divisor.degree D + 1 - genus k F := by
  obtain ⟨A, hA⟩ := exists_degree_add_one_sub_dim_eq_genus hF hex
  refine ⟨Divisor.degree A + genus k F, fun D hD ↦ ?_⟩
  -- `L(D - A)` is nonzero, so `A ≤ D + div z` for some `z`.
  have hgap : (1 : ℤ) ≤ Divisor.dim (D - A) := by
    have := Divisor.degree_add_one_sub_genus_le_dim hF (D - A)
    rw [Divisor.degree_sub] at this
    linarith
  have hne : riemannRochSpace (D - A) ≠ ⊥ :=
    (Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF _).mp (by exact_mod_cast hgap)
  have hstep := dim_sub_degree_le_of_riemannRochSpace_ne_bot hF hne
  have hupper := Divisor.degree_add_one_sub_dim_le_genus hF D
  linarith

/-! ### The index of specialty -/

/-- **The index of specialty** of a divisor (Stichtenoth, Definition 1.5.1):
`i(D) = ℓ(D) - deg D - 1 + g`, the defect in Riemann's theorem. -/
noncomputable def Divisor.indexOfSpecialty (D : Divisor k F) : ℤ :=
  Divisor.dim D - Divisor.degree D - 1 + genus k F

/-- Unfolding formula for the index of specialty. -/
theorem Divisor.indexOfSpecialty_def (D : Divisor k F) :
    Divisor.indexOfSpecialty D = Divisor.dim D - Divisor.degree D - 1 + genus k F := (rfl)

/-- The index of specialty is unchanged by subtracting a principal divisor. -/
@[simp]
theorem Divisor.indexOfSpecialty_sub_principal (hF : IsFunctionField k F) (z : Fˣ)
    (D : Divisor k F) :
    Divisor.indexOfSpecialty (D - Divisor.principal hF z) = Divisor.indexOfSpecialty D := by
  rw [Divisor.indexOfSpecialty_def, Divisor.indexOfSpecialty_def,
    Divisor.dim_sub_principal, Divisor.degree_sub, Divisor.degree_principal, sub_zero]

/-- The index of specialty is nonnegative: this is exactly Riemann's theorem. -/
theorem Divisor.indexOfSpecialty_nonneg (hF : IsFunctionField k F) (D : Divisor k F) :
    0 ≤ Divisor.indexOfSpecialty D := by
  have := Divisor.degree_add_one_sub_genus_le_dim hF D
  rw [Divisor.indexOfSpecialty_def]
  omega

/-- The index of specialty vanishes in large degree (Stichtenoth, Definition 1.5.1, following
Theorem 1.4.17). -/
theorem exists_forall_indexOfSpecialty_eq_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) :
    ∃ c : ℤ, ∀ D : Divisor k F, c ≤ Divisor.degree D → Divisor.indexOfSpecialty D = 0 := by
  obtain ⟨c, hc⟩ := exists_forall_dim_eq_degree_add_one_sub_genus hF hex
  refine ⟨c, fun D hD ↦ ?_⟩
  have := hc D hD
  rw [Divisor.indexOfSpecialty_def]
  omega

end TauCeti
