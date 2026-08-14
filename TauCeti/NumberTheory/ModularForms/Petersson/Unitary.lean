/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.DiamondOperators
public import TauCeti.NumberTheory.ModularForms.Petersson.Orthogonal

/-!
# The Petersson product is unitary under a normalising slash

The Petersson product `CuspForm.peterssonInnerCosets` on `S_k(Γ)` is a sum over the cosets of
`Γ·{±I}` in `SL₂(ℤ)` of level-one-domain pairings of slashed forms. Slashing both arguments by
an `α ∈ SL₂(ℤ)` that *normalises* `Γ·{±I}` permutes those cosets — right multiplication by `α⁻¹`
is a well-defined permutation of `SL₂(ℤ)/Γ·{±I}` exactly because `α` normalises the group — so it
leaves the whole sum unchanged: such a slash is **unitary** for the Petersson product.

The case this roadmap needs is `Γ = Γ₁(N)` and `α ∈ Γ₀(N)`, that is, the **diamond operators**
`⟨d⟩` of `TauCeti/NumberTheory/ModularForms/DiamondOperators.lean`: `⟪⟨d⟩f, ⟨d⟩g⟫ = ⟪f, g⟫`.
Two consequences carry Layer 3 of the ModularForms roadmap forward. First, the
Petersson-orthogonal complement of a diamond-stable subspace is again diamond-stable — the
diamonds form a *group* of unitaries, so a stable subspace is mapped *onto* itself, which is
what an orthogonal complement needs. Second, cusp forms with distinct nebentypus characters are
Petersson-orthogonal, since the diamond eigenvalues `χ(d)` are roots of unity: unitarity turns
`⟪f, g⟫` into `conj (χ d) * ψ d * ⟪f, g⟫`, and the scalar differs from `1` at some `d`.

## Main results

* `TauCeti.CuspForm.peterssonInnerCosets_slash`: the Petersson product is unchanged by slashing
  both arguments with an element of the normaliser of `Γ·{±I}`.
* `TauCeti.CuspForm.peterssonInnerCosets_diamondOpCusp`: the diamond operators are
  Petersson-unitary.
* `TauCeti.CuspForm.diamondOpCusp_mem_peterssonOrthogonal`: the Petersson-orthogonal complement
  of a diamond-stable subspace is diamond-stable.
* `TauCeti.CuspForm.peterssonInnerCosets_eq_zero_of_mem_cuspFormCharSpace_of_ne` and its
  submodule form
  `TauCeti.CuspForm.cuspFormCharSpace_le_peterssonOrthogonal_of_ne`: cusp forms with distinct
  nebentypus characters are Petersson-orthogonal, so the nebentypus decomposition of
  `S_k(Γ₁(N))` is an orthogonal one.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Section 5.5.
* Miyake, *Modular forms*, Section 4.5.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup

open scoped MatrixGroups ModularForm ComplexConjugate

namespace TauCeti

open _root_.CuspForm

namespace CuspForm

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

/-! ### Slashing by a normalising element -/

/-- Right multiplication by an element normalising `Γ·{±I}`, as a permutation of the coset space
`SL₂(ℤ)/Γ·{±I}`. Right multiplication is well defined on left cosets precisely because
`α (Γ·{±I}) α⁻¹ = Γ·{±I}`; this permutation is the reindexing behind
`peterssonInnerCosets_slash`. -/
private def cosetRightMul {α : SL(2, ℤ)}
    (hα : α ∈ Subgroup.normalizer (Γ.withCenter : Set SL(2, ℤ))) :
    SL(2, ℤ) ⧸ Γ.withCenter ≃ SL(2, ℤ) ⧸ Γ.withCenter where
  toFun := Quotient.map' (· * α⁻¹) fun a b hab ↦ by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have h := (Subgroup.mem_normalizer_iff.mp hα (a⁻¹ * b)).mp hab
    have hconj : (a * α⁻¹)⁻¹ * (b * α⁻¹) = α * (a⁻¹ * b) * α⁻¹ := by group
    simpa only [hconj] using h
  invFun := Quotient.map' (· * α) fun a b hab ↦ by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have h := (Subgroup.mem_normalizer_iff''.mp hα (a⁻¹ * b)).mp hab
    have hconj : (a * α)⁻¹ * (b * α) = α⁻¹ * (a⁻¹ * b) * α := by group
    simpa only [hconj] using h
  left_inv q := by
    induction q using QuotientGroup.induction_on
    simp only [Quotient.map'_mk'', inv_mul_cancel_right]
  right_inv q := by
    induction q using QuotientGroup.induction_on
    simp only [Quotient.map'_mk'', mul_inv_cancel_right]

omit [Γ.FiniteIndex] in
private lemma cosetRightMul_apply {α : SL(2, ℤ)}
    (hα : α ∈ Subgroup.normalizer (Γ.withCenter : Set SL(2, ℤ)))
    (q : SL(2, ℤ) ⧸ Γ.withCenter) :
    cosetRightMul hα q = (QuotientGroup.mk (q.out * α⁻¹) : SL(2, ℤ) ⧸ Γ.withCenter) := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

omit [Γ.FiniteIndex] in
/-- Slashing by an element of `Γ·{±I}` is invisible to the level-one-domain pairing, even after
a further slash: the two forms pick up the same unimodular constant, and the pairing is
conjugate-linear in one argument and linear in the other. -/
private theorem peterssonInner_slash_slash_of_mem_withCenter (f g : CuspForm (Γ.map (mapGL ℝ)) k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ.withCenter) (β : SL(2, ℤ)) :
    UpperHalfPlane.peterssonInner k fd ((⇑f ∣[k] γ) ∣[k] β) ((⇑g ∣[k] γ) ∣[k] β) =
      UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] β) (⇑g ∣[k] β) := by
  obtain ⟨c, hc, hslash⟩ := exists_slash_eq_smul_of_mem_withCenter (k := k) hγ
  rw [hslash f, hslash g, ModularForm.SL_smul_slash, ModularForm.SL_smul_slash,
    peterssonInner_smul_left, peterssonInner_smul_right, ← mul_assoc, hc, one_mul]

omit [Γ.FiniteIndex] in
/-- **The summand of the Petersson product is a function of the coset.** Replacing the chosen
representative `q.out` of a coset by any other element of it does not change the level-one-domain
pairing of the correspondingly slashed forms. -/
private theorem peterssonInner_slash_inv_out (f g : CuspForm (Γ.map (mapGL ℝ)) k) (δ : SL(2, ℤ)) :
    UpperHalfPlane.peterssonInner k fd
        (⇑f ∣[k] ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ.withCenter).out)⁻¹)
        (⇑g ∣[k] ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ.withCenter).out)⁻¹) =
      UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] δ⁻¹) (⇑g ∣[k] δ⁻¹) := by
  have hmem : ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ.withCenter).out)⁻¹ * δ ∈ Γ.withCenter :=
    QuotientGroup.eq.mp (Quotient.out_eq _)
  have h := peterssonInner_slash_slash_of_mem_withCenter f g hmem δ⁻¹
  have hcancel : ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ.withCenter).out)⁻¹ * δ * δ⁻¹ =
      ((QuotientGroup.mk δ : SL(2, ℤ) ⧸ Γ.withCenter).out)⁻¹ := by group
  rwa [← SlashAction.slash_mul, ← SlashAction.slash_mul, hcancel] at h

/-- **The Petersson product is unitary under a normalising slash.** If `α ∈ SL₂(ℤ)` normalises
`Γ·{±I}` and the slashes `f ∣[k] α`, `g ∣[k] α` are again cusp forms `F`, `G` for `Γ`, then
`⟪F, G⟫ = ⟪f, g⟫`: right multiplication by `α⁻¹` permutes the cosets of `Γ·{±I}` indexing the
defining sum, and the summands match up term by term.

It is `Γ·{±I}`, not `Γ`, that the hypothesis constrains, that being the group whose cosets the
sum runs over; an `α` normalising `Γ` normalises `Γ·{±I}` too, by
`Subgroup.normalizer_le_normalizer_sup_normal`.

The forms `F` and `G` are taken as data with their defining equations, rather than built here,
because the operators that arise this way — the diamond operators of Layer 0, the Atkin–Lehner
involutions later — each package the slashed function as a cusp form in their own way. -/
theorem peterssonInnerCosets_slash {α : SL(2, ℤ)}
    (hα : α ∈ Subgroup.normalizer (Γ.withCenter : Set SL(2, ℤ)))
    {f g F G : CuspForm (Γ.map (mapGL ℝ)) k} (hF : ⇑F = ⇑f ∣[k] α) (hG : ⇑G = ⇑g ∣[k] α) :
    peterssonInnerCosets F G = peterssonInnerCosets f g := by
  have hsummand : ∀ q : SL(2, ℤ) ⧸ Γ.withCenter,
      UpperHalfPlane.peterssonInner k fd (⇑F ∣[k] (q.out)⁻¹) (⇑G ∣[k] (q.out)⁻¹) =
        UpperHalfPlane.peterssonInner k fd (⇑f ∣[k] ((cosetRightMul hα q).out)⁻¹)
          (⇑g ∣[k] ((cosetRightMul hα q).out)⁻¹) := fun q ↦ by
    have hinv : (q.out * α⁻¹)⁻¹ = α * (q.out)⁻¹ := by group
    rw [cosetRightMul_apply hα q, peterssonInner_slash_inv_out f g (q.out * α⁻¹), hF, hG,
      ← SlashAction.slash_mul, ← SlashAction.slash_mul, hinv]
  rw [peterssonInnerCosets_def, peterssonInnerCosets_def, Finset.sum_congr rfl fun q _ ↦ hsummand q]
  exact Fintype.sum_equiv (cosetRightMul hα) _ _ fun _ ↦ rfl

/-! ### The diamond operators are unitary -/

variable {N : ℕ} [NeZero N]

/-- **The diamond operators are Petersson-unitary**: `⟪⟨d⟩f, ⟨d⟩g⟫ = ⟪f, g⟫`. The operator
`⟨d⟩` is slashing by a representative of `d` in `Γ₀(N)`, and `Γ₀(N)` normalises `Γ₁(N)`, hence
also `Γ₁(N)·{±I}`. -/
@[simp]
theorem peterssonInnerCosets_diamondOpCusp (k : ℤ) (d : (ZMod N)ˣ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInnerCosets (diamondOpCusp k d f) (diamondOpCusp k d g) =
      peterssonInnerCosets f g := by
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  have hnorm : (γ : SL(2, ℤ)) ∈ Subgroup.normalizer ((Gamma1 N).withCenter : Set SL(2, ℤ)) := by
    rw [Subgroup.withCenter_def]
    exact Subgroup.normalizer_le_normalizer_sup_normal (Gamma0_le_normalizer_Gamma1 N γ.2)
  exact peterssonInnerCosets_slash hnorm
    (coe_diamondOpCusp k d γ hγ f) (coe_diamondOpCusp k d γ hγ g)

/-- **The Petersson-orthogonal complement of a diamond-stable subspace is diamond-stable.**
Unitarity alone would not suffice: what is used is that the diamonds form a *group*, so a stable
subspace `V` is carried *onto* itself by `⟨d⟩`, and every `g ∈ V` is `⟨d⟩` of the element
`⟨d⁻¹⟩ g` of `V`. -/
theorem diamondOpCusp_mem_peterssonOrthogonal {k : ℤ}
    {V : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (hV : ∀ u : (ZMod N)ˣ, ∀ f ∈ V, diamondOpCusp k u f ∈ V) (d : (ZMod N)ˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ peterssonOrthogonal V) :
    diamondOpCusp k d f ∈ peterssonOrthogonal V := by
  refine mem_peterssonOrthogonal_iff.mpr fun g hg ↦ ?_
  have hgd : diamondOpCusp k d (diamondOpCusp k d⁻¹ g) = g := by
    rw [← LinearMap.comp_apply, ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one,
      LinearMap.id_apply]
  rw [← hgd, peterssonInnerCosets_diamondOpCusp k d (diamondOpCusp k d⁻¹ g) f]
  exact mem_peterssonOrthogonal_iff.mp hf _ (hV d⁻¹ g hg)

/-! ### Distinct nebentypus characters are orthogonal -/

/-- A character of the finite group `(ZMod N)ˣ` takes unimodular values. -/
private lemma conj_mul_char_eq_one (χ : (ZMod N)ˣ →* ℂˣ) (d : (ZMod N)ˣ) :
    conj (χ d : ℂ) * (χ d : ℂ) = 1 := by
  have hpow : ((χ d : ℂ)) ^ Nat.card (ZMod N)ˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have hnorm : ‖(χ d : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow Nat.card_pos.ne'
  rw [RCLike.conj_mul, hnorm]
  norm_num

/-- **Cusp forms with distinct nebentypus characters are Petersson-orthogonal.** The diamond
operators are unitary and act on the two forms by the scalars `χ(d)` and `ψ(d)`, so the pairing
is multiplied by `conj (χ d) * ψ d`; at a `d` where the characters differ this scalar is not `1`,
the values being unimodular. Hence the nebentypus decomposition of `S_k(Γ₁(N))` is an orthogonal
decomposition. -/
theorem peterssonInnerCosets_eq_zero_of_mem_cuspFormCharSpace_of_ne {k : ℤ}
    {χ ψ : (ZMod N)ˣ →* ℂˣ} (hne : χ ≠ ψ)
    {f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hg : g ∈ cuspFormCharSpace k ψ) : peterssonInnerCosets f g = 0 := by
  obtain ⟨d, hd⟩ : ∃ d, χ d ≠ ψ d := by
    by_contra hcon
    exact hne (MonoidHom.ext fun d ↦ not_not.mp fun h ↦ hcon ⟨d, h⟩)
  have hscal : conj (χ d : ℂ) * (ψ d : ℂ) ≠ 1 := fun h ↦ hd <| Units.ext <| by
    have h2 : (χ d : ℂ) * (conj (χ d : ℂ) * (ψ d : ℂ)) = (χ d : ℂ) * 1 := by rw [h]
    rwa [← mul_assoc, mul_comm (χ d : ℂ) (conj (χ d : ℂ)), conj_mul_char_eq_one, one_mul,
      mul_one, eq_comm] at h2
  have key : peterssonInnerCosets f g =
      conj (χ d : ℂ) * (ψ d : ℂ) * peterssonInnerCosets f g := by
    conv_lhs => rw [← peterssonInnerCosets_diamondOpCusp k d f g]
    rw [diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ d hf,
      diamondOpCusp_apply_of_mem_cuspFormCharSpace k ψ d hg,
      peterssonInnerCosets_smul_left, peterssonInnerCosets_smul_right, ← mul_assoc]
  have hfactor : (1 - conj (χ d : ℂ) * (ψ d : ℂ)) * peterssonInnerCosets f g = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp hfactor with h | h
  · exact absurd (sub_eq_zero.mp h).symm hscal
  · exact h

/-- **The nebentypus decomposition of `S_k(Γ₁(N))` is orthogonal**: distinct nebentypus spaces
are Petersson-orthogonal, the submodule form of
`peterssonInnerCosets_eq_zero_of_mem_cuspFormCharSpace_of_ne`. -/
theorem cuspFormCharSpace_le_peterssonOrthogonal_of_ne {k : ℤ} {χ ψ : (ZMod N)ˣ →* ℂˣ}
    (hne : χ ≠ ψ) :
    cuspFormCharSpace k ψ ≤ peterssonOrthogonal (cuspFormCharSpace (N := N) k χ) := fun _ hg ↦
  mem_peterssonOrthogonal_iff.mpr fun _ hf ↦
    peterssonInnerCosets_eq_zero_of_mem_cuspFormCharSpace_of_ne hne hf hg

end CuspForm

end TauCeti
