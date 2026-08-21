/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Transfer

/-!
# The transversal word of a left transversal

Let `U` be a subgroup of a group `G` and let `t : G ⧸ U → G` be a set-theoretic section of the
projection `G → G ⧸ U`, that is, a left transversal of `U` presented as a function. The
**transversal word**
```
lWord U t u γ = (t u)⁻¹ * γ * t (γ⁻¹ • u)
```
is the element of `U` measuring the failure of left translation by `γ` to carry the chosen
representative of the coset `γ⁻¹ • u` to the chosen representative of `u`.

## Main definitions and results

* `TauCeti.lWord`: the transversal word.
* `TauCeti.lWord_mem`: it takes its values in `U`.
* `TauCeti.mul_lWord`: the defining identity `t u * lWord U t u γ = γ * t (γ⁻¹ • u)`.
* `TauCeti.lWord_mul`: the 1-cocycle law `ℓᵗ_u(γ * η) = ℓᵗ_u(γ) * ℓᵗ_{γ⁻¹ • u}(η)`, which needs no
  hypothesis on `t` at all.
* `TauCeti.lWord_changeTransversal`: replacing `t` by another section multiplies the word by the
  `U`-valued differences of the two sections, on the two sides.
* `TauCeti.transfer_eq_prod_lWord`: Mathlib's transfer homomorphism is the product of `ϕ` over the
  transversal words, which is the multiplicative form of the degree-one corestriction formula.

## Implementation notes

The transversal is a *variable* function `t` together with the hypothesis `∀ x, ↑(t x) = x`, rather
than a bundled `Subgroup.LeftTransversal`, because the intended consumers state independence of the
transversal as a theorem and so must quantify over two of them at once. Mathlib's
`Subgroup.isComplement_range_left` and `Subgroup.IsComplement.leftQuotientEquiv_apply` translate
between the two presentations, and `TauCeti.transfer_eq_prod_lWord` uses both.

Mathlib's `Subgroup.leftTransversals.diff` and `MonoidHom.transfer` are built from the same group
element without naming it; `TauCeti.transfer_eq_prod_lWord` records that agreement.

This is the transversal calculus of Layer 6 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`, where the transversal word is the input of the
corestriction cochain formulas in degrees `0`, `1` and `2`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

section Basic

variable (U : Subgroup G) (t t' : G ⧸ U → G)

/-- The **transversal word** `ℓᵗ_u(γ) = (t u)⁻¹ * γ * t (γ⁻¹ • u)` of a section
`t : G ⧸ U → G` of the projection `G → G ⧸ U`. It lies in `U` as soon as `t` really is a
section (`TauCeti.lWord_mem`). -/
@[expose] def lWord (u : G ⧸ U) (γ : G) : G := (t u)⁻¹ * γ * t (γ⁻¹ • u)

/-- The defining formula of `TauCeti.lWord`, for rewriting. -/
theorem lWord_def (u : G ⧸ U) (γ : G) : lWord U t u γ = (t u)⁻¹ * γ * t (γ⁻¹ • u) := rfl

/-- The defining identity of the transversal word: `t u * ℓᵗ_u(γ) = γ * t (γ⁻¹ • u)`. It holds for
any function `t`, and it is what turns a cocycle identity on `U` into one on `G`. -/
theorem mul_lWord (u : G ⧸ U) (γ : G) : t u * lWord U t u γ = γ * t (γ⁻¹ • u) := by
  rw [lWord_def, mul_assoc, mul_inv_cancel_left]

/-- The transversal word of the identity is trivial. -/
@[simp]
theorem lWord_one (u : G ⧸ U) : lWord U t u 1 = 1 := by
  simp [lWord_def]

/-- The **1-cocycle law** for the transversal word:
`ℓᵗ_u(γ * η) = ℓᵗ_u(γ) * ℓᵗ_{γ⁻¹ • u}(η)`. No normality, no finite index, and no condition on `t`
is needed. -/
theorem lWord_mul (u : G ⧸ U) (γ η : G) :
    lWord U t u (γ * η) = lWord U t u γ * lWord U t (γ⁻¹ • u) η := by
  simp [lWord_def, mul_smul, mul_assoc]

/-- The transversal word of `γ⁻¹` at `u` is the inverse of the word of `γ` at `γ • u`. -/
theorem lWord_inv (u : G ⧸ U) (γ : G) : lWord U t u γ⁻¹ = (lWord U t (γ • u) γ)⁻¹ := by
  have h := lWord_mul U t u γ⁻¹ γ
  rw [inv_mul_cancel, lWord_one, inv_inv] at h
  exact eq_inv_of_mul_eq_one_left h.symm

variable {U t t'}

/-- The transversal word takes its values in `U`. -/
theorem lWord_mem (ht : ∀ x : G ⧸ U, (t x : G ⧸ U) = x) (u : G ⧸ U) (γ : G) :
    lWord U t u γ ∈ U := by
  rw [lWord_def, mul_assoc, ← QuotientGroup.eq, ht, ← smul_eq_mul,
    ← MulAction.Quotient.smul_coe, ht, smul_inv_smul]

/-- The difference of two sections of `G → G ⧸ U` at a coset lies in `U`. -/
theorem inv_mul_mem_of_mk_eq (ht : ∀ x : G ⧸ U, (t x : G ⧸ U) = x)
    (ht' : ∀ x : G ⧸ U, (t' x : G ⧸ U) = x) (u : G ⧸ U) : (t u)⁻¹ * t' u ∈ U :=
  QuotientGroup.eq.mp ((ht u).trans (ht' u).symm)

variable (U t t')

/-- **Change of transversal.** The transversal word for `t'` is the word for `t` multiplied on the
two sides by the differences `(t x)⁻¹ * t' x`, which lie in `U` by
`TauCeti.inv_mul_mem_of_mk_eq`. This is the identity behind the change-of-transversal coboundaries
of corestriction. -/
theorem lWord_changeTransversal (u : G ⧸ U) (γ : G) :
    lWord U t' u γ =
      ((t u)⁻¹ * t' u)⁻¹ * lWord U t u γ * ((t (γ⁻¹ • u))⁻¹ * t' (γ⁻¹ • u)) := by
  simp [lWord_def, mul_assoc]

end Basic

section Degenerate

/-- Over the trivial subgroup every transversal word is trivial. -/
theorem lWord_bot {t : G ⧸ (⊥ : Subgroup G) → G}
    (ht : ∀ x : G ⧸ (⊥ : Subgroup G), (t x : G ⧸ (⊥ : Subgroup G)) = x)
    (u : G ⧸ (⊥ : Subgroup G)) (γ : G) : lWord ⊥ t u γ = 1 :=
  Subgroup.mem_bot.mp (lWord_mem ht u γ)

/-- Over the whole group the transversal word is conjugation by the single chosen
representative. -/
theorem lWord_top (t : G ⧸ (⊤ : Subgroup G) → G) (u : G ⧸ (⊤ : Subgroup G)) (γ : G) :
    lWord ⊤ t u γ = (t u)⁻¹ * γ * t u := by
  rw [lWord_def, @Subsingleton.elim _ QuotientGroup.subsingleton_quotient_top (γ⁻¹ • u) u]

end Degenerate

section Transfer

variable {H : Subgroup G} {A : Type*} [CommGroup A] (ϕ : H →* A)

/-- **The transfer homomorphism is the degree-one corestriction formula.** For a section
`t` of `G → G ⧸ H`, Mathlib's `MonoidHom.transfer ϕ` is the product of `ϕ` over the transversal
words `ℓᵗ_u(γ)`. Multiplicatively this is the corestriction of the 1-cocycle `ϕ` on `H` with values
in the trivial `G`-module `A`. -/
theorem transfer_eq_prod_lWord [H.FiniteIndex] [Fintype (G ⧸ H)] {t : G ⧸ H → G}
    (ht : ∀ x : G ⧸ H, (t x : G ⧸ H) = x) (γ : G) :
    MonoidHom.transfer ϕ γ = ∏ u : G ⧸ H, ϕ ⟨lWord H t u γ, lWord_mem ht u γ⟩ := by
  set S : H.LeftTransversal := ⟨Set.range t, Subgroup.isComplement_range_left ht⟩
  have hSt : ∀ q : G ⧸ H, (S.2.leftQuotientEquiv q : G) = t q := fun q =>
    Subgroup.IsComplement.leftQuotientEquiv_apply ht q
  rw [MonoidHom.transfer_def ϕ S, Subgroup.leftTransversals.diff]
  refine Finset.prod_congr (congrArg _ (Subsingleton.elim _ _)) fun u _ => ?_
  have key : ((S.2.leftQuotientEquiv u : G))⁻¹ * (((γ • S).2.leftQuotientEquiv u : G))
      = lWord H t u γ := by
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, hSt, hSt, lWord_def, smul_eq_mul, mul_assoc]
  exact congrArg ϕ (Subtype.ext key)

end Transfer

end TauCeti
