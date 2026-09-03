/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Agent
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Finite
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Closeness of the two finite homomorphism densities

For a pattern graph `F` on `k` vertices and a host graph `G` on `n` vertices, the
all-homomorphism density `t(F, G)` and the injective density `t₀(F, G)` satisfy

`|homDensityFin F G - injHomDensity F G| ≤ (k.choose 2 : ℝ) / n`.

The two densities count the same homomorphism events and differ only in how a vertex map
`V(F) → V(G)` is drawn: with replacement (`homDensityFin`, denominator `n ^ k`) or without
(`injHomDensity`, denominator `(n)_k`). Their gap is therefore bounded by the share of
non-injective maps among all maps. A non-injective map repeats some value, so at most
`C(k,2) · n ^ (k - 1)` of the `n ^ k` maps are non-injective, and dividing by `n ^ k` gives the
bound. The same estimate is what pins the falling-factorial denominator of `injHomDensity`: it
is the normalization that makes the injective density the unbiased estimator of the graphon
homomorphism density under random sampling.

## Main results

* `abs_homDensityFin_sub_injHomDensity_le` — the closeness bound above, for an arbitrary
  finite host graph; the bound depends only on the cardinality of the host.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`, Layer 9a — the finite
  hom-versus-injective closeness bound. The statement here is adapted from that declaration,
  generalized from a `SimpleGraph (Fin m)` host to an arbitrary finite host.
* L. Lovász, *Large Networks and Graph Limits*, §5.2.
-/

public section

namespace TauCeti

namespace DenseGraphLimits

variable {V W : Type*} [Fintype V] [Fintype W]

/-! ### The falling-factorial shortfall -/

/-- The falling product never exceeds the power: this is `Nat.descFactorial_le_pow` cast to
`ℝ`. -/
private theorem falling_prod_le_pow (n k : ℕ) :
    ∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ)) ≤ (n : ℝ) ^ k := by
  by_cases hk : k ≤ n
  · have hprod : (n.descFactorial k : ℝ)
        = ∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ)) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro i hi
      have hin : i ≤ n :=
        le_trans (le_of_lt (Finset.mem_range.mp hi)) hk
      exact Nat.cast_sub hin
    rw [← hprod]
    exact_mod_cast Nat.descFactorial_le_pow n k
  · push Not at hk
    have hmem : n ∈ Finset.range k := Finset.mem_range.mpr hk
    have hzero : ∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ)) = 0 :=
      Finset.prod_eq_zero hmem (sub_self _)
    rw [hzero]
    positivity

/-- The shortfall of the falling product against the power is at most `C(k,2) * n ^ (k-1)`:
peeling off the last factor contributes `k * P_k`, and the induction hypothesis handles the
rest. -/
private theorem pow_sub_falling_prod_le (n k : ℕ) :
    (n : ℝ) ^ k - ∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ))
      ≤ ((k.choose 2 : ℕ) : ℝ) * (n : ℝ) ^ (k - 1) := by
  induction k with
  | zero =>
    have hc0 : Nat.choose 0 2 = 0 := by decide
    simp [hc0]
  | succ k ih =>
    have hP := falling_prod_le_pow n k
    have hchooseR : (((k + 1).choose 2 : ℕ) : ℝ)
        = ((k.choose 2 : ℕ) : ℝ) + (k : ℝ) := by
      have h := Nat.choose_succ_succ' k 1
      rw [Nat.choose_one_right] at h
      have h2 : (k + 1).choose 2 = k.choose 2 + k := h.trans (add_comm _ _)
      rw [h2]
      push_cast
      ring
    rw [Finset.prod_range_succ]
    by_cases hk0 : k = 0
    · subst hk0
      have hc0 : (0 + 1).choose 2 = 0 :=
        Nat.choose_eq_zero_of_lt (by decide)
      rw [hc0]
      simp
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hpow : (n : ℝ) ^ (k - 1) * (n : ℝ) = (n : ℝ) ^ k := by
        have hps := pow_succ (n : ℝ) (k - 1)
        rw [Nat.sub_add_cancel hk1] at hps
        exact hps.symm
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have hkk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      calc (n : ℝ) ^ (k + 1)
            - (∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ))) * ((n : ℝ) - (k : ℝ))
          = (n : ℝ) * ((n : ℝ) ^ k - ∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ)))
            + (k : ℝ) * (∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ))) := by ring
        _ ≤ (n : ℝ) * (((k.choose 2 : ℕ) : ℝ) * (n : ℝ) ^ (k - 1))
            + (k : ℝ) * (n : ℝ) ^ k := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left ih hnn
              · exact mul_le_mul_of_nonneg_left hP hkk
        _ = (((k + 1).choose 2 : ℕ) : ℝ) * (n : ℝ) ^ (k + 1 - 1) := by
              rw [hchooseR, Nat.add_sub_cancel, ← hpow]
              ring

/-- The shortfall of the falling factorial against the power. For `k ≤ n` this is the product
bound above; for `n < k` the falling factorial vanishes and the power is absorbed by
`n ≤ C(k,2)`. -/
private theorem pow_sub_descFactorial_le (n k : ℕ) :
    (n : ℝ) ^ k - (n.descFactorial k : ℝ)
      ≤ ((k.choose 2 : ℕ) : ℝ) * (n : ℝ) ^ (k - 1) := by
  by_cases hk : k ≤ n
  · have hprod : (n.descFactorial k : ℝ)
        = ∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ)) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro i hi
      have hin : i ≤ n :=
        le_trans (le_of_lt (Finset.mem_range.mp hi)) hk
      exact Nat.cast_sub hin
    rw [hprod]
    exact pow_sub_falling_prod_le n k
  · push Not at hk
    have hz : n.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hk
    rw [hz, Nat.cast_zero, sub_zero]
    by_cases hn0 : n = 0
    · subst hn0
      have hkpos : k ≠ 0 := ne_of_gt hk
      simp only [Nat.cast_zero, zero_pow hkpos]
      positivity
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hk1 : 1 ≤ k := le_trans hn1 (le_of_lt hk)
      have hkle : n ≤ k.choose 2 := by
        rw [Nat.choose_two_right]
        have h1 : n + 1 ≤ k := hk
        have h2 : n ≤ k - 1 := by omega
        have hk2 : 2 ≤ k := by omega
        have h5 : 2 * n ≤ k * (k - 1) :=
          le_trans (Nat.mul_le_mul hk2 (le_refl n)) (Nat.mul_le_mul (le_refl k) h2)
        omega
      have hexp : (n : ℝ) ^ k = (n : ℝ) ^ (k - 1) * (n : ℝ) := by
        have hps := pow_succ (n : ℝ) (k - 1)
        rw [Nat.sub_add_cancel hk1] at hps
        exact hps
      calc (n : ℝ) ^ k = (n : ℝ) ^ (k - 1) * (n : ℝ) := hexp
        _ ≤ (n : ℝ) ^ (k - 1) * ((k.choose 2 : ℕ) : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
              exact_mod_cast hkle
        _ = ((k.choose 2 : ℕ) : ℝ) * (n : ℝ) ^ (k - 1) := by ring

/-! ### Non-injective maps are rare -/

/-- Non-injective homomorphisms are outnumbered by non-injective maps: removing the injective
ones from both sides preserves the inequality. -/
private theorem card_hom_sub_card_inj_le (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card (F →g G) - Nat.card {φ : F →g G // Function.Injective ⇑φ}
      ≤ Fintype.card W ^ Fintype.card V
        - (Fintype.card W).descFactorial (Fintype.card V) := by
  classical
  set A : Finset (V → W) :=
    Finset.univ.filter (fun f => ∀ a b, F.Adj a b → G.Adj (f a) (f b)) with hA
  set B : Finset (V → W) := A.filter (fun f => Function.Injective f) with hB
  set I : Finset (V → W) := Finset.univ.filter (fun f => Function.Injective f) with hI
  have hBA : B ⊆ A := by
    intro x hx
    rw [hB] at hx
    exact (Finset.mem_filter.mp hx).1
  have hmaps : Nat.card (V → W) = Fintype.card W ^ Fintype.card V := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hemb : Nat.card (V ↪ W)
      = (Fintype.card W).descFactorial (Fintype.card V) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  have hcardA : A.card = Nat.card (F →g G) := by
    rw [card_hom_eq_card_adjPreservingMaps F G, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  have hcardB : B.card = Nat.card {φ : F →g G // Function.Injective ⇑φ} := by
    have e : {ψ : V → W // (∀ a b, F.Adj a b → G.Adj (ψ a) (ψ b)) ∧ Function.Injective ψ}
        ≃ {φ : F →g G // Function.Injective ⇑φ} :=
      { toFun := fun ψ => ⟨⟨ψ.1, fun {a b} h => ψ.2.1 a b h⟩, ψ.2.2⟩,
        invFun := fun φ => ⟨⇑φ.1, (fun a b h => φ.1.map_rel h), φ.2⟩,
        left_inv := fun _ => rfl,
        right_inv := fun _ => rfl }
    have hB' : B.card = Nat.card {ψ : V → W //
        (∀ a b, F.Adj a b → G.Adj (ψ a) (ψ b)) ∧ Function.Injective ψ} := by
      rw [hB, hA, Finset.filter_filter, ← Fintype.card_subtype,
        ← Nat.card_eq_fintype_card]
    rw [hB', Nat.card_congr e]
  have hcardI : I.card
      = (Fintype.card W).descFactorial (Fintype.card V) := by
    have e : {f : V → W // Function.Injective f} ≃ (V ↪ W) :=
      { toFun := fun f => ⟨f.1, f.2⟩,
        invFun := fun e => ⟨e.1, e.2⟩,
        left_inv := fun _ => rfl,
        right_inv := fun _ => rfl }
    have h1 : I.card = Nat.card {f : V → W // Function.Injective f} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h1, Nat.card_congr e, hemb]
  have hcardU : (Finset.univ : Finset (V → W)).card
      = Fintype.card W ^ Fintype.card V := by
    have h1 : (Finset.univ : Finset (V → W)).card = Nat.card (V → W) := by
      rw [Nat.card_eq_fintype_card, Finset.card_univ]
    rw [h1, hmaps]
  have hsub : A \ B ⊆ Finset.univ \ I := by
    grind
  have hle := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hBA, Finset.card_sdiff_of_subset (Finset.subset_univ I)] at hle
  rw [hcardA, hcardB, hcardU, hcardI] at hle
  exact hle

/-! ### From counts to densities -/

/-- Two fractions with different denominators are close when their numerators differ by at most
the denominators' gap: `|a / N - b / M| ≤ (N - M) / N`. -/
private theorem abs_div_sub_div_le (a b N M : ℝ) (hN : 0 < N)
    (ha : 0 ≤ a) (haN : a ≤ N) (hb : 0 ≤ b) (hbM : b ≤ M) (hM : 0 ≤ M)
    (hMN : M ≤ N) (hba : b ≤ a) (hab : a - b ≤ N - M) :
    |a / N - b / M| ≤ (N - M) / N := by
  by_cases hM0 : M = 0
  · subst hM0
    have hb0 : b = 0 := le_antisymm hbM hb
    simp only [hb0, zero_div, sub_zero, div_self (ne_of_gt hN),
      abs_of_nonneg (div_nonneg ha (le_of_lt hN))]
    exact div_le_one_of_le₀ haN (le_of_lt hN)
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    have hNM : 0 < N * M := mul_pos hN hMpos
    have hN' : N ≠ 0 := ne_of_gt hN
    have hM' : M ≠ 0 := ne_of_gt hMpos
    have h1 : (a - b) * M ≤ (N - M) * M := mul_le_mul_of_nonneg_right hab hM
    have h2 : 0 ≤ b * (N - M) := mul_nonneg hb (sub_nonneg.mpr hMN)
    have h3 : b * (N - M) ≤ M * (N - M) :=
      mul_le_mul_of_nonneg_right hbM (sub_nonneg.mpr hMN)
    have h4 : (b - a) * M ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hba) hM
    have hub : a * M - b * N ≤ M * (N - M) := by linarith [h1, h2]
    have hlb : -(M * (N - M)) ≤ a * M - b * N := by linarith [h3, h4]
    have habs : |a * M - b * N| ≤ M * (N - M) := abs_le.mpr ⟨hlb, hub⟩
    have hNM' : N * M ≠ 0 := mul_ne_zero hN' hM'
    have e1 : a / N = (a * M) / (N * M) := by
      rw [div_eq_div_iff hN' hNM']
      ring
    have e2 : b / M = (b * N) / (N * M) := by
      rw [div_eq_div_iff hM' hNM']
      ring
    have hdiv : a / N - b / M = (a * M - b * N) / (N * M) := by
      rw [e1, e2, ← sub_div]
    rw [hdiv, abs_div, abs_of_pos hNM]
    calc |a * M - b * N| / (N * M) ≤ M * (N - M) / (N * M) :=
            div_le_div_of_nonneg_right habs (le_of_lt hNM)
      _ = (N - M) / N := by
            rw [div_eq_div_iff (mul_ne_zero hN' hM') hN']
            ring

/-- The homomorphism density and the injective homomorphism density differ by at most
`C(k,2) / n`, where `k` is the number of vertices of the pattern and `n` the number of
vertices of the host. -/
theorem abs_homDensityFin_sub_injHomDensity_le (F : SimpleGraph V) (G : SimpleGraph W) :
    |homDensityFin F G - injHomDensity F G|
      ≤ ((Fintype.card V).choose 2 : ℝ) / (Fintype.card W : ℝ) := by
  classical
  by_cases hW0 : Fintype.card W = 0
  · -- Empty host: both densities coincide, so the left side vanishes.
    have hRHS : (0 : ℝ)
        ≤ ((Fintype.card V).choose 2 : ℝ) / (Fintype.card W : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    suffices heq : homDensityFin F G = injHomDensity F G by
      rw [heq, sub_self, abs_zero]
      exact hRHS
    rw [homDensityFin_def, injHomDensity_def]
    by_cases hk0 : Fintype.card V = 0
    · -- Empty pattern: every homomorphism is vacuously injective.
      have hV : IsEmpty V := Fintype.card_eq_zero_iff.mp hk0
      have hsub : ∀ φ : F →g G, Function.Injective (⇑φ : V → W) := by
        intro φ a b _
        exact False.elim (hV.false a)
      have e : (F →g G) ≃ {φ : F →g G // Function.Injective ⇑φ} :=
        { toFun := fun φ => ⟨φ, hsub φ⟩
          invFun := Subtype.val
          left_inv := fun _ => rfl
          right_inv := fun ⟨_, _⟩ => rfl }
      have hcards : Nat.card (F →g G)
          = Nat.card {φ : F →g G // Function.Injective ⇑φ} :=
        Nat.card_congr e
      rw [hcards, hk0, pow_zero, Nat.descFactorial_zero, Nat.cast_one]
    · -- Nonempty pattern over an empty host: there are no maps at all.
      have hmaps0 : Nat.card (V → W) = 0 := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hW0]
        exact zero_pow hk0
      have hhom0 : Nat.card (F →g G) = 0 := by
        apply Nat.eq_zero_of_le_zero
        calc Nat.card (F →g G) ≤ Nat.card (V → W) :=
              Nat.card_le_card_of_injective (fun φ : F →g G => (φ : V → W))
                (fun a b h => by ext x; exact congrFun h x)
          _ = 0 := hmaps0
      have hemb0 : Nat.card (V ↪ W) = 0 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, hW0]
        exact Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      have hinj0 : Nat.card {φ : F →g G // Function.Injective ⇑φ} = 0 := by
        apply Nat.eq_zero_of_le_zero
        calc Nat.card {φ : F →g G // Function.Injective ⇑φ} ≤ Nat.card (V ↪ W) :=
              Nat.card_le_card_of_injective
                (fun φ : {φ : F →g G // Function.Injective ⇑φ} =>
                  (⟨(φ.1 : V → W), φ.2⟩ : V ↪ W))
                (fun a b h => by
                  ext x
                  exact congrFun (congrArg (fun e : V ↪ W => (e : V → W)) h) x)
          _ = 0 := hemb0
      rw [hhom0, hinj0, Nat.cast_zero, zero_div, zero_div]
  · have hn : 0 < Fintype.card W := Nat.pos_of_ne_zero hW0
    rw [homDensityFin_def, injHomDensity_def]
    set k := Fintype.card V with hk
    set n := Fintype.card W with hn'
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hN : (0 : ℝ) < (n : ℝ) ^ k := pow_pos hnR k
    have hmaps : Nat.card (V → W) = n ^ k := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have hemb : Nat.card (V ↪ W) = n.descFactorial k := by
      rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
    have haN : (Nat.card (F →g G) : ℝ) ≤ (n : ℝ) ^ k := by
      have h : Nat.card (F →g G) ≤ Nat.card (V → W) :=
        Nat.card_le_card_of_injective (fun φ : F →g G => (φ : V → W))
          (fun a b h => by ext x; exact congrFun h x)
      rw [hmaps] at h
      exact_mod_cast h
    have hbM : (Nat.card {φ : F →g G // Function.Injective ⇑φ} : ℝ)
        ≤ ((n.descFactorial k : ℕ) : ℝ) := by
      have h : Nat.card {φ : F →g G // Function.Injective ⇑φ} ≤ Nat.card (V ↪ W) :=
        Nat.card_le_card_of_injective
          (fun φ : {φ : F →g G // Function.Injective ⇑φ} =>
            (⟨(φ.1 : V → W), φ.2⟩ : V ↪ W))
          (fun a b h => by
            ext x
            exact congrFun (congrArg (fun e : V ↪ W => (e : V → W)) h) x)
      rw [hemb] at h
      exact_mod_cast h
    have hba_nat : Nat.card {φ : F →g G // Function.Injective ⇑φ}
        ≤ Nat.card (F →g G) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    have hMNnat : n.descFactorial k ≤ n ^ k := Nat.descFactorial_le_pow n k
    have hba : (Nat.card {φ : F →g G // Function.Injective ⇑φ} : ℝ)
        ≤ (Nat.card (F →g G) : ℝ) := by
      exact_mod_cast hba_nat
    have hMN : ((n.descFactorial k : ℕ) : ℝ) ≤ (n : ℝ) ^ k := by
      exact_mod_cast hMNnat
    have hab : (Nat.card (F →g G) : ℝ) - (Nat.card {φ : F →g G // Function.Injective ⇑φ} : ℝ)
        ≤ (n : ℝ) ^ k - ((n.descFactorial k : ℕ) : ℝ) := by
      have h := card_hom_sub_card_inj_le F G
      have hR : ((Nat.card (F →g G) - Nat.card {φ : F →g G // Function.Injective ⇑φ} : ℕ) : ℝ)
          ≤ ((Fintype.card W ^ Fintype.card V
            - (Fintype.card W).descFactorial (Fintype.card V) : ℕ) : ℝ) := by
        exact_mod_cast h
      rw [Nat.cast_sub hba_nat, Nat.cast_sub hMNnat] at hR
      push_cast at hR
      exact hR
    have hstep := abs_div_sub_div_le _ _ _ _ hN (Nat.cast_nonneg _) haN (Nat.cast_nonneg _)
      hbM (Nat.cast_nonneg _) hMN hba hab
    have hC := pow_sub_descFactorial_le n k
    have hdiv1 : ((n : ℝ) ^ k - ((n.descFactorial k : ℕ) : ℝ)) / (n : ℝ) ^ k
        ≤ (((k.choose 2 : ℕ) : ℝ) * (n : ℝ) ^ (k - 1)) / (n : ℝ) ^ k :=
      div_le_div_of_nonneg_right hC (le_of_lt hN)
    have hdiv2 : ((((k.choose 2 : ℕ) : ℝ) * (n : ℝ) ^ (k - 1))) / (n : ℝ) ^ k
        ≤ ((k.choose 2 : ℕ) : ℝ) / (n : ℝ) := by
      by_cases hk0 : k = 0
      · have hc0 : Nat.choose 0 2 = 0 := by decide
        simp only [hk0, hc0, Nat.cast_zero, zero_mul, zero_div, le_refl]
      · have hk1 : 1 ≤ k := by omega
        have hpow : (n : ℝ) ^ (k - 1) * (n : ℝ) = (n : ℝ) ^ k := by
          have hps := pow_succ (n : ℝ) (k - 1)
          rw [Nat.sub_add_cancel hk1] at hps
          exact hps.symm
        have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
        have hP : (n : ℝ) ^ (k - 1) ≠ 0 := pow_ne_zero _ hn0
        have key : (((k.choose 2 : ℕ) : ℝ) * (n : ℝ) ^ (k - 1))
              / ((n : ℝ) ^ (k - 1) * (n : ℝ))
            = ((k.choose 2 : ℕ) : ℝ) / (n : ℝ) := by
          rw [div_eq_div_iff (mul_ne_zero hP hn0) hn0]
          ring
        rw [← hpow, key]
    exact le_trans hstep (le_trans hdiv1 hdiv2)

end DenseGraphLimits

end TauCeti
