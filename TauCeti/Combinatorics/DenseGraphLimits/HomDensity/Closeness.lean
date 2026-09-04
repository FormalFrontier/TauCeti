/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Agent
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Finite
public import TauCeti.Data.Nat.Factorial.Bounds
public import TauCeti.Algebra.Order.Field.Bounds
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Choose.Basic
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

* `homDensityFin_sub_injHomDensity_le` — the closeness bound above, for an arbitrary
  finite host graph; the bound depends only on the cardinality of the host.

## References

* L. Lovász, *Large Networks and Graph Limits*, §5.2.
-/

public section

namespace TauCeti

namespace DenseGraphLimits

variable {V W : Type*} [Fintype V] [Fintype W]

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


/-- The homomorphism density and the injective homomorphism density differ by at most
`C(k,2) / n`, where `k` is the number of vertices of the pattern and `n` the number of
vertices of the host. -/
theorem homDensityFin_sub_injHomDensity_le (F : SimpleGraph V) (G : SimpleGraph W) :
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
      have hhom0 : Nat.card (F →g G) = 0 := by
        apply Nat.eq_zero_of_le_zero
        calc Nat.card (F →g G) ≤ Fintype.card W ^ Fintype.card V :=
              card_hom_le F G
          _ = 0 := by rw [hW0]; exact zero_pow hk0
      have hinj0 : Nat.card {φ : F →g G // Function.Injective ⇑φ} = 0 := by
        apply Nat.eq_zero_of_le_zero
        calc Nat.card {φ : F →g G // Function.Injective ⇑φ} ≤
                (Fintype.card W).descFactorial (Fintype.card V) :=
              card_injective_hom_le F G
          _ = 0 := by
            rw [hW0]
            exact Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hhom0, hinj0, Nat.cast_zero, zero_div, zero_div]
  · have hn : 0 < Fintype.card W := Nat.pos_of_ne_zero hW0
    rw [homDensityFin_def, injHomDensity_def]
    set k := Fintype.card V with hk
    set n := Fintype.card W with hn'
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hN : (0 : ℝ) < (n : ℝ) ^ k := pow_pos hnR k
    have haN : (Nat.card (F →g G) : ℝ) ≤ (n : ℝ) ^ k := by
      have h : Nat.card (F →g G) ≤ n ^ k := by
        simpa [n, k] using card_hom_le F G
      exact_mod_cast h
    have hbM : (Nat.card {φ : F →g G // Function.Injective ⇑φ} : ℝ)
        ≤ ((n.descFactorial k : ℕ) : ℝ) := by
      have h : Nat.card {φ : F →g G // Function.Injective ⇑φ} ≤ n.descFactorial k := by
        simpa [n, k] using card_injective_hom_le F G
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
