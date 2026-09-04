/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Agent
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Finite
import TauCeti.Probability.UniformSampling
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

/-- The homomorphism density and the injective homomorphism density differ by at most
`C(k,2) / n`, where `k` is the number of vertices of the pattern and `n` the number of
vertices of the host, for every finite pattern and host graph.
-/
theorem homDensityFin_sub_injHomDensity_le (F : SimpleGraph V) (G : SimpleGraph W) :
    |homDensityFin F G - injHomDensity F G|
      ≤ ((Fintype.card V).choose 2 : ℝ) / (Fintype.card W : ℝ) := by
  classical
  by_cases hW0 : Fintype.card W = 0
  · rw [homDensityFin_def, injHomDensity_def]
    by_cases hk0 : Fintype.card V = 0
    · have hV : IsEmpty V := Fintype.card_eq_zero_iff.mp hk0
      have hsub : ∀ φ : F →g G, Function.Injective (⇑φ : V → W) := by
        intro φ a b _
        exact False.elim (hV.false a)
      have e : (F →g G) ≃ {φ : F →g G // Function.Injective ⇑φ} :=
        { toFun := fun φ => ⟨φ, hsub φ⟩
          invFun := Subtype.val
          left_inv := fun _ => rfl
          right_inv := fun ⟨_, _⟩ => rfl }
      rw [Nat.card_congr e, hk0, pow_zero, Nat.descFactorial_zero, Nat.cast_one]
      simp [hW0]
    · have hhom0 : Nat.card (F →g G) = 0 := by
        apply Nat.eq_zero_of_le_zero
        calc Nat.card (F →g G) ≤ Fintype.card W ^ Fintype.card V :=
              F.card_hom_le G
          _ = 0 := by rw [hW0]; exact zero_pow hk0
      have hinj0 : Nat.card {φ : F →g G // Function.Injective ⇑φ} = 0 := by
        apply Nat.eq_zero_of_le_zero
        calc Nat.card {φ : F →g G // Function.Injective ⇑φ} ≤
                (Fintype.card W).descFactorial (Fintype.card V) :=
              F.card_injective_hom_le G
          _ = 0 := by
            rw [hW0]
            exact Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hhom0, hinj0, Nat.cast_zero, zero_div, zero_div]
      simp [hW0]
  · have hn : 0 < Fintype.card W := Nat.pos_of_ne_zero hW0
    let _ : MeasurableSpace W := ⊤
    let A : Set (V → W) := {f | ∀ a b, F.Adj a b → G.Adj (f a) (f b)}
    let E : Set (V → W) := {f | Function.Injective f}
    have hA : Nat.card {f : V → W // f ∈ A} = Nat.card (F →g G) := by
      simpa [A] using (card_hom_eq_card_adjPreservingMaps F G).symm
    have hEA : Nat.card {f : V → W // f ∈ E ∩ A} =
        Nat.card {φ : F →g G // Function.Injective ⇑φ} := by
      let e : {f : V → W // f ∈ E ∩ A} ≃ {φ : F →g G // Function.Injective ⇑φ} :=
        { toFun := fun f => ⟨⟨f.1, fun {a b} hab => f.2.2 a b hab⟩, f.2.1⟩
          invFun := fun φ => ⟨⇑φ.1, φ.2, fun {a b} hab => φ.1.map_rel hab⟩
          left_inv := by intro f; rfl
          right_inv := by
            intro φ
            apply Subtype.ext
            exact RelHom.ext (fun _ => rfl) }
      exact Nat.card_congr e
    have hE : Nat.card {f : V → W // f ∈ E} =
        (Fintype.card W).descFactorial (Fintype.card V) := by
      let e : {f : V → W // f ∈ E} ≃ (V ↪ W) :=
        { toFun := fun f => ⟨f.1, f.2⟩
          invFun := fun e => ⟨e.1, e.2⟩
          left_inv := by intro f; rfl
          right_inv := by intro e; rfl }
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
    have hU : Nat.card (V → W) = Fintype.card W ^ Fintype.card V := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have hleft := Probability.uniformOn_injective_le_add_choose_two_div (ι := V) (κ := W) A
    have hright := Probability.uniformOn_univ_le_injective_add_choose_two_div (ι := V) (κ := W) A
    have hleftR :
        (Nat.card {f : V → W // f ∈ E ∩ A} : ℝ) /
            (Nat.card {f : V → W // f ∈ E} : ℝ) ≤
          (Nat.card {f : V → W // f ∈ Set.univ ∩ A} : ℝ) /
              (Nat.card {f : V → W // f ∈ Set.univ} : ℝ) +
            ((Fintype.card V).choose 2 : ℝ) / (Fintype.card W : ℝ) := by
      rw [← Probability.uniformOn_toReal E A, ← Probability.uniformOn_toReal Set.univ A]
      have h := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).2 hleft
      rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_div] at h
      simpa [E, ENNReal.toReal_natCast] using h
    have hrightR :
        (Nat.card {f : V → W // f ∈ Set.univ ∩ A} : ℝ) /
            (Nat.card {f : V → W // f ∈ Set.univ} : ℝ) ≤
          (Nat.card {f : V → W // f ∈ E ∩ A} : ℝ) /
              (Nat.card {f : V → W // f ∈ E} : ℝ) +
            ((Fintype.card V).choose 2 : ℝ) / (Fintype.card W : ℝ) := by
      rw [← Probability.uniformOn_toReal Set.univ A, ← Probability.uniformOn_toReal E A]
      have h := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).2 hright
      rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_div] at h
      simpa [E, ENNReal.toReal_natCast] using h
    rw [homDensityFin_def, injHomDensity_def]
    have hU0 : Nat.card {f : V → W // f ∈ Set.univ} = Nat.card (V → W) := by
      rw [Nat.card_congr]
      exact Equiv.Set.univ (V → W)
    have hUA : Nat.card {f : V → W // f ∈ Set.univ ∩ A} = Nat.card {f : V → W // f ∈ A} := by
      apply Nat.card_congr
      exact { toFun := fun f => ⟨f.1, by simpa using f.2⟩
              invFun := fun f => ⟨f.1, by simp [f.2]⟩
              left_inv := by intro f; rfl
              right_inv := by intro f; rfl }
    rw [hUA, hU0, hA, hEA, hE, hU] at hleftR hrightR
    push_cast at hleftR hrightR
    rw [abs_le]
    constructor <;> linarith [hleftR, hrightR]

end DenseGraphLimits

end TauCeti
