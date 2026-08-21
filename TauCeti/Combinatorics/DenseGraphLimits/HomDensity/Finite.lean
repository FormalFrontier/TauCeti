/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Homomorphism densities in a finite graph

Two densities of a finite pattern graph `F` in a finite host graph `G`:

* `homDensityFin F G = |Hom(F, G)| / |V(G)| ^ |V(F)|` — all homomorphisms;
* `injHomDensity F G = |Inj(F, G)| / (|V(G)|)_{|V(F)|}` — the *injective* ones, normalized by the
  **falling factorial**.

These are the finite-graph front of the sampling theory. Nothing here is about graphons, and nothing
here samples: these are the estimators the later sampling laws are estimators *of*.

## The falling factorial, not the binomial coefficient

`injHomDensity` divides by `(Fintype.card W).descFactorial (Fintype.card V)`, the number of
*ordered* injections of a `|V(F)|`-element set into `V(G)`. Its numerator counts ordered injective
homomorphisms, so the two agree as conventions. Dividing instead by `Nat.choose` would count
unordered images against ordered maps and bias the sampling estimator by `|V(F)|!` — the later
unbiasedness identity would read `k! · t(F, W)` rather than `t(F, W)`. The convention is fixed here
so that no downstream statement has to carry the correction.

## One counting convention, not two

`card_injective_hom_eq_labelledCopyCount` identifies the count in the numerator of `injHomDensity`
with Mathlib's `SimpleGraph.labelledCopyCount`, and `injHomDensity_eq_labelledCopyCount_div` carries
that to the density itself. This is proved, not assumed, and it is in this file deliberately:
without it, `injHomDensity` would silently establish a second counting convention alongside
Mathlib's. `SimpleGraph.Copy F G` is definitionally an injective homomorphism, so the bridge is an
equivalence of subtypes; note that Mathlib puts the **host** graph first, so the copy count of `F`
inside `G` is `G.labelledCopyCount F`.

This settles the *numerator*. Mathlib has no hom-density primitive, so nothing here pins the
`descFactorial` denominator; that convention is chosen here and is pinned later by the unbiasedness
anchor `injHomDensity_integral_sampleGraph`.

## Counting with `Nat.card`

Both densities count with `Nat.card`, which is total: it returns `0` on an infinite type and needs
no `Fintype` instance or decidability on the hom type, on `G`, or on `G.Adj`. The counted types are
finite here, so no generality is lost — but the definitions can be stated and rewritten without
carrying decidability hypotheses that the analytic statements downstream would then inherit.

## Main definitions

* `TauCeti.DenseGraphLimits.homDensityFin` — the homomorphism density `t(F, G)`.
* `TauCeti.DenseGraphLimits.injHomDensity` — the injective homomorphism density `t₀(F, G)`.
Both density bodies stay unexposed; `homDensityFin_def` and `injHomDensity_def` are the unfolding
lemmas downstream modules should use.

## Main results

* `card_injective_hom_eq_labelledCopyCount`, `injHomDensity_eq_labelledCopyCount_div` — the bridge
  to Mathlib's counting primitive, at the level of the count and of the density;
* `card_hom_eq_card_adjPreservingMaps` — homomorphisms are counted by the
  adjacency-preserving vertex maps;
* `homDensityFin_nonneg`, `homDensityFin_le_one`, `injHomDensity_nonneg`, `injHomDensity_le_one` —
  both densities lie in `[0, 1]`, unconditionally. The degenerate cases are included: when the host
  is empty and the pattern is not, numerator and denominator both vanish and `x / 0 = 0` gives `0`.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 9a — the finite hom-density
  estimators. The signatures and the counting-bridge proof are taken from
  `TauCetiRoadmap/DenseGraphLimits/Suggested.lean` (Layer 9a), generalized here from a
  `SimpleGraph (Fin m)` host to an arbitrary finite host. The hom-versus-injective closeness bound,
  the sampling laws, the unbiasedness anchor, and finite-graph graphons are separate targets and are
  not built here.
* The roadmap lists this bridge under its migration-backed routes, with an independent proof in
  `cameronfreer/graphon` (pin `6eccca5`). No material is adapted from that source; the proof here
  follows `Suggested.lean`.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §5.2.
-/

public section

namespace TauCeti

namespace DenseGraphLimits

variable {V W : Type*} [Fintype V] [Fintype W]

/-- The **homomorphism density** `t(F, G) = |Hom(F, G)| / |V(G)| ^ |V(F)|` of a finite pattern
graph `F` in a finite host graph `G`.

Counted with `Nat.card`, so no `Fintype` or decidability instance on the hom type or on `G` is
required. Use `homDensityFin_def` to unfold. -/
noncomputable def homDensityFin (F : SimpleGraph V) (G : SimpleGraph W) : ℝ :=
  (Nat.card (F →g G) : ℝ) / (Fintype.card W ^ Fintype.card V : ℝ)

/-- The **injective homomorphism density** `t₀(F, G)`: ordered injective homomorphisms over the
falling factorial `(|V(G)|)_{|V(F)|}`.

The denominator counts *ordered* injections `V ↪ W`, matching the ordered numerator. `Nat.choose`
would not: it counts unordered images, and would bias the sampling estimator by `|V(F)|!`. Use
`injHomDensity_def` to unfold. -/
noncomputable def injHomDensity (F : SimpleGraph V) (G : SimpleGraph W) : ℝ :=
  (Nat.card {φ : F →g G // Function.Injective φ} : ℝ) /
    ((Fintype.card W).descFactorial (Fintype.card V) : ℝ)

variable (F : SimpleGraph V) (G : SimpleGraph W)

/-- The defining equation of `homDensityFin`. The definition's body is not exposed, so this is the
lemma downstream modules should rewrite with. -/
theorem homDensityFin_def :
    homDensityFin F G = (Nat.card (F →g G) : ℝ) / (Fintype.card W ^ Fintype.card V : ℝ) := (rfl)

/-- The defining equation of `injHomDensity`. The definition's body is not exposed, so this is the
lemma downstream modules should rewrite with. -/
theorem injHomDensity_def :
    injHomDensity F G = (Nat.card {φ : F →g G // Function.Injective φ} : ℝ) /
      ((Fintype.card W).descFactorial (Fintype.card V) : ℝ) := (rfl)

/-! ### The bridge to Mathlib's counting primitive -/

/-- The count in the numerator of `injHomDensity` is Mathlib's labelled copy count.

`SimpleGraph.Copy F G` is definitionally an injective homomorphism, so this is an equivalence of
subtypes. Mathlib takes the host graph first: `G.labelledCopyCount F` counts copies of `F` inside
`G`.

This settles the numerator against the existing Mathlib primitive, so `injHomDensity` does not
introduce a parallel counting convention.

Deliberately not `@[simp]`: the left-hand side is not in simp normal form, since `Nat.card` of a
`Fintype` rewrites to `Fintype.card`, and the repo's `simpNF` linter rejects the annotation. Stating
it with a `Fintype.card` left-hand side instead would abandon the `Nat.card` counting convention the
roadmap pins for these densities. -/
theorem card_injective_hom_eq_labelledCopyCount :
    Nat.card {φ : F →g G // Function.Injective φ} = G.labelledCopyCount F := by
  -- `labelledCopyCount` is defined by `classical exact Fintype.card (Copy H G)`, so unfolding it
  -- exposes a `Fintype (Copy F G)` that only `classical` provides.
  classical
  rw [SimpleGraph.labelledCopyCount, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun φ => ⟨φ.1, φ.2⟩
      invFun := fun c => ⟨c.toHom, c.injective'⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The injective homomorphism density in terms of Mathlib's labelled copy count. -/
theorem injHomDensity_eq_labelledCopyCount_div :
    injHomDensity F G =
      (G.labelledCopyCount F : ℝ) / ((Fintype.card W).descFactorial (Fintype.card V) : ℝ) := by
  rw [injHomDensity_def, card_injective_hom_eq_labelledCopyCount]

/-! ### Homomorphisms as adjacency-preserving vertex maps -/

private def relHomEquivPreservingMaps {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) :
    (r →r s) ≃ {f : α → β // ∀ a b, r a b → s (f a) (f b)} where
  toFun φ := ⟨⇑φ, fun _ _ h => φ.map_rel h⟩
  invFun ψ := ⟨ψ.1, fun {_ _} h => ψ.2 _ _ h⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] [Fintype W] in
/-- Homomorphisms and adjacency-preserving vertex maps are counted alike. -/
theorem card_hom_eq_card_adjPreservingMaps :
    Nat.card (F →g G) = Nat.card {ψ : V → W // ∀ a b, F.Adj a b → G.Adj (ψ a) (ψ b)} :=
  Nat.card_congr (relHomEquivPreservingMaps F.Adj G.Adj)

/-! ### Both densities lie in `[0, 1]` -/

private theorem card_hom_le : Nat.card (F →g G) ≤ Fintype.card W ^ Fintype.card V := by
  classical
  calc Nat.card (F →g G) ≤ Nat.card (V → W) :=
        Nat.card_le_card_of_injective (fun φ => (φ : V → W))
          (fun a b h => by ext x; exact congrFun h x)
    _ = Fintype.card W ^ Fintype.card V := by rw [Nat.card_eq_fintype_card, Fintype.card_fun]

private theorem card_injective_hom_le :
    Nat.card {φ : F →g G // Function.Injective φ}
      ≤ (Fintype.card W).descFactorial (Fintype.card V) := by
  classical
  calc Nat.card {φ : F →g G // Function.Injective φ} ≤ Nat.card (V ↪ W) :=
        Nat.card_le_card_of_injective (fun φ => ⟨(φ.1 : V → W), φ.2⟩)
          (fun a b h => by
            ext x; exact congrFun (congrArg (fun e : V ↪ W => (e : V → W)) h) x)
    _ = (Fintype.card W).descFactorial (Fintype.card V) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]

/-- The homomorphism density is nonnegative. -/
theorem homDensityFin_nonneg : 0 ≤ homDensityFin F G :=
  div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

/-- The homomorphism density is at most `1`, since every homomorphism is in particular a function
`V(F) → V(G)`.

No hypothesis is needed. When the host is empty and the pattern is not, numerator and denominator
both vanish and `x / 0 = 0` gives `0`. -/
theorem homDensityFin_le_one : homDensityFin F G ≤ 1 := by
  refine div_le_one_of_le₀ ?_ (pow_nonneg (Nat.cast_nonneg _) _)
  exact_mod_cast card_hom_le F G

/-- The injective homomorphism density is nonnegative. -/
theorem injHomDensity_nonneg : 0 ≤ injHomDensity F G :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The injective homomorphism density is at most `1`, since every injective homomorphism is in
particular an embedding `V(F) ↪ V(G)`, and those are counted by the falling factorial.

No hypothesis is needed; the degenerate cases behave as for `homDensityFin_le_one`. -/
theorem injHomDensity_le_one : injHomDensity F G ≤ 1 := by
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  exact_mod_cast card_injective_hom_le F G

end DenseGraphLimits

end TauCeti
