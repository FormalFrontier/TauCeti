/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Dimension
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Uniqueness

/-!
# The divisor of a Weil differential, and the Riemann–Roch theorem

`TauCeti.Divisor.IsRiemannRochDivisor` records what it means for a divisor `W` to satisfy the
Riemann–Roch identity `ℓ(D) = deg D + 1 - g₀ + ℓ(W - D)`, and everything about such a `W` —
that `g₀` is the genus, that `deg W = 2g - 2` and `ℓ(W) = g`, that any two are linearly
equivalent — is proved there.  What is missing, and is supplied here, is that **one exists**.
That is the Riemann–Roch theorem.

The witness is the divisor of a nonzero Weil differential.  Enlarging a divisor shrinks the space
`Ω_F(D)` of Weil differentials it bounds, so the divisors bounding a fixed `ω` form a downward
closed family; the two facts that make it have a *greatest* element are that the family is stable
under suprema — because `A_F(D ⊔ E) = A_F(D) + A_F(E)`, which is
`TauCeti.adeleFiltration_sup` — and that its degrees are bounded above, because past the
threshold of Riemann's theorem the index of specialty vanishes and with it `Ω_F(D)`.
A divisor of maximal degree in the family is then the greatest, since places have positive degree.

Writing `W` for that greatest divisor, multiplication by a function is an injective `k`-linear map
`F → Ω_F` carrying `L(W - D)` onto `Ω_F(D)`: a nonzero `x` has `x · ω ∈ Ω_F(D)` exactly when
`ω ∈ Ω_F(D - div x)`, which by maximality says `D - div x ≤ W`, that is `x ∈ L(W - D)`; and it is
onto because every Weil differential is a multiple of `ω` (Proposition 1.5.9, already available as
`TauCeti.exists_repartitionDualMul_eq`).  So `ℓ(W - D) = dim_k Ω_F(D) = i(D)`, which rearranges to
the Riemann–Roch identity.

This completes Section I.5 of Stichtenoth.  It also supplies the divisor whose absence is noted in
`TauCeti/FieldTheory/FunctionField/Differential/LocalComponent.lean`, where the remaining
statements of Section I.7 are held back for want of it.

## Main results

* `TauCeti.mem_weilDifferentialFiltration_sup`: a Weil differential bounded by `D` and by `E` is
  bounded by `D ⊔ E`.
* `TauCeti.exists_forall_degree_lt_of_mem_weilDifferentialFiltration`: the divisors bounding a
  fixed nonzero Weil differential have bounded degree.
* `TauCeti.exists_isGreatest_mem_weilDifferentialFiltration`: **the divisor of a nonzero Weil
  differential** — among the divisors bounding it there is a greatest (Stichtenoth,
  Proposition 1.5.11).
* `TauCeti.mem_weilDifferentialFiltration_iff_le_of_isGreatest`: `ω ∈ Ω_F(D) ↔ D ≤ (ω)`, the
  characteristic property of that divisor.
* `TauCeti.repartitionDualMul_mem_weilDifferentialFiltration_iff_mem_riemannRochSpace`: the
  duality `x · ω ∈ Ω_F(D) ↔ x ∈ L(W - D)` that carries the theorem.
* `TauCeti.isRiemannRochDivisor_of_isGreatest_mem_weilDifferentialFiltration`: that divisor is a
  Riemann–Roch divisor for the genus (Stichtenoth, Theorem 1.5.15).
* `TauCeti.exists_isRiemannRochDivisor`: **the Riemann–Roch theorem** — a Riemann–Roch divisor
  exists.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5, in particular Proposition 1.5.11 and Theorem 1.5.15.
* [The algebraic curves roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/AlgebraicCurves/README.md),
  Layer 4.
-/

public section

namespace TauCeti

open AlgebraicGeometry

open scoped WithZero

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-! ### Weil differentials bounded by a supremum -/

/-- A Weil differential bounded by each of two divisors is bounded by their supremum: by
`TauCeti.adeleFiltration_sup` a repartition bounded by `D ⊔ E` is a sum of two on which the
differential already vanishes. -/
theorem mem_weilDifferentialFiltration_sup {D E : Divisor k F}
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hD : ω ∈ weilDifferentialFiltration D)
    (hE : ω ∈ weilDifferentialFiltration E) :
    ω ∈ weilDifferentialFiltration (D ⊔ E) := by
  refine mem_weilDifferentialFiltration_of_apply_eq_zero (fun a ha ↦ ?_) (fun a ha ↦
    weilDifferentialFiltration_apply_eq_zero_of_mem_diagonalRepartitions hD a ha)
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ((adeleFiltration_sup D E).le ha)
  have hxA : x ∈ repartitionSpace k F := adeleFiltration_le_repartitionSpace D hx
  have hyA : y ∈ repartitionSpace k F := adeleFiltration_le_repartitionSpace E hy
  have hsplit : a = ⟨x, hxA⟩ + ⟨y, hyA⟩ := Subtype.ext hxy.symm
  rw [hsplit, map_add]
  simp [weilDifferentialFiltration_apply_eq_zero_of_mem_adeleFiltration hD ⟨x, hxA⟩ hx,
    weilDifferentialFiltration_apply_eq_zero_of_mem_adeleFiltration hE ⟨y, hyA⟩ hy]

/-! ### The divisor of a nonzero Weil differential -/

/-- The divisors bounding a fixed nonzero Weil differential have bounded degree: past the
threshold of `TauCeti.exists_forall_indexOfSpecialty_eq_zero` the divisor is nonspecial, and a
nonspecial divisor bounds no nonzero Weil differential. -/
theorem exists_forall_degree_lt_of_mem_weilDifferentialFiltration (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ≠ 0) :
    ∃ c : ℤ, ∀ D : Divisor k F, ω ∈ weilDifferentialFiltration D → Divisor.degree D < c := by
  obtain ⟨c, hc⟩ := exists_forall_indexOfSpecialty_eq_zero hF hex
  refine ⟨c, fun D hD ↦ ?_⟩
  by_contra hcon
  push Not at hcon
  have hbot : weilDifferentialFiltration D = ⊥ :=
    (weilDifferentialFiltration_eq_bot_iff_indexOfSpecialty_eq_zero hF hex D).2 (hc D hcon)
  exact hω (by simpa [hbot] using hD)

/-- **The divisor of a nonzero Weil differential** (Stichtenoth, Proposition 1.5.11): the
divisors bounding `ω` have a greatest element.

Degrees are bounded above, so a divisor `W` of maximal degree among them exists; for any other
`D` bounding `ω`, the supremum `D ⊔ W` also bounds `ω` and has degree at least that of `W` by
monotonicity and at most by maximality, hence equals `W` because places have positive degree. -/
theorem exists_isGreatest_mem_weilDifferentialFiltration (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hmem : ω ∈ weilDifferentialSpace k F) (hω : ω ≠ 0) :
    ∃ W : Divisor k F, IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W := by
  classical
  obtain ⟨c, hc⟩ := exists_forall_degree_lt_of_mem_weilDifferentialFiltration hF hex hω
  obtain ⟨D₀, hD₀⟩ := mem_weilDifferentialSpace_iff.mp hmem
  obtain ⟨m, ⟨W, hWmem, hWdeg⟩, hmax⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun n : ℤ => ∃ D : Divisor k F, ω ∈ weilDifferentialFiltration D ∧
        Divisor.degree D = n)
      ⟨c, fun n ⟨D, hD, hDn⟩ => hDn ▸ (hc D hD).le⟩
      ⟨Divisor.degree D₀, D₀, hD₀, rfl⟩
  refine ⟨W, hWmem, fun D hD ↦ ?_⟩
  have hsup : ω ∈ weilDifferentialFiltration (D ⊔ W) := mem_weilDifferentialFiltration_sup hD hWmem
  have hle : Divisor.degree (D ⊔ W) ≤ Divisor.degree W := hWdeg ▸ hmax _ ⟨D ⊔ W, hsup, rfl⟩
  have hge : Divisor.degree W ≤ Divisor.degree (D ⊔ W) := Divisor.degree_le_of_le le_sup_right
  have hWeq : W = D ⊔ W := Divisor.eq_of_le_of_degree_eq hF le_sup_right (le_antisymm hge hle)
  exact hWeq ▸ le_sup_left

/-- The characteristic property of the divisor of `ω`, in the form consumers use: `ω` is bounded
by `D` exactly when `D` is at most the divisor of `ω`.  The forward direction is maximality; the
reverse is antitonicity of the filtration. -/
theorem mem_weilDifferentialFiltration_iff_le_of_isGreatest
    {ω : Module.Dual k ↥(repartitionSpace k F)} {W : Divisor k F}
    (hW : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W) (D : Divisor k F) :
    ω ∈ weilDifferentialFiltration D ↔ D ≤ W :=
  ⟨fun h => hW.2 h, fun h => weilDifferentialFiltration_antitone h hW.1⟩

/-! ### The Riemann–Roch theorem -/

/-- **Duality between `L(W - D)` and `Ω_F(D)`**, for `W` the divisor of `ω`: a function `x`
multiplies `ω` into `Ω_F(D)` exactly when it lies in `L(W - D)`.

For nonzero `x`, multiplication translates the filtration by the principal divisor of `x`
(`TauCeti.repartitionDualMul_mem_weilDifferentialFiltration_iff`), so `x · ω ∈ Ω_F(D)` says
`ω ∈ Ω_F(D - div x)`, which by maximality of `W` says `D - div x ≤ W`. -/
theorem repartitionDualMul_mem_weilDifferentialFiltration_iff_mem_riemannRochSpace
    (hF : IsFunctionField k F) {ω : Module.Dual k ↥(repartitionSpace k F)} {W : Divisor k F}
    (hW : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W)
    (D : Divisor k F) (x : F) :
    repartitionDualMul hF x ω ∈ weilDifferentialFiltration D ↔ x ∈ riemannRochSpace (W - D) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, (z : F) = x := ⟨Units.mk0 x hx, rfl⟩
  have habel : W - (D - Divisor.principal hF z) = Divisor.principal hF z + (W - D) := by abel
  have hrw : D - Divisor.principal hF z + Divisor.principal hF z = D := by abel
  have hiff : (D - Divisor.principal hF z ≤ W) ↔ 0 ≤ Divisor.principal hF z + (W - D) := by
    rw [← habel]; exact sub_nonneg.symm
  rw [mem_riemannRochSpace_units_iff hF, ← hiff]
  constructor
  · intro h
    refine hW.2 ((repartitionDualMul_mem_weilDifferentialFiltration_iff hF z).mp ?_)
    rwa [hrw]
  · intro h
    have hmem := (repartitionDualMul_mem_weilDifferentialFiltration_iff hF z).mpr
      (weilDifferentialFiltration_antitone h hW.1)
    rwa [hrw] at hmem

/-- **The Riemann–Roch theorem** (Stichtenoth, Theorem 1.5.15): the divisor of a nonzero Weil
differential is a Riemann–Roch divisor for the genus.

Multiplication by a function is an injective `k`-linear map `F → Ω_F` carrying `L(W - D)` onto
`Ω_F(D)`: membership transfers by
`TauCeti.repartitionDualMul_mem_weilDifferentialFiltration_iff_mem_riemannRochSpace`, and
surjectivity is Proposition 1.5.9, every Weil differential being a multiple of `ω`.  Hence
`ℓ(W - D) = dim_k Ω_F(D) = i(D)`, which rearranges to the Riemann–Roch identity. -/
theorem isRiemannRochDivisor_of_isGreatest_mem_weilDifferentialFiltration
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ≠ 0) {W : Divisor k F}
    (hW : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W) :
    W.IsRiemannRochDivisor (genus k F) := by
  set φ : F →ₗ[k] Module.Dual k ↥(repartitionSpace k F) :=
    { toFun := fun x => repartitionDualMul hF x ω
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl } with hφ
  have hφ_apply : ∀ x : F, φ x = repartitionDualMul hF x ω := fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨z, rfl⟩ : ∃ z : Fˣ, (z : F) = x := ⟨Units.mk0 x hx0, rfl⟩
    refine hω ?_
    rw [← repartitionDualMul_inv_repartitionDualMul hF z ω, ← hφ_apply, hx, map_zero]
  rw [Divisor.isRiemannRochDivisor_iff]
  intro D
  have key : ∀ x : F, φ x ∈ weilDifferentialFiltration D ↔ x ∈ riemannRochSpace (W - D) :=
    fun x => by
      rw [hφ_apply]
      exact repartitionDualMul_mem_weilDifferentialFiltration_iff_mem_riemannRochSpace hF hW D x
  have himg : Submodule.map φ (riemannRochSpace (W - D)) = weilDifferentialFiltration D := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (key x).mpr hx
    · intro η hη
      obtain ⟨c, hc⟩ := exists_repartitionDualMul_eq hF hex
        (weilDifferentialFiltration_le_weilDifferentialSpace W hW.1) hω
        (weilDifferentialFiltration_le_weilDifferentialSpace D hη)
      exact ⟨c, (key c).mp (by rw [hφ_apply, hc]; exact hη), hc⟩
  have hdim : Divisor.dim (W - D) = Module.finrank k ↥(weilDifferentialFiltration D) := by
    rw [Divisor.dim_def, ← himg]
    exact (Submodule.equivMapOfInjective φ hinj (riemannRochSpace (W - D))).finrank_eq
  have hi := finrank_weilDifferentialFiltration hF hex D
  rw [← hdim, Divisor.indexOfSpecialty_def] at hi
  omega

/-- **The Riemann–Roch theorem, existence form** (Stichtenoth, Theorem 1.5.15 with
Corollary 1.5.16): every algebraic function field with exact constant field has a Riemann–Roch
divisor, namely the divisor of any nonzero Weil differential.  With
`TauCeti.Divisor.IsRiemannRochDivisor.dim_eq` and
`TauCeti.Divisor.IsRiemannRochDivisor.degree_eq` this gives `ℓ(W) = g` and `deg W = 2g - 2`, and
with `TauCeti.Divisor.IsRiemannRochDivisor.linearlyEquivalent` the class of `W` — the canonical
class — is well defined. -/
theorem exists_isRiemannRochDivisor (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) :
    ∃ W : Divisor k F, W.IsRiemannRochDivisor (genus k F) := by
  obtain ⟨ω, hωmem, hω0⟩ := (Submodule.ne_bot_iff _).mp (weilDifferentialSpace_ne_bot hF hex)
  obtain ⟨W, hW⟩ := exists_isGreatest_mem_weilDifferentialFiltration hF hex hωmem hω0
  exact ⟨W, isRiemannRochDivisor_of_isGreatest_mem_weilDifferentialFiltration hF hex hω0 hW⟩

end TauCeti
