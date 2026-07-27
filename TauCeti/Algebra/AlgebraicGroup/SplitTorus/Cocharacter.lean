/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# The character–cocharacter perfect pairing of a split torus

`TauCeti.Algebra.AlgebraicGroup.Cocharacter` builds, for the diagonalizable group `D(M)`, the
`ℤ`-valued character–cocharacter pairing `DiagonalizableGroup.pairing m ψ = (ψ m).toAdd`, whose
value is the exponent of the power endomorphism of `𝔾ₘ` that realizes it on points
(`charPoints_comp_cocharPoints`), and computes it in the rank-`1`
case `𝔾ₘ = D(Multiplicative ℤ)` as multiplication of integers (`pairing_ofAdd`). This file does
the arbitrary-rank case, the **split torus** `T = D(Multiplicative (σ →₀ ℤ))` of
`TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic`, whose character lattice is
`X*(T) = σ →₀ ℤ` (the free `ℤ`-module on `σ`).

* The **cocharacter lattice** `X_*(T)` is identified with `σ → ℤ` by `SplitTorus.cocharEquiv`,
  reading a cocharacter `ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ` off on the standard
  generators; this is `TauCeti.freeAbelianCharEquiv` composed with `Multiplicative.toAdd`.
* The **pairing is the dot product**: `SplitTorus.pairing_ofAdd_eq` computes
  `⟨ofAdd m, ψ⟩ = ∑ᵢ mᵢ · cocharEquiv ψ i`, so that `X*(T) × X_*(T) → ℤ` is the canonical
  evaluation pairing between `σ →₀ ℤ` and `σ → ℤ`. It is realized on the group as the
  corresponding power endomorphism of `𝔾ₘ` (`SplitTorus.charPoints_comp_cocharPoints_ofAdd`).
* The pairing is **non-degenerate** in each slot for arbitrary `σ`:
  `SplitTorus.eq_zero_of_forall_pairing_eq_zero` and
  `SplitTorus.eq_one_of_forall_pairing_eq_zero` — a character pairing to `0` against every
  cocharacter is trivial, and vice versa.
* For a **finite-rank** split torus (`Finite σ`) the pairing is genuinely **perfect**:
  `SplitTorus.instIsPerfPair` gives Mathlib's `LinearMap.IsPerfPair` for the dot-product
  bilinear map `SplitTorus.dotPairing`, i.e. both induced maps to the `ℤ`-duals are
  isomorphisms. Transported along the bundled identification `SplitTorus.cocharAddEquiv` of the
  cocharacter lattice with `σ → ℤ`, this is `SplitTorus.latticePairing`, the perfect pairing
  between the genuine character lattice `X*(T) = σ →₀ ℤ` and cocharacter lattice
  `X_*(T) = Additive (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ)`. We prove perfectness only
  in finite rank, the case relevant to root data.

This advances the reductive-groups roadmap (`ReductiveGroups/README.md` in TauCetiRoadmap),
Layer 4: "Tori: split ... the **character lattice `X*(T)`** and **cocharacter lattice
`X_*(T)`** with their **perfect pairing**: the input to root data", extending the rank-`1`
pairing of `DiagonalizableGroup.pairing_ofAdd` to the finite-rank split torus.

## Main declarations

* `TauCeti.SplitTorus.cocharEquiv`: the identification of the cocharacter lattice `X_*(T)` of
  the rank-`σ` split torus with `σ → ℤ`, and `TauCeti.SplitTorus.cocharAddEquiv` its bundled
  additive form `Additive (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) ≃+ (σ → ℤ)`.
* `TauCeti.SplitTorus.pairing_ofAdd_eq`: the character–cocharacter pairing is the dot product
  `⟨ofAdd m, ψ⟩ = ∑ᵢ mᵢ · cocharEquiv ψ i`.
* `TauCeti.SplitTorus.charPoints_comp_cocharPoints_ofAdd`: the dot-product pairing is realized
  on points as the corresponding power endomorphism of `𝔾ₘ`.
* `TauCeti.SplitTorus.eq_zero_of_forall_pairing_eq_zero`,
  `TauCeti.SplitTorus.eq_one_of_forall_pairing_eq_zero`: the pairing is non-degenerate in each
  slot, for arbitrary `σ`.
* `TauCeti.SplitTorus.dotPairing`: the pairing as a `ℤ`-bilinear map between `X*(T) = σ →₀ ℤ`
  and the coordinate model `σ → ℤ`, with `TauCeti.SplitTorus.instIsPerfPair` proving it perfect
  (`LinearMap.IsPerfPair`) for a finite-rank split torus (`Finite σ`).
* `TauCeti.SplitTorus.latticePairing`: the same pairing between `X*(T)` and the genuine
  cocharacter lattice `Additive (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ)`, perfect in
  finite rank (`instLatticePairingIsPerfPair`).

## References

The abstract diagonalizable-group character–cocharacter pairing is Tau Ceti's
`TauCeti.Algebra.AlgebraicGroup.Cocharacter`, and the free-abelian-group character
identification `TauCeti.freeAbelianCharEquiv` is `TauCeti.Algebra.Group.FreeAbelianCharacter`.
The dot-product form reuses Mathlib's `Finsupp.linearCombination` and the additive/multiplicative
type-tag adjunction `AddMonoidHom.toMultiplicative`; the bilinear packaging `dotPairing` and its
perfectness use Mathlib's free-forgetful adjunction `Finsupp.llift` and `LinearMap.IsPerfPair`.
This realizes the finite-rank split-torus perfect pairing of the Tau Ceti reductive-groups
roadmap (Layer 4).
-/

public section

namespace TauCeti

namespace SplitTorus

universe u v w

variable {σ : Type w}

/-- The **cocharacter lattice `X_*(T)`** of the rank-`σ` split torus
`T = D(Multiplicative (σ →₀ ℤ))`, identified with `σ → ℤ`. A cocharacter
`ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ` is read off on the standard generators
`ofAdd (single i 1)`, its coordinate at `i` being `(ψ (ofAdd (single i 1))).toAdd`. This is
`TauCeti.freeAbelianCharEquiv` (with target `Multiplicative ℤ`) followed by `Multiplicative.toAdd`
in each coordinate. -/
noncomputable def cocharEquiv :
    (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) ≃ (σ → ℤ) :=
  freeAbelianCharEquiv.toEquiv.trans (Equiv.piCongrRight fun _ => Multiplicative.toAdd)

/-- The `i`-th coordinate of a cocharacter is its value on the standard generator
`ofAdd (single i 1)`, read as an integer through `Multiplicative.toAdd`. -/
@[simp]
theorem cocharEquiv_apply (ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) (i : σ) :
    cocharEquiv ψ i = (ψ (Multiplicative.ofAdd (Finsupp.single i 1))).toAdd := by
  simp [cocharEquiv, Equiv.piCongrRight_apply]

/-- Reading off cocharacter coordinates is additive: the trivial cocharacter has zero
coordinates. -/
@[simp]
theorem cocharEquiv_one : cocharEquiv (1 : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) = 0 := by
  ext i
  simp

/-- Reading off cocharacter coordinates is additive: the product of cocharacters (the group
operation on the cocharacter lattice) corresponds to pointwise addition of coordinates. -/
@[simp]
theorem cocharEquiv_mul (ψ φ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) :
    cocharEquiv (ψ * φ) = cocharEquiv ψ + cocharEquiv φ := by
  ext i
  simp [MonoidHom.mul_apply, toAdd_mul]

/-- The **cocharacter lattice `X_*(T)`** as a `ℤ`-module, bundled: the additive form of
`cocharEquiv`, identifying `Additive (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ)` (the
cocharacter group with its natural additive structure) with `σ → ℤ` as an `AddEquiv`. This
carries the algebraic compatibility that `cocharEquiv` reads off pointwise (`cocharEquiv_one`,
`cocharEquiv_mul`), so it transports the natural `ℤ`-module structure. -/
noncomputable def cocharAddEquiv :
    Additive (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) ≃+ (σ → ℤ) :=
  (MulEquiv.toAdditive freeAbelianCharEquiv).trans <|
    (AddEquiv.funAdditive σ (Multiplicative ℤ)).trans <|
      AddEquiv.piCongrRight fun _ => AddEquiv.toAdditive_toMultiplicative

/-- `cocharAddEquiv` agrees coordinatewise with the unbundled `cocharEquiv`. -/
@[simp]
theorem cocharAddEquiv_apply (ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) (i : σ) :
    cocharAddEquiv (Additive.ofMul ψ) i = cocharEquiv ψ i := by
  simp [cocharAddEquiv, cocharEquiv]

/-- **The split-torus character–cocharacter pairing is the dot product.** For a character
`ofAdd m` of `T` (`m : σ →₀ ℤ = X*(T)`) and a cocharacter `ψ` (with coordinates
`cocharEquiv ψ : σ → ℤ = X_*(T)`), the pairing `⟨ofAdd m, ψ⟩` of
`TauCeti.Algebra.AlgebraicGroup.Cocharacter` is `∑ᵢ mᵢ · cocharEquiv ψ i`. This is the
canonical evaluation pairing between the free `ℤ`-module `σ →₀ ℤ` and its dual `σ → ℤ`,
extending the rank-`1` `DiagonalizableGroup.pairing_ofAdd` to arbitrary rank. -/
theorem pairing_ofAdd_eq (ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) (m : σ →₀ ℤ) :
    DiagonalizableGroup.pairing (Multiplicative.ofAdd m) ψ =
      m.sum fun i c => c * cocharEquiv ψ i := by
  -- Extend `ψ` off the standard generators via the free-abelian universal property
  -- `freeAbelianCharEquiv`, then read `toAdd` of the resulting product of powers as a sum.
  rw [DiagonalizableGroup.pairing_def]
  conv_lhs => rw [← freeAbelianCharEquiv.symm_apply_apply ψ, freeAbelianCharEquiv_symm_apply_ofAdd]
  rw [Finsupp.prod, Finsupp.sum, toAdd_prod]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toAdd_zpow, cocharEquiv_apply, freeAbelianCharEquiv_apply, smul_eq_mul]

/-- **The split-torus character–cocharacter pairing as a `ℤ`-bilinear map.** On the character
lattice `X*(T) = σ →₀ ℤ` and the cocharacter lattice `X_*(T) = σ → ℤ` (via `cocharEquiv`) the
pairing is the evaluation/dot product `⟨m, v⟩ = ∑ᵢ mᵢ vᵢ`, packaged from Mathlib's
`Finsupp.llift`. It agrees with the character–cocharacter pairing of
`TauCeti.Algebra.AlgebraicGroup.Cocharacter` through `cocharEquiv` (`pairing_eq_dotPairing`). -/
noncomputable def dotPairing : (σ →₀ ℤ) →ₗ[ℤ] (σ → ℤ) →ₗ[ℤ] ℤ :=
  (Finsupp.llift ℤ ℤ ℤ σ).toLinearMap.flip

@[simp]
theorem dotPairing_apply (m : σ →₀ ℤ) (v : σ → ℤ) :
    dotPairing m v = m.sum fun i c => c * v i := by
  simp only [dotPairing, LinearMap.flip_apply, LinearEquiv.coe_coe, Finsupp.llift_apply,
    Finsupp.lift_apply, smul_eq_mul]

/-- **The dot-product pairing computes the character–cocharacter pairing.** For a character
`ofAdd m` and a cocharacter `ψ` (with coordinates `cocharEquiv ψ`), the pairing
`⟨ofAdd m, ψ⟩` of `TauCeti.Algebra.AlgebraicGroup.Cocharacter` is `dotPairing m (cocharEquiv ψ)`. -/
@[simp]
theorem pairing_eq_dotPairing (ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) (m : σ →₀ ℤ) :
    DiagonalizableGroup.pairing (Multiplicative.ofAdd m) ψ = dotPairing m (cocharEquiv ψ) := by
  rw [pairing_ofAdd_eq, dotPairing_apply]

/-- **The split-torus character–cocharacter pairing is perfect (finite rank).** For a
finite-rank split torus (`Finite σ`), the dot-product pairing `dotPairing` between the character
lattice `X*(T) = σ →₀ ℤ` and the cocharacter lattice `X_*(T) = σ → ℤ` is a perfect pairing in the
sense of Mathlib's `LinearMap.IsPerfPair`: both induced maps to the `ℤ`-duals are isomorphisms.
This is the split-torus perfect pairing that is the input to root data. (For arbitrary `σ` the
pairing stays non-degenerate in each slot — `eq_zero_of_forall_pairing_eq_zero`,
`eq_one_of_forall_pairing_eq_zero` — while perfectness is proved only in finite rank.) -/
instance instIsPerfPair [Finite σ] : (dotPairing (σ := σ)).IsPerfPair := by
  -- `dotPairing` is the flip of the linear equivalence `Finsupp.llift`, so it is perfect by
  -- Mathlib's `LinearEquiv.instIsPerfPair` (for the reflexive finite free module `σ →₀ ℤ`) and
  -- `LinearMap.flip.instIsPerfPair`.
  unfold dotPairing
  infer_instance

/-- **The split-torus character–cocharacter pairing on the genuine lattices.** The dot-product
pairing `dotPairing`, with its coordinate model `σ → ℤ` of the cocharacter lattice transported
back along `cocharAddEquiv` to the genuine cocharacter lattice
`X_*(T) = Additive (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ)`. On a cocharacter `ψ` it is
still `⟨ofAdd m, ψ⟩ = ∑ᵢ mᵢ · cocharEquiv ψ i` (`latticePairing_ofMul`). -/
noncomputable def latticePairing :
    (σ →₀ ℤ) →ₗ[ℤ]
      Additive (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) →ₗ[ℤ] ℤ :=
  dotPairing.compl₁₂ (LinearEquiv.refl ℤ (σ →₀ ℤ)).toLinearMap
    cocharAddEquiv.toIntLinearEquiv.toLinearMap

/-- `latticePairing` evaluated on a cocharacter is the character–cocharacter pairing, the dot
product `⟨ofAdd m, ψ⟩ = ∑ᵢ mᵢ · cocharEquiv ψ i`. -/
@[simp]
theorem latticePairing_ofMul (m : σ →₀ ℤ)
    (ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) :
    latticePairing m (Additive.ofMul ψ) =
      DiagonalizableGroup.pairing (Multiplicative.ofAdd m) ψ := by
  rw [pairing_ofAdd_eq]
  simp [latticePairing]

/-- **The split-torus character–cocharacter pairing is perfect (finite rank), on the genuine
cocharacter lattice.** For a finite-rank split torus (`Finite σ`), `latticePairing` between the
character lattice `X*(T) = σ →₀ ℤ` and the genuine cocharacter lattice
`X_*(T) = Additive (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ)` is a perfect pairing in the
sense of Mathlib's `LinearMap.IsPerfPair`, transported from `instIsPerfPair` along
`cocharAddEquiv`. -/
instance instLatticePairingIsPerfPair [Finite σ] : (latticePairing (σ := σ)).IsPerfPair := by
  unfold latticePairing
  infer_instance

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- **The dot-product pairing is realized on points as a power endomorphism of `𝔾ₘ`.**
Composing the character `ofAdd m` after the cocharacter `ψ` is the power endomorphism of `𝔾ₘ`
with exponent the dot product `∑ᵢ mᵢ · cocharEquiv ψ i`, so on points it raises a unit to that
power. This is the split-torus instance of `DiagonalizableGroup.charPoints_comp_cocharPoints`. -/
theorem charPoints_comp_cocharPoints_ofAdd
    (m : σ →₀ ℤ) (ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) :
    (DiagonalizableGroup.charPoints (R := R) (A := A) (Multiplicative.ofAdd m)).comp
        (DiagonalizableGroup.cocharPoints ψ) =
      DiagonalizableGroup.powEnd (m.sum fun i c => c * cocharEquiv ψ i) := by
  rw [DiagonalizableGroup.charPoints_comp_cocharPoints, pairing_ofAdd_eq]

/-- **Left non-degeneracy of the split-torus pairing.** A character `ofAdd m` pairing to `0`
against every cocharacter is trivial: `m = 0`. This holds for arbitrary `σ`; for finite `σ` the
pairing is moreover perfect (`instIsPerfPair`). -/
theorem eq_zero_of_forall_pairing_eq_zero {m : σ →₀ ℤ}
    (h : ∀ ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ,
      DiagonalizableGroup.pairing (Multiplicative.ofAdd m) ψ = 0) :
    m = 0 := by
  ext j
  -- Pair against the coordinate cocharacter `m ↦ ofAdd (m j)`.
  have hj := h (AddMonoidHom.toMultiplicative (Finsupp.applyAddHom j))
  rw [DiagonalizableGroup.pairing_def] at hj
  simpa [AddMonoidHom.coe_toMultiplicative] using hj

/-- **Right non-degeneracy of the split-torus pairing.** A cocharacter `ψ` pairing to `0`
against every character is trivial: `ψ = 1`. This holds for arbitrary `σ`; for finite `σ` the
pairing is moreover perfect (`instIsPerfPair`). -/
theorem eq_one_of_forall_pairing_eq_zero {ψ : Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ}
    (h : ∀ m : σ →₀ ℤ, DiagonalizableGroup.pairing (Multiplicative.ofAdd m) ψ = 0) :
    ψ = 1 := by
  refine freeAbelianCharEquiv.injective ?_
  ext j
  rw [freeAbelianCharEquiv_apply, map_one, Pi.one_apply]
  have hj := h (Finsupp.single j 1)
  rw [DiagonalizableGroup.pairing_def] at hj
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_one]
  exact hj

end SplitTorus

end TauCeti
