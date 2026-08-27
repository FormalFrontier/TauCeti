/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.NumberTheory.ModularForms.Fricke.Matrix
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# Conjugating `Γ₀(N)` and `Γ₁(N)` by the Fricke matrix

Over a field in which `N` is invertible, and for `σ = !![a, b; c, d] ∈ Γ₀(N)`, so `N ∣ c`,
conjugating by the Fricke matrix `W = !![0, -1; N, 0]` of
`TauCeti/NumberTheory/ModularForms/Fricke/Matrix.lean` gives

`W · σ · W⁻¹ = !![d, -c/N; -N·b, a]`,

which is again integral, again of determinant one, and again in `Γ₀(N)`. This file builds the
right-hand side as an honest `SL(2, ℤ)` matrix — `frickeConjSL` — reading it off the entries of
`σ`, so that it is defined at every level; records that a `Γ₀(N)` input stays inside `Γ₀(N)`
and that a `Γ₁(N)` input stays inside `Γ₁(N)`, again at every level; and proves, over a field
in which `N` is invertible, the two matrix identities that move `W` past `σ` and are what make
`frickeConjSL σ` the conjugate `W · σ · W⁻¹`.

`frickeConjSL` is defined directly by its entries rather than as a product `W * σ * W⁻¹`: the
latter lives in `GL (Fin 2) K` and is only *incidentally* integral, so reading an `SL(2, ℤ)`
element back out of it would need the divisibility argument anyway. Defining it by entries and
proving the product identities afterwards keeps the divisibility in one place.

## Level

`(N : K) ≠ 0` is what makes `W` invertible, and so what makes conjugation by `W` mean
anything. Over the arbitrary field `K` of the identities below that is strictly stronger than
`N ≠ 0`: a nonzero level casts to zero whenever the characteristic of `K` divides it. It is
needed for the *conjugation*, not for the entry formula that computes it, so it is stated where
`W` itself appears: as `[NeZero (N : K)]` on the two normalization identities over `K`, which are
the statements that exhibit `frickeConjSL σ` as a conjugate.

The formula itself needs no level hypothesis: `!![d, -c'; -N·b, a]` has determinant `1`, lies in
`Γ₀(N)` for every `N`, lies in `Γ₁(N)` whenever `σ` does, and is multiplicative in `σ`,
`c = N · (c / N)` holding at `N = 0` as well, both sides being zero. At `N = 0` the value is junk
rather than a conjugation: `Γ₀(0)` is the upper-triangular subgroup, the quotient `c / N` is `0`,
the formula collapses to `!![a, b; 0, d] ↦ !![d, 0; 0, a]`, which forgets `b`, and `frickeGL K 0`
does not exist for it to be a conjugation by.

The names follow the intended meaning rather than that degenerate value, as mathlib's do for
`Matrix.inv` at a singular matrix, for `Int.ediv` by `0`, and for `Gamma0 0` itself:
`frickeConjSL`, `frickeConjGamma0` and `frickeConjGamma1` are named for the Fricke conjugation
they compute. The level hypothesis then appears only on the declarations that need it —
`[NeZero N]` on the two `MulEquiv`s and the involution lemmas, `[NeZero (N : K)]` on the
identities over `K` — and not on the all-level declarations, where `unusedArguments` would reject
it as an argument the definition never uses.

`[NeZero N]` is a hypothesis on the natural number `N`, not on its image in a field: what fails
at level zero is the integer division `c / N`. The entry map is a homomorphism at every level
but an isomorphism only at nonzero level, so `[NeZero N]` is what the two involution lemmas and
the two automorphisms take.

## Base field

The conjugation identities are stated over an arbitrary field `K` in which `N` is invertible,
matching the parameterization of `frickeGL`. The weight-`k` slash action needs them over `ℝ`
while the `GL (Fin 2) ℚ` Hecke-ring stack needs them over `ℚ`; stating them over `K` serves both
directly, with no transport lemma between the two, since `Matrix.SpecialLinearGroup.mapGL` is
itself defined at an arbitrary algebra.

## Main definitions

* `TauCeti.frickeConjSL`: the matrix `!![d, -c/N; -N·b, a]` as an element of `SL(2, ℤ)`, read
  off the entries of `σ` at every level; over a field in which `N` is invertible it is the
  conjugate `W · σ · W⁻¹`.
* `TauCeti.frickeConjGamma0`, `TauCeti.frickeConjGamma1`: that map bundled as a group
  endomorphism `Γ₀(N) →* Γ₀(N)`, and its restriction `Γ₁(N) →* Γ₁(N)`. Like the map itself these
  exist at every level, so what they record is that the entry formula preserves the subgroup —
  not, on its own, that `W` normalizes it.
* `TauCeti.frickeConjGamma0MulEquiv`, `TauCeti.frickeConjGamma1MulEquiv`: for `[NeZero N]`, the
  same maps as automorphisms `Γ₀(N) ≃* Γ₀(N)` and `Γ₁(N) ≃* Γ₁(N)`, each its own inverse. These
  are the declarations that say `W` *normalizes* the subgroup.

## Main results

* `TauCeti.coe_frickeConjSL`: the entries of `frickeConjSL σ`, namely `!![d, -c/N; -N·b, a]`.
* `TauCeti.frickeConjSL_mem_Gamma0`: a `Γ₀(N)` input has `frickeConjSL σ ∈ Γ₀(N)`, at every
  level.
* `TauCeti.frickeConjSL_mem_Gamma1`: a `Γ₁(N)` input has `frickeConjSL σ ∈ Γ₁(N)`, at every
  level. This is a second hypothesis on `σ`, not a consequence of the previous line.
* `TauCeti.frickeConjSL_mul`, `TauCeti.frickeConjSL_one`: the entry map is multiplicative and
  unital, at every level. These are what the bundled endomorphisms above are built from.
* `TauCeti.frickeConjGamma0_frickeConjGamma0`, `TauCeti.frickeConjGamma1_frickeConjGamma1`:
  for `[NeZero N]`, applying the entry map twice is the identity.
* `TauCeti.gamma0Map_frickeConjGamma0_mul`: the `Gamma0Map` images of `frickeConjGamma0 σ` and
  of `σ` are inverse in `ZMod N`, at every level. This is the `ZMod`-level content of AINTLIB's
  diamond-character companion; see the Provenance section.
* `TauCeti.frickeConjGamma0MulEquiv_apply`, `TauCeti.frickeConjGamma0MulEquiv_symm`, and their
  `Γ₁` twins: the automorphisms act as the endomorphisms and are their own inverses. These, with
  `coe_frickeConjGamma0` and `coe_frickeConjGamma1`, are the intended interface for the bundled
  declarations: a consumer works through these simp lemmas rather than through the bodies.
* `TauCeti.frickeGL_mul_mapGL`, `TauCeti.mapGL_mul_frickeGL`: for `(N : K) ≠ 0`, the two
  normalization identities `W · σ = (W σ W⁻¹) · W` and `σ · W = W · (W σ W⁻¹)` in
  `GL (Fin 2) K`. These are the statements that exhibit `frickeConjSL σ` as the conjugate
  `W σ W⁻¹`; that `W` normalizes the subgroup is the two `MulEquiv`s.

## Relation to the Atkin–Lehner anti-involution

`TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/AtkinLehner.lean` also carries `Γ₀(N)` into itself,
so the two results look superficially alike. They are different maps. That one is
`g ↦ w · gᵀ · w⁻¹` for the diagonal `w = natDiagGL 2 ![1, N]`: it transposes, and it is an
*anti*-homomorphism, bundled as `HeckeRing.GL2.atkinLehnerAntiInvolution_bar` on the Hecke ring
`Δ₀(N)`. `frickeConjSL` is the entry formula for plain conjugation by `!![0, -1; N, 0]`, with
no transpose, and lives on `Γ₀(N)` itself. The two *matrices* are already distinguished in
`Fricke/Matrix.lean`; this is the corresponding note for the two conjugation maps.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Fricke.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `340875adfb2`, Apache-2.0, Chris Birkbeck), realizing part of Layer 6 of the ModularForms
roadmap.

Ported from there: the divisibility witness and its spec (`botLeftDiv`, `botLeftDiv_spec`
upstream, `natCast_mul_lowerLeft_ediv` here), `frickeConjSL` with its coercion lemma,
`frickeConjSL_mem_Gamma0` and `frickeConjSL_mem_Gamma1`, and the two normalization identities
`frickeGL_mul_mapGL` and `mapGL_mul_frickeGL`. Added here, with no counterpart upstream:
`frickeConjSL_one`, `frickeConjSL_mul`, `lowerLeft_ediv_mul`, `mapGL_frickeConjSL`, the bundled
`frickeConjGamma0` and `frickeConjGamma1` with their involution lemmas, and the two `MulEquiv`s
`frickeConjGamma0MulEquiv` and `frickeConjGamma1MulEquiv` with their `apply`/`symm` lemmas.

AINTLIB names the divisibility witness `botLeftDiv` and keeps it private. Here its spec is
**public**, as `natCast_mul_lowerLeft_ediv`, and it is `@[simp]`: `coe_frickeConjSL` writes the
quotient `c / N` out as an `Int.ediv`, so a consumer of that `simp` lemma needs the spec to make
progress, and keeping it private would force every use site to re-derive `(N : ℤ) ∣ c` from
`Gamma0_mem`. The public API is therefore the matrix formula together with that one normalization
rule.

AINTLIB obtains the witness as the `Exists.choose` of the `Γ₀(N)` divisibility, which makes it and
`frickeConjSL` `noncomputable` and their entries opaque; here it
is the honest quotient `c / N`, exact because `N ∣ c`, so both definitions are computable and
reduce entrywise. AINTLIB states the two normalization identities over `ℚ` and then transports
each along `ℚ → ℝ` by hand, in `glMap_frickeGL_mul_mapGL` and `mapGL_mul_glMap_frickeGL`; stating
them over `K` as below makes both transports the corresponding instance, so those two lemmas have
no counterpart here.

The diamond-character companion `Gamma0MapUnits_frickeConjSL` is ported in both of its halves.
Its `ZMod`-level content is `gamma0Map_frickeConjGamma0_mul` below, and its unit-valued content is
`toHomUnits_gamma0Map_frickeConjGamma0_eq_inv`. The two differ from upstream in how they reach the
units: AINTLIB states the refinement in terms of its own `Gamma0MapUnits`, a unit-valued refinement
of mathlib's `CongruenceSubgroup.Gamma0Map`, whereas here the same content is obtained from the
`ZMod` identity through mathlib's `MonoidHom.toHomUnits`. What is *not* ported is that
`Gamma0MapUnits` definition itself: TauCeti does not have it, and it belongs with the `Gamma0Map`
API rather than with the Fricke conjugation.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ}

/-- **The `Γ₀(N)` divisibility, in the exact form the entry formula needs**: the lower-left entry
`c` of `σ` is `N` times the quotient `c / N`, that quotient being exact because `N ∣ c`.

Public because `coe_frickeConjSL` displays `c / N`, an `Int.ediv`: without this a consumer of that
`simp` lemma is left with an opaque quotient and has to re-derive `(N : ℤ) ∣ c` from `Gamma0_mem`
at every use site. This is the only place the `Γ₀(N)` divisibility is used. -/
@[simp]
public theorem natCast_mul_lowerLeft_ediv (σ : ↥(Gamma0 N)) :
    (N : ℤ) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (N : ℤ)) =
      (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
  Int.mul_ediv_cancel'
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp σ.property))

/-- **The Fricke conjugate** of `σ = !![a, b; N·c', d] ∈ Γ₀(N)`, as an element of `SL(2, ℤ)`:
the matrix `!![d, -c'; -N·b, a]`.

It is defined by its entries rather than as a product, so it exists at every level; the
conjugation it computes exists only at nonzero level, and at `N = 0` the value is junk — see the
`Level` section of the module docstring.

Over a field `K` with `(N : K) ≠ 0` this is `W · σ · W⁻¹`, and equally `W⁻¹ · σ · W` since
`W² = (-N) • 1` is central; that is the content of `frickeGL_mul_mapGL` and
`mapGL_mul_frickeGL`, which carry the invertibility hypothesis. At `N = 0` the formula still
defines a matrix, but a degenerate one; see the `Level` section of the module docstring. -/
public def frickeConjSL (σ : ↥(Gamma0 N)) : SL(2, ℤ) :=
  ⟨!![(σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (N : ℤ));
      -(N : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0], by
    have hc := (natCast_mul_lowerLeft_ediv σ).symm
    set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
    have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := fin_two_mul_sub_mul_eq_one (σ : SL(2, ℤ))
    rw [det_fin_two_of]
    linear_combination hdet + M 0 1 * hc⟩

/-- The underlying matrix of `frickeConjSL σ`, with the exact quotient `c / N` of the lower-left
entry `c` written out. -/
@[simp]
public theorem coe_frickeConjSL (σ : ↥(Gamma0 N)) :
    (frickeConjSL σ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (N : ℤ));
         -(N : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0] := by
  simp [frickeConjSL]

/-- **`frickeConjSL` preserves `Γ₀(N)`**: its lower-left entry `-N·b` is visibly divisible by
`N`. This maps `Γ₀(N)` into `Γ₀(N)` at every level; that `W` *normalizes* the subgroup is
`frickeConjGamma0MulEquiv`, which needs `[NeZero N]`. -/
public theorem frickeConjSL_mem_Gamma0 (σ : ↥(Gamma0 N)) :
    frickeConjSL σ ∈ Gamma0 N := by
  rw [Gamma0_mem, coe_frickeConjSL]
  simp

/-- **`frickeConjSL` preserves `Γ₁(N)`**: the formula swaps the two diagonal entries, so both
remain `≡ 1 (mod N)`. Note that this needs `σ ∈ Γ₁(N)`, not merely `σ ∈ Γ₀(N)`. As for `Γ₀(N)` it
maps the subgroup into itself at every level; normalization is `frickeConjGamma1MulEquiv`. -/
public theorem frickeConjSL_mem_Gamma1 (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N) :
    frickeConjSL ⟨σ, Gamma1_in_Gamma0 N hσ⟩ ∈ Gamma1 N := by
  obtain ⟨ha, hd, -⟩ := (Gamma1_mem N σ).mp hσ
  rw [Gamma1_mem, coe_frickeConjSL]
  exact ⟨by simpa using hd, by simpa using ha, by simp⟩

/-- The lower-left quotient of a product, from the quotients of the two factors. At level zero
both sides are `0`, the quotient being division by `0` there. -/
private theorem lowerLeft_ediv_mul (σ τ : ↥(Gamma0 N)) :
    ((σ * τ : ↥(Gamma0 N)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (N : ℤ) =
      (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (N : ℤ) * (τ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
        (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * ((τ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (N : ℤ)) := by
  rcases eq_or_ne (N : ℤ) 0 with hN | hN
  · simp [hN]
  · refine mul_left_cancel₀ hN ?_
    have hmul : ((σ * τ : ↥(Gamma0 N)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
        (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
          (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (norm := ring_nf) natCast_mul_lowerLeft_ediv (σ * τ) + hmul -
      (τ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * natCast_mul_lowerLeft_ediv σ -
      (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * natCast_mul_lowerLeft_ediv τ

/-- **`frickeConjSL` sends `1` to `1`**. -/
@[simp]
public theorem frickeConjSL_one : frickeConjSL (1 : ↥(Gamma0 N)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frickeConjSL]

/-- **`frickeConjSL` is multiplicative.** Conjugation by `W` is a group homomorphism, and the
entry formula records that at every level — including `N = 0`, where it is not a conjugation. -/
@[simp]
public theorem frickeConjSL_mul (σ τ : ↥(Gamma0 N)) :
    frickeConjSL (σ * τ) = frickeConjSL σ * frickeConjSL τ := by
  have hmul := lowerLeft_ediv_mul σ τ
  ext i j
  rw [SpecialLinearGroup.coe_mul, coe_frickeConjSL, coe_frickeConjSL, coe_frickeConjSL,
    Matrix.mul_fin_two]
  -- Name the two quotients once the entries are in place. They are then opaque, so the exactness
  -- lemma can be used in the expanding direction `c = N * c'` without rewriting inside the
  -- quotients themselves — which is what makes the entrywise computation terminate.
  set c := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (N : ℤ)
  set e := (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (N : ℤ)
  have hσ : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (N : ℤ) * c :=
    (natCast_mul_lowerLeft_ediv σ).symm
  have hτ : (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (N : ℤ) * e :=
    (natCast_mul_lowerLeft_ediv τ).symm
  -- Discharge the product's own quotient first. Left to `simp`, the entry `(σ * τ) 1 0` is
  -- expanded by `Matrix.mul_apply` instead, and the quotient that remains needs `N ≠ 0` to
  -- cancel — which this lemma does not assume, since it holds at every level.
  rw [hmul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hσ, hτ] <;>
    ring

/-- **The Fricke entry formula as a group endomorphism `Γ₀(N) →* Γ₀(N)`.** This is the bundled
form of `frickeConjSL_mem_Gamma0`, and it is what a consumer needs in order to transport a
subgroup along the map.

Like `frickeConjSL` it exists at every level, so on its own it records that the entry formula
preserves `Γ₀(N)` rather than that `W` normalizes it. At nonzero level it is an isomorphism,
`frickeConjGamma0MulEquiv`, and that is the declaration that states the normalization. -/
public def frickeConjGamma0 : ↥(Gamma0 N) →* ↥(Gamma0 N) where
  toFun σ := ⟨frickeConjSL σ, frickeConjSL_mem_Gamma0 σ⟩
  map_one' := Subtype.ext frickeConjSL_one
  map_mul' σ τ := Subtype.ext (frickeConjSL_mul σ τ)

/-- The `SL(2, ℤ)` matrix underlying `frickeConjGamma0 σ` is `frickeConjSL σ`: the
characterizing lemma for the bundled map. -/
@[simp]
public theorem coe_frickeConjGamma0 (σ : ↥(Gamma0 N)) :
    (frickeConjGamma0 σ : SL(2, ℤ)) = frickeConjSL σ :=
  (rfl)

/-- **The Fricke entry formula restricted to `Γ₁(N)`**, as a group endomorphism
`Γ₁(N) →* Γ₁(N)`; the `Γ₁` counterpart of `frickeConjGamma0`, bundling
`frickeConjSL_mem_Gamma1`, and like it defined at every level. -/
public def frickeConjGamma1 : ↥(Gamma1 N) →* ↥(Gamma1 N) where
  toFun σ := ⟨frickeConjSL ⟨σ, Gamma1_in_Gamma0 N σ.property⟩,
    frickeConjSL_mem_Gamma1 (σ : SL(2, ℤ)) σ.property⟩
  map_one' := Subtype.ext frickeConjSL_one
  map_mul' σ τ := Subtype.ext (frickeConjSL_mul ⟨σ, Gamma1_in_Gamma0 N σ.property⟩
    ⟨τ, Gamma1_in_Gamma0 N τ.property⟩)

/-- The `SL(2, ℤ)` matrix underlying `frickeConjGamma1 σ` is `frickeConjSL σ`: the
characterizing lemma for the bundled map, as `coe_frickeConjGamma0` is at level `Γ₀(N)`. -/
@[simp]
public theorem coe_frickeConjGamma1 (σ : ↥(Gamma1 N)) :
    (frickeConjGamma1 σ : SL(2, ℤ)) = frickeConjSL ⟨σ, Gamma1_in_Gamma0 N σ.property⟩ :=
  (rfl)

section NeZero

/-- The value of mathlib's `Gamma0Map` on a `Γ₀(N)` element: it is the lower-right entry, reduced.
`Gamma0Map` is a bare `MonoidHom.mk`, so this is definitional; naming it keeps the one
definitional step out of the `simp` sets below. -/
private theorem gamma0Map_apply (g : ↥(Gamma0 N)) :
    Gamma0Map N g = (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) := rfl

/-- **The Fricke conjugation inverts the diamond label.** `Gamma0Map` reads the lower-right entry
mod `N`; conjugation swaps the two diagonal entries, so it reads `a` where it read `d`, and
`a · d ≡ 1 (mod N)` because `det σ = 1` and `N ∣ c`.

Stated at the `ZMod` level, which is where `Gamma0Map` lands; the unit-valued form is
`toHomUnits_gamma0Map_frickeConjGamma0_eq_inv`, derived from this one. Without it a consumer
computing a nebentypus along the Fricke involution has to redo the determinant argument. -/
public theorem gamma0Map_frickeConjGamma0_mul (σ : ↥(Gamma0 N)) :
    Gamma0Map N (frickeConjGamma0 σ) * Gamma0Map N σ = 1 := by
  have hcast := intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 (M := N) σ.property
  simp only [gamma0Map_apply, coe_frickeConjGamma0, coe_frickeConjSL]
  simpa using hcast

/-- **The unit-valued form of `gamma0Map_frickeConjGamma0_mul`**: on units, the `Gamma0Map` image
of `frickeConjGamma0 σ` is the inverse of that of `σ`. This is the shape the diamond-character and
nebentypus consumers work in, obtained from the `ZMod` identity through Mathlib's
`MonoidHom.toHomUnits`. -/
@[simp]
public theorem toHomUnits_gamma0Map_frickeConjGamma0_eq_inv (σ : ↥(Gamma0 N)) :
    (Gamma0Map N).toHomUnits (frickeConjGamma0 σ) = ((Gamma0Map N).toHomUnits σ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  simpa [MonoidHom.coe_toHomUnits] using gamma0Map_frickeConjGamma0_mul σ

variable [NeZero N]

/-- **Applying the entry map twice is the identity, at nonzero level**, on `SL(2, ℤ)` itself:
this is the entrywise content of the involution, stated where a consumer holding a plain
`frickeConjSL σ` can use it without wrapping into `Γ₀(N)`. The two bundled involutions below are
`Subtype.ext` of this.

This genuinely needs `N ≠ 0`. At level zero the lower-left entry `-N·b` of `frickeConjSL σ` is
`0` whatever `b` is, so the formula forgets `b` and cannot be undone; see the `Level` section of
the module docstring. -/
-- The reason is that `W² = (-N) • 1` is central, so conjugating twice does nothing; the proof
-- below is the entrywise form of that over `ℤ`, with no `W` in sight.
public theorem frickeConjSL_frickeConjSL (σ : ↥(Gamma0 N)) :
    frickeConjSL ⟨frickeConjSL σ, frickeConjSL_mem_Gamma0 σ⟩ = (σ : SL(2, ℤ)) := by
  have hN : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)
  have hdiv : ((frickeConjSL σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (N : ℤ) =
      -(σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
    have hentry : ((frickeConjSL σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
        (N : ℤ) * -(σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
      rw [coe_frickeConjSL]
      simp
    rw [hentry, Int.mul_ediv_cancel_left _ hN]
  ext i j
  rw [coe_frickeConjSL, hdiv, coe_frickeConjSL]
  fin_cases i <;> fin_cases j <;> simp [natCast_mul_lowerLeft_ediv]

/-- **The Fricke conjugation is an involution at nonzero level**: applying it twice is the
identity on `Γ₀(N)`. This is `frickeConjSL_frickeConjSL` read through `Subtype.ext`. -/
@[simp]
public theorem frickeConjGamma0_frickeConjGamma0 (σ : ↥(Gamma0 N)) :
    frickeConjGamma0 (frickeConjGamma0 σ) = σ :=
  Subtype.ext (frickeConjSL_frickeConjSL σ)

/-- `frickeConjGamma0` is involutive, in the form `Function.Involutive` consumes. -/
public theorem frickeConjGamma0_involutive :
    Function.Involutive (frickeConjGamma0 (N := N)) :=
  frickeConjGamma0_frickeConjGamma0

/-- **The Fricke conjugation as an automorphism of `Γ₀(N)`**, for nonzero level: the isomorphism
`Γ₀(N) ≃* Γ₀(N)` that `frickeConjGamma0` becomes once it is known to be involutive. It is its
own inverse.

This is the declaration that expresses that `W` *normalizes* `Γ₀(N)`: `frickeConjGamma0` maps
the subgroup into itself at every level, and the level hypothesis is what upgrades that to an
isomorphism. -/
public def frickeConjGamma0MulEquiv : ↥(Gamma0 N) ≃* ↥(Gamma0 N) :=
  -- Mathlib's `Function.Involutive.toPerm` already supplies the `toFun = invFun`
  -- scaffolding; only multiplicativity is ours to add.
  { frickeConjGamma0_involutive.toPerm (frickeConjGamma0 (N := N)) with
    map_mul' := map_mul frickeConjGamma0 }

/-- `frickeConjGamma0MulEquiv` acts as `frickeConjGamma0`. This is its defining lemma and, with
`frickeConjGamma0MulEquiv_symm`, the intended interface: a consumer simplifies through these
rather than through the body of the bundled definition. -/
@[simp]
public theorem frickeConjGamma0MulEquiv_apply (σ : ↥(Gamma0 N)) :
    frickeConjGamma0MulEquiv σ = frickeConjGamma0 σ :=
  (rfl)

/-- **`frickeConjGamma0MulEquiv` is its own inverse.** The underlying map is an involution, so
`symm` returns the automorphism unchanged; this is the simp lemma that normalizes `e.symm`. -/
@[simp]
public theorem frickeConjGamma0MulEquiv_symm :
    (frickeConjGamma0MulEquiv (N := N)).symm = frickeConjGamma0MulEquiv :=
  (rfl)

/-- The `Γ₁(N)` counterpart of `frickeConjGamma0_frickeConjGamma0`. -/
@[simp]
-- Read off the value of `frickeConjGamma1` through `coe_frickeConjGamma1` and closed by the
-- `SL(2, ℤ)`-level involution, so this leans on no identification between two different bundled
-- maps. The one remaining definitional step is `coe_frickeConjGamma1` itself, which is `(rfl)`.
public theorem frickeConjGamma1_frickeConjGamma1 (σ : ↥(Gamma1 N)) :
    frickeConjGamma1 (frickeConjGamma1 σ) = σ :=
  Subtype.ext (frickeConjSL_frickeConjSL ⟨σ, Gamma1_in_Gamma0 N σ.property⟩)

/-- `frickeConjGamma1` is involutive, in the form `Function.Involutive` consumes. -/
public theorem frickeConjGamma1_involutive :
    Function.Involutive (frickeConjGamma1 (N := N)) :=
  frickeConjGamma1_frickeConjGamma1

/-- **The Fricke conjugation as an automorphism of `Γ₁(N)`**, for nonzero level; the `Γ₁`
counterpart of `frickeConjGamma0MulEquiv`. -/
public def frickeConjGamma1MulEquiv : ↥(Gamma1 N) ≃* ↥(Gamma1 N) :=
  -- Mathlib's `Function.Involutive.toPerm` already supplies the `toFun = invFun`
  -- scaffolding; only multiplicativity is ours to add.
  { frickeConjGamma1_involutive.toPerm (frickeConjGamma1 (N := N)) with
    map_mul' := map_mul frickeConjGamma1 }

/-- `frickeConjGamma1MulEquiv` acts as `frickeConjGamma1`; the `Γ₁(N)` counterpart of
`frickeConjGamma0MulEquiv_apply`. -/
@[simp]
public theorem frickeConjGamma1MulEquiv_apply (σ : ↥(Gamma1 N)) :
    frickeConjGamma1MulEquiv σ = frickeConjGamma1 σ :=
  (rfl)

/-- The `Γ₁(N)` counterpart of `frickeConjGamma0MulEquiv_symm`. -/
@[simp]
public theorem frickeConjGamma1MulEquiv_symm :
    (frickeConjGamma1MulEquiv (N := N)).symm = frickeConjGamma1MulEquiv :=
  (rfl)

end NeZero

section Field

variable (K : Type*) [Field K]

/-- The lower-left entry of `σ ∈ Γ₀(N)`, read in `K`, is `N` times the quotient `c / N`. The
`K`-valued form of `natCast_mul_lowerLeft_ediv`, which is what the entrywise computations below
consume. -/
private theorem lowerLeft_ediv_spec_field (σ : ↥(Gamma0 N)) :
    ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : K) =
      (N : K) * (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (N : ℤ) : ℤ) : K) := by
  exact_mod_cast congrArg (Int.cast : ℤ → K) (natCast_mul_lowerLeft_ediv σ).symm

variable [NeZero (N : K)]

/-- **The normalization identity** `W · σ = (W σ W⁻¹) · W` in `GL (Fin 2) K`, for `σ ∈ Γ₀(N)`.
This is the form that moves `W` from the left of `σ` to its right, which is what a slash-action
computation needs. -/
public theorem frickeGL_mul_mapGL (σ : ↥(Gamma0 N)) :
    frickeGL K N * mapGL K (σ : SL(2, ℤ)) = mapGL K (frickeConjSL σ) * frickeGL K N := by
  apply Units.ext
  have hc := lowerLeft_ediv_spec_field K σ
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    coe_mapGL_fin_two, coe_mapGL_fin_two, coe_frickeGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, coe_frickeConjSL, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, algebraMap_int_eq, Int.coe_castRingHom, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Int.cast_mul, Int.cast_neg, Int.cast_natCast, hc] <;>
    ring

/-- **`frickeConjSL σ` is the Fricke conjugate**, in the form the name asserts:
`mapGL K (frickeConjSL σ) = W · σ · W⁻¹`. This is `frickeGL_mul_mapGL` with `W` moved across,
and it is the characterization the `frickeConj*` names advertise. -/
public theorem mapGL_frickeConjSL (σ : ↥(Gamma0 N)) :
    mapGL K (frickeConjSL σ) = frickeGL K N * mapGL K (σ : SL(2, ℤ)) * (frickeGL K N)⁻¹ :=
  eq_mul_inv_of_mul_eq (frickeGL_mul_mapGL K σ).symm

/-- `W²` commutes with everything in `GL (Fin 2) K`: it is the scalar matrix `(-N) • 1`. -/
private theorem frickeGL_sq_mul_comm (A : GL (Fin 2) K) :
    frickeGL K N ^ 2 * A = A * frickeGL K N ^ 2 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_frickeGL_sq]
  simp

/-- **The mirror normalization identity** `σ · W = W · (W σ W⁻¹)` in `GL (Fin 2) K`, for
`σ ∈ Γ₀(N)`; equivalently `frickeConjSL σ = W⁻¹ · σ · W`. -/
-- `frickeGL_mul_mapGL` carried across `W²` rather than a second entrywise computation:
-- `(σ · W) · W = σ · W² = W² · σ = W · (W · σ) = W · (W σ W⁻¹) · W`, and `W` cancels on the right.
public theorem mapGL_mul_frickeGL (σ : ↥(Gamma0 N)) :
    mapGL K (σ : SL(2, ℤ)) * frickeGL K N = frickeGL K N * mapGL K (frickeConjSL σ) := by
  refine mul_right_cancel (b := frickeGL K N) ?_
  calc mapGL K (σ : SL(2, ℤ)) * frickeGL K N * frickeGL K N
      = frickeGL K N ^ 2 * mapGL K (σ : SL(2, ℤ)) := by
        rw [mul_assoc, ← sq, ← frickeGL_sq_mul_comm]
    _ = frickeGL K N * (frickeGL K N * mapGL K (σ : SL(2, ℤ))) := by rw [sq, mul_assoc]
    _ = frickeGL K N * (mapGL K (frickeConjSL σ) * frickeGL K N) := by
        rw [frickeGL_mul_mapGL]
    _ = frickeGL K N * mapGL K (frickeConjSL σ) * frickeGL K N := (mul_assoc _ _ _).symm

end Field

end TauCeti
