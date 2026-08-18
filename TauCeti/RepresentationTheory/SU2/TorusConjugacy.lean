/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.Matrix.UnitaryGroup
public import TauCeti.RepresentationTheory.SU2.Weyl.Basic

/-!
# Every element of `SU(2)` is conjugate into the maximal torus

The maximal torus `T` of `SU(2)` built in `TauCeti/RepresentationTheory/SU2/Basic.lean` meets
every conjugacy class: for every `g : SU(2)` there is `u : SU(2)` with `u g u⁻¹ ∈ T`. This is the
torus-conjugacy input the compact-group roadmap asks for before the classification of the
irreducible representations of `SU(2)`, and it is what makes a class function on `SU(2)`
determined by its restriction to the circle.

The proof is unitary diagonalisation, arranged so that it only needs Mathlib's spectral theorem
for *Hermitian* matrices. Mathlib has no spectral theorem for normal or unitary matrices, but in
`SU(2)` one is not needed: writing `G` for the matrix of `g`, the determinant condition forces the
Hermitian part of `G` to be a scalar,

`G + G* = (tr G) • 1`   (`TauCeti.SU2.coe_add_star`),

because `G* = G⁻¹` is the adjugate of `G` (`TauCeti.Matrix.specialUnitaryGroup.star_eq_adjugate`)
and a `2 × 2` matrix and its adjugate add up to the trace. So `G` differs from the Hermitian
matrix `H = i (G - G*)` by a scalar matrix, and any unitary that diagonalises `H` diagonalises
`G`. The eigenvector unitary supplied by the spectral theorem need not have determinant one, but
it can be rescaled by a scalar of modulus one until it does
(`TauCeti.Matrix.exists_circle_smul_mem_specialUnitaryGroup`), and rescaling by a scalar does not
change the conjugation it induces.

## Main results

* `TauCeti.SU2.exists_conj_mem_torus`: **torus conjugacy**, every element of `SU(2)` is conjugate
  into the maximal torus.
* `TauCeti.SU2.exists_isConj_torusHom` and `TauCeti.SU2.exists_isConj_torusExp`: the same
  statement read through the parametrisations of `T`, every element of `SU(2)` being conjugate to
  `diag (z, z⁻¹)` for some `z` on the circle, equivalently to `diag (e^{iθ}, e^{-iθ})` for some
  angle `θ`.
* `TauCeti.SU2.isConj_inv_of_mem_torus` and `TauCeti.SU2.isConj_torusExp_neg`: the Weyl reflection,
  every element of the torus is conjugate in `SU(2)` to its inverse. This is the conjugation by
  the quarter turn `TauCeti.SU2.weylElement` of `TauCeti/RepresentationTheory/SU2/Weyl/Basic.lean`
  (`TauCeti.SU2.weylElement_conj_torusHom`), read as an existential. With torus conjugacy it says
  every conjugacy class of `SU(2)` meets `T` in a nonempty set closed under inversion. The
  converse, that conjugate elements of `T` are equal or inverse, is
  `TauCeti.SU2.eq_or_eq_inv_of_conj_torusHom` of `TauCeti/RepresentationTheory/SU2/Basic.lean`.
* `TauCeti.SU2.isConj_torusHom_iff`: putting those two together, each conjugacy class of `SU(2)`
  meets `T` in exactly one orbit `{z, z⁻¹}` of the Weyl group computed in
  `TauCeti/RepresentationTheory/SU2/Weyl/Basic.lean`.
* `TauCeti.SU2.eq_of_conjInvariant_of_eqOn_torus` and
  `TauCeti.SU2.exists_conjInvariant_torusHom_eq`: restricting a class function on `SU(2)` to `T`
  is injective, and its image is exactly the functions on `T` invariant under the Weyl action.
  This is the identification of the class functions of `SU(2)` with the `W`-invariant functions
  on `T`.
-/

public section

namespace TauCeti

namespace SU2

/-! ### Torus conjugacy -/

/-- **Conjugating by `U` carries `a • 1 + b • H` to `a • 1 + b • (star U * H * U)`.** So whenever
`star U` is a left inverse of `U`, any `U` that diagonalises `H` also diagonalises every matrix of
that form: conjugation is linear, and it fixes the identity precisely because `star U * U = 1`. -/
private theorem isDiag_star_left_conjugate_of_eq_smul_one_add_smul {R n : Type*}
    [CommSemiring R] [Star R] [Fintype n] [DecidableEq n] {G H U : Matrix n n R} {a b : R}
    (hdecomp : G = a • (1 : Matrix n n R) + b • H)
    (hUU : star U * U = 1) (hdiagH : (star U * H * U).IsDiag) :
    (star U * G * U).IsDiag := by
  have hexpand : star U * G * U = a • (1 : Matrix n n R) + b • (star U * H * U) := by
    conv_lhs => rw [hdecomp]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [hUU]
  rw [hexpand]
  exact (Matrix.isDiag_one.smul _).add (hdiagH.smul _)

/-- **A special unitary matrix is a scalar plus a multiple of `I • (g - star g)`.** The identity
`g = (tr g / 2) • 1 + (-I / 2) • (I • (g - star g))` holds because `g + star g` is the scalar
`tr g`. -/
private theorem coe_eq_smul_one_add_smul_I_smul_sub_star (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ)
      = (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + (-Complex.I / 2) •
          (Complex.I • ((g : Matrix (Fin 2) (Fin 2) ℂ) - star (g : Matrix (Fin 2) (Fin 2) ℂ))) := by
  have hscalar : (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) / 2) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = (2⁻¹ : ℂ) • ((g : Matrix (Fin 2) (Fin 2) ℂ) + star (g : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [coe_add_star g, smul_smul]
    congr 1
    ring
  have hI : (-Complex.I / 2) * Complex.I = 2⁻¹ := by
    rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]
    norm_num
  rw [smul_smul, hI, hscalar]
  module

/-- **A unitary that diagonalises `g` rescales to a special unitary one.** Multiplying a unitary by
a unit-modulus scalar leaves the conjugate `star u * g * u` unchanged, and some such multiple is
special unitary, so `g` is conjugate into the torus inside `SU(2)`. -/
private theorem exists_conj_mem_torus_of_isDiag_star_left_conjugate (g : SU2)
    {U : Matrix.unitaryGroup (Fin 2) ℂ}
    (hdiagG : (star (U : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)
      * (U : Matrix (Fin 2) (Fin 2) ℂ)).IsDiag) :
    ∃ u : SU2, u * g * u⁻¹ ∈ torus := by
  obtain ⟨c, hc⟩ := Matrix.exists_circle_smul_mem_specialUnitaryGroup U
  obtain ⟨u, hu⟩ : ∃ u : SU2,
    (u : Matrix (Fin 2) (Fin 2) ℂ) = (c : ℂ) • (U : Matrix (Fin 2) (Fin 2) ℂ) := ⟨⟨_, hc⟩, rfl⟩
  refine ⟨u⁻¹, mem_torus_iff.mpr ?_⟩
  -- Inversion in `SU(2)` is `star`, which commutes with the coercion to matrices.
  have hcoe : ((u⁻¹ * g * (u⁻¹)⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
      = star (u : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)
        * (u : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [inv_inv, Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.star_eq_inv,
      Matrix.specialUnitaryGroup.coe_star]
  have hcmul : (c : ℂ) * star (c : ℂ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  rw [hcoe, hu]
  simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcmul, one_smul]
  exact hdiagG

/-- **Torus conjugacy for `SU(2)`**: every element of `SU(2)` is conjugate into the maximal torus.
Equivalently, every special unitary `2 × 2` matrix is diagonalised by a special unitary matrix. -/
theorem exists_conj_mem_torus (g : SU2) : ∃ u : SU2, u * g * u⁻¹ ∈ torus := by
  set G : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ)
  set H : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • (G - star G) with hHdef
  -- `H` is Hermitian: conjugating negates both `Complex.I` and `G - star G`.
  have hHerm : H.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSelfAdjoint, isSelfAdjoint_iff, hHdef, star_smul, star_sub,
      star_star, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]
  -- Mathlib's spectral theorem diagonalises `H` by a unitary matrix.
  obtain ⟨U, hdiagH⟩ : ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      (star (U : Matrix (Fin 2) (Fin 2) ℂ) * H * (U : Matrix (Fin 2) (Fin 2) ℂ)).IsDiag := by
    refine ⟨hHerm.eigenvectorUnitary, ?_⟩
    have h := hHerm.conjStarAlgAut_star_eigenvectorUnitary (𝕜 := ℂ)
    rw [Unitary.conjStarAlgAut_star_apply] at h
    rw [h]
    exact Matrix.isDiag_diagonal _
  -- `G` is a scalar plus a multiple of `H`, so that unitary diagonalises `G` too.
  exact exists_conj_mem_torus_of_isDiag_star_left_conjugate g
    (isDiag_star_left_conjugate_of_eq_smul_one_add_smul
      (coe_eq_smul_one_add_smul_I_smul_sub_star g) (Matrix.UnitaryGroup.star_mul_self U) hdiagH)

/-- Every element of `SU(2)` is conjugate to the torus element `diag (z, z⁻¹)` for some point `z`
of the circle: `TauCeti.SU2.exists_conj_mem_torus` read through the parametrisation
`TauCeti.SU2.torusHom` of the maximal torus. -/
theorem exists_isConj_torusHom (g : SU2) : ∃ z : Circle, IsConj g (torusHom z) := by
  obtain ⟨u, hu⟩ := exists_conj_mem_torus g
  obtain ⟨z, hz⟩ := mem_torus_iff_exists_torusHom.mp hu
  exact ⟨z, isConj_iff.mpr ⟨u, hz.symm⟩⟩

/-- Every element of `SU(2)` is conjugate to the torus element `diag (e^{iθ}, e^{-iθ})` for some
angle `θ`. This is `TauCeti.SU2.exists_isConj_torusHom` in the angle parametrisation. -/
theorem exists_isConj_torusExp (g : SU2) : ∃ θ : ℝ, IsConj g (torusExp θ) := by
  obtain ⟨z, hz⟩ := exists_isConj_torusHom g
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
  exact ⟨θ, by rwa [torusExp_def]⟩

/-! ### The Weyl reflection -/

/-- The Weyl group of `SU(2)` acts on the maximal torus by inversion: every element of the torus
is conjugate in `SU(2)` to its inverse, by the quarter turn `TauCeti.SU2.weylElement` that swaps
the two coordinate axes. Together with `TauCeti.SU2.exists_conj_mem_torus` this says that every
conjugacy class of `SU(2)` meets the torus in a nonempty set closed under inversion. -/
theorem isConj_inv_of_mem_torus {g : SU2} (hg : g ∈ torus) : IsConj g g⁻¹ := by
  obtain ⟨z, rfl⟩ := mem_torus_iff_exists_torusHom.mp hg
  exact isConj_iff.mpr ⟨weylElement, by rw [weylElement_conj_torusHom, map_inv]⟩

/-- Every element of the maximal torus is conjugate to its inverse in the angle parametrisation:
`diag (e^{iθ}, e^{-iθ})` and `diag (e^{-iθ}, e^{iθ})` are conjugate in `SU(2)`. -/
theorem isConj_torusExp_neg (θ : ℝ) : IsConj (torusExp θ) (torusExp (-θ)) := by
  rw [torusExp_neg]
  exact isConj_inv_of_mem_torus (torusExp_mem_torus θ)

/-! ### Conjugacy on the maximal torus -/

/-- **Each conjugacy class of `SU(2)` meets the maximal torus in exactly one Weyl orbit:** two
torus elements are conjugate in `SU(2)` precisely when they are equal or inverse. The forward
direction is `TauCeti.SU2.eq_or_eq_inv_of_conj_torusHom` and the backward direction is the Weyl
reflection `TauCeti.SU2.isConj_inv_of_mem_torus`. -/
theorem isConj_torusHom_iff {z w : Circle} :
    IsConj (torusHom z) (torusHom w) ↔ w = z ∨ w = z⁻¹ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := isConj_iff.mp h
    exact eq_or_eq_inv_of_conj_torusHom hu
  · rintro (rfl | rfl)
    · exact IsConj.refl _
    · rw [map_inv]
      exact isConj_inv_of_mem_torus (torusHom_mem_torus z)

/-! ### Class functions -/

/-- A class function on `SU(2)` is determined by its restriction to the maximal torus: two
conjugation-invariant functions that agree on `T` agree everywhere. -/
theorem eq_of_conjInvariant_of_eqOn_torus {α : Type*} {f₁ f₂ : SU2 → α}
    (h₁ : ∀ u g : SU2, f₁ (u * g * u⁻¹) = f₁ g) (h₂ : ∀ u g : SU2, f₂ (u * g * u⁻¹) = f₂ g)
    (h : Set.EqOn f₁ f₂ (torus : Set SU2)) : f₁ = f₂ := by
  funext g
  obtain ⟨u, hu⟩ := exists_conj_mem_torus g
  rw [← h₁ u g, ← h₂ u g]
  exact h hu

/-- **Every Weyl-invariant function on the maximal torus is the restriction of a class function
on `SU(2)`:** a function on the circle that takes the same value at `z` and at `z⁻¹` extends to a
conjugation-invariant function on `SU(2)`. The extension sends `g` to the value of the given
function at any torus element `g` is conjugate to
(`TauCeti.SU2.exists_isConj_torusHom`), which is well defined because two such torus elements are
equal or inverse (`TauCeti.SU2.isConj_torusHom_iff`). Together with the uniqueness statement
`TauCeti.SU2.eq_of_conjInvariant_of_eqOn_torus` this identifies the class functions of `SU(2)`
with the `W`-invariant functions on `T`. -/
theorem exists_conjInvariant_torusHom_eq {α : Type*} {φ : Circle → α}
    (hφ : ∀ z : Circle, φ z⁻¹ = φ z) :
    ∃ f : SU2 → α, (∀ u g : SU2, f (u * g * u⁻¹) = f g) ∧ ∀ z : Circle, f (torusHom z) = φ z := by
  -- The chosen torus element is only well defined up to the Weyl action, which `φ` cannot see.
  have key : ∀ {g : SU2} {z : Circle}, IsConj g (torusHom z) →
      φ (exists_isConj_torusHom g).choose = φ z := fun {g z} hz => by
    rcases isConj_torusHom_iff.mp
      ((exists_isConj_torusHom g).choose_spec.symm.trans hz) with h' | h'
    · rw [h']
    · rw [h', hφ]
  refine ⟨fun g => φ (exists_isConj_torusHom g).choose, fun u g => ?_, fun z => ?_⟩
  · exact key ((isConj_iff.mpr ⟨u, rfl⟩).symm.trans (exists_isConj_torusHom g).choose_spec)
  · exact key (IsConj.refl (torusHom z))

end SU2

end TauCeti
