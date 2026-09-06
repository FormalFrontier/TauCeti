/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.AtkinLehner
public import TauCeti.NumberTheory.HeckeRing.LinearExtension
public import TauCeti.NumberTheory.HeckeRing.Multiplicity.Equiv
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Composition
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.ModularForm
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.One

/-!
# The Hecke-ring action on nebentypus spaces

The twisted slash operators give a right action, so composing the operators attached to `D₁`
and `D₂` naturally produces the right-coset collision coefficient
`m(D₂⁻¹, D₁⁻¹; D⁻¹)`. The multiplication of the Hecke ring instead uses
`m(D₁, D₂; D)`. This file reconciles the two conventions using the Atkin–Lehner
anti-involution of `Γ₀(N)`: composing it with inversion is an ambient automorphism preserving
`Γ₀(N)`, and the Atkin–Lehner bar fixes every `Γ₀(N)` double coset.

The resulting basis identity extends by linearity to an anti-homomorphism. Since the `Γ₀(N)`
Hecke ring is commutative, this is a ring homomorphism. The construction is given first on the
function character space on which composition was proved, and then on the bundled modular-form
and cusp-form character spaces.

## Main definitions

* `HeckeRing.GL2.heckeRingHomFunctionCharSpace`: the Hecke-ring action on twisted-invariant
  functions.
* `HeckeRing.GL2.heckeRingHomCharSpace`: the action on modular forms of nebentypus `χ`.
* `HeckeRing.GL2.heckeRingHomCuspCharSpace`: its restriction to cusp forms.

## Provenance

The final ring-homomorphism packaging is adapted from AINTLIB's
`LeanModularForms/HeckeRIngs/GL2/Unified/NebentypusHeckeRingHom.lean`, declaration
`heckeRingHomCharSpace` (Chris Birkbeck, Apache-2.0), at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`. The convention bridge is new: AINTLIB proves its
composition formula directly with the Hecke-ring structure constants, while this repository's
right-coset composition theorem first exposes the reversed, inverted multiplicity.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn
open scoped MatrixGroups ModularForm HeckeCosetModule Pointwise

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) [NeZero N]

attribute [local instance] Fintype.ofFinite

local notation "Γ₀Q(" N ")" => Subgroup.map (mapGL ℚ) (Gamma0 N)
local notation "Coset₀(" N ")" => HeckeCoset (Delta0 N) (Γ₀Q(N)) (Γ₀Q(N))

/-- The Atkin-Lehner bar of a coset's chosen representative stays inside that coset. -/
private lemma bar_out_mem_doubleCoset_rep (D : Coset₀(N)) :
    ((atkinLehnerAntiInvolution N).bar D.out D.out.2 : GL (Fin 2) ℚ) ∈
      doubleCoset (D.rep : GL (Fin 2) ℚ) (Γ₀Q(N)) (Γ₀Q(N)) := by
  rw [HeckeCoset.rep_def]
  exact atkinLehnerAntiInvolution_bar_mem_doubleCoset N D.out D.out.2

/-- The reversed, inverted multiplicity from a right slash action is the ordinary `Γ₀(N)`
Hecke-ring structure constant. -/
theorem multiplicity_inv_reverse_eq (D₁ D₂ D : Coset₀(N)) :
    multiplicity (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        (D₂.out : GL (Fin 2) ℚ)⁻¹ (D₁.out : GL (Fin 2) ℚ)⁻¹
          (D.out : GL (Fin 2) ℚ)⁻¹ =
      multiplicity (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        (D₁.rep : GL (Fin 2) ℚ) (D₂.rep : GL (Fin 2) ℚ) (D.rep : GL (Fin 2) ℚ) := by
  let ι := atkinLehnerAntiInvolution N
  let b₁ : Delta0 N := ⟨ι.bar D₁.out D₁.out.2, ι.bar_mem_Δ _ D₁.out.2⟩
  let b₂ : Delta0 N := ⟨ι.bar D₂.out D₂.out.2, ι.bar_mem_Δ _ D₂.out.2⟩
  let b : Delta0 N := ⟨ι.bar D.out D.out.2, ι.bar_mem_Δ _ D.out.2⟩
  have hmap := multiplicity_map_equiv (atkinLehnerAutomorphism N)
    (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N)) (D₂.out : GL (Fin 2) ℚ)⁻¹
      (D₁.out : GL (Fin 2) ℚ)⁻¹ (D.out : GL (Fin 2) ℚ)⁻¹
  have hfix := atkinLehnerAntiInvolution_onHeckeCoset_eq_self N
  have hcomm (a c d : Delta0 N) :
      multiplicity (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
          (a : GL (Fin 2) ℚ) (c : GL (Fin 2) ℚ) (d : GL (Fin 2) ℚ) =
        multiplicity (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
          (c : GL (Fin 2) ℚ) (a : GL (Fin 2) ℚ) (d : GL (Fin 2) ℚ) :=
    ι.multiplicity_comm hfix a c d
  rw [atkinLehnerAutomorphism_map_Gamma0] at hmap
  rw [atkinLehnerAutomorphism_inv_apply N D₂.out.2,
    atkinLehnerAutomorphism_inv_apply N D₁.out.2,
    atkinLehnerAutomorphism_inv_apply N D.out.2] at hmap
  calc
    _ = multiplicity (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        (b₂ : GL (Fin 2) ℚ) (b₁ : GL (Fin 2) ℚ) (b : GL (Fin 2) ℚ) := hmap.symm
    _ = multiplicity (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        (b₂ : GL (Fin 2) ℚ) (b₁ : GL (Fin 2) ℚ) (D.rep : GL (Fin 2) ℚ) :=
      multiplicity_doubleCoset_congr _ _ (bar_out_mem_doubleCoset_rep D)
    _ = multiplicity (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        (b₁ : GL (Fin 2) ℚ) (b₂ : GL (Fin 2) ℚ) (D.rep : GL (Fin 2) ℚ) :=
      hcomm b₂ b₁ D.rep
    _ = multiplicity (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        (b₁ : GL (Fin 2) ℚ) (D₂.rep : GL (Fin 2) ℚ) (D.rep : GL (Fin 2) ℚ) :=
      multiplicity_doubleCoset_congr_second (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        b₁ D.rep (bar_out_mem_doubleCoset_rep D₂)
    _ = multiplicity (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        (D₂.rep : GL (Fin 2) ℚ) (b₁ : GL (Fin 2) ℚ) (D.rep : GL (Fin 2) ℚ) :=
      (hcomm D₂.rep b₁ D.rep).symm
    _ = multiplicity (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        (D₂.rep : GL (Fin 2) ℚ) (D₁.rep : GL (Fin 2) ℚ) (D.rep : GL (Fin 2) ℚ) :=
      multiplicity_doubleCoset_congr_second (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        D₂.rep D.rep (bar_out_mem_doubleCoset_rep D₁)
    _ = _ := hcomm D₂.rep D₁.rep D.rep

open Classical in
/-- The double cosets met by pairs of right-coset representatives are exactly the support of
the Hecke-ring structure constants. -/
private lemma image_pairCoset_eq_support_structureConstants (D₁ D₂ : Coset₀(N)) :
    Finset.univ.image (pairCoset D₁ D₂) =
      (HeckeCosetModule.structureConstants ℤ (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        D₁.rep D₂.rep).support := by
  ext D
  simp only [Finset.mem_image, Finset.mem_univ, true_and,
    HeckeCosetModule.mem_support_iff, HeckeCosetModule.structureConstants_apply,
    Nat.cast_ne_zero]
  constructor
  · rintro ⟨p, hp⟩
    have hx := pairCoset_eq_iff.mp hp
    have hcard := card_pairs_pairCoset_rightCoset_eq_multiplicity (D₁ := D₁) (D₂ := D₂) hx
    have : Nonempty {i : {q // pairCoset D₁ D₂ q = D} //
        MulOpposite.op (rightCosetRep D₁ i.1.1 * rightCosetRep D₂ i.1.2) •
            ((Γ₀Q(N)) : Set (GL (Fin 2) ℚ)) =
          MulOpposite.op (rightCosetRep D₁ p.1 * rightCosetRep D₂ p.2) •
            ((Γ₀Q(N)) : Set (GL (Fin 2) ℚ))} :=
      ⟨⟨⟨p, hp⟩, rfl⟩⟩
    have hne : multiplicity (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        (D₂.out : GL (Fin 2) ℚ)⁻¹ (D₁.out : GL (Fin 2) ℚ)⁻¹
          (D.out : GL (Fin 2) ℚ)⁻¹ ≠ 0 := by
      rw [← hcard]
      exact (Nat.card_pos (α := {i : {q // pairCoset D₁ D₂ q = D} //
        MulOpposite.op (rightCosetRep D₁ i.1.1 * rightCosetRep D₂ i.1.2) •
            ((Γ₀Q(N)) : Set (GL (Fin 2) ℚ)) =
          MulOpposite.op (rightCosetRep D₁ p.1 * rightCosetRep D₂ p.2) •
            ((Γ₀Q(N)) : Set (GL (Fin 2) ℚ))})).ne'
    rwa [multiplicity_inv_reverse_eq D₁ D₂ D] at hne
  · intro hne
    have hne' : multiplicity (Γ₀Q(N)) (Γ₀Q(N)) (Γ₀Q(N))
        (D₂.out : GL (Fin 2) ℚ)⁻¹ (D₁.out : GL (Fin 2) ℚ)⁻¹
          (D.out : GL (Fin 2) ℚ)⁻¹ ≠ 0 := by
      rwa [multiplicity_inv_reverse_eq D₁ D₂ D]
    have hcard := card_pairs_pairCoset_rightCoset_eq_multiplicity (D₁ := D₁) (D₂ := D₂)
      (mem_doubleCoset_self (Γ₀Q(N)) (Γ₀Q(N)) (D.out : GL (Fin 2) ℚ))
    have hcardne : Nat.card {i : {q // pairCoset D₁ D₂ q = D} //
        MulOpposite.op (rightCosetRep D₁ i.1.1 * rightCosetRep D₂ i.1.2) •
            ((Γ₀Q(N)) : Set (GL (Fin 2) ℚ)) =
          MulOpposite.op (D.out : GL (Fin 2) ℚ) •
            ((Γ₀Q(N)) : Set (GL (Fin 2) ℚ))} ≠ 0 := by
      rwa [hcard]
    obtain ⟨i⟩ := (Nat.card_ne_zero.mp hcardne).1
    exact ⟨i.1.1, i.1.2⟩

/-- The linear extension of the twisted slash action is anti-multiplicative on Hecke-ring basis
elements. -/
private theorem twistedHeckeSlashRingCharLinearMap_map_mul_reverse_single
    (D₁ D₂ : Coset₀(N)) :
    twistedHeckeSlashRingCharLinearMap k χ
        (HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1) =
      twistedHeckeSlashRingCharLinearMap k χ (HeckeCosetModule.single ℤ D₂ 1) *
        twistedHeckeSlashRingCharLinearMap k χ (HeckeCosetModule.single ℤ D₁ 1) := by
  rw [HeckeCosetModule.single_mul_single]
  rw [map_smul, map_smul, one_smul, one_smul]
  rw [
    twistedHeckeSlashRingCharLinearMap_single, twistedHeckeSlashRingCharLinearMap_single,
    one_smul, one_smul, twistedHeckeSlashSumCharEnd_mul_eq_sum_nsmul]
  rw [twistedHeckeSlashRingCharLinearMap_apply]
  rw [HeckeCosetModule.sum_def, ← image_pairCoset_eq_support_structureConstants D₁ D₂]
  refine Finset.sum_congr rfl fun D _ ↦ ?_
  rw [HeckeCosetModule.structureConstants_apply, ← multiplicity_inv_reverse_eq D₁ D₂ D]
  exact Nat.cast_smul_eq_nsmul ℤ _ _

/-- The linear extension of the twisted slash action is anti-multiplicative. This is the order
forced by a right action and multiplication by composition in `Module.End`. -/
theorem twistedHeckeSlashRingCharLinearMap_map_mul_reverse
    (S T : 𝕋 (Delta0 N) (Γ₀Q(N)) ℤ) :
    twistedHeckeSlashRingCharLinearMap k χ (S * T) =
      twistedHeckeSlashRingCharLinearMap k χ T *
        twistedHeckeSlashRingCharLinearMap k χ S :=
  LinearMap.map_mul_reverse_of_basis (twistedHeckeSlashRingCharLinearMap k χ)
    (twistedHeckeSlashRingCharLinearMap_map_mul_reverse_single k χ) S T

/-- The linear extension is multiplicative. Anti-multiplicativity becomes multiplicativity
because the `Γ₀(N)` Hecke ring is commutative. -/
theorem twistedHeckeSlashRingCharLinearMap_map_mul
    (S T : 𝕋 (Delta0 N) (Γ₀Q(N)) ℤ) :
    twistedHeckeSlashRingCharLinearMap k χ (S * T) =
      twistedHeckeSlashRingCharLinearMap k χ S *
        twistedHeckeSlashRingCharLinearMap k χ T := by
  rw [HeckeCosetModule.mul_comm_of_antiInvolution ℤ (atkinLehnerAntiInvolution N)
    (atkinLehnerAntiInvolution_onHeckeCoset_eq_self N) S T]
  exact twistedHeckeSlashRingCharLinearMap_map_mul_reverse k χ T S

/-- The integral `Γ₀(N)` Hecke ring acts on the space of `χ`-invariant functions. -/
noncomputable def heckeRingHomFunctionCharSpace :
    𝕋 (Delta0 N) (Γ₀Q(N)) ℤ →+* Module.End ℂ (functionCharSpace k χ) where
  toFun := twistedHeckeSlashRingCharLinearMap k χ
  map_zero' := (twistedHeckeSlashRingCharLinearMap k χ).map_zero
  map_one' := twistedHeckeSlashRingCharLinearMap_one k χ
  map_add' := (twistedHeckeSlashRingCharLinearMap k χ).map_add
  map_mul' := twistedHeckeSlashRingCharLinearMap_map_mul k χ

/-- The function-space Hecke action has the original linear extension as its underlying map. -/
@[simp] lemma heckeRingHomFunctionCharSpace_apply (T : 𝕋 (Delta0 N) (Γ₀Q(N)) ℤ) :
    heckeRingHomFunctionCharSpace k χ T = twistedHeckeSlashRingCharLinearMap k χ T :=
  (rfl)

/-- The `ℤ`-linear extension of the twisted operators on modular forms of nebentypus `χ`. -/
noncomputable def twistedHeckeSlashModularFormCharLinearMap :
    𝕋 (Delta0 N) (Γ₀Q(N)) ℤ →ₗ[ℤ] Module.End ℂ (modFormCharSpace k χ) :=
  Finsupp.linearCombination ℤ fun D ↦ twistedHeckeSlashModularFormCharEnd k χ D

/-- The modular-form linear extension on a basis element. -/
@[simp] lemma twistedHeckeSlashModularFormCharLinearMap_single (D : Coset₀(N)) (c : ℤ) :
    twistedHeckeSlashModularFormCharLinearMap k χ (HeckeCosetModule.single ℤ D c) =
      c • twistedHeckeSlashModularFormCharEnd k χ D :=
  (Finsupp.linearCombination_apply (R := ℤ)
    (v := fun D ↦ twistedHeckeSlashModularFormCharEnd k χ D) _).trans
    (HeckeCosetModule.sum_single_index ℤ (zero_smul _ _))

/-- On underlying functions, the modular-form extension is the function-space extension. -/
@[simp] lemma coe_twistedHeckeSlashModularFormCharLinearMap
    (T : 𝕋 (Delta0 N) (Γ₀Q(N)) ℤ) (f : modFormCharSpace k χ) :
    ⇑((twistedHeckeSlashModularFormCharLinearMap k χ T f :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      (twistedHeckeSlashRingCharLinearMap k χ T
        ⟨⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
          (coe_mem_functionCharSpace_iff k χ _).mpr f.2⟩ : functionCharSpace k χ) := by
  induction T using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd S T hS hT =>
      rw [map_add, map_add]
      simpa only [LinearMap.add_apply, Submodule.coe_add, FunLike.coe_add, Pi.add_apply] using
        congrArg₂ (· + ·) hS hT
  | hsingle D c =>
      rw [twistedHeckeSlashModularFormCharLinearMap_single,
        twistedHeckeSlashRingCharLinearMap_single]
      ext τ
      -- Scalar multiplication is bundled independently on `Module.End`, the character
      -- submodule, `ModularForm`, and functions. After evaluating at `τ`, `change` only exposes
      -- those coercions; the two named `coe_...` lemmas then supply the substantive equality.
      change c • (⇑((twistedHeckeSlashModularFormCharEnd k χ D f :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) : ℍ → ℂ) τ =
          c • (twistedHeckeSlashSumCharEnd k χ D
            ⟨⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
              (coe_mem_functionCharSpace_iff k χ _).mpr f.2⟩ : ℍ → ℂ) τ
      rw [coe_twistedHeckeSlashModularFormCharEnd, coe_twistedHeckeSlashSumCharEnd]

/-- The modular-form extension sends one to the identity endomorphism. -/
@[simp] theorem twistedHeckeSlashModularFormCharLinearMap_one :
    twistedHeckeSlashModularFormCharLinearMap k χ 1 = 1 := by
  refine LinearMap.ext fun f ↦ Subtype.ext (ModularForm.ext fun τ ↦ ?_)
  have h := congrFun (coe_twistedHeckeSlashModularFormCharLinearMap k χ 1 f) τ
  simpa only [twistedHeckeSlashRingCharLinearMap_one, Module.End.one_apply] using h

/-- The modular-form extension is multiplicative. -/
theorem twistedHeckeSlashModularFormCharLinearMap_map_mul
    (S T : 𝕋 (Delta0 N) (Γ₀Q(N)) ℤ) :
    twistedHeckeSlashModularFormCharLinearMap k χ (S * T) =
      twistedHeckeSlashModularFormCharLinearMap k χ S *
        twistedHeckeSlashModularFormCharLinearMap k χ T := by
  refine LinearMap.ext fun f ↦ Subtype.ext (ModularForm.ext fun τ ↦ ?_)
  let f₀ : functionCharSpace k χ :=
    ⟨⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      (coe_mem_functionCharSpace_iff k χ _).mpr f.2⟩
  let Tf := twistedHeckeSlashModularFormCharLinearMap k χ T f
  let Tf₀ : functionCharSpace k χ :=
    ⟨⇑(Tf : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      (coe_mem_functionCharSpace_iff k χ _).mpr Tf.2⟩
  have hT : Tf₀ = twistedHeckeSlashRingCharLinearMap k χ T f₀ :=
    Subtype.ext (coe_twistedHeckeSlashModularFormCharLinearMap k χ T f)
  calc
    _ = (twistedHeckeSlashRingCharLinearMap k χ (S * T) f₀ : ℍ → ℂ) τ :=
      congrFun (coe_twistedHeckeSlashModularFormCharLinearMap k χ (S * T) f) τ
    _ = ((twistedHeckeSlashRingCharLinearMap k χ S *
        twistedHeckeSlashRingCharLinearMap k χ T) f₀ : ℍ → ℂ) τ := by
      rw [twistedHeckeSlashRingCharLinearMap_map_mul]
    _ = (twistedHeckeSlashRingCharLinearMap k χ S Tf₀ : ℍ → ℂ) τ := by
      rw [hT, Module.End.mul_apply]
    _ = _ := (congrFun
      (coe_twistedHeckeSlashModularFormCharLinearMap k χ S Tf) τ).symm

/-- The integral `Γ₀(N)` Hecke ring acts on modular forms of weight `k` and nebentypus `χ`. -/
noncomputable def heckeRingHomCharSpace :
    𝕋 (Delta0 N) (Γ₀Q(N)) ℤ →+* Module.End ℂ (modFormCharSpace k χ) where
  toFun := twistedHeckeSlashModularFormCharLinearMap k χ
  map_zero' := (twistedHeckeSlashModularFormCharLinearMap k χ).map_zero
  map_one' := twistedHeckeSlashModularFormCharLinearMap_one k χ
  map_add' := (twistedHeckeSlashModularFormCharLinearMap k χ).map_add
  map_mul' := twistedHeckeSlashModularFormCharLinearMap_map_mul k χ

/-- The modular-form Hecke action evaluates through its underlying linear extension. -/
@[simp] lemma heckeRingHomCharSpace_apply (T : 𝕋 (Delta0 N) (Γ₀Q(N)) ℤ) :
    heckeRingHomCharSpace k χ T = twistedHeckeSlashModularFormCharLinearMap k χ T :=
  (rfl)

/-- The `ℤ`-linear extension of the twisted operators on cusp forms of nebentypus `χ`. -/
noncomputable def twistedHeckeSlashCuspFormCharLinearMap :
    𝕋 (Delta0 N) (Γ₀Q(N)) ℤ →ₗ[ℤ] Module.End ℂ (cuspFormCharSpace k χ) :=
  Finsupp.linearCombination ℤ fun D ↦ twistedHeckeSlashCuspFormCharEnd k χ D

/-- The cusp-form linear extension on a basis element. -/
@[simp] lemma twistedHeckeSlashCuspFormCharLinearMap_single (D : Coset₀(N)) (c : ℤ) :
    twistedHeckeSlashCuspFormCharLinearMap k χ (HeckeCosetModule.single ℤ D c) =
      c • twistedHeckeSlashCuspFormCharEnd k χ D :=
  (Finsupp.linearCombination_apply (R := ℤ)
    (v := fun D ↦ twistedHeckeSlashCuspFormCharEnd k χ D) _).trans
    (HeckeCosetModule.sum_single_index ℤ (zero_smul _ _))

/-- On underlying functions, the cusp-form extension is the function-space extension. -/
@[simp] lemma coe_twistedHeckeSlashCuspFormCharLinearMap
    (T : 𝕋 (Delta0 N) (Γ₀Q(N)) ℤ) (f : cuspFormCharSpace k χ) :
    ⇑((twistedHeckeSlashCuspFormCharLinearMap k χ T f :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      (twistedHeckeSlashRingCharLinearMap k χ T
        ⟨⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
          (coe_mem_functionCharSpace_iff k χ
            ((f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
              ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).mpr
            ((coe_mem_modFormCharSpace_iff k χ _).mpr f.2)⟩ : functionCharSpace k χ) := by
  induction T using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd S T hS hT =>
      rw [map_add, map_add]
      simpa only [LinearMap.add_apply, Submodule.coe_add, FunLike.coe_add, Pi.add_apply] using
        congrArg₂ (· + ·) hS hT
  | hsingle D c =>
      rw [twistedHeckeSlashCuspFormCharLinearMap_single,
        twistedHeckeSlashRingCharLinearMap_single]
      ext τ
      -- As in the modular-form proof, this exposes only the four bundled scalar/coercion
      -- layers after evaluation; the explicit coercion lemmas prove the mathematical step.
      change c • (⇑((twistedHeckeSlashCuspFormCharEnd k χ D f :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) : ℍ → ℂ) τ =
          c • (twistedHeckeSlashSumCharEnd k χ D
            ⟨⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
              (coe_mem_functionCharSpace_iff k χ
                ((f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
                  ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).mpr
                ((coe_mem_modFormCharSpace_iff k χ _).mpr f.2)⟩ : ℍ → ℂ) τ
      rw [coe_twistedHeckeSlashCuspFormCharEnd, coe_twistedHeckeSlashSumCharEnd]

/-- The cusp-form extension sends one to the identity endomorphism. -/
@[simp] theorem twistedHeckeSlashCuspFormCharLinearMap_one :
    twistedHeckeSlashCuspFormCharLinearMap k χ 1 = 1 := by
  refine LinearMap.ext fun f ↦ Subtype.ext (CuspForm.ext fun τ ↦ ?_)
  have h := congrFun (coe_twistedHeckeSlashCuspFormCharLinearMap k χ 1 f) τ
  simpa only [twistedHeckeSlashRingCharLinearMap_one, Module.End.one_apply] using h

/-- The cusp-form extension is multiplicative. -/
theorem twistedHeckeSlashCuspFormCharLinearMap_map_mul
    (S T : 𝕋 (Delta0 N) (Γ₀Q(N)) ℤ) :
    twistedHeckeSlashCuspFormCharLinearMap k χ (S * T) =
      twistedHeckeSlashCuspFormCharLinearMap k χ S *
        twistedHeckeSlashCuspFormCharLinearMap k χ T := by
  refine LinearMap.ext fun f ↦ Subtype.ext (CuspForm.ext fun τ ↦ ?_)
  let f₀ : functionCharSpace k χ :=
    ⟨⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      (coe_mem_functionCharSpace_iff k χ
        ((f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
          ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).mpr
        ((coe_mem_modFormCharSpace_iff k χ _).mpr f.2)⟩
  let Tf := twistedHeckeSlashCuspFormCharLinearMap k χ T f
  let Tf₀ : functionCharSpace k χ :=
    ⟨⇑(Tf : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      (coe_mem_functionCharSpace_iff k χ
        ((Tf : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
          ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).mpr
        ((coe_mem_modFormCharSpace_iff k χ _).mpr Tf.2)⟩
  have hT : Tf₀ = twistedHeckeSlashRingCharLinearMap k χ T f₀ :=
    Subtype.ext (coe_twistedHeckeSlashCuspFormCharLinearMap k χ T f)
  calc
    _ = (twistedHeckeSlashRingCharLinearMap k χ (S * T) f₀ : ℍ → ℂ) τ :=
      congrFun (coe_twistedHeckeSlashCuspFormCharLinearMap k χ (S * T) f) τ
    _ = ((twistedHeckeSlashRingCharLinearMap k χ S *
        twistedHeckeSlashRingCharLinearMap k χ T) f₀ : ℍ → ℂ) τ := by
      rw [twistedHeckeSlashRingCharLinearMap_map_mul]
    _ = (twistedHeckeSlashRingCharLinearMap k χ S Tf₀ : ℍ → ℂ) τ := by
      rw [hT, Module.End.mul_apply]
    _ = _ := (congrFun
      (coe_twistedHeckeSlashCuspFormCharLinearMap k χ S Tf) τ).symm

/-- The integral `Γ₀(N)` Hecke ring acts on cusp forms of weight `k` and nebentypus `χ`. -/
noncomputable def heckeRingHomCuspCharSpace :
    𝕋 (Delta0 N) (Γ₀Q(N)) ℤ →+* Module.End ℂ (cuspFormCharSpace k χ) where
  toFun := twistedHeckeSlashCuspFormCharLinearMap k χ
  map_zero' := (twistedHeckeSlashCuspFormCharLinearMap k χ).map_zero
  map_one' := twistedHeckeSlashCuspFormCharLinearMap_one k χ
  map_add' := (twistedHeckeSlashCuspFormCharLinearMap k χ).map_add
  map_mul' := twistedHeckeSlashCuspFormCharLinearMap_map_mul k χ

/-- The cusp-form Hecke action evaluates through its underlying linear extension. -/
@[simp] lemma heckeRingHomCuspCharSpace_apply (T : 𝕋 (Delta0 N) (Γ₀Q(N)) ℤ) :
    heckeRingHomCuspCharSpace k χ T = twistedHeckeSlashCuspFormCharLinearMap k χ T :=
  (rfl)

end HeckeRing.GL2

end
