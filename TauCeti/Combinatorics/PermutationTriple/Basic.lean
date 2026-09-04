/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod

/-!
# Permutation triples

This file defines the finite permutation data underlying a three-point cover.  A permutation
triple records the monodromies around `0`, `1`, and `∞`; the product relation fixes the convention
that their ordered product is trivial.  The two-component constructor and the finite carrier
equivalence make the data convenient for both structural arguments and enumeration.

The formal prototype for this module is `TauCetiRoadmap/BelyiMaps/Suggested.lean`.
-/

public section

namespace TauCeti

/-- A degree-`n` permutation triple with trivial ordered product. -/
@[ext]
structure PermutationTriple (n : ℕ) where
  /-- Monodromy around `0`. -/
  σ0 : Equiv.Perm (Fin n)
  /-- Monodromy around `1`. -/
  σ1 : Equiv.Perm (Fin n)
  /-- Monodromy around `∞`. -/
  σinf : Equiv.Perm (Fin n)
  /-- The product of the three branch monodromies is trivial. -/
  product_eq_one : σinf * σ1 * σ0 = 1

namespace PermutationTriple

variable {n : ℕ}

/-- Construct a permutation triple from its first two monodromies. -/
@[expose] def ofTwo (σ0 σ1 : Equiv.Perm (Fin n)) : PermutationTriple n where
  σ0 := σ0
  σ1 := σ1
  σinf := (σ1 * σ0)⁻¹
  product_eq_one := by simp [mul_assoc]

@[simp] theorem ofTwo_σ0 (σ0 σ1 : Equiv.Perm (Fin n)) : (ofTwo σ0 σ1).σ0 = σ0 := rfl

@[simp] theorem ofTwo_σ1 (σ0 σ1 : Equiv.Perm (Fin n)) : (ofTwo σ0 σ1).σ1 = σ1 := rfl

@[simp] theorem ofTwo_σinf (σ0 σ1 : Equiv.Perm (Fin n)) :
    (ofTwo σ0 σ1).σinf = (σ1 * σ0)⁻¹ := rfl

/-- The third monodromy is determined by the first two. -/
theorem σinf_eq (t : PermutationTriple n) : t.σinf = (t.σ1 * t.σ0)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa [mul_assoc] using t.product_eq_one

/-- Equality of triples is determined by equality of their first two monodromies. -/
theorem ext_of_two {t t' : PermutationTriple n} (h0 : t.σ0 = t'.σ0)
    (h1 : t.σ1 = t'.σ1) : t = t' := by
  apply PermutationTriple.ext
  · exact h0
  · exact h1
  · rw [t.σinf_eq, t'.σinf_eq, h0, h1]

/-- A permutation triple is equivalent to the pair of its first two monodromies. -/
def equivPair (n : ℕ) : PermutationTriple n ≃
    Equiv.Perm (Fin n) × Equiv.Perm (Fin n) where
  toFun t := (t.σ0, t.σ1)
  invFun p := ofTwo p.1 p.2
  left_inv t := (ext_of_two (t := t) (t' := ofTwo t.σ0 t.σ1) rfl rfl).symm
  right_inv _ := rfl

/-- Transport a permutation triple along an equivalence of its degree sets. -/
@[expose] def transport {m : ℕ} (e : Fin n ≃ Fin m) :
    PermutationTriple n ≃ PermutationTriple m where
  toFun t :=
    { σ0 := e.permCongrHom t.σ0
      σ1 := e.permCongrHom t.σ1
      σinf := e.permCongrHom t.σinf
      product_eq_one := by
        simpa only [map_mul, map_one] using congrArg e.permCongrHom t.product_eq_one }
  invFun t :=
    { σ0 := e.symm.permCongrHom t.σ0
      σ1 := e.symm.permCongrHom t.σ1
      σinf := e.symm.permCongrHom t.σinf
      product_eq_one := by
        simpa only [map_mul, map_one] using congrArg e.symm.permCongrHom t.product_eq_one }
  left_inv t := by
    apply ext_of_two
    · ext x
      simp [Equiv.permCongr_def]
    · ext x
      simp [Equiv.permCongr_def]
  right_inv t := by
    apply ext_of_two
    · ext x
      simp [Equiv.permCongr_def]
    · ext x
      simp [Equiv.permCongr_def]

@[simp] theorem transport_σ0 {m : ℕ} (e : Fin n ≃ Fin m) (t : PermutationTriple n) :
    (transport e t).σ0 = e.permCongrHom t.σ0 := rfl

@[simp] theorem transport_σ1 {m : ℕ} (e : Fin n ≃ Fin m) (t : PermutationTriple n) :
    (transport e t).σ1 = e.permCongrHom t.σ1 := rfl

@[simp] theorem transport_σinf {m : ℕ} (e : Fin n ≃ Fin m) (t : PermutationTriple n) :
    (transport e t).σinf = e.permCongrHom t.σinf := rfl

/-- The triple carrier is finite because its first two components are finite. -/
instance : Fintype (PermutationTriple n) :=
  Fintype.ofEquiv _ (equivPair n).symm

/-- Equality of triples is decidable through their first two components. -/
instance : DecidableEq (PermutationTriple n) := fun t t' =>
  decidable_of_iff (t.σ0 = t'.σ0 ∧ t.σ1 = t'.σ1)
    ⟨fun h => ext_of_two h.1 h.2, fun h => h ▸ ⟨rfl, rfl⟩⟩

/-- The trivial triple, whose three monodromies are identity permutations. -/
instance : One (PermutationTriple n) where
  one := ⟨1, 1, 1, by simp⟩

@[simp] theorem one_σ0 : (1 : PermutationTriple n).σ0 = 1 := rfl

@[simp] theorem one_σ1 : (1 : PermutationTriple n).σ1 = 1 := rfl

@[simp] theorem one_σinf : (1 : PermutationTriple n).σinf = 1 := rfl

@[simp] theorem ofTwo_one_one : ofTwo (1 : Equiv.Perm (Fin n)) 1 = 1 := by
  apply ext_of_two <;> rfl

/-- There is only one permutation triple of degree zero. -/
instance : Subsingleton (PermutationTriple 0) where
  allEq _ _ := by
    apply ext_of_two <;> apply Subsingleton.elim

/-- The cyclically rotated form of the product relation. -/
theorem σ0_mul_σinf_mul_σ1_eq_one (t : PermutationTriple n) :
    t.σ0 * t.σinf * t.σ1 = 1 := by
  simp [t.σinf_eq, mul_inv_rev]

/-- The other cyclically rotated form of the product relation. -/
theorem σ1_mul_σ0_mul_σinf_eq_one (t : PermutationTriple n) :
    t.σ1 * t.σ0 * t.σinf = 1 := by
  simp [t.σinf_eq, mul_assoc]

/-- The reverse convention for permutation triples uses the opposite multiplication order. -/
structure ReversePermutationTriple (n : ℕ) where
  /-- The component labelled `0`. -/
  σ0 : Equiv.Perm (Fin n)
  /-- The component labelled `1`. -/
  σ1 : Equiv.Perm (Fin n)
  /-- The component labelled `∞`. -/
  σinf : Equiv.Perm (Fin n)
  /-- The reverse ordered product is trivial. -/
  product_eq_one : σ0 * σ1 * σinf = 1

/-- Inverting all components translates between the two product conventions. -/
@[expose] def invComponents : PermutationTriple n ≃ ReversePermutationTriple n where
  toFun t :=
    { σ0 := t.σ0⁻¹
      σ1 := t.σ1⁻¹
      σinf := t.σinf⁻¹
      product_eq_one := by
        have h := congrArg Inv.inv t.product_eq_one
        simpa [mul_inv_rev, mul_assoc] using h }
  invFun t :=
    { σ0 := t.σ0⁻¹
      σ1 := t.σ1⁻¹
      σinf := t.σinf⁻¹
      product_eq_one := by
        have h := congrArg Inv.inv t.product_eq_one
        simpa [mul_inv_rev, mul_assoc] using h }
  left_inv t := by cases t; simp
  right_inv t := by cases t; simp

@[simp] theorem invComponents_σ0 (t : PermutationTriple n) :
    (invComponents t).σ0 = t.σ0⁻¹ := rfl

@[simp] theorem invComponents_σ1 (t : PermutationTriple n) :
    (invComponents t).σ1 = t.σ1⁻¹ := rfl

@[simp] theorem invComponents_σinf (t : PermutationTriple n) :
    (invComponents t).σinf = t.σinf⁻¹ := rfl

end PermutationTriple

end TauCeti

end
