/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod

/-!
# Permutation triples

This file defines the finite permutation data underlying a three-point cover.  A permutation
triple records the monodromies around `0`, `1`, and `∞`; the product relation fixes the convention
that their ordered product is trivial.  The two-component constructor and the finite carrier
equivalence make the data convenient for both structural arguments and enumeration.
The defining product convention and the opposite-convention translation follow the conventions
recorded in the [Belyi maps roadmap README](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/BelyiMaps/README.md):
the defining relation is `σinf * σ1 * σ0 = 1`, while componentwise inversion translates to
the rival relation `σ0 * σ1 * σinf = 1`.

-/

public section

namespace TauCeti

/-- A degree-`n` permutation triple with trivial ordered product. -/
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
def ofTwo (σ0 σ1 : Equiv.Perm (Fin n)) : PermutationTriple n where
  σ0 := σ0
  σ1 := σ1
  σinf := (σ1 * σ0)⁻¹
  product_eq_one := by simp [mul_assoc]

@[simp] theorem ofTwo_σ0 (σ0 σ1 : Equiv.Perm (Fin n)) : (ofTwo σ0 σ1).σ0 = σ0 :=
  (rfl)

@[simp] theorem ofTwo_σ1 (σ0 σ1 : Equiv.Perm (Fin n)) : (ofTwo σ0 σ1).σ1 = σ1 :=
  (rfl)

theorem ofTwo_σinf (σ0 σ1 : Equiv.Perm (Fin n)) :
    (ofTwo σ0 σ1).σinf = (σ1 * σ0)⁻¹ := (rfl)

/-- The third monodromy is determined by the first two. -/
theorem σinf_eq (t : PermutationTriple n) : t.σinf = (t.σ1 * t.σ0)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa [mul_assoc] using t.product_eq_one

/-- The infinity monodromy is the product of the inverses of the first two monodromies, in
the order fixed by the product convention. -/
@[simp] theorem σinf_eq_inv_mul_inv (t : PermutationTriple n) :
    t.σinf = t.σ0⁻¹ * t.σ1⁻¹ := by
  rw [t.σinf_eq, mul_inv_rev]

/-- The product of the first two monodromies is the inverse of the monodromy around `∞`. -/
theorem σ1_mul_σ0_eq_σinf_inv (t : PermutationTriple n) :
    t.σ1 * t.σ0 = t.σinf⁻¹ := by
  rw [t.σinf_eq]
  simp only [inv_inv]

/-- Equality of triples is determined by equality of their first two monodromies. -/
@[ext] theorem ext {t t' : PermutationTriple n} (h0 : t.σ0 = t'.σ0)
    (h1 : t.σ1 = t'.σ1) : t = t' := by
  have hinf : t.σinf = t'.σinf := by
    rw [t.σinf_eq, t'.σinf_eq, h0, h1]
  cases t
  cases t'
  simp_all

/-- A permutation triple is equivalent to the pair of its first two monodromies. -/
def equivPair (n : ℕ) : PermutationTriple n ≃
    Equiv.Perm (Fin n) × Equiv.Perm (Fin n) where
  toFun t := (t.σ0, t.σ1)
  invFun p := ofTwo p.1 p.2
  left_inv t := (ext (t := t) (t' := ofTwo t.σ0 t.σ1) rfl rfl).symm
  right_inv _ := rfl

@[simp] theorem equivPair_apply (t : PermutationTriple n) :
    equivPair n t = (t.σ0, t.σ1) := (rfl)

@[simp] theorem equivPair_symm_apply (p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) :
    (equivPair n).symm p = ofTwo p.1 p.2 := (rfl)

/-- Transport a permutation triple along an equivalence of its degree sets. -/
def transport {m : ℕ} (e : Fin n ≃ Fin m) :
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
    apply ext
    · ext x
      simp [Equiv.permCongr_def]
    · ext x
      simp [Equiv.permCongr_def]
  right_inv t := by
    apply ext
    · ext x
      simp [Equiv.permCongr_def]
    · ext x
      simp [Equiv.permCongr_def]

@[simp] theorem transport_σ0 {m : ℕ} (e : Fin n ≃ Fin m) (t : PermutationTriple n) :
    (transport e t).σ0 = e.permCongrHom t.σ0 := (rfl)

@[simp] theorem transport_σ1 {m : ℕ} (e : Fin n ≃ Fin m) (t : PermutationTriple n) :
    (transport e t).σ1 = e.permCongrHom t.σ1 := (rfl)

theorem transport_σinf {m : ℕ} (e : Fin n ≃ Fin m) (t : PermutationTriple n) :
    (transport e t).σinf = e.permCongrHom t.σinf := (rfl)

/-- Transporting along the identity equivalence does nothing. -/
@[simp] theorem transport_refl (t : PermutationTriple n) :
    transport (Equiv.refl (Fin n)) t = t := by
  apply ext <;> ext x <;> simp

/-- Transport is functorial in the equivalence of degree sets. -/
@[simp] theorem transport_trans {m k : ℕ} (e₁ : Fin n ≃ Fin m) (e₂ : Fin m ≃ Fin k)
    (t : PermutationTriple n) :
    transport e₂ (transport e₁ t) = transport (e₁.trans e₂) t := by
  apply ext <;> ext x <;> simp [Equiv.permCongr_def]

/-- The triple carrier is finite because its first two components are finite. -/
instance : Fintype (PermutationTriple n) :=
  Fintype.ofEquiv _ (equivPair n).symm

/-- Equality of triples is decidable through their first two components. -/
instance : DecidableEq (PermutationTriple n) := fun t t' =>
  decidable_of_iff (t.σ0 = t'.σ0 ∧ t.σ1 = t'.σ1)
    ⟨fun h => ext h.1 h.2, fun h => h ▸ ⟨rfl, rfl⟩⟩

/-- The trivial triple, whose three monodromies are identity permutations. -/
instance : One (PermutationTriple n) where
  one := ⟨1, 1, 1, by simp⟩

@[simp] theorem one_σ0 : (1 : PermutationTriple n).σ0 = 1 := rfl

@[simp] theorem one_σ1 : (1 : PermutationTriple n).σ1 = 1 := rfl

@[simp] theorem one_σinf : (1 : PermutationTriple n).σinf = 1 := rfl

@[simp] theorem ofTwo_one_one : ofTwo (1 : Equiv.Perm (Fin n)) 1 = 1 := by
  apply ext <;> rfl

/-- There is only one permutation triple of degree zero. -/
instance : Subsingleton (PermutationTriple 0) where
  allEq _ _ := by
    apply ext <;> apply Subsingleton.elim

/-- There is only one permutation triple of degree one. -/
instance : Subsingleton (PermutationTriple 1) where
  allEq _ _ := by
    apply ext <;> apply Subsingleton.elim

/-- The cyclically rotated form of the product relation. -/
theorem σ0_mul_σinf_mul_σ1_eq_one (t : PermutationTriple n) :
    t.σ0 * t.σinf * t.σ1 = 1 := by
  rw [t.σinf_eq, mul_inv_rev]
  simp only [mul_assoc, inv_mul_cancel, mul_one, mul_inv_cancel]

/-- The other cyclically rotated form of the product relation. -/
theorem σ1_mul_σ0_mul_σinf_eq_one (t : PermutationTriple n) :
    t.σ1 * t.σ0 * t.σinf = 1 := by
  rw [σ1_mul_σ0_eq_σinf_inv t]
  simp

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

/-- The third monodromy of a reverse triple is determined by the first two. -/
theorem ReversePermutationTriple.σinf_eq (t : ReversePermutationTriple n) :
    t.σinf = (t.σ0 * t.σ1)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  simpa [mul_assoc] using t.product_eq_one

/-- Equality of reverse triples is determined by equality of their first two monodromies. -/
@[ext] theorem ReversePermutationTriple.ext {t t' : ReversePermutationTriple n}
    (h0 : t.σ0 = t'.σ0) (h1 : t.σ1 = t'.σ1) : t = t' := by
  have hinf : t.σinf = t'.σinf := by
    rw [t.σinf_eq, t'.σinf_eq, h0, h1]
  cases t
  cases t'
  simp_all

/-- Inverting all components translates between the two product conventions. -/
def invComponents : PermutationTriple n ≃ ReversePermutationTriple n where
  toFun t :=
    { σ0 := t.σ0⁻¹
      σ1 := t.σ1⁻¹
      σinf := t.σinf⁻¹
      product_eq_one := by
        have h := congrArg Inv.inv t.product_eq_one
        simpa only [mul_inv_rev, inv_inv, inv_one, mul_assoc] using h }
  invFun t :=
    { σ0 := t.σ0⁻¹
      σ1 := t.σ1⁻¹
      σinf := t.σinf⁻¹
      product_eq_one := by
        have h := congrArg Inv.inv t.product_eq_one
        simpa only [mul_inv_rev, inv_inv, inv_one, mul_assoc] using h }
  left_inv t := by cases t; simp
  right_inv t := by cases t; simp

@[simp] theorem invComponents_σ0 (t : PermutationTriple n) :
    (invComponents t).σ0 = t.σ0⁻¹ := (rfl)

@[simp] theorem invComponents_σ1 (t : PermutationTriple n) :
    (invComponents t).σ1 = t.σ1⁻¹ := (rfl)

@[simp] theorem invComponents_σinf (t : PermutationTriple n) :
    (invComponents t).σinf = t.σinf⁻¹ := (rfl)

@[simp] theorem invComponents_symm_σ0 (t : ReversePermutationTriple n) :
    (invComponents.symm t).σ0 = t.σ0⁻¹ := (rfl)

@[simp] theorem invComponents_symm_σ1 (t : ReversePermutationTriple n) :
    (invComponents.symm t).σ1 = t.σ1⁻¹ := (rfl)

theorem invComponents_symm_σinf (t : ReversePermutationTriple n) :
    (invComponents.symm t).σinf = t.σinf⁻¹ := (rfl)

end PermutationTriple

end TauCeti

end
