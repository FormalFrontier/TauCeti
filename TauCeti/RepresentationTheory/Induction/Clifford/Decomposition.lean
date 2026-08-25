/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
public import TauCeti.RepresentationTheory.Induction.Clifford.Multiplicity
public import TauCeti.RepresentationTheory.Induction.Clifford.Orbit.Index
import TauCeti.GroupTheory.Index
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.Simple.Basic

/-!
# The character form of Clifford's theorem

Let `N` be a normal subgroup of a finite group `G`, and let `W` be an irreducible
finite-dimensional representation of `G` over a splitting field.  The restriction of `W` to `N`
has irreducible constituents in one `G`-orbit, indexed by the left cosets of the inertia group of
any constituent `V`, and every constituent occurs with one common positive multiplicity `e`.
Consequently

`W.character n = e * ∑ g in reps, (conjNormalFDRep g V).character n`

for a left transversal `reps` of `inertia V`.

The orbit, its inertia-coset indexing and the common Hom-space dimension are already provided by
`TauCeti/RepresentationTheory/Induction/Clifford/Orbit/Basic.lean`,
`TauCeti/RepresentationTheory/Induction/Clifford/Orbit/Index.lean` and
`TauCeti/RepresentationTheory/Induction/Clifford/Multiplicity.lean`.  This file assembles them
using the irreducible-character basis: pairing either side with an irreducible character counts
the same constituent, and a transversal contains exactly one representative when it occurs.

## Main result

* `TauCeti.clifford_restrict_character`: **Clifford's theorem, character form**.  It supplies a
  simple constituent, its positive common multiplicity, a genuine inertia-group transversal, and
  the restriction-character formula indexed by that transversal.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §49.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

universe u v

namespace TauCeti

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal]

private noncomputable def inertiaTransversal (A : FDRep k N) [Fintype G] : Finset G := by
  classical
  let _ : Fintype (G ⧸ inertia A) := Fintype.ofFinite _
  exact Finset.univ.image fun q : G ⧸ inertia A => Quotient.out q

private theorem inertiaTransversal_spec (A : FDRep k N) [Fintype G] :
    ∀ g : G, ∃! r, r ∈ inertiaTransversal A ∧ g⁻¹ * r ∈ inertia A := by
  classical
  let _ : Fintype (G ⧸ inertia A) := Fintype.ofFinite _
  intro g
  let q : G ⧸ inertia A := QuotientGroup.mk g
  refine ⟨Quotient.out q, ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
  · rw [← QuotientGroup.eq]
    exact (Quotient.out_eq' q).symm
  · rintro r ⟨hr, hgr⟩
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp (by simpa only [inertiaTransversal] using hr)
    exact congrArg Quotient.out
      ((QuotientGroup.eq.mpr hgr).trans (Quotient.out_eq' p)).symm

private theorem nonempty_iso_conjNormalFDRep_of_coset {A : FDRep k N} {g r : G}
    (hgr : g⁻¹ * r ∈ inertia A) :
    Nonempty (conjNormalFDRep g A ≅ conjNormalFDRep r A) := by
  have hstab : (g⁻¹ * r) • toSkeleton A = toSkeleton A := by
    obtain ⟨i⟩ := mem_inertia_iff.mp hgr
    rw [smul_toSkeleton]
    exact congr_toSkeleton_of_iso i
  have horbit : g • toSkeleton A = r • toSkeleton A := by
    calc
      g • toSkeleton A = g • ((g⁻¹ * r) • toSkeleton A) := congrArg (g • ·) hstab.symm
      _ = r • toSkeleton A := by rw [← mul_smul]; simp
  rw [smul_toSkeleton, smul_toSkeleton, toSkeleton_eq_toSkeleton_iff] at horbit
  exact horbit

private theorem eq_of_mem_inertiaTransversal_of_nonempty_iso {A U : FDRep k N} [Fintype G]
    {r s : G} (hr : r ∈ inertiaTransversal A) (hs : s ∈ inertiaTransversal A)
    (hir : Nonempty (U ≅ conjNormalFDRep r A))
    (his : Nonempty (U ≅ conjNormalFDRep s A)) : r = s := by
  obtain ⟨ir⟩ := hir
  obtain ⟨is⟩ := his
  have hrs : r • toSkeleton A = s • toSkeleton A := by
    rw [smul_toSkeleton, smul_toSkeleton]
    exact congr_toSkeleton_of_iso (ir.symm ≪≫ is)
  have hfix : (r⁻¹ * s) • toSkeleton A = toSkeleton A := by
    calc
      (r⁻¹ * s) • toSkeleton A = r⁻¹ • (s • toSkeleton A) := mul_smul _ _ _
      _ = r⁻¹ • (r • toSkeleton A) := congrArg (r⁻¹ • ·) hrs.symm
      _ = toSkeleton A := by rw [← mul_smul]; simp
  have hrsInertia : r⁻¹ * s ∈ inertia A := by
    rw [mem_inertia_iff, ← toSkeleton_eq_toSkeleton_iff, ← smul_toSkeleton]
    exact hfix
  exact ((inertiaTransversal_spec A r).unique ⟨hs, hrsInertia⟩ ⟨hr, by simp⟩).symm

private theorem simple_conjNormalFDRep (A : FDRep k N) [Simple A] (g : G) :
    Simple (conjNormalFDRep g A) := by
  rw [conjNormalFDRep, ← conjNormalFDRepEquiv_functor]
  exact CategoryTheory.simple_obj _ A

private theorem finrank_intertwiningMap_eq_common_of_iso
    {Y : Type u} [AddCommGroup Y] [Module k Y]
    (rho : Representation k G Y) [FiniteDimensional k Y]
    (sigma : Subrepresentation (rho.comp N.subtype)) (hsigma : IsAtom sigma)
    (U : FDRep k N) (g : G) (e : Nat)
    (hcommon : ∀ tau : Subrepresentation (rho.comp N.subtype), IsAtom tau →
      Module.finrank k
        (tau.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (rho.comp N.subtype)) = e)
    (hiso : Nonempty (U ≅ conjNormalFDRep g (FDRep.of sigma.toRepresentation))) :
    Module.finrank k (Representation.IntertwiningMap U.ρ (rho.comp N.subtype)) = e := by
  let tau := Representation.conjSubrep rho g sigma
  have htau : IsAtom tau := Representation.isAtom_conjSubrep_iff.mpr hsigma
  obtain ⟨i⟩ := hiso
  let j : U ≅ FDRep.of tau.toRepresentation :=
    i ≪≫ (Representation.fdRepIsoConjSubrep rho g sigma).symm
  obtain ⟨jrep⟩ := nonempty_fdRepIso_iff.mp ⟨j⟩
  let jmodule : _root_.Representation.asModule U.ρ ≃ₗ[k[N]] tau.asSubmodule :=
    (Representation.asModuleLinearEquivOfEquiv jrep).trans
      (_root_.Subrepresentation.asModuleEquivAsSubmodule tau)
  calc
    Module.finrank k (Representation.IntertwiningMap U.ρ (rho.comp N.subtype)) =
        Module.finrank k
          (_root_.Representation.asModule U.ρ →ₗ[k[N]]
            _root_.Representation.asModule (rho.comp N.subtype)) :=
      (Representation.IntertwiningMap.equivLinearMapAsModule U.ρ
        (rho.comp N.subtype)).finrank_eq
    _ = Module.finrank k
        (tau.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (rho.comp N.subtype)) :=
      (LinearEquiv.congrLeft
        (_root_.Representation.asModule (rho.comp N.subtype)) k jmodule).finrank_eq
    _ = e := hcommon tau htau

private theorem exists_nonempty_iso_conjNormalFDRep_of_ne_zero
    {Y : Type u} [AddCommGroup Y] [Module k Y]
    (rho : Representation k G Y) [FiniteDimensional k Y] [rho.IsIrreducible]
    (sigma : Subrepresentation (rho.comp N.subtype)) (hsigma : IsAtom sigma)
    (U : FDRep k N) [Simple U]
    (f : Representation.IntertwiningMap U.ρ (rho.comp N.subtype)) (hf : f ≠ 0) :
    ∃ g : G, Nonempty (U ≅ conjNormalFDRep g (FDRep.of sigma.toRepresentation)) := by
  let _ : Representation.IsIrreducible U.ρ := FDRep.isIrreducible_of_simple U
  have hinj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let tau := f.range
  let eRange : Representation.Equiv U.ρ tau.toRepresentation :=
    f.equivOfRange hinj (by rfl)
  let eModule : _root_.Representation.asModule U.ρ ≃ₗ[k[N]] tau.asSubmodule :=
    (Representation.asModuleLinearEquivOfEquiv eRange).trans
      (_root_.Subrepresentation.asModuleEquivAsSubmodule tau)
  let _ : IsSimpleModule k[N] tau.asSubmodule := IsSimpleModule.congr eModule.symm
  have htau : IsAtom tau := _root_.Subrepresentation.isSimpleModule_asSubmodule_iff.mp inferInstance
  obtain ⟨g, ⟨eg⟩⟩ :=
    Representation.exists_nonempty_linearEquiv_asSubmodule_conjSubrep
      (N := N) rho hsigma tau.asSubmodule
  let tauG := Representation.conjSubrep rho g sigma
  let eUG : _root_.Representation.asModule U.ρ ≃ₗ[k[N]] tauG.asSubmodule :=
    eModule.trans eg
  let iUG : U ≅ FDRep.of tauG.toRepresentation :=
    fdRepIsoOfAsModuleLinearEquiv
      (eUG.trans (_root_.Subrepresentation.asModuleEquivAsSubmodule tauG).symm)
  exact ⟨g, ⟨iUG ≪≫ Representation.fdRepIsoConjSubrep rho g sigma⟩⟩

open scoped Classical in
private theorem characterPairing_smul_sum_conjNormalFDRep [Fintype G] [Fintype N]
    [IsAlgClosed k] [Invertible (Nat.card N : k)]
    (A U : FDRep k N) [Simple A] [Simple U] (e : ℕ) :
    ClassFunction.characterPairing (ClassFunction.ofFDRep U)
        ((e : k) • ∑ g ∈ inertiaTransversal A,
          ClassFunction.ofFDRep (conjNormalFDRep g A)) =
      if ∃ r ∈ inertiaTransversal A, Nonempty (U ≅ conjNormalFDRep r A)
      then (e : k) else 0 := by
  classical
  simp only [map_smul, map_sum]
  by_cases hocc : ∃ r ∈ inertiaTransversal A, Nonempty (U ≅ conjNormalFDRep r A)
  · rw [ite_eq_left hocc]
    obtain ⟨r, hr, hir⟩ := hocc
    rw [Finset.sum_eq_single r]
    · let _ : Simple (conjNormalFDRep r A) := simple_conjNormalFDRep A r
      rw [ClassFunction.characterPairing_ofFDRep_orthonormal,
        ite_eq_left hir, smul_eq_mul, mul_one]
    · intro s hs hsr
      let _ : Simple (conjNormalFDRep s A) := simple_conjNormalFDRep A s
      rw [ClassFunction.characterPairing_ofFDRep_orthonormal, ite_eq_right]
      intro his
      exact hsr (eq_of_mem_inertiaTransversal_of_nonempty_iso
        (A := A) (U := U) (r := r) (s := s) hr hs hir his).symm
    · exact fun hnr ↦ (hnr hr).elim
  · rw [ite_eq_right hocc]
    apply smul_eq_zero.mpr
    right
    apply Finset.sum_eq_zero
    intro r hr
    let _ : Simple (conjNormalFDRep r A) := simple_conjNormalFDRep A r
    rw [ClassFunction.characterPairing_ofFDRep_orthonormal, ite_eq_right]
    exact fun hir ↦ hocc ⟨r, hr, hir⟩

open scoped Classical in
private theorem characterPairing_resFDRep_eq_ite [Fintype G] [Fintype N]
    [Invertible (Nat.card N : k)] (W : FDRep k G) [Simple W]
    (sigma : Subrepresentation (W.ρ.comp N.subtype)) (hsigma : IsAtom sigma)
    (U : FDRep k N) [Simple U] (e : ℕ)
    (hcommon : ∀ tau : Subrepresentation (W.ρ.comp N.subtype), IsAtom tau →
      Module.finrank k
        (tau.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (W.ρ.comp N.subtype)) = e) :
    ClassFunction.characterPairing (ClassFunction.ofFDRep U)
        (ClassFunction.ofFDRep (resFDRep N W)) =
      if ∃ r ∈ inertiaTransversal (FDRep.of sigma.toRepresentation),
        Nonempty (U ≅ conjNormalFDRep r (FDRep.of sigma.toRepresentation))
      then (e : k) else 0 := by
  classical
  let _ : Representation.IsIrreducible W.ρ := FDRep.isIrreducible_of_simple W
  by_cases hocc : ∃ r ∈ inertiaTransversal (FDRep.of sigma.toRepresentation),
      Nonempty (U ≅ conjNormalFDRep r (FDRep.of sigma.toRepresentation))
  · rw [ite_eq_left hocc]
    obtain ⟨r, -, hir⟩ := hocc
    rw [ClassFunction.ofFDRep_eq_ofCharacter, ClassFunction.ofFDRep_eq_ofCharacter,
      ClassFunction.characterPairing_symm,
      ClassFunction.characterPairing_ofCharacter_eq_finrank]
    exact congrArg (fun m : ℕ ↦ (m : k))
      (finrank_intertwiningMap_eq_common_of_iso W.ρ sigma hsigma U r e hcommon hir)
  · rw [ite_eq_right hocc, ClassFunction.ofFDRep_eq_ofCharacter,
      ClassFunction.ofFDRep_eq_ofCharacter, ClassFunction.characterPairing_symm,
      ClassFunction.characterPairing_ofCharacter_eq_finrank]
    have hsub : Subsingleton
        (Representation.IntertwiningMap U.ρ (W.ρ.comp N.subtype)) := by
      constructor
      intro f g
      apply sub_eq_zero.mp
      by_contra hfg
      obtain ⟨a, hUa⟩ := exists_nonempty_iso_conjNormalFDRep_of_ne_zero
        W.ρ sigma hsigma U (f - g) hfg
      obtain ⟨r, ⟨hr, har⟩, -⟩ :=
        inertiaTransversal_spec (FDRep.of sigma.toRepresentation) a
      exact hocc ⟨r, hr, hUa.map fun i ↦
        i ≪≫ (nonempty_iso_conjNormalFDRep_of_coset har).some⟩
    let _ : Subsingleton
        (Representation.IntertwiningMap U.ρ (W.ρ.comp N.subtype)) := hsub
    have hzero : Module.finrank k
        (Representation.IntertwiningMap U.ρ (W.ρ.comp N.subtype)) = 0 :=
      Module.finrank_zero_of_subsingleton
    calc
      (Module.finrank k
          (Representation.IntertwiningMap U.ρ (resFDRep N W).ρ) : k) =
          (Module.finrank k
            (Representation.IntertwiningMap U.ρ (W.ρ.comp N.subtype)) : k) := rfl
      _ = ((0 : ℕ) : k) := congrArg (fun m : ℕ ↦ (m : k)) hzero
      _ = 0 := Nat.cast_zero

/-- **Clifford's theorem, character form.**  The character of the restriction of an irreducible
representation to a normal subgroup is a positive common multiple of the sum of the distinct
conjugates of a fixed irreducible constituent, indexed by representatives of the left cosets of its
inertia group.  The finite set `reps` is a genuine left transversal for the inertia group: for every
`g`, it contains a unique `r` with `g⁻¹ * r ∈ inertia V`.

The hypothesis on `Nat.card G` is Maschke's condition.  Algebraic closure makes `k` a splitting
field, so irreducible characters form an orthonormal basis and their pairings compute
multiplicities. -/
theorem clifford_restrict_character [Finite G] [IsAlgClosed k]
    (hG : IsUnit (Nat.card G : k)) (W : FDRep k G) [Simple W] :
    ∃ (V : FDRep k N) (_ : Simple V) (e : ℕ) (reps : Finset G),
      e ≠ 0 ∧
      (∀ g : G, ∃! r, r ∈ reps ∧ g⁻¹ * r ∈ inertia V) ∧
      ∀ n : N, W.character (n : G) =
        (e : k) * ∑ g ∈ reps, (conjNormalFDRep g V).character n := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Invertible (Nat.card G : k) := hG.invertible
  let _ : Fintype N := Fintype.ofFinite N
  have hN : IsUnit (Nat.card N : k) := isUnit_natCard_subgroup N hG
  let _ : Invertible (Nat.card N : k) := hN.invertible
  let _ : Representation.IsIrreducible W.ρ := FDRep.isIrreducible_of_simple W
  obtain ⟨sigma, hsigma, -⟩ :=
    Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep (N := N) W.ρ
  let V : FDRep k N := FDRep.of sigma.toRepresentation
  let _ : Representation.IsIrreducible V.ρ :=
    Representation.isIrreducible_toRepresentation_of_isAtom hsigma
  let _ : Simple V := FDRep.simple_of_isIrreducible V
  obtain ⟨e, he, hcommon⟩ :=
    Representation.exists_forall_finrank_linearMap_eq (N := N) W.ρ
  let reps := inertiaTransversal V
  refine ⟨V, inferInstance, e, reps, Nat.ne_of_gt he, inertiaTransversal_spec V, ?_⟩
  let lhs : ClassFunction k N := ClassFunction.ofFDRep (resFDRep N W)
  let rhs : ClassFunction k N :=
    (e : k) • ∑ g ∈ reps, ClassFunction.ofFDRep (conjNormalFDRep g V)
  have hpair : ∀ i : Fin (Nat.card (ConjClasses N)),
      ClassFunction.characterPairing
          (ClassFunction.ofCharacter (irreducibleRepresentation k i)) lhs =
        ClassFunction.characterPairing
          (ClassFunction.ofCharacter (irreducibleRepresentation k i)) rhs := by
    intro i
    let U : FDRep k N := FDRep.of (irreducibleRepresentation k i)
    let _ : Representation.IsIrreducible U.ρ := by
      dsimp only [U, FDRep.of_ρ']
      infer_instance
    let _ : Simple U := FDRep.simple_of_isIrreducible U
    have hU : ClassFunction.ofCharacter (irreducibleRepresentation k i) =
        ClassFunction.ofFDRep U := (ClassFunction.ofFDRep_eq_ofCharacter U).symm
    rw [hU]
    have hlhs := characterPairing_resFDRep_eq_ite W sigma hsigma U e hcommon
    have hrhs := characterPairing_smul_sum_conjNormalFDRep V U e
    simpa only [lhs, rhs, reps, V] using hlhs.trans hrhs.symm
  have hclass : lhs = rhs := by
    calc
      lhs = ∑ i, ClassFunction.characterPairing
          (ClassFunction.ofCharacter (irreducibleRepresentation k i)) lhs •
            ClassFunction.ofCharacter (irreducibleRepresentation k i) :=
        (ClassFunction.sum_characterPairing_smul_ofCharacter
          (irreducibleRepresentation k)
          (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) lhs).symm
      _ = ∑ i, ClassFunction.characterPairing
          (ClassFunction.ofCharacter (irreducibleRepresentation k i)) rhs •
            ClassFunction.ofCharacter (irreducibleRepresentation k i) := by
        exact Finset.sum_congr rfl fun i _ ↦ by rw [hpair i]
      _ = rhs := ClassFunction.sum_characterPairing_smul_ofCharacter
        (irreducibleRepresentation k)
        (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) rhs
  intro n
  have hn := congrArg (fun f : ClassFunction k N ↦ f.1 n) hclass
  dsimp only [lhs, rhs] at hn
  simp only [ClassFunction.ofFDRep_apply, character_resFDRep,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at hn
  let eval : ClassFunction k N →+ k :=
    (Pi.evalAddMonoidHom (fun _ : N => k) n).comp
      (ClassFunction k N).subtype.toAddMonoidHom
  have hsum : (∑ g ∈ reps, ClassFunction.ofFDRep (conjNormalFDRep g V)).1 n =
      ∑ g ∈ reps, (conjNormalFDRep g V).character n := by
    calc
      (∑ g ∈ reps, ClassFunction.ofFDRep (conjNormalFDRep g V)).1 n =
          eval (∑ g ∈ reps, ClassFunction.ofFDRep (conjNormalFDRep g V)) := rfl
      _ = ∑ g ∈ reps, eval (ClassFunction.ofFDRep (conjNormalFDRep g V)) :=
        map_sum eval (fun g ↦ ClassFunction.ofFDRep (conjNormalFDRep g V)) reps
      _ = ∑ g ∈ reps, (conjNormalFDRep g V).character n := by
        apply Finset.sum_congr rfl
        intro g _
        exact ClassFunction.ofFDRep_apply (conjNormalFDRep g V) n
  rw [hsum] at hn
  exact hn

end TauCeti
