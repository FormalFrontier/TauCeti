/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Specht.SubmoduleTheorem

/-!
# The endomorphisms of a Specht module are the scalars

Irreducibility of `S^μ` says that a nonzero endomorphism of it is invertible; over a field that is
not algebraically closed that leaves room for a division ring of endomorphisms larger than the
field, and the Schur index of the representation measures the room.  For the Specht modules over
`ℚ` there is none: every endomorphism is a scalar.

The argument is the one behind James's submodule theorem, run inside `S^μ`.  The column
antisymmetrizer `b_t` of a `μ`-tableau `t` collapses the whole Young permutation module onto the
line spanned by the polytabloid `e_t` (`TauCeti.YoungTableau.exists_eq_smul_polytabloid`), and on
`e_t` itself it is multiplication by the order of the column group of `t`
(`TauCeti.YoungTableau.asAlgebraHom_columnAntisymmetrizer_polytabloid`), which is nonzero in
characteristic zero.  An endomorphism `φ` of `S^μ` commutes with `b_t`, so
`|C_t| • φ e_t = b_t · φ e_t` is a multiple of `e_t`; hence `φ e_t = c • e_t`, and since the
`Sₙ`-orbit of `e_t` spans `S^μ` this forces `φ = c • id`.

## Main results

* `TauCeti.YoungTableau.asAlgebraHom_columnAntisymmetrizer_polytabloid`: `b_t · e_t = |C_t| • e_t`.
* `TauCeti.exists_intertwiningMap_eq_smul`: **every endomorphism of the Specht module is a
  scalar**.
* `TauCeti.finrank_intertwiningMap_spechtSubrepresentation`: consequently its endomorphism space
  is a line.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapters 3--4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),

  Layer 4: completeness and irreducibility (the classification)
-/

public section

namespace TauCeti

namespace YoungTableau

variable {μ : YoungDiagram}

/-- Classical decidability of membership in the column group, used to form its finite sum, as in
`TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean`. -/
noncomputable local instance decidableMemColSubgroupTableau
    (t : YoungTableau μ) : DecidablePred (· ∈ colSubgroup t) :=
  Classical.decPred _

/-- **The column antisymmetrizer scales the polytabloid by the order of the column group.**  It
collapses `M^μ` onto the line spanned by `e_t`, and pairing the resulting multiple of `e_t` with
the tabloid `{t}` reads the multiple off as `⟨e_t, e_t⟩ = |C_t|`, using that `b_t` is self-adjoint
for the tabloid form and that `{t}` occurs in `e_t` with coefficient `1`. -/
theorem asAlgebraHom_columnAntisymmetrizer_polytabloid (t : YoungTableau μ) :
    (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t)
        (polytabloid t) = (Nat.card (colSubgroup t) : ℚ) • polytabloid t := by
  obtain ⟨κ, hκ⟩ := exists_eq_smul_polytabloid t (polytabloid t)
  have hself := tabloidForm_asAlgebraHom_columnAntisymmetrizer t (polytabloid t)
    (MonoidAlgebra.single (tabloid t) 1)
  rw [hκ, ← polytabloid_def, tabloidForm_polytabloid_self, map_smul, LinearMap.smul_apply,
    permutationForm_single_right, polytabloid_coeff_tabloid] at hself
  rw [hκ]
  congr 1
  simpa using hself

end YoungTableau

open YoungTableau

variable {μ : YoungDiagram}

/-- Classical decidability of membership in the column group, used to form its finite sum. -/
noncomputable local instance decidableMemColSubgroupEndomorphism
    (t : YoungTableau μ) : DecidablePred (· ∈ colSubgroup t) :=
  Classical.decPred _

/-- **Every endomorphism of the Specht module is a scalar.**  Both the tabloid form argument and
the collapsing property of the column antisymmetrizer enter: `b_t` carries the image of a
polytabloid back into the line it spans, while it multiplies the polytabloid itself by the nonzero
scalar `|C_t|`, and the polytabloid generates `S^μ` as a representation. -/
theorem exists_intertwiningMap_eq_smul (μ : YoungDiagram)
    (φ : Representation.IntertwiningMap (spechtSubrepresentation μ).toRepresentation
      (spechtSubrepresentation μ).toRepresentation) :
    ∃ c : ℚ, ∀ v, φ v = c • v := by
  classical
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  -- the action on the Specht module is the restriction of the ambient action
  have hact : ∀ (g : Equiv.Perm (Fin μ.card)) (v : (spechtSubrepresentation μ).toSubmodule),
      ((spechtSubrepresentation μ).toRepresentation g v :
          (permutationModule (shapePartition μ)).V) =
        (permutationModule (shapePartition μ)).ρ g v :=
    fun g v =>
      LinearMap.coe_restrict_apply ((spechtSubrepresentation μ).apply_mem_toSubmodule g) v
  set e : (spechtSubrepresentation μ).toSubmodule :=
    ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩ with he
  set lam : ℚ := (Nat.card (colSubgroup t) : ℚ) with hlamdef
  have hlam : lam ≠ 0 := by
    have : 0 < Nat.card (colSubgroup t) := Nat.card_pos
    rw [hlamdef]
    exact_mod_cast this.ne'
  -- the column antisymmetrizer, acting on the Specht module
  set B : (spechtSubrepresentation μ).toSubmodule → (spechtSubrepresentation μ).toSubmodule :=
    fun x => ∑ q : colSubgroup t,
      ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
        (spechtSubrepresentation μ).toRepresentation q x with hB
  have hBcoe : ∀ x, ((B x : (spechtSubrepresentation μ).toSubmodule) :
      (permutationModule (shapePartition μ)).V) =
      (permutationModule (shapePartition μ)).ρ.asAlgebraHom (columnAntisymmetrizer t)
        (x : (permutationModule (shapePartition μ)).V) := by
    intro x
    rw [asAlgebraHom_columnAntisymmetrizer_apply, hB]
    push_cast
    exact Finset.sum_congr rfl fun q _ => by rw [hact]
  have hBphi : ∀ x, φ (B x) = B (φ x) := by
    intro x
    rw [hB]
    simp only [map_sum, map_smul, φ.isIntertwining]
  have hBe : B e = lam • e := by
    apply Subtype.ext
    rw [hBcoe, SetLike.val_smul, hlamdef]
    exact asAlgebraHom_columnAntisymmetrizer_polytabloid t
  obtain ⟨κ, hκ⟩ := exists_eq_smul_polytabloid t
    ((φ e : (spechtSubrepresentation μ).toSubmodule) :
      (permutationModule (shapePartition μ)).V)
  have hkey : lam • φ e = κ • e := by
    apply Subtype.ext
    have h1 : φ (B e) = lam • φ e := by rw [hBe, map_smul]
    have h2 : ((B (φ e) : (spechtSubrepresentation μ).toSubmodule) :
        (permutationModule (shapePartition μ)).V) = κ • polytabloid t := by
      rw [hBcoe, hκ]
    rw [← h1, hBphi, h2]
    simp [he]
  refine ⟨κ / lam, fun v => ?_⟩
  have hphie : φ e = (κ / lam) • e := by
    have := congrArg (fun x => lam⁻¹ • x) hkey
    simp only [smul_smul, inv_mul_cancel₀ hlam, one_smul] at this
    rw [this, div_eq_inv_mul]
  -- the orbit of the polytabloid spans the Specht module, and `φ` is a scalar on it
  have hspan : ∀ y ∈ Submodule.span ℚ (Set.range fun σ : Equiv.Perm (Fin μ.card) =>
        (permutationModule (shapePartition μ)).ρ σ (polytabloid t)),
      ∀ hy : y ∈ (spechtSubrepresentation μ).toSubmodule,
        ((φ ⟨y, hy⟩ : (spechtSubrepresentation μ).toSubmodule) :
          (permutationModule (shapePartition μ)).V) = (κ / lam) • y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨σ, rfl⟩ := hx
      intro hmem
      have hxe : (⟨(permutationModule (shapePartition μ)).ρ σ (polytabloid t), hmem⟩ :
          (spechtSubrepresentation μ).toSubmodule) =
          (spechtSubrepresentation μ).toRepresentation σ e := by
        apply Subtype.ext
        rw [hact]
      rw [hxe, φ.isIntertwining, hphie, map_smul, SetLike.val_smul, hact]
    | zero =>
      intro hmem
      have hz : (⟨0, hmem⟩ : (spechtSubrepresentation μ).toSubmodule) = 0 := rfl
      rw [hz, map_zero, smul_zero]
      rfl
    | add x y hx hy ihx ihy =>
      intro hmem
      have hx' : x ∈ (spechtSubrepresentation μ).toSubmodule := by
        rw [spechtSubrepresentation_eq_span_orbit t]; exact hx
      have hy' : y ∈ (spechtSubrepresentation μ).toSubmodule := by
        rw [spechtSubrepresentation_eq_span_orbit t]; exact hy
      have hsum : (⟨x + y, hmem⟩ : (spechtSubrepresentation μ).toSubmodule) =
          ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
      rw [hsum, map_add]
      push_cast [ihx hx', ihy hy']
      rw [smul_add]
    | smul r x hx ih =>
      intro hmem
      have hx' : x ∈ (spechtSubrepresentation μ).toSubmodule := by
        rw [spechtSubrepresentation_eq_span_orbit t]; exact hx
      have hsmul : (⟨r • x, hmem⟩ : (spechtSubrepresentation μ).toSubmodule) =
          r • ⟨x, hx'⟩ := rfl
      rw [hsmul, map_smul]
      push_cast [ih hx']
      rw [smul_comm]
  apply Subtype.ext
  have hv : (v : (permutationModule (shapePartition μ)).V) ∈
      Submodule.span ℚ (Set.range fun σ : Equiv.Perm (Fin μ.card) =>
        (permutationModule (shapePartition μ)).ρ σ (polytabloid t)) := by
    rw [← spechtSubrepresentation_eq_span_orbit t]
    exact v.2
  have := hspan _ hv v.2
  simpa using this

/-- **The Specht module has a one-dimensional endomorphism space.**  This is the absolute
irreducibility of `S^μ` over `ℚ`: irreducibility alone would only give a division ring of
endomorphisms, and here that division ring is `ℚ` itself. -/
theorem finrank_intertwiningMap_spechtSubrepresentation (μ : YoungDiagram) :
    Module.finrank ℚ (Representation.IntertwiningMap
      (spechtSubrepresentation μ).toRepresentation
      (spechtSubrepresentation μ).toRepresentation) = 1 := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  have hne : (Representation.IntertwiningMap.id
      (spechtSubrepresentation μ).toRepresentation) ≠ 0 := by
    intro h
    have := congrArg (fun f => f (⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩ :
      (spechtSubrepresentation μ).toSubmodule)) h
    simp only [Representation.IntertwiningMap.coe_zero, Pi.zero_apply] at this
    exact polytabloid_ne_zero t (congrArg Subtype.val this)
  rw [finrank_eq_one_iff_of_nonzero' _ hne]
  intro w
  obtain ⟨c, hc⟩ := exists_intertwiningMap_eq_smul μ w
  refine ⟨c, DFunLike.ext _ _ fun v => ?_⟩
  rw [Representation.IntertwiningMap.smul_apply]
  exact (hc v).symm

end TauCeti
