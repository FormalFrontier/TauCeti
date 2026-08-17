/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# Joint eigenvectors of commuting semisimple families

The eigenvalue function of a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` is a character: it maps `1` to `1`, is multiplicative, and, for
a group, valued in units, assembling into `unitHomOfJointEigenvector : G →* Kˣ`. This much
needs no division — a nonzero vector cancels over a commutative domain acting torsion-freely,
and on a group multiplicativity exhibits the inverse of `χ g` as `χ g⁻¹`. This
yields the simultaneous-diagonalization toolkit for a commuting family of semisimple
endomorphisms: the joint eigenspaces are supremum-independent, they span (over an
algebraically closed field, in finite dimension), and every invariant submodule is the
supremum of its intersections with them.

When `G` is a *finite commutative group* there is a second, unconditional route to the same
spanning statements. Averaging against the characters of `G` produces Fourier projectors onto
the joint eigenspaces, so they exhaust the whole space — and cut out every invariant submodule —
with no algebraic-closedness, finite-dimensionality or semisimplicity hypothesis; all that is
needed is enough roots of unity in `K` and `Nat.card G` invertible there.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/CharacterDecomp.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), extracted as
representation-theoretic infrastructure with no modular-forms dependence: there `G` is the
group `(ZMod N)ˣ` of diamond operators, and the character eigenspaces are the nebentypus
components of `M_k(Γ₁(N))`.

## Main results

* `unitHomOfJointEigenvector`: the eigenvalue function of a nonzero joint eigenvector of a
  group representation, as a monoid homomorphism `G →* Kˣ`.
* `iSupIndep_iInf_eigenspace`,
  `iSup_iInf_eigenspace_eq_top_of_isSemisimple`,
  `iSup_inf_iInf_eigenspace_of_invariant`: joint eigenspaces of a commuting family are
  independent (with no further hypotheses), exhaust the space when semisimple, and
  decompose every invariant submodule — with the character-indexed forms (`…_unitHom…`)
  for group representations.
* `iSup_iInf_eigenspace_unitHom_eq_top_of_commGroup`,
  `iSup_inf_iInf_eigenspace_unitHom_of_invariant_of_commGroup`: for a finite commutative `G`
  with `[HasEnoughRootsOfUnity K (Monoid.exponent G)]` and `IsUnit (Nat.card G : K)`, the
  character eigenspaces span the whole space, and every invariant submodule is the supremum of
  its intersections with them — proved by finite-group Fourier projectors, so neither
  semisimplicity nor finite dimension is assumed.
-/

public section

noncomputable section

open Polynomial

variable {G K V : Type*} [AddCommGroup V]

/-! ### Eigenvalues of a joint eigenvector

Over a commutative domain acting torsion-freely, so that a nonzero vector cancels.
-/

/-! ### The restriction bridge

Needs only the ring and module structure that `Submodule.inf_genEigenspace` uses.
-/

section BridgeScalars

variable [CommRing K] [Module K V]

/-- **The restriction bridge for joint eigenspaces**: for a family of endomorphisms mapping a
submodule `p` into itself, the part of a joint eigenspace lying in `p` is the image of the
joint eigenspace of the restricted family. This is the eigenspace analogue of
`Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo`. -/
theorem _root_.Submodule.inf_iInf_eigenspace_of_forall_mapsTo {ι : Type*}
    {f : ι → Module.End K V} (p : Submodule K V) (hp : ∀ i, Set.MapsTo (f i) p p)
    (χ : ι → K) :
    p ⊓ ⨅ i, (f i).eigenspace (χ i) =
      (⨅ i, Module.End.eigenspace ((f i).restrict (hp i)) (χ i)).map p.subtype := by
  cases isEmpty_or_nonempty ι
  · simp [iInf_of_isEmpty]
  · simp_rw [Module.End.eigenspace, inf_iInf, p.inf_genEigenspace _ (hp _),
      Submodule.map_iInf _ p.injective_subtype]

end BridgeScalars

section RingScalars

variable [CommRing K] [IsCancelMulZero K] [Module K V] [Module.IsTorsionFree K V]

omit [IsCancelMulZero K] in
/-- The joint eigenspaces of **any** family of endomorphisms, indexed by their eigenvalue
functions, are supremum-independent — no commutation and no semisimplicity. A single
endomorphism has independent eigenspaces (`Module.End.eigenspaces_iSupIndep`), and pointwise
infima of independent families are independent (`iSupIndep.iInf`). -/
lemma iSupIndep_iInf_eigenspace [IsDomain K] {ι : Type*} (f : ι → Module.End K V) :
    iSupIndep fun χ : ι → K ↦ ⨅ i, (f i).eigenspace (χ i) :=
  iSupIndep.iInf (fun i ↦ (f i).eigenspace) fun i ↦ (f i).eigenspaces_iSupIndep

section Monoid

variable [Monoid G]

/-- If `v ≠ 0` is a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` with eigenvalues `χ g`, then the eigenvalue at the
identity is `1`. -/
lemma eigenvalue_one_of_jointEigenvector (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) : χ 1 = 1 := by
  have h1 := hv_mem 1
  rw [Module.End.mem_eigenspace_iff, map_one, Module.End.one_apply] at h1
  exact (smul_left_inj hv).mp (by rw [← h1, one_smul])

/-- If `v ≠ 0` is a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` with eigenvalues `χ g`, then the eigenvalues are
multiplicative: `χ (g₁ * g₂) = χ g₁ * χ g₂`. -/
lemma eigenvalue_mul_of_jointEigenvector (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g₁ g₂ : G) :
    χ (g₁ * g₂) = χ g₁ * χ g₂ := by
  have h := hv_mem (g₁ * g₂)
  rw [Module.End.mem_eigenspace_iff, map_mul] at h
  refine (smul_left_inj hv).mp ?_
  rw [← h, Module.End.mul_apply, Module.End.mem_eigenspace_iff.mp (hv_mem g₂), map_smul,
    Module.End.mem_eigenspace_iff.mp (hv_mem g₁), smul_smul, mul_comm (χ g₂) (χ g₁)]

end Monoid

section Group

variable [Group G]

/-- The eigenvalues of a nonzero joint eigenvector of a group representation are
nonzero: `χ g · χ g⁻¹ = χ 1 = 1`. -/
lemma eigenvalue_ne_zero_of_jointEigenvector [Nontrivial K]
    (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g : G) :
    χ g ≠ 0 :=
  left_ne_zero_of_mul_eq_one (b := χ g⁻¹) (by
    rw [← eigenvalue_mul_of_jointEigenvector ρ χ v hv hv_mem, mul_inv_cancel,
      eigenvalue_one_of_jointEigenvector ρ χ v hv hv_mem])

/-- Given a joint eigenvector `v ≠ 0` for a monoid-hom representation
`ρ : G →* Module.End K V` of a group `G`, the eigenvalue function `χ : G → K`
factors through a monoid homomorphism `G →* Kˣ`. -/
def unitHomOfJointEigenvector (ρ : G →* Module.End K V) (χ : G → K) (v : V)
    (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) : G →* Kˣ where
  -- multiplicativity supplies the inverse outright: `χ g * χ g⁻¹ = χ 1 = 1`
  toFun g :=
    ⟨χ g, χ g⁻¹,
      by rw [← eigenvalue_mul_of_jointEigenvector ρ χ v hv hv_mem, mul_inv_cancel,
          eigenvalue_one_of_jointEigenvector ρ χ v hv hv_mem],
      by rw [← eigenvalue_mul_of_jointEigenvector ρ χ v hv hv_mem, inv_mul_cancel,
          eigenvalue_one_of_jointEigenvector ρ χ v hv hv_mem]⟩
  map_one' := Units.ext (eigenvalue_one_of_jointEigenvector ρ χ v hv hv_mem)
  map_mul' g₁ g₂ :=
    Units.ext (eigenvalue_mul_of_jointEigenvector ρ χ v hv hv_mem g₁ g₂)

@[simp]
lemma unitHomOfJointEigenvector_apply (ρ : G →* Module.End K V) (χ : G → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g : G) :
    ((unitHomOfJointEigenvector ρ χ v hv hv_mem g) : K) = χ g := (rfl)

/-- If the joint eigenspace of an eigenvalue function `χ` of a group representation is
nonzero, then `χ` is (the underlying function of) a character `G →* Kˣ`. -/
lemma exists_unitHom_of_iInf_eigenspace_ne_bot {ρ : G →* Module.End K V}
    {χ : G → K} (hχ : ⨅ g, (ρ g).eigenspace (χ g) ≠ ⊥) :
    ∃ χ₀ : G →* Kˣ, (fun g ↦ ((χ₀ g) : K)) = χ := by
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hχ
  exact ⟨unitHomOfJointEigenvector ρ χ v hv_ne ((Submodule.mem_iInf _).mp hv_mem), rfl⟩

end Group

end RingScalars

/-! ### Simultaneous diagonalization

The remaining results need a field: independence goes through the generalized eigenspaces,
and the spanning statements are the algebraically-closed finite-dimensional ones.
-/

section FieldScalars

variable [Field K] [Module K V]

/-- Over an algebraically closed field and in finite dimension, the joint eigenspaces of a
pairwise-commuting family of semisimple endomorphisms exhaust the space. -/
lemma iSup_iInf_eigenspace_eq_top_of_isSemisimple [IsAlgClosed K]
    [FiniteDimensional K V] {ι : Type*} (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j)) (hss : ∀ i, (f i).IsSemisimple) :
    (⨆ χ : ι → K, ⨅ i, (f i).eigenspace (χ i)) = ⊤ := by
  have heq (i : ι) (μ : K) : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  simpa only [heq] using
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      hcomm fun i ↦ by simpa only [heq] using (hss i).iSup_eigenspace_eq_top

/-- A finite-dimensional submodule invariant under a pairwise-commuting family of
endomorphisms whose **restrictions** to it are semisimple is the supremum of its
intersections with the joint eigenspaces: the restricted family diagonalizes, with no
assumption on the ambient operators. -/
lemma iSup_inf_iInf_eigenspace_of_invariant [IsAlgClosed K] {ι : Type*}
    (f : ι → Module.End K V)
    (p : Submodule K V) [FiniteDimensional K p] (hp : ∀ i, ∀ x ∈ p, f i x ∈ p)
    (hcomm : Pairwise fun i j ↦ Commute ((f i).restrict (hp i)) ((f j).restrict (hp j)))
    (hss : ∀ i, Module.End.IsSemisimple ((f i).restrict (hp i))) :
    (⨆ χ : ι → K, p ⊓ ⨅ i, (f i).eigenspace (χ i)) = p := by
  simp_rw [fun χ ↦ Submodule.inf_iInf_eigenspace_of_forall_mapsTo (f := f) p hp χ,
    ← Submodule.map_iSup]
  suffices h_restrict_top :
      (⨆ χ : ι → K, ⨅ i,
        Module.End.eigenspace ((f i).restrict (hp i)) (χ i)) = ⊤ by
    rw [h_restrict_top, Submodule.map_top, Submodule.range_subtype]
  exact iSup_iInf_eigenspace_eq_top_of_isSemisimple (fun i ↦ (f i).restrict (hp i))
    hcomm hss

section CharHom

variable [Group G] {ρ : G →* Module.End K V}

/-- **Character-indexed spanning**: for a commuting semisimple representation of a group
over an algebraically closed field, in finite dimension, the joint eigenspaces indexed by
characters `G →* Kˣ` exhaust the space — eigenvalue functions that are not
characters contribute `⊥`. -/
lemma iSup_iInf_eigenspace_unitHom_eq_top [IsAlgClosed K] [FiniteDimensional K V]
    (hcomm : Pairwise fun g₁ g₂ ↦ Commute (ρ g₁) (ρ g₂))
    (hss : ∀ g, (ρ g).IsSemisimple) :
    (⨆ χ₀ : G →* Kˣ, ⨅ g, (ρ g).eigenspace (χ₀ g)) = ⊤ := by
  have h := iSup_iInf_eigenspace_eq_top_of_isSemisimple (fun g ↦ ρ g) hcomm hss
  refine le_antisymm le_top (h ▸ iSup_le fun χ ↦ ?_)
  by_cases hχ : (⨅ g, (ρ g).eigenspace (χ g)) = ⊥
  · simp only [hχ, bot_le]
  · obtain ⟨χ₀, rfl⟩ := exists_unitHom_of_iInf_eigenspace_ne_bot hχ
    exact le_iSup (fun ψ : G →* Kˣ ↦ ⨅ g, (ρ g).eigenspace (ψ g)) χ₀

/-- **Character-indexed independence** of the joint eigenspaces, for any representation. -/
lemma iSupIndep_iInf_eigenspace_unitHom :
    iSupIndep fun χ₀ : G →* Kˣ ↦ ⨅ g, (ρ g).eigenspace (χ₀ g) :=
  (iSupIndep_iInf_eigenspace (fun g ↦ ρ g)).comp
    fun _ _ h ↦ MonoidHom.ext fun g ↦ Units.ext (congr_fun h g)

/-- **Character-indexed decomposition of a finite-dimensional invariant submodule**,
assuming only that the restricted representation is semisimple. -/
lemma iSup_inf_iInf_eigenspace_unitHom_of_invariant [IsAlgClosed K]
    (p : Submodule K V) [FiniteDimensional K p] (hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p)
    (hcomm : Pairwise fun g₁ g₂ ↦
      Commute ((ρ g₁).restrict (hp g₁)) ((ρ g₂).restrict (hp g₂)))
    (hss : ∀ g, Module.End.IsSemisimple ((ρ g).restrict (hp g))) :
    (⨆ χ₀ : G →* Kˣ, p ⊓ ⨅ g, (ρ g).eigenspace (χ₀ g)) = p := by
  have h := iSup_inf_iInf_eigenspace_of_invariant (fun g ↦ ρ g) p hp hcomm hss
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) ?_
  conv_lhs => rw [← h]
  refine iSup_le fun χ ↦ ?_
  by_cases hχ : p ⊓ (⨅ g, (ρ g).eigenspace (χ g)) = ⊥
  · simp only [hχ, bot_le]
  · obtain ⟨χ₀, rfl⟩ := exists_unitHom_of_iInf_eigenspace_ne_bot
      (fun h_bot ↦ hχ (by rw [h_bot, inf_bot_eq]))
    exact le_iSup (fun ψ : G →* Kˣ ↦ p ⊓ ⨅ g, (ρ g).eigenspace (ψ g)) χ₀

end CharHom


end FieldScalars

/-! ### Fourier decomposition

Needs only a commutative domain in which `Nat.card G` is invertible.
-/

section DomainScalars

variable [CommRing K] [IsDomain K] [Module K V]

section FourierDecomposition

/-! ### Unconditional decomposition for finite commutative groups

For a finite commutative group `G` acting through `ρ : G →* Module.End K V` on any module
over a commutative domain with enough roots of unity — with no finite-dimensionality
assumption — the classical character projectors `|G|⁻¹ • ∑ d, χ(d)⁻¹ • ρ d` decompose every
vector into joint eigenvectors, so the joint eigenspaces indexed by `G →* Kˣ` span. -/

variable [CommGroup G] [Finite G]

private noncomputable instance : Fintype G :=
  Fintype.ofFinite _

private noncomputable instance : Fintype (G →* Kˣ) :=
  Fintype.ofFinite _

open Finset

variable {ρ : G →* Module.End K V}

/-- The Fourier projector for `χ₀`, applied to a vector. -/
private noncomputable def fourierComponent (χ₀ : G →* Kˣ) (v : V) : V :=
  Ring.inverse (Nat.card G : K) • ∑ d : G, (((χ₀ d)⁻¹ : Kˣ) : K) • ρ d v

variable (ρ) in
-- the projector lands in the joint eigenspace, by reindexing the averaged sum
omit [IsDomain K] in
private lemma fourierComponent_mem (χ₀ : G →* Kˣ) (v : V) (g : G) :
    fourierComponent (ρ := ρ) χ₀ v ∈ (ρ g).eigenspace (χ₀ g) := by
  rw [Module.End.mem_eigenspace_iff, fourierComponent, map_smul,
    smul_comm ((χ₀ g : Kˣ) : K) (Ring.inverse (Nat.card G : K))]
  congr 1
  rw [map_sum]
  calc ∑ d : G, ρ g ((((χ₀ d)⁻¹ : Kˣ) : K) • ρ d v)
      = ∑ d : G, (((χ₀ d)⁻¹ : Kˣ) : K) • ρ (g * d) v := by
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        rw [map_smul, map_mul, Module.End.mul_apply]
    _ = ∑ e : G, (((χ₀ (g⁻¹ * e))⁻¹ : Kˣ) : K) • ρ e v := by
        exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun d ↦ by simp
    _ = (χ₀ g : K) • ∑ e : G, (((χ₀ e)⁻¹ : Kˣ) : K) • ρ e v := by
        rw [smul_sum]
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [smul_smul]
        congr 1
        rw [map_mul, map_inv, mul_inv, inv_inv, Units.val_mul]

variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

private instance : HasEnoughRootsOfUnity K (Monoid.exponent Gˣ) :=
  Monoid.exponent_eq_of_mulEquiv (toUnits (G := G)).symm ▸ inferInstance

-- the character group of a finite commutative group over a commutative domain with enough
-- roots of unity has the size of the group, by Mathlib's character duality
omit [IsDomain K] in
private lemma card_unitHom : Nat.card (G →* Kˣ) = Nat.card G := by
  rw [Nat.card_congr (MulChar.equivToUnitHom.trans
      (toUnits (G := G)).monoidHomCongrLeftEquiv.symm).symm,
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity G K,
    Nat.card_congr (toUnits (G := G)).toEquiv.symm]

/-- Evaluation at `d`, as a multiplicative character of the finite character group `G →* Kˣ`. -/
private noncomputable def evalCharHom (d : G) : MulChar (G →* Kˣ) K :=
  MulChar.ofUnitHom ((MonoidHom.eval d).comp (Units.coeHom (G →* Kˣ)))

omit [Finite G] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
omit [IsDomain K] in
private lemma evalCharHom_apply (d : G) (χ : G →* Kˣ) :
    evalCharHom (K := K) d χ = ((χ d : Kˣ) : K) := by
  simpa [evalCharHom] using
    MulChar.ofUnitHom_coe ((MonoidHom.eval d).comp (Units.coeHom (G →* Kˣ))) (toUnits χ)

-- second orthogonality, from Mathlib's character-sum vanishing applied to `evalCharHom d`
private lemma sum_unitHom_apply_eq_zero
    {d : G} (hd : d ≠ 1) :
    ∑ χ : G →* Kˣ, ((χ d : Kˣ) : K) = 0 := by
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G K hd
  have hne : evalCharHom (K := K) d ≠ 1 := fun h ↦ hψ <| by
    have hval := congrArg (fun χ : MulChar (G →* Kˣ) K ↦ χ ψ) h
    rw [evalCharHom_apply, MulChar.one_apply (Group.isUnit ψ)] at hval
    exact Units.val_eq_one.mp hval
  simpa [evalCharHom_apply] using MulChar.sum_eq_zero_of_ne_one hne


-- every vector is the sum of its projections, by second orthogonality
private lemma sum_fourierComponent (hunit : IsUnit (Nat.card G : K)) (v : V) :
    ∑ χ₀ : G →* Kˣ, fourierComponent (ρ := ρ) χ₀ v = v := by
  unfold fourierComponent
  rw [← smul_sum, Finset.sum_comm]
  have hcol : ∀ d : G, ∑ χ₀ : G →* Kˣ, (((χ₀ d)⁻¹ : Kˣ) : K) • ρ d v =
      (∑ χ₀ : G →* Kˣ, ((χ₀ d⁻¹ : Kˣ) : K)) • ρ d v := by
    intro d
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun χ₀ _ ↦ by rw [map_inv]
  rw [Finset.sum_congr rfl fun d _ ↦ hcol d]
  have hsplit : ∀ d : G, d ≠ 1 → (∑ χ₀ : G →* Kˣ, ((χ₀ d⁻¹ : Kˣ) : K)) • ρ d v = 0 := by
    intro d hd
    rw [sum_unitHom_apply_eq_zero (by simpa using hd), zero_smul]
  rw [Finset.sum_eq_single 1 (fun d _ hd ↦ hsplit d hd) (by simp)]
  have hone : ∀ χ₀ : G →* Kˣ, ((χ₀ (1 : G)⁻¹ : Kˣ) : K) = 1 := by simp
  rw [Finset.sum_congr rfl fun χ₀ _ ↦ hone χ₀]
  have hcard : (∑ _χ₀ : G →* Kˣ, (1 : K)) = (Nat.card G : K) := by
    rw [Finset.sum_const, card_univ, nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card,
      card_unitHom]
  rw [hcard, map_one, Module.End.one_apply, smul_smul,
    Ring.inverse_mul_cancel _ hunit, one_smul]

/-- **Unconditional character-indexed spanning** for a finite commutative group acting on
an arbitrary module over a commutative domain with enough roots of unity: the classical
character projectors decompose every vector, with no finite-dimensionality or
semisimplicity hypotheses. -/
theorem iSup_iInf_eigenspace_unitHom_eq_top_of_commGroup
    (hcard : IsUnit (Nat.card G : K)) :
    (⨆ χ₀ : G →* Kˣ, ⨅ g, (ρ g).eigenspace (χ₀ g)) = ⊤ := by
  refine top_unique fun v _ ↦ ?_
  rw [← sum_fourierComponent (ρ := ρ) hcard v]
  exact Submodule.sum_mem _ fun χ₀ _ ↦ Submodule.mem_iSup_of_mem χ₀
    (Submodule.mem_iInf _ |>.mpr fun g ↦ fourierComponent_mem ρ χ₀ v g)

/-- **Unconditional decomposition of an invariant submodule**: the character projectors
preserve every `ρ`-invariant submodule, so it is the supremum of its intersections with
the joint eigenspaces — again with no finite-dimensionality hypothesis. -/
theorem iSup_inf_iInf_eigenspace_unitHom_of_invariant_of_commGroup
    (hcard : IsUnit (Nat.card G : K))
    (p : Submodule K V) (hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p) :
    (⨆ χ₀ : G →* Kˣ, p ⊓ ⨅ g, (ρ g).eigenspace (χ₀ g)) = p := by
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) fun v hv ↦ ?_
  rw [← sum_fourierComponent (ρ := ρ) hcard v]
  refine Submodule.sum_mem _ fun χ₀ _ ↦ Submodule.mem_iSup_of_mem χ₀ ?_
  refine Submodule.mem_inf.mpr ⟨?_, Submodule.mem_iInf _ |>.mpr fun g ↦
    fourierComponent_mem ρ χ₀ v g⟩
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun d _ ↦
    Submodule.smul_mem _ _ (hp d v hv))

end FourierDecomposition

end DomainScalars

end
