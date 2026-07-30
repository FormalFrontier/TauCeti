/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.TensorSquare
public import TauCeti.LinearAlgebra.ExteriorPower
public import TauCeti.RepresentationTheory.ExteriorPower
public import TauCeti.RepresentationTheory.SymmetricPower
public import TauCeti.RepresentationTheory.Tensor.Power

/-!
# Tensor-square decompositions of representations

When `2` is invertible, the tensor square of a representation splits into its symmetric and
exterior squares. This file lifts the natural linear decomposition to representations. It also
proves the corresponding trace identity over every field, including characteristic two where the
decomposition does not split.

## Main definitions

* `Representation.tensorSquareEquivSymmetricExterior` is the natural representation equivalence.
* `Representation.char_tensorSquare` is the tensor-square character identity.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “The first decomposition”.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 6.
* Mathlib's exterior-power universal-property, pairing, and basis APIs, by Sophie Morel,
  Joël Riou, and Daniel Morrison.
-/

public section

open scoped TensorProduct

universe v w

variable {R : Type} {G : Type v} {M : Type w}

namespace TauCeti.TensorSquare

private theorem toTensorPower_ιMulti_two {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] (f : Fin 2 → M) :
    exteriorPower.toTensorPower R M 2 (exteriorPower.ιMulti R 2 f) =
      PiTensorProduct.tprod R f -
        PiTensorProduct.tprod R (fun i ↦ f (Equiv.swap 0 1 i)) := by
  classical
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by
    ext e
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact perm_fin_two_eq_one_or_swap e
  rw [exteriorPower.toTensorPower_apply_ιMulti, hperm,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  simp [sub_eq_add_neg]

private theorem mk_comp_toTensorPower {R : Type} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] :
    (SymmetricPower.mk R (Fin 2) M).comp
      (exteriorPower.toTensorPower R M 2) = 0 := by
  classical
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  -- `SymmetricPower.tprod` is `SymmetricPower.mk` of a pure tensor power, so `tprod_equiv`
  -- says the two orders have the same symmetric class once that definition is unfolded.
  have hswap : SymmetricPower.mk R (Fin 2) M (PiTensorProduct.tprod R f) =
      SymmetricPower.mk R (Fin 2) M
        (PiTensorProduct.tprod R fun i ↦ f (Equiv.swap 0 1 i)) := by
    simpa only [SymmetricPower.tprod, LinearMap.compMultilinearMap_apply] using
      (SymmetricPower.tprod_equiv (Equiv.swap (0 : Fin 2) 1) f).symm
  rw [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    toTensorPower_ιMulti_two, map_sub, hswap, sub_self]
  simp

private noncomputable def symToAlternatingQuotient {R : Type} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] :
    Sym[R]^2 M →ₗ[R]
      (⨂[R]^2 M) ⧸ LinearMap.range (exteriorPower.toTensorPower R M 2) where
  toFun :=
    (addConGen (SymmetricPower.Rel R (Fin 2) M)).lift
      (LinearMap.toAddMonoidHom
        (Submodule.mkQ (LinearMap.range (exteriorPower.toTensorPower R M 2))))
      (by
        apply AddCon.addConGen_le.2
        intro x y h
        cases h with
        | perm e f =>
          apply (AddCon.ker_rel _).2
          apply (Submodule.Quotient.eq _).2
          rcases perm_fin_two_eq_one_or_swap e with rfl | rfl
          · simp
          · exact ⟨exteriorPower.ιMulti R 2 f, toTensorPower_ιMulti_two f⟩)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x ↦ by
    exact congrArg
      (Submodule.Quotient.mk
        (p := LinearMap.range (exteriorPower.toTensorPower R M 2)))
      ((LinearMap.id.map_smul r x))

private theorem symToAlternatingQuotient_mk {R : Type} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] (x : ⨂[R]^2 M) :
    symToAlternatingQuotient (R := R) (M := M)
        (SymmetricPower.mk R (Fin 2) M x) =
      Submodule.Quotient.mk x := by
  simp [symToAlternatingQuotient, SymmetricPower.mk]

-- These maps form the characteristic-free exact sequence `⋀²M → M⊗M → Sym²M`.
private theorem range_toTensorPower_eq_ker_mk {R : Type} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] :
    LinearMap.range (exteriorPower.toTensorPower R M 2) =
      LinearMap.ker (SymmetricPower.mk R (Fin 2) M) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have h := LinearMap.congr_fun (mk_comp_toTensorPower (R := R) (M := M)) x
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    apply (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (exteriorPower.toTensorPower R M 2))).mp
    rw [← symToAlternatingQuotient_mk x, hx, map_zero]

-- Mathlib builds `exteriorPower.pairingDual` by dualizing `exteriorPower.toTensorPower`, but
-- records that factorization only inside the definitions; this states it.
private theorem pairingDual_ιMulti_apply {R : Type} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    (g : Fin 2 → Module.Dual R M) (x : ⋀[R]^2 M) :
    exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 g) x =
      TensorPower.multilinearMapToDual R M 2 g (exteriorPower.toTensorPower R M 2 x) := by
  simp [exteriorPower.pairingDual, exteriorPower.alternatingMapToDual]

private theorem toTensorPower_injective {R : Type} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M] :
    Function.Injective (exteriorPower.toTensorPower R M 2) := by
  classical
  let b := Module.finBasis R M
  intro x y h
  apply (b.exteriorPower 2).repr.injective
  ext s
  -- Every basis coordinate on `⋀[R]^2 M` factors through `exteriorPower.toTensorPower`.
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_repr_apply]
  simp only [exteriorPower.ιMultiDual, exteriorPower.ιMulti_family,
    pairingDual_ιMulti_apply, h]

-- Split an exact sequence as vector spaces. In that splitting the middle action is block
-- triangular, so its trace is the sum of the traces on the subspace and the quotient.
private theorem trace_eq_add_of_exact
    {K A B C : Type*} [Field K]
    [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    (i : A →ₗ[K] B) (q : B →ₗ[K] C)
    (fA : A →ₗ[K] A) (fB : B →ₗ[K] B) (fC : C →ₗ[K] C)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : LinearMap.range i = LinearMap.ker q)
    (hfi : fB.comp i = i.comp fA) (hfq : q.comp fB = fC.comp q) :
    LinearMap.trace K B fB =
      LinearMap.trace K A fA + LinearMap.trace K C fC := by
  classical
  -- Split `B ≃ₗ A × C`, using Mathlib's correspondence between sections of `q` and splittings.
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  obtain ⟨e, hie, hqe⟩ :=
    (LinearMap.exact_iff.mpr hexact.symm).splitSurjectiveEquiv hi ⟨s, hs⟩
  -- `B` inherits finite-dimensionality from the splitting, so it need not be assumed.
  haveI : FiniteDimensional K B := e.symm.finiteDimensional
  -- In that splitting `fB` becomes block upper triangular: it fixes the `A` summand, acting there
  -- as `fA`, and covers `fC` on the `C` factor.
  set F : (A × C) →ₗ[K] (A × C) := e.conj fB with hF_def
  have hia : ∀ x : A, e.symm ((LinearMap.inl K A C) x) = i x := fun x => by rw [hie]; rfl
  have hie' : ∀ x : A, e (i x) = (LinearMap.inl K A C) x := fun x => by
    rw [← hia x, LinearEquiv.apply_symm_apply]
  have hF_inl : F.comp (LinearMap.inl K A C) = (LinearMap.inl K A C).comp fA := by
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, hF_def, LinearEquiv.conj_apply_apply, hia]
    rw [← LinearMap.comp_apply, hfi, LinearMap.comp_apply, hie']
  have hsnd : ∀ b : B, (LinearMap.snd K A C) (e b) = q b := fun b => by rw [hqe]; rfl
  have hqsymm : ∀ x : A × C, q (e.symm x) = (LinearMap.snd K A C) x := fun x => by
    rw [← hsnd (e.symm x), LinearEquiv.apply_symm_apply]
  have hsndF : (LinearMap.snd K A C).comp F = fC.comp (LinearMap.snd K A C) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, hF_def, LinearEquiv.conj_apply_apply, hsnd]
    rw [← LinearMap.comp_apply, hfq, LinearMap.comp_apply, hqsymm]
  -- Triangularity: the only off-diagonal block is `C → A`. Composed the other way round it is
  -- zero, so `trace_comp_comm'` makes its contribution vanish.
  set u : C →ₗ[K] A := (LinearMap.fst K A C).comp (F.comp (LinearMap.inr K A C)) with hu_def
  have hF : F = LinearMap.prodMap fA fC +
      (LinearMap.inl K A C).comp (u.comp (LinearMap.snd K A C)) := by
    apply LinearMap.ext
    rintro ⟨a, c⟩
    have hsplit : ((a, c) : A × C) = (LinearMap.inl K A C) a + (LinearMap.inr K A C) c := by
      ext <;> simp
    apply Prod.ext
    · rw [hsplit, map_add, ← LinearMap.comp_apply, hF_inl]
      simp [hu_def]
    · simpa only [LinearMap.add_apply, LinearMap.prodMap_apply, LinearMap.comp_apply,
        LinearMap.inl_apply, LinearMap.snd_apply, Prod.snd_add, add_zero] using
          LinearMap.congr_fun hsndF (a, c)
  have hoff : LinearMap.trace K (A × C)
      ((LinearMap.inl K A C).comp (u.comp (LinearMap.snd K A C))) = 0 := by
    rw [LinearMap.trace_comp_comm']
    have hz : (u.comp (LinearMap.snd K A C)).comp (LinearMap.inl K A C) = 0 := by
      apply LinearMap.ext
      intro a
      simp
    rw [hz, map_zero]
  rw [← LinearMap.trace_conj' fB e, ← hF_def, hF, map_add, LinearMap.trace_prodMap', hoff,
    add_zero]

end TauCeti.TensorSquare

namespace Representation

section CommRing

variable [CommRing R] [Invertible (2 : R)] [Monoid G]
variable [AddCommGroup M] [Module R M]

/-- The tensor square of a representation is equivalent to the product of its symmetric and
exterior squares when `2` is invertible. -/
noncomputable def tensorSquareEquivSymmetricExterior (ρ : Representation R G M) :
    (ρ.tensorPower 2).Equiv ((ρ.symmetricPower 2).prod (ρ.exteriorPower 2)) :=
  .mk (TauCeti.tensorSquareEquivSymmetricExterior R M) fun g ↦ by
    apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := R))
    rintro _ ⟨f, rfl⟩
    simp only [LinearMap.comp_apply, tensorPower_apply, PiTensorProduct.map_tprod]
    -- Unfold the representation action and product wrappers to compare their pure-tensor values.
    change TauCeti.tensorSquareEquivSymmetricExterior R M
        (PiTensorProduct.tprod R fun i ↦ ρ g (f i)) =
      ((ρ.symmetricPower 2).prod (ρ.exteriorPower 2)) g
        (TauCeti.tensorSquareEquivSymmetricExterior R M (PiTensorProduct.tprod R f))
    have h₁ := TauCeti.tensorSquareEquivSymmetricExterior_tprod R M
      (fun i ↦ ρ g (f i))
    have h₂ := TauCeti.tensorSquareEquivSymmetricExterior_tprod R M f
    rw [h₁, h₂]
    simp only [prod_apply_apply, symmetricPower_apply, SymmetricPower.map_tprod,
      exteriorPower_apply, exteriorPower.map_apply_ιMulti, Prod.mk.injEq, true_and]
    apply congrArg (exteriorPower.ιMulti R 2)
    funext i
    rfl

/-- The underlying linear equivalence of the tensor-square decomposition is the natural
linear-algebraic decomposition. -/
@[simp]
theorem tensorSquareEquivSymmetricExterior_toLinearEquiv (ρ : Representation R G M) :
    ρ.tensorSquareEquivSymmetricExterior.toLinearEquiv =
      TauCeti.tensorSquareEquivSymmetricExterior R M :=
  (rfl)

end CommRing

section Field

variable [Field R] [Monoid G]
variable [AddCommGroup M] [Module R M] [FiniteDimensional R M]

/-- Over any field, the tensor-square character is the sum of the symmetric-square and
exterior-square characters. -/
theorem char_tensorSquare (ρ : Representation R G M) (g : G) :
    (ρ.character g) ^ 2 =
      (ρ.symmetricPower 2).character g + (ρ.exteriorPower 2).character g := by
  classical
  rw [← char_tensorPower ρ 2 g]
  simp only [Representation.character, tensorPower_apply, symmetricPower_apply,
    exteriorPower_apply]
  -- The alternating inclusion and symmetric quotient intertwine the three induced actions.
  have hfi :
      (PiTensorProduct.map fun _ : Fin 2 ↦ ρ g).comp
          (exteriorPower.toTensorPower R M 2) =
        (exteriorPower.toTensorPower R M 2).comp
          (exteriorPower.map 2 (ρ g)) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
    rw [TauCeti.TensorSquare.toTensorPower_ιMulti_two,
      exteriorPower.map_apply_ιMulti,
      TauCeti.TensorSquare.toTensorPower_ιMulti_two]
    simp only [map_sub, PiTensorProduct.map_tprod, Function.comp_apply]
    congr 1
  have hfq :
      (SymmetricPower.mk R (Fin 2) M).comp
          (PiTensorProduct.map fun _ : Fin 2 ↦ ρ g) =
        (SymmetricPower.map (ρ g)).comp
          (SymmetricPower.mk R (Fin 2) M) := by
    apply LinearMap.ext
    intro x
    simp
  -- Trace is additive along the exact sequence `⋀²M → M⊗M → Sym²M`.
  have h := TauCeti.TensorSquare.trace_eq_add_of_exact
    (exteriorPower.toTensorPower R M 2)
    (SymmetricPower.mk R (Fin 2) M)
    (exteriorPower.map 2 (ρ g))
    (PiTensorProduct.map fun _ : Fin 2 ↦ ρ g)
    (SymmetricPower.map (ρ g))
    TauCeti.TensorSquare.toTensorPower_injective
    (LinearMap.range_eq_top.mp (SymmetricPower.range_mk R (Fin 2) M))
    TauCeti.TensorSquare.range_toTensorPower_eq_ker_mk hfi hfq
  simpa only [add_comm] using h

end Field

end Representation
