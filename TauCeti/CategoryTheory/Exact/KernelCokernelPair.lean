/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.Biproduct
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels

/-!
# Kernel–cokernel pairs

A *kernel–cokernel pair* in a category with zero morphisms is a pair of composable morphisms
`X ⟶ Y ⟶ Z` with zero composite in which the first morphism is a kernel of the second **and**
the second is a cokernel of the first. Following Bühler, the first morphism of such a pair is
called its *inflation* and the second its *deflation*. Quillen exact structures are, by
definition, isomorphism-closed classes of such pairs, so this file supplies the objects an
`ExactStructure` will range over, together with the calculus those axioms are stated in.

The point of the notion is that it makes sense in an arbitrary additive category: neither
kernels nor cokernels are assumed to exist, so the two universal properties are asserted
explicitly rather than read off from ambient (co)completeness. In a balanced preadditive
category with homology the notion coincides with Mathlib's
`CategoryTheory.ShortComplex.ShortExact`; that comparison is
`TauCeti.isKernelCokernelPair_iff_shortExact`.

## Main definitions

* `TauCeti.IsKernelCokernelPair`: the predicate on a `CategoryTheory.ShortComplex` saying that
  its two morphisms form a kernel–cokernel pair. Its noncomputable accessors
  `TauCeti.IsKernelCokernelPair.fIsKernel` and `TauCeti.IsKernelCokernelPair.gIsCokernel`
  produce the two universal properties.
* `TauCeti.IsKernelCokernelPair.lift` and `TauCeti.IsKernelCokernelPair.desc`: the two
  factorizations, with their defining equations and their uniqueness.

## Main results

* `TauCeti.IsKernelCokernelPair.of_iso` and `TauCeti.isKernelCokernelPair_iff_of_iso`: the
  class of kernel–cokernel pairs is closed under isomorphism of short complexes, as an exact
  structure requires.
* `TauCeti.IsKernelCokernelPair.map`: a functor preserving the two relevant (co)limits carries
  kernel–cokernel pairs to kernel–cokernel pairs.
* `TauCeti.IsKernelCokernelPair.op`, `TauCeti.isKernelCokernelPair_op_iff` and
  `TauCeti.isKernelCokernelPair_unop_iff`: the notion is self-dual, which is what makes the
  Bühler axioms transport to the opposite category.
* `TauCeti.IsKernelCokernelPair.of_isIso_f_of_isZero` and
  `TauCeti.IsKernelCokernelPair.of_isIso_g_of_isZero`: an isomorphism is both an inflation and
  a deflation.
* `TauCeti.IsKernelCokernelPair.of_splitting` and
  `TauCeti.IsKernelCokernelPair.of_hasBinaryBiproduct`: split short complexes, in particular
  `X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂`, are kernel–cokernel pairs. These are the conflations of the split
  exact structure.
* `TauCeti.IsKernelCokernelPair.biprod`: a direct sum of kernel–cokernel pairs is a
  kernel–cokernel pair.
* `TauCeti.isKernelCokernelPair_iff_shortExact`: in a balanced preadditive category the
  kernel–cokernel pairs among the short complexes with homology are exactly the short exact
  ones. These are the conflations of the canonical exact structure on an abelian category.

## Implementation notes

`IsKernelCokernelPair` is a `Prop` whose fields are `Nonempty` universal properties, following
`CategoryTheory.IsPushout`. A class of conflations must be a class in the set-theoretic sense,
so membership has to be a proposition; the universal properties are recovered by choice, which
is harmless because `CategoryTheory.Limits.IsLimit` is a subsingleton.

`of_isIso_f_of_isZero` and `of_isIso_g_of_isZero` are proved directly rather than deduced from
`CategoryTheory.ShortComplex.Splitting.ofIsIsoOfIsZero` and its sibling together with
`of_splitting`, which would need a preadditive category with a zero object. The direct proofs
are no longer, and they keep these two statements — Bühler's axiom E0, that an isomorphism is
both an inflation and a deflation — in the same bare `CategoryTheory.Limits.HasZeroMorphisms`
generality as the rest of the core API. For the same reason `of_hasBinaryBiproduct` and
`biprod` are stated for a bare `CategoryTheory.Limits.HasZeroMorphisms` category with the
biproducts they mention: Mathlib's `CategoryTheory.Limits.biprod.isKernelSndKernelFork` and
its siblings already provide the witnesses there, so routing through `of_splitting` would
gratuitously assume a preadditive category with a zero object.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>. Definition 2.1 and Remarks 2.2–2.8 fix the notion of a
  kernel–cokernel pair and the axioms an exact structure imposes on a class of them.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C]

section HasZeroMorphisms

variable [HasZeroMorphisms C] {S S₁ S₂ : ShortComplex C}

/-- A short complex `S : X₁ ⟶ X₂ ⟶ X₃` is a **kernel–cokernel pair** when `S.f` is a kernel of
`S.g` and `S.g` is a cokernel of `S.f`. This is Bühler's notion of a kernel–cokernel pair; the
conflations of a Quillen exact structure are an isomorphism-closed class of these. -/
structure IsKernelCokernelPair (S : ShortComplex C) : Prop where
  /-- `S.f` is a kernel of `S.g`. -/
  nonempty_fIsKernel : Nonempty (IsLimit (KernelFork.ofι S.f S.zero))
  /-- `S.g` is a cokernel of `S.f`. -/
  nonempty_gIsCokernel : Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero))

namespace IsKernelCokernelPair

/-- The universal property exhibiting `S.f` as a kernel of `S.g`. -/
noncomputable def fIsKernel (h : IsKernelCokernelPair S) :
    IsLimit (KernelFork.ofι S.f S.zero) :=
  h.nonempty_fIsKernel.some

/-- The universal property exhibiting `S.g` as a cokernel of `S.f`. -/
noncomputable def gIsCokernel (h : IsKernelCokernelPair S) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) :=
  h.nonempty_gIsCokernel.some

/-- The inflation of a kernel–cokernel pair is a monomorphism. -/
theorem mono_f (h : IsKernelCokernelPair S) : Mono S.f :=
  mono_of_isLimit_fork h.fIsKernel

/-- The deflation of a kernel–cokernel pair is an epimorphism. -/
theorem epi_g (h : IsKernelCokernelPair S) : Epi S.g :=
  epi_of_isColimit_cofork h.gIsCokernel

section Factorizations

variable {A : C}

/-- The factorization through the kernel `S.f` of a morphism into `S.X₂` killed by `S.g`. -/
noncomputable def lift (h : IsKernelCokernelPair S) (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) :
    A ⟶ S.X₁ :=
  (KernelFork.IsLimit.lift' h.fIsKernel k hk).1

/-- The kernel factorization `lift` satisfies `lift ≫ S.f = k`. -/
@[reassoc (attr := simp)]
theorem lift_f (h : IsKernelCokernelPair S) (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) :
    h.lift k hk ≫ S.f = k :=
  (KernelFork.IsLimit.lift' h.fIsKernel k hk).2

/-- `IsKernelCokernelPair.lift` is the unique factorization through `S.f`. -/
theorem eq_lift (h : IsKernelCokernelPair S) (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) (l : A ⟶ S.X₁)
    (hl : l ≫ S.f = k) : l = h.lift k hk := by
  have := h.mono_f
  rw [← cancel_mono S.f, hl, h.lift_f]

/-- The factorization through the cokernel `S.g` of a morphism out of `S.X₂` killed by `S.f`. -/
noncomputable def desc (h : IsKernelCokernelPair S) (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) :
    S.X₃ ⟶ A :=
  (CokernelCofork.IsColimit.desc' h.gIsCokernel k hk).1

/-- The cokernel factorization `desc` satisfies `S.g ≫ desc = k`. -/
@[reassoc (attr := simp)]
theorem g_desc (h : IsKernelCokernelPair S) (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) :
    S.g ≫ h.desc k hk = k :=
  (CokernelCofork.IsColimit.desc' h.gIsCokernel k hk).2

/-- `IsKernelCokernelPair.desc` is the unique factorization through `S.g`. -/
theorem eq_desc (h : IsKernelCokernelPair S) (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) (l : S.X₃ ⟶ A)
    (hl : S.g ≫ l = k) : l = h.desc k hk := by
  have := h.epi_g
  rw [← cancel_epi S.g, hl, h.g_desc]

end Factorizations

/-- Being a kernel–cokernel pair is invariant under isomorphism of short complexes; this is the
closure property an exact structure demands of its class of conflations. -/
theorem of_iso (h : IsKernelCokernelPair S₁) (e : S₁ ≅ S₂) : IsKernelCokernelPair S₂ where
  nonempty_fIsKernel := ⟨IsKernel.ofIso _ h.fIsKernel _ (asIso e.hom.τ₂) (asIso e.hom.τ₃)
    (asIso e.hom.τ₁) e.hom.comm₂₃ (by simpa using e.hom.comm₁₂)⟩
  nonempty_gIsCokernel := ⟨IsCokernel.ofIso _ h.gIsCokernel _ (asIso e.hom.τ₁) (asIso e.hom.τ₂)
    (asIso e.hom.τ₃) e.hom.comm₁₂ (by simpa using e.hom.comm₂₃)⟩

/-- A functor preserving zero morphisms and the two relevant (co)limits — for instance an
equivalence, or an exact functor between abelian categories — carries kernel–cokernel pairs to
kernel–cokernel pairs. -/
theorem map {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] (h : IsKernelCokernelPair S)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesLimit (parallelPair S.g 0) F]
    [PreservesColimit (parallelPair S.f 0) F] : IsKernelCokernelPair (S.map F) :=
  ⟨⟨KernelFork.mapIsLimit _ h.fIsKernel F⟩, ⟨CokernelCofork.mapIsColimit _ h.gIsCokernel F⟩⟩

/-- A short complex whose first morphism is an isomorphism and whose last object is zero is a
kernel–cokernel pair: an isomorphism is an inflation. -/
theorem of_isIso_f_of_isZero (S : ShortComplex C) [IsIso S.f] (h₃ : IsZero S.X₃) :
    IsKernelCokernelPair S where
  nonempty_fIsKernel := ⟨KernelFork.IsLimit.ofι' _ _ fun k _ => ⟨k ≫ inv S.f, by simp⟩⟩
  nonempty_gIsCokernel := ⟨CokernelCofork.IsColimit.ofEpiOfIsZero _ inferInstance h₃⟩

/-- A short complex whose second morphism is an isomorphism and whose first object is zero is a
kernel–cokernel pair: an isomorphism is a deflation. -/
theorem of_isIso_g_of_isZero (S : ShortComplex C) [IsIso S.g] (h₁ : IsZero S.X₁) :
    IsKernelCokernelPair S where
  nonempty_fIsKernel := ⟨KernelFork.IsLimit.ofMonoOfIsZero _ inferInstance h₁⟩
  nonempty_gIsCokernel := ⟨CokernelCofork.IsColimit.ofπ' _ _ fun k _ => ⟨inv S.g ≫ k, by simp⟩⟩

/-- The opposite of a kernel–cokernel pair is a kernel–cokernel pair. -/
theorem op (h : IsKernelCokernelPair S) : IsKernelCokernelPair S.op :=
  ⟨⟨CokernelCofork.IsColimit.ofπOp S.g S.zero h.gIsCokernel⟩,
    ⟨KernelFork.IsLimit.ofιOp S.f S.zero h.fIsKernel⟩⟩

/-- The un-opposite of a kernel–cokernel pair is a kernel–cokernel pair. -/
theorem unop {S : ShortComplex Cᵒᵖ} (h : IsKernelCokernelPair S) :
    IsKernelCokernelPair S.unop :=
  ⟨⟨CokernelCofork.IsColimit.ofπUnop S.g S.zero h.gIsCokernel⟩,
    ⟨KernelFork.IsLimit.ofιUnop S.f S.zero h.fIsKernel⟩⟩

/-- The biproduct short complex `X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂` is a kernel–cokernel pair. -/
theorem of_hasBinaryBiproduct (X₁ X₂ : C) [HasBinaryBiproduct X₁ X₂] :
    IsKernelCokernelPair (ShortComplex.mk (biprod.inl : X₁ ⟶ _) (biprod.snd : _ ⟶ X₂) (by simp)) :=
  ⟨⟨biprod.isKernelSndKernelFork X₁ X₂⟩, ⟨biprod.isCokernelInlCokernelFork X₁ X₂⟩⟩

/-- A direct sum of two kernel–cokernel pairs is a kernel–cokernel pair. -/
theorem biprod [HasBinaryBiproduct S₁.X₁ S₂.X₁] [HasBinaryBiproduct S₁.X₂ S₂.X₂]
    [HasBinaryBiproduct S₁.X₃ S₂.X₃] (h₁ : IsKernelCokernelPair S₁)
    (h₂ : IsKernelCokernelPair S₂) :
    IsKernelCokernelPair (shortComplexBiprod S₁ S₂) := by
  rw [shortComplexBiprod_eq_mk]
  have := h₁.mono_f
  have := h₂.mono_f
  have := h₁.epi_g
  have := h₂.epi_g
  exact
    { nonempty_fIsKernel := ⟨KernelFork.IsLimit.ofι' _ _ fun k hk =>
        ⟨biprod.lift
          (h₁.lift (k ≫ biprod.fst) (by
            rw [Category.assoc, ← biprod.map_fst S₁.g S₂.g, ← Category.assoc, hk,
              zero_comp]))
          (h₂.lift (k ≫ biprod.snd) (by
            rw [Category.assoc, ← biprod.map_snd S₁.g S₂.g, ← Category.assoc, hk,
              zero_comp])),
          by apply biprod.hom_ext <;> simp⟩⟩
      nonempty_gIsCokernel := ⟨CokernelCofork.IsColimit.ofπ' _ _ fun k hk =>
        ⟨biprod.desc
          (h₁.desc (biprod.inl ≫ k) (by
            rw [← Category.assoc, ← biprod.inl_map S₁.f S₂.f, Category.assoc, hk,
              comp_zero]))
          (h₂.desc (biprod.inr ≫ k) (by
            rw [← Category.assoc, ← biprod.inr_map S₁.f S₂.f, Category.assoc, hk,
              comp_zero])),
          by apply biprod.hom_ext' <;> simp⟩⟩ }

end IsKernelCokernelPair

/-- Being a kernel–cokernel pair only depends on the isomorphism class of a short complex. -/
theorem isKernelCokernelPair_iff_of_iso (e : S₁ ≅ S₂) :
    IsKernelCokernelPair S₁ ↔ IsKernelCokernelPair S₂ :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/-- A short complex is a kernel–cokernel pair if and only if its opposite is; the notion is
self-dual. -/
@[simp]
theorem isKernelCokernelPair_op_iff : IsKernelCokernelPair S.op ↔ IsKernelCokernelPair S :=
  ⟨fun h => h.unop.of_iso S.opUnop, fun h => h.op⟩

/-- A short complex in `Cᵒᵖ` is a kernel–cokernel pair if and only if its un-opposite is; the
notion is self-dual. -/
@[simp]
theorem isKernelCokernelPair_unop_iff {S : ShortComplex Cᵒᵖ} :
    IsKernelCokernelPair S.unop ↔ IsKernelCokernelPair S :=
  ⟨fun h => h.op.of_iso S.unopOp, fun h => h.unop⟩

end HasZeroMorphisms

section Preadditive

variable [Preadditive C] {S : ShortComplex C}

namespace IsKernelCokernelPair

/-- A split short complex is a kernel–cokernel pair. These are the conflations of the split
exact structure on an additive category. -/
theorem of_splitting (s : S.Splitting) : IsKernelCokernelPair S where
  nonempty_fIsKernel := ⟨KernelFork.IsLimit.ofι S.f S.zero
    (fun k _ => k ≫ s.r)
    (fun k hk => by simp only [Category.assoc, s.r_f, Preadditive.comp_sub, Category.comp_id,
      sub_eq_self, reassoc_of% hk, zero_comp])
    (fun k _ l hl => by simp only [← hl, Category.assoc, s.f_r, Category.comp_id])⟩
  nonempty_gIsCokernel := ⟨CokernelCofork.IsColimit.ofπ S.g S.zero
    (fun k _ => s.s ≫ k)
    (fun k hk => by simp only [s.g_s_assoc, Preadditive.sub_comp, Category.id_comp, sub_eq_self,
      Category.assoc, hk, comp_zero])
    (fun k _ l hl => by simp only [← hl, s.s_g_assoc])⟩

/-- A kernel–cokernel pair with homology is a short exact short complex. -/
theorem shortExact [S.HasHomology] (h : IsKernelCokernelPair S) : S.ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel S h.fIsKernel
  mono_f := h.mono_f
  epi_g := h.epi_g

/-- In a balanced preadditive category, a short exact short complex is a kernel–cokernel
pair. -/
theorem of_shortExact [Balanced C] (h : S.ShortExact) : IsKernelCokernelPair S :=
  ⟨⟨h.fIsKernel⟩, ⟨h.gIsCokernel⟩⟩

end IsKernelCokernelPair

/-- **In a balanced preadditive category the kernel–cokernel pairs among the short complexes
with homology are exactly the short exact ones.** This identifies the conflations of the
canonical exact structure of an abelian category with Mathlib's
`CategoryTheory.ShortComplex.ShortExact`. -/
theorem isKernelCokernelPair_iff_shortExact [Balanced C] (S : ShortComplex C) [S.HasHomology] :
    IsKernelCokernelPair S ↔ S.ShortExact :=
  ⟨fun h => h.shortExact, fun h => .of_shortExact h⟩

end Preadditive

end TauCeti
