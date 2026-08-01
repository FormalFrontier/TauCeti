/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Action
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.Opposite

/-!
# Deck transformations of the universal cover

For a path-connected, locally path-connected, semilocally simply connected space `X`, the
endpoint projection from the based-path universal cover is regular. Indeed, the explicit
fundamental-group action from `UniversalCover.Action` acts through deck transformations and is
transitive on each fibre.

Combining this regularity with the simple connectedness of the universal cover and the generic
regular-cover comparison gives the convention-correct form of the classical calculation

`Deck (UniversalCover.proj : UniversalCover x₀ → X) ≃* (FundamentalGroup X x₀)ᵐᵒᵖ`.

The opposite is genuine: the fundamental group acts on the universal cover by prepending the
inverse loop, while deck transformations are composed as homeomorphisms. This is the convention
pinned by `TauCeti.Deck.IsRegular.deckFundamentalGroupEquiv`.

## Main declarations

* `TauCeti.UniversalCover.loopDeck`: the deck transformation induced by a loop class.
* `TauCeti.UniversalCover.isRegular_proj`: regularity of the universal-cover projection.
* `TauCeti.UniversalCover.deckFundamentalGroupEquiv`: the deck group of the universal cover is
  the opposite fundamental group.

## References

This completes Stage 1, item 5 of `TauCetiRoadmap/UniversalCovers/README.md`. The construction
uses the universal-cover action adapted from Kim Morrison's mathlib4 PR
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292), and the generic
comparison ultimately uses Junyan Xu's `IsQuotientCoveringMap.fundamentalGroupEquiv` from
`Mathlib.Topology.Homotopy.Lifting`.
-/

public section
noncomputable section

namespace TauCeti.UniversalCover

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

/-- A loop class acts on the universal cover by a deck transformation of the endpoint
projection. -/
def loopDeck (g : FundamentalGroup X x₀) :
    Deck (proj : UniversalCover x₀ → X) :=
  ⟨Homeomorph.smul g, fun p => proj_smul g p⟩

/-- The deck transformation induced by a loop class acts by the fundamental-group action. -/
@[simp]
lemma loopDeck_apply (g : FundamentalGroup X x₀) (p : UniversalCover x₀) :
    (loopDeck x₀ g).1 p = g • p :=
  (rfl)

/-- The identity loop class induces the identity deck transformation. -/
@[simp]
lemma loopDeck_one :
    loopDeck x₀ (CategoryTheory.CategoryStruct.id
      ({ as := x₀ } : FundamentalGroupoid X)) = 1 := by
  apply Subtype.ext
  apply Homeomorph.ext
  intro p
  rw [loopDeck_apply]
  exact one_smul _ _

/-- Multiplication of loop classes corresponds to composition of their deck transformations. -/
@[simp]
lemma loopDeck_mul (g h : FundamentalGroup X x₀) :
    loopDeck x₀ (CategoryTheory.CategoryStruct.comp h g) = loopDeck x₀ g * loopDeck x₀ h := by
  apply Subtype.ext
  apply Homeomorph.ext
  intro p
  exact mul_smul g h p

/-- The fundamental-group action, bundled as a homomorphism into the deck group of the
universal-cover projection. -/
def loopDeckHom :
    FundamentalGroup X x₀ →* Deck (proj : UniversalCover x₀ → X) where
  toFun := loopDeck x₀
  map_one' := loopDeck_one x₀
  map_mul' := loopDeck_mul x₀

@[simp]
lemma loopDeckHom_apply (g : FundamentalGroup X x₀) :
    loopDeckHom x₀ g = loopDeck x₀ g :=
  (rfl)

/-- The constant-path lift of the basepoint, regarded as a point of the fibre over the
basepoint. -/
private def reflFiberPoint : (proj : UniversalCover x₀ → X) ⁻¹' {x₀} :=
  ⟨ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀)),
    Set.mem_singleton_iff.mpr (by
      rw [proj_ofBasedPath]
      exact BasedPath.endpoint_ofPath _)⟩

@[simp]
private lemma reflFiberPoint_val :
    (reflFiberPoint x₀ : UniversalCover x₀) =
      ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀)) :=
  rfl

/-- The endpoint projection of the universal cover has regular deck action. -/
theorem isRegular_proj [PathConnectedSpace X] :
    Deck.IsRegular (proj : UniversalCover x₀ → X) := by
  rw [Deck.isRegular_iff_exists_apply_eq]
  refine ⟨proj_surjective, ?_⟩
  intro p q hpq
  obtain ⟨g, hg⟩ := proj_eq_iff_mem_orbit.mp hpq
  refine ⟨loopDeck x₀ g⁻¹, ?_⟩
  rw [loopDeck_apply, ← hg, inv_smul_smul]

/-- The deck transformation group of the based-path universal cover is the opposite of the
fundamental group of the base. -/
noncomputable def deckFundamentalGroupEquiv
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    Deck (proj : UniversalCover x₀ → X) ≃* (FundamentalGroup X x₀)ᵐᵒᵖ :=
  (isRegular_proj x₀).deckFundamentalGroupEquiv (isCoveringMap x₀)
    (reflFiberPoint x₀)

/-- The inverse deck-to-fundamental-group equivalence recovers the explicit loop deck
transformation, with the inverse forced by the left-action convention. -/
@[simp]
lemma deckFundamentalGroupEquiv_symm_op
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X]
    (g : FundamentalGroup X x₀) :
    (deckFundamentalGroupEquiv x₀).symm (MulOpposite.op g) = loopDeck x₀ g⁻¹ := by
  have hmonodromy : ((isCoveringMap x₀).monodromy g.toPath
      (reflFiberPoint x₀) :
        UniversalCover x₀) =
      g⁻¹ • ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀)) := by
    obtain ⟨γ, hγ⟩ := Quotient.exists_rep g.toPath
    rw [← hγ]
    -- `monodromy` is defined by quotient-lifting the endpoint of `liftPath`; unfolding it
    -- after choosing the representative `γ` exposes exactly that defining computation.
    change (isCoveringMap x₀).liftPath γ
        (ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀))) _ 1 = _
    let δ : Path (BasedPath.endpoint (BasedPath.ofPath (Path.refl x₀))) x₀ :=
      γ.cast (BasedPath.endpoint_ofPath _) rfl
    calc
      _ = (isCoveringMap x₀).liftPath δ
          (ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀))) _ 1 := by
        congr 1
      _ = ofBasedPath x₀ (BasedPath.append (BasedPath.ofPath (Path.refl x₀)) δ) :=
        liftPath_apply_one_eq_ofBasedPath_append δ
      _ = g⁻¹ • ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀)) := by
        rw [ofBasedPath_ofPath, Path.Homotopic.Quotient.mk_refl, inv_smul_mk]
        rw [ofBasedPath_def]
        let hend := BasedPath.endpoint_append (BasedPath.ofPath (Path.refl x₀)) δ
        apply UniversalCover.ext hend
        have hcast : HEq
            (Path.Homotopic.Quotient.mk
              (BasedPath.append (BasedPath.ofPath (Path.refl x₀)) δ).toPath)
            (Path.Homotopic.Quotient.mk
              ((Path.refl x₀).trans γ)) :=
          Path.Homotopic.hpath_hext (fun _ ↦ rfl)
        refine hcast.trans (heq_of_eq ?_)
        -- The preceding `HEq` has aligned the dependent path endpoints.  What remains is
        -- its underlying quotient equality, whose displayed types differ only by those casts.
        change Path.Homotopic.Quotient.mk ((Path.refl x₀).trans γ) =
          g.toPath.trans (Path.Homotopic.Quotient.refl x₀)
        rw [← hγ, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl,
          Path.Homotopic.Quotient.refl_trans]
        exact (Path.Homotopic.Quotient.trans_refl _).symm
  apply (Deck.IsRegular.deckFundamentalGroupEquiv_symm_op_eq_iff
    (isRegular_proj x₀) (isCoveringMap x₀)
      (reflFiberPoint x₀)
      g (loopDeck x₀ g⁻¹)).2
  -- Display the fundamental-group coercion and the chosen fibre point explicitly so the
  -- named monodromy calculation above applies without unfolding either wrapper.
  change ((isCoveringMap x₀).monodromy g.toPath (reflFiberPoint x₀) :
    UniversalCover x₀) = (loopDeck x₀ g⁻¹).1 (reflFiberPoint x₀)
  simpa only [Deck.smul_eq_apply, loopDeck_apply, reflFiberPoint_val] using hmonodromy

end TauCeti.UniversalCover
