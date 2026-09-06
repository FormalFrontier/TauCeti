/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Finite completions of number fields are local fields

The completion of a number field at a nonzero prime ideal is a nonarchimedean local field. The
valuative relation on such a completion, its compatibility with the existing topology and its
nontriviality, and the resulting local-field instance under a finite-residue-field hypothesis are
supplied for an arbitrary Dedekind domain in
`TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel`. For rings of integers of number
fields that finiteness hypothesis is automatic.

This instance lets local-field results apply directly to the canonical finite completions used in
global arithmetic, without choosing another valuation or another completion.
-/
