/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.JordanCurve.Basic
public import TauCeti.Topology.JordanCurve.EmptyInterior
public import TauCeti.Topology.JordanCurve.Path
public import TauCeti.Topology.JordanCurve.Separation
public import TauCeti.Topology.JordanCurve.SmallArc

/-!
# Jordan curves

This module re-exports the Jordan-curve API: the predicate `TauCeti.IsJordanCurve` together with
its transfer lemmas (`TauCeti.Topology.JordanCurve.Basic`), the criterion recognizing the range of
a simple closed path as a Jordan curve (`TauCeti.Topology.JordanCurve.Path`), the cutting of a
Jordan curve at one or two of its points (`TauCeti.Topology.JordanCurve.Separation`), the fact
that two nearby points cut off an arc of small diameter
(`TauCeti.Topology.JordanCurve.SmallArc`), and the fact that a curve of the plane — a Jordan curve
of `ℂ`, or an arc — has empty interior, so that a Jordan curve is nowhere dense and is its own
frontier (`TauCeti.Topology.JordanCurve.EmptyInterior`). It declares
nothing of its own, and keeps the import path `TauCeti.Topology.JordanCurve` — which named the
basic theory before it moved into the directory — working.
-/
