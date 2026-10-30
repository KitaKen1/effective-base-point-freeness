/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IntegralCentreIncidence
public import Hironaka.Resolution.Algebraic.Hir64.ComponentDeletion
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure
public import Mathlib.Topology.Connected.Clopen

/-! An explicitly connected Noetherian SNC center is integral. This concerns
the center itself; no connectedness conclusion about adjoint cuts is assumed or proved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false

theorem connected_noetherian_regular_isIntegral (Y : Scheme.{u})
    [IsNoetherian Y] [IsRegular Y] [ConnectedSpace Y] : IsIntegral Y := by
  classical
  let y : Y := Classical.arbitrary Y
  have hC : irreducibleComponent y ∈ irreducibleComponents Y := irreducibleComponent_mem_irreducibleComponents y
  have hparts := Hironaka.Sequence.hasDisjointIntegralComponents_of_isRegular (X := Y)
  have hopen : IsOpen (irreducibleComponent y) := by
    rw [← hparts.irreducibleComponentOpen_eq _ hC]
    exact (Y.irreducibleComponentOpen (irreducibleComponent y)).isOpen
  have hall : irreducibleComponent y = Set.univ :=
    IsClopen.eq_univ ⟨isClosed_irreducibleComponent, hopen⟩ ⟨y, mem_irreducibleComponent⟩
  let : IrreducibleSpace Y := {
    isPreirreducible_univ := by rw [← hall]; exact isIrreducible_irreducibleComponent.2
    toNonempty := inferInstance }
  let : IsReduced Y := hparts.1
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

theorem snc_connectedCentre_isIntegral
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : Scheme.DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    [IsNoetherian Z.subscheme] [ConnectedSpace Z.subscheme] : IsIntegral Z.subscheme := by
  let : IsRegular Z.subscheme := HasSncWith.isRegular f hZ
  exact connected_noetherian_regular_isIntegral Z.subscheme

end MixedFujita
