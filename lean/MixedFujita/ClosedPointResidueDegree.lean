/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import TauCeti.AlgebraicGeometry.Scheme.ClosedPoint
public import TauCeti.AlgebraicGeometry.ResidueDegree
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! 代数閉体上の実閉点の剰余次数1。 See reports/check-214-curve-f1-f2-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped Classical
open TauCeti.AlgebraicGeometry
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


theorem finiteTypeOverAlgClosed_residueDegree_eq_one
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) : f.residueDegree x = 1 := by
  let kx := (Spec (CommRingCat.of K)).residueField (f x)
  let e : kx ≃+* K := (Scheme.Spec.residueFieldIsoOfField (f x)).commRingCatIsoToRingEquiv
  letI : IsAlgClosed kx := IsAlgClosed.of_ringEquiv K kx e.symm
  letI : Algebra kx (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have hfinite : (f.residueFieldMap x).hom.Finite :=
    (residueDegree_ne_zero_iff f x).mp (f.residueDegree_ne_zero_of_isClosed hx)
  letI : Module.Finite kx (X.residueField x) := hfinite
  apply (residueDegree_eq_one_iff f x).mpr
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end MixedFujita
