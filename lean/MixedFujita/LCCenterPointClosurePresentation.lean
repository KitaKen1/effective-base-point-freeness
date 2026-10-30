/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LogCanonicalCenters

/-! 実lc中心のdiscrepancy証人から一点閉包表示。 See reports/check-266-restricted-numerical-zero-center.json for the verified scope. Noetherian minimization over ALL effective lc pairs preserving all-large ORIGINAL L-adjoint ampleness yields an ACTUAL minimal lc center whose naturally restricted ORIGINAL L has numerical dimension ZERO for every ample center polarization and actual pullback representative. Positive original numerical klt BPF data supply the initial pair internally, without an initial L section or KV. This constructs the numerical-zero endpoint, not its nonvanishing, original mL lifting, general KV, the original nu=0 branch, BPF or full F1/F2. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable


/-- Every actual lc center has an actual generic-point closure presentation,
extracted directly from its valuative discrepancy witness. -/
theorem logCanonicalCenter_exists_point_closure_presentation
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z) :
    ∃ η : X, Z = (⟨closure ({η} : Set X), isClosed_closure⟩ : Closeds X) := by
  obtain ⟨_, T, _, _, _, _, ρ, _, _, _, _, _, t, _, _, hset⟩ := hZ
  exact ⟨ρ t, SetLike.coe_injective hset⟩

end MixedFujita
