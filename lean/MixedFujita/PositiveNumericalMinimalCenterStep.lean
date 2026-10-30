/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PositiveNumericalMinimalLCDescent
public import MixedFujita.NefNumericalDimensionAmpleIndependence
public import MixedFujita.NefCartierPullbackRepresentatives
public import MixedFujita.AmpleCartierPullbackRepresentatives

/-! 任意ample因子の正の制限νから元L随伴ample保持の厳密降下。 See reports/check-266-restricted-numerical-zero-center.json for the verified scope. Noetherian minimization over ALL effective lc pairs preserving all-large ORIGINAL L-adjoint ampleness yields an ACTUAL minimal lc center whose naturally restricted ORIGINAL L has numerical dimension ZERO for every ample center polarization and actual pullback representative. Positive original numerical klt BPF data supply the initial pair internally, without an initial L section or KV. This constructs the numerical-zero endpoint, not its nonvanishing, original mL lifting, general KV, the original nu=0 branch, BPF or full F1/F2. -/

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
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- A positive RESTRICTED numerical dimension on an actual minimal center
produces a STRICT subcenter for a new effective lc pair, retaining all large
ORIGINAL L-adjoint ampleness. Any ample polarization on the center may be used;
proper nef numerical-dimension independence supplies the adjoint polarization.
No positive dimension, concentrated section or geometric witness is supplied. -/
theorem positive_restricted_numerical_minimal_center_exists_strict_subcenter
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 2 ≤ n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (η : X) (hZ : LogPairIsLogCanonicalCenter c f d D ⟨closure ({η} : Set X), isClosed_closure⟩)
    (hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V →
      V ≤ (⟨closure ({η} : Set X), isClosed_closure⟩ : Closeds X) → V = ⟨closure ({η} : Set X), isClosed_closure⟩)
    [IsProper (pointClosureScheme η ↘ Spec (CommRingCat.of K))]
    (L : CartierDivisor X) (hL : CartierIsNef K L) (b : ℕ)
    (hamp : ∀ m : ℕ, b ≤ m → CartierIsAmpleProj K ((d * m) • L - D))
    (k : ℕ) (hdim : topologicalKrullDim (pointClosureScheme η) = k)
    (LZ J : CartierDivisor (pointClosureScheme η))
    (aL : (Scheme.Modules.pullback (pointClosureι η)).obj L.sheaf ≅ LZ.sheaf)
    (hJ : CartierIsAmpleProj K J)
    (hν : 1 ≤ cartierNumericalDimension K k hdim LZ J) :
    ∃ d' b' : ℕ, 1 ≤ d' ∧ ∃ D' : CartierDivisor X,
      LogPairBoundaryEffective c f d' D' ∧
      (∀ m : ℕ, b' ≤ m → CartierIsAmpleProj K ((d' * m) • L - D')) ∧
      ∃ W : Closeds X, LogPairIsLogCanonicalCenter c f d' D' W ∧
        (∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d' D' V → V ≤ W → V = W) ∧
        W < (⟨closure ({η} : Set X), isClosed_closure⟩ : Closeds X) := by
  have hk : 1 ≤ k := hν.trans (cartierNumericalDimension_le_dim K k hdim LZ J)
  let H := (d * b) • L - D
  obtain ⟨HZ, ⟨aH⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor H (pointClosureι η)
  have hH : CartierIsAmpleProj K H := hamp b le_rfl
  have hHZ : CartierIsAmpleProj K HZ :=
    cartierIsAmpleProj_of_finite_pullback_over K (pointClosureι η) H HZ hH aH
  have hLZ : CartierIsNef K LZ := cartierIsNef_of_pullback_representative K (pointClosureι η) L LZ aL hL
  have hνH : 1 ≤ cartierNumericalDimension K k hdim LZ HZ := by
    rw [← proper_nef_cartierNumericalDimension_ample_independent K k hdim hk LZ J HZ hLZ hJ hHZ]
    exact hν
  have hdim' : topologicalKrullDim (pointClosureScheme η) = (k - 1 + 1 : ℕ) := by
    simpa only [Nat.sub_add_cancel hk] using hdim
  have hνH' : 1 ≤ cartierNumericalDimension K (k - 1 + 1) hdim' LZ HZ := by
    simpa only [Nat.sub_add_cancel hk] using hνH
  obtain ⟨j₀, _, hstep⟩ := positive_numerical_minimal_lc_center_constructs_strict_ample_adjoint_descent
    K hn hnorm c f d hd D heff η hZ hmin (k - 1) hdim' L hL b hH LZ HZ aL aH hνH'
  obtain ⟨s, hs, _, a, q, _, hq, _, heff', _, _, hamp', W, hW, hminW, hWlt, _, _⟩ := hstep j₀ le_rfl
  exact ⟨q * d, b + a * j₀ * ((k - 1 + 1).factorial * (((n - 1) * d + 1) ^ (k - 1 + 1)) + 1),
    Nat.mul_pos (by omega) (by omega), _, heff', hamp', W, hW, hminW, hWlt⟩

end MixedFujita
