/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCCenterPointClosurePresentation
public import MixedFujita.PositiveNumericalMinimalCenterStep
public import MixedFujita.MinimalLogCanonicalCenters

/-! 全有効lc対のNoether極小化で制限数値次元0の中心へ到達。 See reports/check-266-restricted-numerical-zero-center.json for the verified scope. Noetherian minimization over ALL effective lc pairs preserving all-large ORIGINAL L-adjoint ampleness yields an ACTUAL minimal lc center whose naturally restricted ORIGINAL L has numerical dimension ZERO for every ample center polarization and actual pullback representative. Positive original numerical klt BPF data supply the initial pair internally, without an initial L section or KV. This constructs the numerical-zero endpoint, not its nonvanishing, original mL lifting, general KV, the original nu=0 branch, BPF or full F1/F2. -/

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


/-- Minimize over ALL effective lc pairs whose large adjoints of the ORIGINAL
nef L remain ample. Noetherian closed-set minimality replaces an explicit
iteration of changing discrepancy denominators. A terminal actual minimal
center has numerical dimension ZERO for EVERY actual pulled L representative
and EVERY ample center polarization, including zero-dimensional centers.
This constructs the numerical-zero endpoint; it does NOT supply center
nonvanishing, lifting, general KV or original L nonvanishing. -/
theorem original_ample_adjoint_lc_center_contains_restricted_numerical_zero_endpoint
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 2 ≤ n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (L : CartierDivisor X) (hL : CartierIsNef K L)
    (d b : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (hamp : ∀ m : ℕ, b ≤ m → CartierIsAmpleProj K ((d * m) • L - D))
    (Z₀ : Closeds X) (hZ₀ : LogPairIsLogCanonicalCenter c f d D Z₀) :
    ∃ d' b' : ℕ, 1 ≤ d' ∧ ∃ (D' : CartierDivisor X) (η : X)
      (_ : IsProper (pointClosureScheme η ↘ Spec (CommRingCat.of K))),
      LogPairBoundaryEffective c f d' D' ∧
      (∀ m : ℕ, b' ≤ m → CartierIsAmpleProj K ((d' * m) • L - D')) ∧
      (⟨closure ({η} : Set X), isClosed_closure⟩ : Closeds X) ≤ Z₀ ∧
      LogPairIsLogCanonicalCenter c f d' D' ⟨closure ({η} : Set X), isClosed_closure⟩ ∧
      (∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d' D' V →
        V ≤ (⟨closure ({η} : Set X), isClosed_closure⟩ : Closeds X) →
          V = ⟨closure ({η} : Set X), isClosed_closure⟩) ∧
      ∀ (k : ℕ) (hdim : topologicalKrullDim (pointClosureScheme η) = k)
        (LZ J : CartierDivisor (pointClosureScheme η))
        (_aL : (Scheme.Modules.pullback (pointClosureι η)).obj L.sheaf ≅ LZ.sheaf),
        CartierIsAmpleProj K J → cartierNumericalDimension K k hdim LZ J = 0 := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  let : IsNoetherian X := {}
  let P : Closeds X → Prop := fun Z => ∃ d b : ℕ, 1 ≤ d ∧ ∃ D : CartierDivisor X,
    LogPairBoundaryEffective c f d D ∧
    (∀ m : ℕ, b ≤ m → CartierIsAmpleProj K ((d * m) • L - D)) ∧
    LogPairIsLogCanonicalCenter c f d D Z
  have hP₀ : P Z₀ := ⟨d, b, hd, D, heff, hamp, hZ₀⟩
  obtain ⟨Z, hZZ₀, hP, hminimal⟩ := exists_minimal_le_of_wellFoundedLT P Z₀ hP₀
  obtain ⟨r, b', hr, D', heff', hamp', hZ⟩ := hP
  have hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f r D' V → V ≤ Z → V = Z := by
    intro V hV hVZ
    exact le_antisymm hVZ (hminimal (show P V from ⟨r, b', hr, D', heff', hamp', hV⟩) hVZ)
  obtain ⟨η, hη⟩ := logCanonicalCenter_exists_point_closure_presentation c f r D' Z hZ
  have hproper : IsProper (pointClosureScheme η ↘ Spec (CommRingCat.of K)) := by
    change IsProper (pointClosureι η ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  let := hproper
  refine ⟨r, b', hr, D', η, hproper, heff', hamp', ?_, ?_, ?_, ?_⟩
  · simpa only [← hη] using hZZ₀
  · simpa only [← hη] using hZ
  · simpa only [← hη] using hmin
  · intro k hdim LZ J aL hJ
    by_contra hne
    have hν : 1 ≤ cartierNumericalDimension K k hdim LZ J := by omega
    obtain ⟨r', b'', hr', D'', heff'', hamp'', W, hW, _, hWlt⟩ :=
      positive_restricted_numerical_minimal_center_exists_strict_subcenter K hn hnorm c f r hr D' heff' η
        (by simpa only [← hη] using hZ) (by simpa only [← hη] using hmin)
        L hL b' hamp' k hdim LZ J aL hJ hν
    have hWZ : W < Z := by simpa only [← hη] using hWlt
    exact (not_le_of_gt hWZ) (hminimal (show P W from ⟨r', b'', hr', D'', heff'', hamp'', hW⟩) hWZ.le)

end MixedFujita
