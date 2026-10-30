/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.RestrictedNumericalZeroLCCenter
public import MixedFujita.OriginalBPFMinimalLCCenter

/-! 元正ν klt BPF仮定から初期切断なしの制限ν0極小中心。 See reports/check-266-restricted-numerical-zero-center.json for the verified scope. Noetherian minimization over ALL effective lc pairs preserving all-large ORIGINAL L-adjoint ampleness yields an ACTUAL minimal lc center whose naturally restricted ORIGINAL L has numerical dimension ZERO for every ample center polarization and actual pullback representative. Positive original numerical klt BPF data supply the initial pair internally, without an initial L section or KV. This constructs the numerical-zero endpoint, not its nonvanishing, original mL lifting, general KV, the original nu=0 branch, BPF or full F1/F2. -/

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


/-- ORIGINAL normal klt BPF data with positive ORIGINAL numerical dimension
internally construct an effective lc non-klt pair and a genuine lower-dimensional
minimal lc center on which the ACTUAL naturally restricted ORIGINAL L has
numerical dimension ZERO for EVERY ample polarization. The all-large ORIGINAL
L-adjoints remain ample. No initial section, center, model, KV, positive-center
numerical premise or supplied descent chain is an input. Nonvanishing on this
numerical-zero center and lifting to ORIGINAL mL remain separate. -/
theorem original_klt_BPF_positive_numerical_exists_restricted_numerical_zero_lc_center
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 2 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (hklt : LogPairIsKlt c f d D) (L : CartierDivisor X) (hL : CartierIsNef K L)
    (a₀ : ℕ) (hnef : CartierIsNef K ((d * a₀) • L - D))
    (hbig : CartierIsBig K ((d * a₀) • L - D))
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hν : 1 ≤ cartierNumericalDimension K n hdim L J) :
    ∃ r b : ℕ, 1 ≤ r ∧ ∃ (D' : CartierDivisor X) (η : X)
      (_ : IsProper (pointClosureScheme η ↘ Spec (CommRingCat.of K))),
      LogPairBoundaryEffective c f r D' ∧ LogPairIsLogCanonical c f r D' ∧
      (¬ LogPairIsKlt c f r D') ∧
      (∀ m : ℕ, b ≤ m → CartierIsAmpleProj K ((r * m) • L - D')) ∧
      LogPairIsLogCanonicalCenter c f r D' ⟨closure ({η} : Set X), isClosed_closure⟩ ∧
      (∀ V : Closeds X, LogPairIsLogCanonicalCenter c f r D' V →
        V ≤ (⟨closure ({η} : Set X), isClosed_closure⟩ : Closeds X) →
          V = ⟨closure ({η} : Set X), isClosed_closure⟩) ∧
      genericPoint X ∉ closure ({η} : Set X) ∧
      topologicalKrullDim (pointClosureScheme η) ≤ (n - 1 : ℕ) ∧
      ∀ (k : ℕ) (hdimZ : topologicalKrullDim (pointClosureScheme η) = k)
        (LZ HZ : CartierDivisor (pointClosureScheme η))
        (_aL : (Scheme.Modules.pullback (pointClosureι η)).obj L.sheaf ≅ LZ.sheaf),
        CartierIsAmpleProj K HZ → cartierNumericalDimension K k hdimZ LZ HZ = 0 := by
  obtain ⟨r₀, b₀, hr₀, D₀, heff₀, _, _, hamp₀, Z₀, hZ₀, _, _, hgen₀, _⟩ :=
    original_klt_BPF_positive_numerical_exists_minimal_lc_center_without_initial_section
      K n hdim (by omega) hnorm c f d hd D heff hklt L hL a₀ hnef hbig J hJ hν
  obtain ⟨r, b, hr, D', η, hproper, heff', hamp, hZZ₀, hZ, hmin, hzero⟩ :=
    original_ample_adjoint_lc_center_contains_restricted_numerical_zero_endpoint K hn hnorm c f L hL
      r₀ b₀ hr₀ D₀ heff₀ hamp₀ Z₀ hZ₀
  let := hproper
  have hgen : genericPoint X ∉ closure ({η} : Set X) := fun h => hgen₀ (hZZ₀ h)
  have hrange : Set.range (pointClosureι η) ≠ Set.univ := by
    intro h
    apply hgen
    rw [← range_pointClosureι η, h]
    trivial
  have hdimX : topologicalKrullDim X ≤ (n - 1 + 1 : ℕ) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hdim.le
  have hdimZ := properClosedImmersion_topologicalKrullDim_le_predecessor
    (pointClosureι η) hrange (n - 1) hdimX
  have hnot : ¬ LogPairIsKlt c f r D' := by
    intro h
    exact logPairIsLogCanonicalCenter_not_kltOverBasePoint c f r D'
      ⟨closure ({η} : Set X), isClosed_closure⟩ hZ η (subset_closure rfl)
      (((logPairIsKlt_iff_forall_basePoint (𝟙 X) c f r D').mp h) η)
  exact ⟨r, b, hr, D', η, hproper, heff', hZ.1, hnot, hamp, hZ, hmin, hgen, hdimZ, hzero⟩

end MixedFujita
