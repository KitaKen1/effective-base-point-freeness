/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCCenterConcentrationNonLC
public import MixedFujita.MinimalLCSectionAdjointDescent

/-! 正の制限数値次元から元L随伴ample保持と極小中心の実降下。 See reports/check-265-lc-center-positive-numerical-descent.json for the verified scope. Actual lc-center geometry supplies an internal critical proper SNC model, prime-to-center map and good smooth closed center point. Intrinsic stalk orders transfer actual natural restriction concentration to the critical component. Positive RESTRICTED numerical dimension yields all-high original nonzero sections, original ambient nonLC and all exterior LC. For a normal source with effective boundary and minimal center, one strict lower-dimensional minimal integral center is constructed preserving all large ORIGINAL L-adjoint ampleness. Restricted numerical-zero branches, full descent iteration, initial original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- In the POSITIVE RESTRICTED numerical branch, a genuine minimal lc center
now supplies the ORIGINAL concentrated section, its nonzero natural restriction,
ambient nonLC point, exterior LC and a STRICTLY LOWER dimensional new minimal
lc center, preserving all sufficiently large ORIGINAL L-adjoint ampleness.
No perturbing section, model, point, nonLC or exterior-LC certificate is supplied.
This is one actual descent step; iteration through numerical-zero centers and
original L nonvanishing remain separate. -/
theorem positive_numerical_minimal_lc_center_constructs_strict_ample_adjoint_descent
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
    (k : ℕ) (hdim : topologicalKrullDim (pointClosureScheme η) = (k + 1 : ℕ))
    (L : CartierDivisor X) (hL : CartierIsNef K L) (a₀ : ℕ)
    (hA : CartierIsAmpleProj K ((d * a₀) • L - D))
    (LZ HZ : CartierDivisor (pointClosureScheme η))
    (aL : (Scheme.Modules.pullback (pointClosureι η)).obj L.sheaf ≅ LZ.sheaf)
    (aH : (Scheme.Modules.pullback (pointClosureι η)).obj ((d * a₀) • L - D).sheaf ≅ HZ.sheaf)
    (hν : 1 ≤ cartierNumericalDimension K (k + 1) hdim LZ HZ) :
    let l := (k + 1).factorial * (((n - 1) * d + 1) ^ (k + 1)) + 1
    ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j →
      ∃ (s : Γ((j • ((l + d * a₀) • L - D)).sheaf, ⊤)) (hs : s ≠ 0),
        modulePullbackGlobalSections (pointClosureι η) (j • ((l + d * a₀) • L - D)).sheaf s ≠ 0 ∧
        let M := cartierSectionZeroDivisor (j • ((l + d * a₀) • L - D)) s hs
        ∃ a q : ℕ, 1 ≤ a ∧ 1 ≤ q ∧ d * a * j < q ∧
          LogPairBoundaryEffective c f (q * d) (q • D + (d * a) • M) ∧
          LogPairIsLogCanonical c f (q * d) (q • D + (d * a) • M) ∧
          (¬ LogPairIsKlt c f (q * d) (q • D + (d * a) • M)) ∧
          (∀ m : ℕ, a₀ + a * j * l ≤ m →
            CartierIsAmpleProj K (((q * d) * m) • L - (q • D + (d * a) • M))) ∧
          ∃ W : Closeds X, LogPairIsLogCanonicalCenter c f (q * d) (q • D + (d * a) • M) W ∧
            (∀ V : Closeds X, LogPairIsLogCanonicalCenter c f (q * d) (q • D + (d * a) • M) V → V ≤ W → V = W) ∧
            W < (⟨closure ({η} : Set X), isClosed_closure⟩ : Closeds X) ∧
            IsIntegral (Scheme.IdealSheafData.vanishingIdeal W).subscheme ∧
            topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal W).subscheme ≤ k := by
  dsimp only
  let l := (k + 1).factorial * (((n - 1) * d + 1) ^ (k + 1)) + 1
  let H := (d * a₀) • L - D
  have hP : l • L + H = (l + d * a₀) • L - D := by
    dsimp only [H]
    rw [add_nsmul L l (d * a₀)]
    abel
  obtain ⟨_, a, j₀, hj₀, hcuts⟩ :=
    logCanonicalCenter_positive_numerical_pencil_concentration_nonLC_and_exteriorLC K hn
      c f d hd D η hZ (k + 1) hdim (by omega) L H hL hA LZ HZ aL aH hν
  refine ⟨j₀, hj₀, fun j hj => ?_⟩
  obtain ⟨x, s, hs, _, _, ht, _, hnonLC, hout⟩ := hcuts j hj
  have hnat := (cartierPullbackGlobalSectionViaIso_ne_zero_iff _ _ _ _ _).mp ht
  have hcut : ∃ (y : X) (s : Γ((j • (l • L + H)).sheaf, ⊤)) (hs : s ≠ 0),
      modulePullbackGlobalSections (pointClosureι η) (j • (l • L + H)).sheaf s ≠ 0 ∧
      (¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) y c f (j * d)
        (j • D + cartierSectionZeroDivisor (j • (l • L + H)) s hs)) ∧
      ∀ z : X, z ∉ (⟨closure ({η} : Set X), isClosed_closure⟩ : Closeds X) →
        LogPairIsLogCanonicalOverBasePoint (𝟙 X) z c f (j * d)
          (j • D + cartierSectionZeroDivisor (j • (l • L + H)) s hs) := by
    refine ⟨pointClosureι η x, s, hs, hnat, hnonLC, fun z hz => hout z ?_⟩
    have hz' : z ∉ closure ({η} : Set X) := hz
    have heq : ((pointClosureIdeal η).support : Set X) = closure ({η} : Set X) :=
      Scheme.IdealSheafData.coe_support_vanishingIdeal _
    exact fun hmem => hz' (heq ▸ hmem)
  rw [hP] at hcut
  obtain ⟨y, s, hs, hres, hbad, houtside⟩ := hcut
  refine ⟨s, hs, hres, ?_⟩
  exact minimal_lc_center_section_descent_preserves_original_ample_adjoint K hnorm c f d hd D heff
    ⟨closure ({η} : Set X), isClosed_closure⟩ hZ hmin L hL a₀ l j (hj₀.trans hj) hA
    s hs hres y hbad houtside k hdim.le

end MixedFujita
