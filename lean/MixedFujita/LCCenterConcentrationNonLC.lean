/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCCenterCriticalSNCModel
public import MixedFujita.CriticalSNCCenterConcentration

/-! モデル入力なしの実lc中心集中・元非lc・全中心外lc。 See reports/check-265-lc-center-positive-numerical-descent.json for the verified scope. Actual lc-center geometry supplies an internal critical proper SNC model, prime-to-center map and good smooth closed center point. Intrinsic stalk orders transfer actual natural restriction concentration to the critical component. Positive RESTRICTED numerical dimension yields all-high original nonzero sections, original ambient nonLC and all exterior LC. For a normal source with effective boundary and minimal center, one strict lower-dimensional minimal integral center is constructed preserving all large ORIGINAL L-adjoint ampleness. Restricted numerical-zero branches, full descent iteration, initial original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- For ANY ACTUAL positive-dimensional lc center with positive RESTRICTED
numerical dimension, internally construct the critical proper SNC model,
good smooth closed center point and ALL-high natural concentrated sections,
with ORIGINAL ambient nonLC and LC at EVERY exterior point. No model, factor
map, good point, initial L section, center normality or KV is an input. -/
theorem logCanonicalCenter_positive_numerical_pencil_concentration_nonLC_and_exteriorLC
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 2 ≤ n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (η : X)
    (hZ : LogPairIsLogCanonicalCenter cX f d D ⟨closure ({η} : Set X), isClosed_closure⟩)
    [IsProper (pointClosureScheme η ↘ Spec (CommRingCat.of K))]
    (k : ℕ) (hdim : topologicalKrullDim (pointClosureScheme η) = k) (hk : 1 ≤ k)
    (L H : CartierDivisor X) (hL : CartierIsNef K L) (hH : CartierIsAmpleProj K H)
    (LZ HZ : CartierDivisor (pointClosureScheme η))
    (aL : (Scheme.Modules.pullback (pointClosureι η)).obj L.sheaf ≅ LZ.sheaf)
    (aH : (Scheme.Modules.pullback (pointClosureι η)).obj H.sheaf ≅ HZ.sheaf)
    (hν : 1 ≤ cartierNumericalDimension K k hdim LZ HZ) :
    let l := k.factorial * (((n - 1) * d + 1) ^ k) + 1
    CartierIsAmpleProj K (l • L + H) ∧
      ∃ a : (Scheme.Modules.pullback (pointClosureι η)).obj (l • L + H).sheaf ≅ (l • LZ + HZ).sheaf,
        ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j →
          ∃ (x : pointClosureScheme η) (s : Γ((j • (l • L + H)).sheaf, ⊤)) (hs : s ≠ 0),
            IsClosed ({x} : Set _) ∧
            x ∈ (pointClosureScheme η ↘ Spec (CommRingCat.of K)).smoothLocus ∧
            let t := cartierPullbackGlobalSectionViaIso (j • (l • L + H)) (pointClosureι η)
              (j • (l • LZ + HZ)) (cartierPullbackGradedIso (l • L + H) (pointClosureι η) (l • LZ + HZ) a j) s
            t ≠ 0 ∧ ((((n - 1) * d) * j : ℕ) : ℕ∞) < cartierSectionVanishingOrder (j • (l • LZ + HZ)) x t ∧
              (¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) (pointClosureι η x) cX f (j * d)
                (j • D + cartierSectionZeroDivisor (j • (l • L + H)) s hs)) ∧
              ∀ y : X, y ∉ (pointClosureIdeal η).support →
                LogPairIsLogCanonicalOverBasePoint (𝟙 X) y cX f (j * d)
                  (j • D + cartierSectionZeroDivisor (j • (l • L + H)) s hs) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hproper, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp, i₀, hη, hcrit⟩ :=
    logCanonicalCenter_exists_critical_proper_snc_model cX f d hd D η hZ
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hproper
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  subst η
  exact critical_snc_center_positive_numerical_pencil_concentration_nonLC_and_exteriorLC
    K hn ρ hρ cX f d hd D hZ.1 cT ξ hinj hcoh hsnc hsupp i₀ hcrit k hdim hk L H hL hH LZ HZ aL aH hν

end MixedFujita
