/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CriticalSNCCenterNonLC
public import MixedFujita.RestrictedConcentrationExteriorLC

/-! 臨界SNCモデル中心上の集中・元非lc・全中心外lc。 See reports/check-265-lc-center-positive-numerical-descent.json for the verified scope. Actual lc-center geometry supplies an internal critical proper SNC model, prime-to-center map and good smooth closed center point. Intrinsic stalk orders transfer actual natural restriction concentration to the critical component. Positive RESTRICTED numerical dimension yields all-high original nonzero sections, original ambient nonLC and all exterior LC. For a normal source with effective boundary and minimal center, one strict lower-dimensional minimal integral center is constructed preserving all large ORIGINAL L-adjoint ampleness. Restricted numerical-zero branches, full descent iteration, initial original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- POSITIVE restricted numerical dimension on the center of a supplied
actual proper critical SNC model constructs ALL-high original sections with
restricted concentration, ORIGINAL ambient non-lc at that center point, AND
lc at EVERY point outside the center. No initial L section, center normality,
vanishing theorem, high-order transfer or non-lc witness is supplied. -/
theorem critical_snc_center_positive_numerical_pencil_concentration_nonLC_and_exteriorLC
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 2 ≤ n)
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cX : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hlc : LogPairIsLogCanonical cX f d D) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ cX f d D cT etaleCharts_cover) (z : T) = 0)
    (i₀ : Fin r)
    (hcrit : cartierCoefficient (crepantBoundaryCartier ρ hρ cX f d D cT etaleCharts_cover) (ξ i₀) = d)
    [IsProper (pointClosureScheme (ρ (ξ i₀)) ↘ Spec (CommRingCat.of K))]
    (k : ℕ) (hdim : topologicalKrullDim (pointClosureScheme (ρ (ξ i₀))) = k) (hk : 1 ≤ k)
    (L H : CartierDivisor X) (hL : CartierIsNef K L) (hH : CartierIsAmpleProj K H)
    (LZ HZ : CartierDivisor (pointClosureScheme (ρ (ξ i₀))))
    (aL : (Scheme.Modules.pullback (pointClosureι (ρ (ξ i₀)))).obj L.sheaf ≅ LZ.sheaf)
    (aH : (Scheme.Modules.pullback (pointClosureι (ρ (ξ i₀)))).obj H.sheaf ≅ HZ.sheaf)
    (hν : 1 ≤ cartierNumericalDimension K k hdim LZ HZ) :
    let l := k.factorial * (((n - 1) * d + 1) ^ k) + 1
    CartierIsAmpleProj K (l • L + H) ∧
      ∃ a : (Scheme.Modules.pullback (pointClosureι (ρ (ξ i₀)))).obj (l • L + H).sheaf ≅ (l • LZ + HZ).sheaf,
        ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j →
          ∃ (x : pointClosureScheme (ρ (ξ i₀))) (s : Γ((j • (l • L + H)).sheaf, ⊤)) (hs : s ≠ 0),
            IsClosed ({x} : Set _) ∧
            x ∈ (pointClosureScheme (ρ (ξ i₀)) ↘ Spec (CommRingCat.of K)).smoothLocus ∧
            let t := cartierPullbackGlobalSectionViaIso (j • (l • L + H)) (pointClosureι (ρ (ξ i₀)))
              (j • (l • LZ + HZ)) (cartierPullbackGradedIso (l • L + H) (pointClosureι (ρ (ξ i₀))) (l • LZ + HZ) a j) s
            t ≠ 0 ∧ ((((n - 1) * d) * j : ℕ) : ℕ∞) < cartierSectionVanishingOrder (j • (l • LZ + HZ)) x t ∧
              (¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) (pointClosureι (ρ (ξ i₀)) x) cX f (j * d)
                (j • D + cartierSectionZeroDivisor (j • (l • L + H)) s hs)) ∧
              ∀ y : X, y ∉ (pointClosureIdeal (ρ (ξ i₀))).support →
                LogPairIsLogCanonicalOverBasePoint (𝟙 X) y cX f (j * d)
                  (j • D + cartierSectionZeroDivisor (j • (l • L + H)) s hs) := by
  dsimp only
  let l := k.factorial * (((n - 1) * d + 1) ^ k) + 1
  have : IsProper (pointClosureScheme (ρ (ξ i₀)) ↘ Spec (CommRingCat.of K)) := by
    change IsProper (pointClosureι (ρ (ξ i₀)) ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  obtain ⟨hA, a, j₀, hj₀, hsec⟩ := integral_closed_positive_numerical_pencil_exterior_lc_concentration
    K cX f d hd D hlc (pointClosureIdeal (ρ (ξ i₀))) k hdim hk L H hL hH LZ HZ aL aH hν ((n - 1) * d)
  refine ⟨hA, a, j₀, hj₀, fun j hj => ?_⟩
  let e := cartierPullbackGradedIso (l • L + H) (pointClosureι (ρ (ξ i₀))) (l • LZ + HZ) a j
  obtain ⟨x, hxcl, hxsm, hbad⟩ := exists_smooth_closed_center_point_with_high_order_nonLC_obstruction hn
    ρ hρ cX f d hd D cT ξ hinj hξ hsnc hsupp i₀ hcrit (j • (l • L + H)) (j • (l • LZ + HZ)) e
  obtain ⟨s, hs, ht, hord, hout⟩ := hsec j hj x hxcl hxsm
  exact ⟨x, s, hs, hxcl, hxsm, ht, hord, hbad j (hj₀.trans hj) s hs hord, hout⟩

end MixedFujita
