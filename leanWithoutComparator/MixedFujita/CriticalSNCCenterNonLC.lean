/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CriticalSNCComponentNonLC
public import MixedFujita.CartierCompositePullbackOrder
public import MixedFujita.PrimeClosureGoodClosedPoint

/-! 実中心の自然制限高次数から元ambient非lc点。 See reports/check-265-lc-center-positive-numerical-descent.json for the verified scope. Actual lc-center geometry supplies an internal critical proper SNC model, prime-to-center map and good smooth closed center point. Intrinsic stalk orders transfer actual natural restriction concentration to the critical component. Positive RESTRICTED numerical dimension yields all-high original nonzero sections, original ambient nonLC and all exterior LC. For a normal source with effective boundary and minimal center, one strict lower-dimensional minimal integral center is constructed preserving all large ORIGINAL L-adjoint ampleness. Restricted numerical-zero branches, full descent iteration, initial original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- On a supplied actual proper critical SNC model, choose a SMOOTH CLOSED
point of the ORIGINAL reduced center where high NATURAL section restriction
order forces ORIGINAL ambient non-lc. The actual center map, good component
point, target Cartier presentation and order transfer are all internal. -/
theorem exists_smooth_closed_center_point_with_high_order_nonLC_obstruction
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 2 ≤ n)
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cX : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ cX f d D cT etaleCharts_cover) (z : T) = 0)
    (i₀ : Fin r)
    (hcrit : cartierCoefficient (crepantBoundaryCartier ρ hρ cX f d D cT etaleCharts_cover) (ξ i₀) = d)
    (P : CartierDivisor X) (Q : CartierDivisor (pointClosureScheme (ρ (ξ i₀))))
    (aQ : (Scheme.Modules.pullback (pointClosureι (ρ (ξ i₀)))).obj P.sheaf ≅ Q.sheaf) :
    ∃ x : pointClosureScheme (ρ (ξ i₀)), IsClosed ({x} : Set _) ∧
      x ∈ (pointClosureScheme (ρ (ξ i₀)) ↘ Spec (CommRingCat.of K)).smoothLocus ∧
      ∀ (j : ℕ), 1 ≤ j → ∀ (s : Γ(P.sheaf, ⊤)) (hs : s ≠ 0),
        (((n - 1) * d * j : ℕ) : ℕ∞) < cartierSectionVanishingOrder Q x
          (cartierPullbackGlobalSectionViaIso P (pointClosureι (ρ (ξ i₀))) Q aQ s) →
        ¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) (pointClosureι (ρ (ξ i₀)) x) cX f (j * d)
          (j • D + cartierSectionZeroDivisor P s hs) := by
  obtain ⟨ψ, hfac, z, _, hycl, hxcl, hxsm, _, hother⟩ :=
    exists_prime_closure_good_closed_point_over_smooth_center (K := K) ρ ξ hinj hξ i₀
  obtain ⟨R, ⟨aR⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor P (pointClosureι (ξ i₀) ≫ ρ)
  refine ⟨ψ z, hxcl, hxsm, fun j hj s hs hord => ?_⟩
  have hle := commuting_square_natural_cartier_restriction_order_le
    (pointClosureι (ρ (ξ i₀))) ρ (pointClosureι (ξ i₀)) ψ hfac.symm P Q aQ R aR s z
  have hpoint : pointClosureι (ρ (ξ i₀)) (ψ z) = ρ (pointClosureι (ξ i₀) z) :=
    congrArg (fun h : pointClosureScheme (ξ i₀) ⟶ X => h z) hfac
  rw [hpoint]
  exact high_natural_section_order_on_critical_component_not_original_logCanonical hn ρ hρ cX f d hd D cT
    ξ hinj hξ hsnc hsupp i₀ hcrit (pointClosureIdeal (ξ i₀)) rfl z hycl hother P s hs R aR j hj
    (hord.trans_le hle)

end MixedFujita
