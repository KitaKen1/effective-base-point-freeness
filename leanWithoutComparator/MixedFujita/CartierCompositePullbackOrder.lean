/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierActualPullbackOrder

/-! 実合成pullback・可換図式の自然Cartier制限次数非減少。 See reports/check-265-lc-center-positive-numerical-descent.json for the verified scope. Actual lc-center geometry supplies an internal critical proper SNC model, prime-to-center map and good smooth closed center point. Intrinsic stalk orders transfer actual natural restriction concentration to the critical component. Positive RESTRICTED numerical dimension yields all-high original nonzero sections, original ambient nonLC and all exterior LC. For a normal source with effective boundary and minimal center, one strict lower-dimensional minimal integral center is constructed preserving all large ORIGINAL L-adjoint ampleness. Restricted numerical-zero branches, full descent iteration, initial original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra


/-- Actual intrinsic section order cannot decrease after a further scheme
pullback, without dominance, normality or integrality of either target. -/
theorem cartierStalkPullbackOrder_le_composite
    {X Y Z : Scheme.{u}} [IsIntegral X] (φ : Y ⟶ X) (ψ : Z ⟶ Y)
    (P : CartierDivisor X) (s : Γ(P.sheaf, ⊤)) (z : Z) :
    cartierStalkPullbackOrder P φ (ψ z) s ≤ cartierStalkPullbackOrder P (ψ ≫ φ) z s := by
  obtain ⟨f, hf⟩ := P.exists_isLocalEquationAt (φ (ψ z))
  rw [cartierStalkPullbackOrder_eq_localCoefficient P φ (ψ z) f hf,
    cartierStalkPullbackOrder_eq_localCoefficient P (ψ ≫ φ) z f hf]
  have hc : cartierStalkPullbackCoefficient P (ψ ≫ φ) z f hf s =
      (ψ.stalkMap z).hom (cartierStalkPullbackCoefficient P φ (ψ z) f hf s) := by
    simp only [cartierStalkPullbackCoefficient_apply, Scheme.Hom.stalkMap_comp,
      CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  rw [hc]
  exact scheme_stalkMap_localAdicOrder_le ψ z _


/-- In an ACTUAL commuting scheme square, natural Cartier restriction order
on the base center cannot exceed its order on the source center. Comparing
intrinsic stalk orders avoids constructing a composite global-pullback iso. -/
theorem commuting_square_natural_cartier_restriction_order_le
    {X Y T E : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral E]
    (φ : Y ⟶ X) (ρ : T ⟶ X) (ι : E ⟶ T) (ψ : E ⟶ Y)
    (hcomm : ι ≫ ρ = ψ ≫ φ) (P : CartierDivisor X)
    (Q : CartierDivisor Y) (aQ : (Scheme.Modules.pullback φ).obj P.sheaf ≅ Q.sheaf)
    (R : CartierDivisor E) (aR : (Scheme.Modules.pullback (ι ≫ ρ)).obj P.sheaf ≅ R.sheaf)
    (s : Γ(P.sheaf, ⊤)) (z : E) :
    cartierSectionVanishingOrder Q (ψ z) (cartierPullbackGlobalSectionViaIso P φ Q aQ s) ≤
      cartierSectionVanishingOrder R z (cartierPullbackGlobalSectionViaIso P (ι ≫ ρ) R aR s) := by
  rw [← cartierStalkPullbackOrder_eq_actualGlobalPullback P φ Q aQ (ψ z) s,
    ← cartierStalkPullbackOrder_eq_actualGlobalPullback P (ι ≫ ρ) R aR z s, hcomm]
  exact cartierStalkPullbackOrder_le_composite φ ψ P s z

end MixedFujita
