/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CenterPreservingLinearCombination
public import MixedFujita.SemiampleIitakaZero
public import MixedFujita.CartierActualPullbackOrder

/-! 全点での実制限集中次数の厳密保持。 See reports/check-262-concentration-residual-snc.json for the verified scope. Actual natural global pullback is semilinear and linear over the actual base ring. SAME finite linear combinations preserve natural restriction, original nonvanishing and exact restricted concentration order. Actual fixed-part removal retains the rational function and recovers the original section. Given actual dominant principalization, the SAME original finite subsystem yields a residual basepointfree family; its linear combinations recover the original combinations with SAME coefficients. Existing global residual Bertini chooses first coefficient nonzero and an actual smooth reduced SNC cut with indicator coefficients. New model construction, final center-exterior LC coefficient bounds, ambient nonLC from restricted concentration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Multiplying an actual Cartier section by a nonzero base-field scalar
preserves its EXACT local vanishing order at every point of an integral source.
No smoothness, normality or noetherianity is needed. -/
theorem cartierSectionVanishingOrder_smul_base_ne_zero
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (P : CartierDivisor X) (x : X) (s : Γ(P.sheaf, ⊤)) (a : K) (ha : a ≠ 0) :
    cartierSectionVanishingOrder P x (a • s) = cartierSectionVanishingOrder P x s := by
  obtain ⟨f, hf⟩ := P.exists_isLocalEquationAt x
  rw [cartierSectionVanishingOrder_eq_localCoefficient P x f hf,
    cartierSectionVanishingOrder_eq_localCoefficient P x f hf, cartierLocalCoefficient_smul_base]
  let v : (X.presheaf.stalk x)ˣ := Units.map (algebraMap K (X.presheaf.stalk x)).toMonoidHom (Units.mk0 a ha)
  have hv : (v : X.presheaf.stalk x) = algebraMap K (X.presheaf.stalk x) a := rfl
  rw [← hv, localAdicOrder_unit_mul]


/-- Transport to an ACTUAL Cartier representative commutes with scalar
multiplication over the actual base, even for non-dominant pullback. -/
theorem cartierPullbackGlobalSectionViaIso_smul_base
    {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of K))]
    (P : CartierDivisor X) (E : CartierDivisor Y)
    (e : (Scheme.Modules.pullback φ).obj P.sheaf ≅ E.sheaf)
    (a : K) (s : Γ(P.sheaf, ⊤)) :
    cartierPullbackGlobalSectionViaIso P φ E e (a • s) =
      a • cartierPullbackGlobalSectionViaIso P φ E e s := by
  change Scheme.Modules.Hom.app e.hom ⊤ (modulePullbackGlobalSections φ P.sheaf (a • s)) =
    a • Scheme.Modules.Hom.app e.hom ⊤ (modulePullbackGlobalSections φ P.sheaf s)
  rw [modulePullbackGlobalSections_smul_base]
  exact Scheme.Modules.Hom.app_smul e.hom
    (Scheme.Modules.baseRingToGlobalSections K Y a) _


/-- The SAME original finite linear combination has actual Cartier restriction
exactly equal to its first scalar times the fixed restricted representative. -/
theorem fixed_first_linear_combination_cartier_restriction
    {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of K))]
    (P : CartierDivisor X) (E : CartierDivisor Y)
    (e : (Scheme.Modules.pullback φ).obj P.sheaf ≅ E.sheaf)
    (k : ℕ) (s₀ : Γ(P.sheaf, ⊤)) (s : Fin k → Γ(P.sheaf, ⊤))
    (hzero : ∀ i, modulePullbackGlobalSections φ P.sheaf (s i) = 0)
    (a : Fin (k + 1) → K) :
    cartierPullbackGlobalSectionViaIso P φ E e
        (∑ i, a i • (Fin.cons s₀ s : Fin (k + 1) → Γ(P.sheaf, ⊤)) i) =
      a 0 • cartierPullbackGlobalSectionViaIso P φ E e s₀ := by
  change Scheme.Modules.Hom.app e.hom ⊤ (modulePullbackGlobalSections φ P.sheaf _) =
    a 0 • Scheme.Modules.Hom.app e.hom ⊤ (modulePullbackGlobalSections φ P.sheaf s₀)
  rw [fixed_first_linear_combination_natural_restriction φ P.sheaf k s₀ s hzero a]
  exact Scheme.Modules.Hom.app_smul e.hom
    (Scheme.Modules.baseRingToGlobalSections K Y (a 0)) _


/-- Every admissible first coefficient preserves the EXACT concentrated
restricted order at every point, as well as natural and ambient nonvanishing.
No smoothness, normality, dominance or vanishing theorem is needed. -/
theorem fixed_first_linear_combination_preserves_restricted_concentration
    {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of K))]
    (P : CartierDivisor X) (E : CartierDivisor Y)
    (e : (Scheme.Modules.pullback φ).obj P.sheaf ≅ E.sheaf)
    (k : ℕ) (s₀ : Γ(P.sheaf, ⊤)) (h₀ : modulePullbackGlobalSections φ P.sheaf s₀ ≠ 0)
    (s : Fin k → Γ(P.sheaf, ⊤))
    (hzero : ∀ i, modulePullbackGlobalSections φ P.sheaf (s i) = 0)
    (a : Fin (k + 1) → K) (ha : a 0 ≠ 0) :
    let t := ∑ i, a i • (Fin.cons s₀ s : Fin (k + 1) → Γ(P.sheaf, ⊤)) i
    modulePullbackGlobalSections φ P.sheaf t ≠ 0 ∧ t ≠ 0 ∧
      ∀ y : Y, cartierSectionVanishingOrder E y (cartierPullbackGlobalSectionViaIso P φ E e t) =
        cartierSectionVanishingOrder E y (cartierPullbackGlobalSectionViaIso P φ E e s₀) := by
  dsimp only
  obtain ⟨hr, ht⟩ := fixed_first_linear_combination_natural_and_ambient_ne_zero
    φ P.sheaf k s₀ h₀ s hzero a ha
  refine ⟨hr, ht, fun y => ?_⟩
  rw [fixed_first_linear_combination_cartier_restriction φ P E e k s₀ s hzero a,
    cartierSectionVanishingOrder_smul_base_ne_zero E y _ (a 0) ha]

end MixedFujita
