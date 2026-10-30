/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CenterPreservingExteriorLCSections
public import MixedFujita.RestrictedConcentrationPreservation
public import MixedFujita.RestrictedPencilConcentration

/-! 正の制限数値次元から全高次集中と中心外lcを同時構成。 See reports/check-263-exterior-lc-concentration.json for the verified scope. Actual SNC principalization of the SAME original finite subsystem and boundary-avoiding first-nonzero residual Bertini are assembled internally. Fixed-part coefficients vanish at EVERY prime relevant to points outside actual center support. Old LC coefficient bounds and new reduced-cut coefficients 0/1 prove original all-model pointwise exterior LC. Zero sections are filtered while preserving original nonzero indices. ALL high ample powers preserve nonzero natural restriction up to nonzero scalar and prove exterior LC. Positive RESTRICTED numerical dimension gives all-high actual concentrated original lifts preserving exact restricted order AND exterior LC. No original klt, normality, supplied model, initial L section or KV is required. Ambient nonLC from restricted concentration, actual lower-center iteration, original mL/center adjoint vanishing, nu=0, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- ANY actual nonzero-scalar natural restriction identity preserves the
EXACT order in every chosen actual Cartier representative on an integral
center, at EVERY point. -/
theorem natural_restriction_scalar_preserves_actual_cartier_order
    {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (φ : Y ⟶ X) (P : CartierDivisor X) (E : CartierDivisor Y)
    (e : (Scheme.Modules.pullback φ).obj P.sheaf ≅ E.sheaf)
    (s t : Γ(P.sheaf, ⊤)) (a : K) (ha : a ≠ 0)
    (hres : modulePullbackGlobalSections φ P.sheaf t = a • modulePullbackGlobalSections φ P.sheaf s) :
    cartierPullbackGlobalSectionViaIso P φ E e t = a • cartierPullbackGlobalSectionViaIso P φ E e s ∧
      ∀ y : Y, cartierSectionVanishingOrder E y (cartierPullbackGlobalSectionViaIso P φ E e t) =
        cartierSectionVanishingOrder E y (cartierPullbackGlobalSectionViaIso P φ E e s) := by
  have he : cartierPullbackGlobalSectionViaIso P φ E e t = a • cartierPullbackGlobalSectionViaIso P φ E e s := by
    change Scheme.Modules.Hom.app e.hom ⊤ (modulePullbackGlobalSections φ P.sheaf t) =
      a • Scheme.Modules.Hom.app e.hom ⊤ (modulePullbackGlobalSections φ P.sheaf s)
    rw [hres]
    exact Scheme.Modules.Hom.app_smul e.hom (Scheme.Modules.baseRingToGlobalSections K Y a) _
  refine ⟨he, fun y => ?_⟩
  rw [he, cartierSectionVanishingOrder_smul_base_ne_zero E y _ a ha]


/-- Positive RESTRICTED numerical dimension constructs ALL-high original
concentrated sections whose actual perturbation is lc OUTSIDE the center.
The concentrated lift, ideal family, zero filtering, actual SNC principalizing
model, SAME-subsystem residual Bertini and exact concentration preservation
are all internal. No center normality, initial L section or KV is supplied.
An ACTUAL ambient non-lc point still requires a separate restriction theorem. -/
theorem integral_closed_positive_numerical_pencil_exterior_lc_concentration
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hlc : LogPairIsLogCanonical c f d D)
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    [I.subscheme.Over (Spec (CommRingCat.of K))] [I.subschemeι.IsOver (Spec (CommRingCat.of K))]
    [IsProper (I.subscheme ↘ Spec (CommRingCat.of K))]
    (k : ℕ) (hdim : topologicalKrullDim I.subscheme = k) (hk : 1 ≤ k)
    (L H : CartierDivisor X) (hL : CartierIsNef K L) (hH : CartierIsAmpleProj K H)
    (LZ HZ : CartierDivisor I.subscheme)
    (aL : (Scheme.Modules.pullback I.subschemeι).obj L.sheaf ≅ LZ.sheaf)
    (aH : (Scheme.Modules.pullback I.subschemeι).obj H.sheaf ≅ HZ.sheaf)
    (hν : 1 ≤ cartierNumericalDimension K k hdim LZ HZ) (r : ℕ) :
    let l := k.factorial * (r + 1) ^ k + 1
    CartierIsAmpleProj K (l • L + H) ∧
      ∃ a : (Scheme.Modules.pullback I.subschemeι).obj (l • L + H).sheaf ≅ (l • LZ + HZ).sheaf,
        ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j → ∀ x : I.subscheme, IsClosed {x} →
          x ∈ (I.subscheme ↘ Spec (CommRingCat.of K)).smoothLocus →
          ∃ (s : Γ((j • (l • L + H)).sheaf, ⊤)) (hs : s ≠ 0),
            let t := cartierPullbackGlobalSectionViaIso (j • (l • L + H)) I.subschemeι
              (j • (l • LZ + HZ)) (cartierPullbackGradedIso (l • L + H) I.subschemeι (l • LZ + HZ) a j) s
            t ≠ 0 ∧ ((r * j : ℕ) : ℕ∞) < cartierSectionVanishingOrder (j • (l • LZ + HZ)) x t ∧
              ∀ y : X, y ∉ I.support → LogPairIsLogCanonicalOverBasePoint (𝟙 X) y c f (j * d)
                (j • D + cartierSectionZeroDivisor (j • (l • L + H)) s hs) := by
  dsimp only
  let l := k.factorial * (r + 1) ^ k + 1
  obtain ⟨hA, a, j₁, hj₁, hlift⟩ := integral_closed_positive_numerical_pencil_lifts_high_order_sections
    K I k hdim hk L H hL hH LZ HZ aL aH hν r
  obtain ⟨j₂, hpert⟩ := all_high_ample_exists_center_preserving_lc_exterior_section c f d hd D hlc
    (l • L + H) hA I
  refine ⟨hA, a, max j₁ j₂, hj₁.trans (le_max_left _ _), fun j hj x hx hxsm => ?_⟩
  obtain ⟨s₀, hs₀, hr₀, hord⟩ := hlift j ((le_max_left _ _).trans hj) x hx hxsm
  have hnat₀ : modulePullbackGlobalSections I.subschemeι (j • (l • L + H)).sheaf s₀ ≠ 0 :=
    (cartierPullbackGlobalSectionViaIso_ne_zero_iff _ _ _ _ _).mp hr₀
  obtain ⟨s, hs, b, hb, hres, hnat, hout⟩ := hpert j ((le_max_right _ _).trans hj) s₀ hnat₀ j
    (hj₁.trans ((le_max_left _ _).trans hj))
  let e := cartierPullbackGradedIso (l • L + H) I.subschemeι (l • LZ + HZ) a j
  have he := natural_restriction_scalar_preserves_actual_cartier_order I.subschemeι
    (j • (l • L + H)) (j • (l • LZ + HZ)) e s₀ s b hb hres
  refine ⟨s, hs, ?_, ?_, hout⟩
  · exact (cartierPullbackGlobalSectionViaIso_ne_zero_iff _ _ _ _ _).mpr hnat
  · rw [he.2 x]
    exact hord

end MixedFujita
