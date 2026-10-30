/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LogCanonicalCenterClosedSubscheme
public import MixedFujita.CrepantKltDescent
public import MixedFujita.BirationalPrimeLifts

/-! 実lc中心を像とする係数d素因子つきproper SNCモデル。 See reports/check-265-lc-center-positive-numerical-descent.json for the verified scope. Actual lc-center geometry supplies an internal critical proper SNC model, prime-to-center map and good smooth closed center point. Intrinsic stalk orders transfer actual natural restriction concentration to the critical component. Positive RESTRICTED numerical dimension yields all-high original nonzero sections, original ambient nonLC and all exterior LC. For a normal source with effective boundary and minimal center, one strict lower-dimensional minimal integral center is constructed preserving all large ORIGINAL L-adjoint ampleness. Restricted numerical-zero branches, full descent iteration, initial original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- Every ACTUAL lc center on a proper original variety is represented by a
critical coefficient-d component on an internally constructed proper SNC
model. The given discrepancy prime is preserved when resolving its witness
model; no chosen SNC model or strict-transform prime is an input. -/
theorem logCanonicalCenter_exists_critical_proper_snc_model
    {K : Type u} [Field K] [CharZero K] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (η : X)
    (hZ : LogPairIsLogCanonicalCenter c f d D ⟨closure ({η} : Set X), isClosed_closure⟩) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (z : T) = 0) ∧
      ∃ i₀ : Fin r, ρ (ξ i₀) = η ∧
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i₀) = d := by
  classical
  obtain ⟨_, T₀, hT₀i, hT₀N, hT₀o, hT₀s, ρ₀, hdom₀, hover₀, hproper₀,
    hρ₀, c₀, t₀, ht₀, hdiscr₀, hcenter⟩ := hZ
  let := hT₀i
  let := hT₀N
  let := hT₀o
  let := hT₀s
  let := hdom₀
  let := hover₀
  let := hproper₀
  have : IsProper (T₀ ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ₀) (S := Spec (CommRingCat.of K))]
    infer_instance
  obtain ⟨T, hTi, hTo, hTN, hTs, σ, hdom, hover, hproper, hσ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp⟩ := exists_proper_snc_model c₀
      (crepantPullbackFormUnit ρ₀ hρ₀ c f c₀) d (cartierPullback ρ₀ D)
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hproper
  let hρ := dominantFunctionFieldAlgHom_comp_bijective ρ₀ σ hρ₀ hσ
  obtain ⟨t, ht, hdiscr⟩ := proper_birational_exists_prime_discrepancy_lift
    ρ₀ σ hρ₀ hσ c f d D c₀ cT ⟨t₀, ht₀⟩
  have hcrit : cartierCoefficient
      (crepantBoundaryCartier (σ ≫ ρ₀) hρ c f d D cT etaleCharts_cover) (t : T) = d := by
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg, hdiscr, hdiscr₀, neg_neg]
  have hsupp' : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier (σ ≫ ρ₀) hρ c f d D cT etaleCharts_cover) (z : T) = 0 := by
    intro z hz
    rw [crepantBoundaryCartier_comp ρ₀ σ hρ₀ hσ]
    exact hsupp z hz
  have hmem : (t : T) ∈ Set.range ξ := by
    by_contra hnmem
    have hzero := hsupp' t hnmem
    rw [hcrit] at hzero
    omega
  obtain ⟨i₀, hi₀⟩ := hmem
  have hη : ρ₀ t₀ = η :=
    (isGenericPoint_closure : IsGenericPoint (ρ₀ t₀) (closure ({ρ₀ t₀} : Set X))).eq
      (show IsGenericPoint η (closure ({ρ₀ t₀} : Set X)) from hcenter)
  refine ⟨T, hTi, hTo, hTN, hTs, σ ≫ ρ₀, inferInstance, inferInstance, inferInstance,
    hρ, cT, r, ξ, hinj, hcoh, hsnc, hsupp', i₀, ?_, ?_⟩
  · change ρ₀ (σ (ξ i₀)) = η
    rw [hi₀, ht]
    exact hη
  · simpa only [hi₀] using hcrit

end MixedFujita
