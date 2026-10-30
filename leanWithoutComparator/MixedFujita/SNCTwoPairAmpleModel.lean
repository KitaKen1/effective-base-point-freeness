/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveKawamataViehwegOfAmple
public import MixedFujita.PrincipalizingSNCBaseSequence
public import MixedFujita.OpenImmersionModelRestriction
public import MixedFujita.CartierPositivityPullback
public import MixedFujita.KodairaLemmaNormal
public import MixedFujita.TwistedCartierApproximation
public import MixedFujita.BirationalComposition

/-!
A projective SNC model of two log pairs with an ample divisor of the form p*(c A) − G, G effective
and supported on the SNC family (step 16, the tie-breaking of the base point free theorem).

Let X be a normal projective variety with two log pairs (c₀, f₀, d₁, D₁), (c₀, f₀, d₂, D₂) and an
ample A. Take any smooth projective model ρ : T₁ → X, an ample J₁ on T₁ and, by Kodaira's lemma,
an effective F₁ with j ρ*A − J₁ = F₁ + div. Principalize the closed set Z ⊆ T₁ formed by the
supports of the two crepant boundaries and of F₁ (`exists_principalizing_smooth_snc_base_sequence`):
σ : T → T₁ with an SNC family off which every codimension-one point lies outside Z. The blow-up
sequence has a relative ample correction σ*(c H₀) − G with G supported over Z
(`blowUpSequence_exists_relative_ample`), and k J₁ − H₀ is nef for some k. Hence
p*((c k j) A) − ((c k) σ*F₁ + G) is ample on T, p = σ ≫ ρ, with the correction supported on the
SNC family; both crepant boundaries are supported there as well.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- **Two-pair SNC model with a supported ample correction.** -/
theorem exists_snc_two_pair_model_with_supported_ample
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d₁ d₂ : ℕ)
    (D₁ D₂ : CartierDivisor X) (A : CartierDivisor X) (hA : CartierIsAmpleProj K A) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (_ : IsProper (T ↘ Spec (CommRingCat.of K)))
      (p : T ⟶ X) (_ : IsDominant p) (_ : p.IsOver (Spec (CommRingCat.of K))) (_ : IsProper p)
      (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
      (cT : EtaleChart K T n) (R : ℕ) (ξ : Fin R → T) (c : ℕ) (G : CartierDivisor T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier p hp c₀ f₀ d₁ D₁ cT etaleCharts_cover)
          (t : T) = 0) ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier p hp c₀ f₀ d₂ D₂ cT etaleCharts_cover)
          (t : T) = 0) ∧
      1 ≤ c ∧ G.IsEffective ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient G (t : T) = 0) ∧
      CartierIsAmpleProj K (cartierPullback p (c • A) - G) := by
  -- a smooth projective model with a projective embedding
  obtain ⟨T₁, hT₁i, hT₁o, hT₁N, hT₁s, ρ, hρdom, hρover, hρprop, -, hρ, cT₁, -, -, -, -, -, -, -,
    hemb⟩ := exists_projective_snc_model_with_embedding c₀ f₀ d₁ D₁ (fun k : Fin 0 => k.elim0)
  let := hT₁i
  let := hT₁o
  let := hT₁N
  let := hT₁s
  let := hρdom
  let := hρover
  let := hρprop
  let : IsProper (T₁ ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ)]
    infer_instance
  let : Smooth (T₁ ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let : IsRegular T₁ := ⟨fun y => isRegularLocalRing_stalk (T₁ ↘ Spec (CommRingCat.of K)) y⟩
  have hnormT₁ : ∀ t : T₁, IsIntegrallyClosed (T₁.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hdimT₁ : topologicalKrullDim T₁ = n := etaleChart_topologicalKrullDim cT₁
  obtain ⟨-, -, N, e, he, hbase, -⟩ := id hA
  obtain ⟨M, e₁, he₁, hbase₁⟩ := hemb N e he hbase
  let := he₁
  obtain ⟨J₁, hJ₁⟩ := exists_cartierIsVeryAmpleProj_of_closedImmersion e₁ hbase₁
  have hJ₁a : CartierIsAmpleProj K J₁ := cartierIsAmpleProj_of_veryAmple hJ₁
  -- Kodaira's lemma on the model for the pullback of A
  have hbigA : CartierIsBig K (cartierPullback ρ A) :=
    cartierIsBig_cartierPullback hnorm hnormT₁ ρ hρ (hdimT₁.trans hdim.symm)
      (cartierIsAmpleProj_isBig hdim hn hA)
  obtain ⟨j, hj, sK, hsK⟩ := exists_section_nsmul_sub_of_isBig_of_isAmpleProj hdimT₁ hn hnormT₁
    cT₁ (cartierPullback ρ A) J₁ hbigA hJ₁a
  set F₁ := cartierSectionZeroDivisor (j • cartierPullback ρ A - J₁) sK hsK with hF₁def
  have hF₁eff : F₁.IsEffective := cartierSectionZeroDivisor_isEffective _ _ _
  -- the closed set to principalize
  set C₁ := crepantBoundaryCartier ρ hρ c₀ f₀ d₁ D₁ cT₁ etaleCharts_cover with hC₁def
  set C₂ := crepantBoundaryCartier ρ hρ c₀ f₀ d₂ D₂ cT₁ etaleCharts_cover with hC₂def
  obtain ⟨Z, hZ⟩ : ∃ Z : Closeds T₁, (Z : Set T₁) =
      (cartierSupportCloseds C₁ : Set T₁) ∪ (cartierSupportCloseds C₂ : Set T₁) ∪
        (cartierSupportCloseds F₁ : Set T₁) :=
    ⟨⟨_, ((cartierSupportCloseds C₁).isClosed.union (cartierSupportCloseds C₂).isClosed).union
      (cartierSupportCloseds F₁).isClosed⟩, rfl⟩
  have hZη : genericPoint T₁ ∉ (Z : Set T₁) := by
    rw [hZ]
    rintro ((h | h) | h)
    · exact genericPoint_notMem_cartierSupportCloseds _ h
    · exact genericPoint_notMem_cartierSupportCloseds _ h
    · exact genericPoint_notMem_cartierSupportCloseds _ h
  -- the principalization
  obtain ⟨S, hc, hBi, instB, hBN, hBsm, hμdom, hμover, hμprop, -, -, -, hBsep, cB, hμ, -, R, ξ,
      hinj, hξ, hsnc, hβ, -⟩ :=
    exists_principalizing_smooth_snc_base_sequence (K := K) cT₁ Z hZη ⊤
      (by rw [Scheme.IdealSheafData.support_top]; exact fun x hx => absurd hx (by simp))
  let := hBi
  let := instB
  let := hBN
  let := hBsm
  let := hμdom
  let := hμover
  let := hμprop
  let : IsProper (S.last ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := S.composite)]
    infer_instance
  let : Smooth (S.last ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hstalk : ∀ t : CodimensionOnePoint S.last, (t : S.last) ∉ Set.range ξ →
      Function.Bijective (S.composite.stalkMap (t : S.last)) ∧
        Order.coheight (S.composite (t : S.last)) = 1 ∧
        S.composite (t : S.last) ∉ (Z : Set T₁) := by
    intro t ht
    have hnZ := hβ t ht
    have hiso : IsIso (S.composite.stalkMap (t : S.last)) :=
      blowUpSequence_isIso_stalkMap_of_centers_over S Z hc (t : S.last) hnZ
    have hbij : Function.Bijective (S.composite.stalkMap (t : S.last)) :=
      ConcreteCategory.bijective_of_isIso _
    refine ⟨hbij, ?_, hnZ⟩
    rw [← coheight_eq_of_stalkMap_bijective S.composite (t : S.last) hbij]
    exact t.property
  let p : S.last ⟶ X := S.composite ≫ ρ
  have hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p) :=
    dominantFunctionFieldAlgHom_comp_bijective ρ S.composite hρ hμ
  -- relative ampleness of the principalization, compared with J₁
  obtain ⟨H₀, cc, G, hH₀, hcc, hGeff, hG0, hGamp⟩ :=
    blowUpSequence_exists_relative_ample e₁ hbase₁ S Z hZη hc
  obtain ⟨kk, hkk, hkH⟩ := exists_nsmul_sub_isNef hJ₁a H₀
  -- the supported correction and the ample identity
  set G' := (cc * kk) • cartierPullback S.composite F₁ + G with hG'def
  have hG'eff : G'.IsEffective := by
    rw [hG'def]
    exact CartierDivisor.IsEffective.add
      (nsmul_isEffective_of_isEffective (cartierPullback_isEffective S.composite F₁ hF₁eff) _)
      hGeff
  have hampJ : CartierIsAmpleProj K (cartierPullback S.composite ((cc * kk) • J₁) - G) := by
    have hsplit : cartierPullback S.composite ((cc * kk) • J₁) - G =
        cartierPullback S.composite (cc • (kk • J₁ - H₀)) +
          (cartierPullback S.composite (cc • H₀) - G) := by
      rw [cartierPullback_nsmul, cartierPullback_nsmul, cartierPullback_nsmul,
        cartierPullback_sub, cartierPullback_nsmul, ← smul_smul, smul_sub]
      abel
    rw [hsplit]
    exact proper_nef_add_ample_isAmpleProj K _ _
      (cartierIsNef_cartierPullback_of_dominant S.composite (cartierIsNef_nsmul hkH cc)) hGamp
  set u := cartierSectionUnit (j • cartierPullback ρ A - J₁) sK hsK with hu
  have hF₁eq : F₁ = (j • cartierPullback ρ A - J₁) + principalCartierDivisor T₁ u := rfl
  have hJ₁eq : J₁ = j • cartierPullback ρ A - F₁ + principalCartierDivisor T₁ u := by
    rw [hF₁eq]
    abel
  have hkey : cartierPullback p ((cc * kk * j) • A) - G' =
      (cartierPullback S.composite ((cc * kk) • J₁) - G) +
        principalCartierDivisor S.last
          ((Units.map (dominantFunctionFieldMap S.composite).hom.toMonoidHom u ^ (cc * kk))⁻¹) := by
    rw [principalCartierDivisor_inv, principalCartierDivisor_power, ← cartierPullback_principal]
    conv_rhs => rw [hJ₁eq]
    simp only [p, hG'def, cartierPullback_comp, cartierPullback_nsmul, cartierPullback_add,
      cartierPullback_sub, smul_add, smul_sub, smul_smul]
    abel
  have hampT : CartierIsAmpleProj K (cartierPullback p ((cc * kk * j) • A) - G') := by
    rw [hkey]
    exact cartierIsAmpleProj_add_principal hampJ _
  -- the supports
  have hoff : ∀ (B₁ : CartierDivisor T₁), (cartierSupportCloseds B₁ : Set T₁) ⊆ (Z : Set T₁) →
      ∀ t : CodimensionOnePoint S.last, (t : S.last) ∉ Set.range ξ →
        cartierCoefficient B₁ (S.composite (t : S.last)) = 0 := by
    intro B₁ hB₁ t ht
    obtain ⟨-, hcoht, hnZ⟩ := hstalk t ht
    exact cartierCoefficient_eq_zero_of_notMem_cartierSupportCloseds B₁ _ hcoht
      (fun h => hnZ (hB₁ h))
  have hC₁Z : (cartierSupportCloseds C₁ : Set T₁) ⊆ (Z : Set T₁) := by
    rw [hZ]
    exact Set.subset_union_left.trans Set.subset_union_left
  have hC₂Z : (cartierSupportCloseds C₂ : Set T₁) ⊆ (Z : Set T₁) := by
    rw [hZ]
    exact Set.subset_union_right.trans Set.subset_union_left
  have hF₁Z : (cartierSupportCloseds F₁ : Set T₁) ⊆ (Z : Set T₁) := by
    rw [hZ]
    exact Set.subset_union_right
  have hcrep : ∀ (d : ℕ) (D : CartierDivisor X) (Cd : CartierDivisor T₁),
      Cd = crepantBoundaryCartier ρ hρ c₀ f₀ d D cT₁ etaleCharts_cover →
      (cartierSupportCloseds Cd : Set T₁) ⊆ (Z : Set T₁) →
      ∀ t : CodimensionOnePoint S.last, (t : S.last) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier p hp c₀ f₀ d D cB etaleCharts_cover)
          (t : S.last) = 0 := by
    intro d D Cd hCd hCdZ t ht
    obtain ⟨hbij, hcoht, -⟩ := hstalk t ht
    rw [crepantBoundaryCartier_coefficient_comp_of_stalkMap_bijective ρ S.composite hρ hμ hp
      c₀ f₀ d D cT₁ cB t hcoht hbij, ← hCd]
    exact hoff Cd hCdZ t ht
  refine ⟨S.last, hBi, instB, hBN, hBsm, inferInstance, p, inferInstance, inferInstance,
    inferInstance, hp, cB, R, ξ, cc * kk * j, G', hinj, hξ, hsnc,
    hcrep d₁ D₁ C₁ hC₁def hC₁Z, hcrep d₂ D₂ C₂ hC₂def hC₂Z,
    Nat.one_le_iff_ne_zero.mpr (by positivity), hG'eff, ?_, hampT⟩
  intro t ht
  obtain ⟨hbij, hcoht, hnZ⟩ := hstalk t ht
  have := smoothOverField_codimensionOne_stalk_DVR (K := K)
    (⟨S.composite (t : S.last), hcoht⟩ : CodimensionOnePoint T₁)
  have := smoothOverField_codimensionOne_stalk_DVR (K := K) t
  rw [hG'def, cartierCoefficient_add, cartierCoefficient_nsmul,
    cartierCoefficient_pullback_of_stalkMap_bijective S.composite t hcoht hbij,
    hoff F₁ hF₁Z t ht, hG0 _ hnZ]
  simp

end MixedFujita
