/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantRoundupDirectImageIso
public import MixedFujita.PrincipalizingSNCBaseSequence
public import MixedFujita.SNCSourceOverBaseSequence
public import MixedFujita.CompatibleSteinSNCModel

/-! Retain a principalizing base blow-up sequence and reuse the actual source
lift. Construct the changed Stein fibration and its genuine crepant roundup,
then compare its pushforward to the original base with the original direct
image. This is not a base-pullback comparison or a semipositivity theorem. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

variable {K : Type u} [Field K] [CharZero K] {n k : ℕ} {T B : Scheme.{u}}
  [IsIntegral T] [IsNoetherian T] [IsIntegral B] [IsNoetherian B] [IsRegular B]
  [T.Over (Spec (CommRingCat.of K))] [B.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of K))]
  [IsSeparated (T ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (B ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (B ↘ Spec (CommRingCat.of K))]
  [IsSeparated (B ↘ Spec (CommRingCat.of K))]

/-- Principalizing an actual ideal and lifting the source constructs a genuine
changed Stein fibration and its rounded direct-image pushforward comparison. -/
theorem exists_principalized_changed_stein_fibration_with_roundup_pushforward
    (q : T ⟶ B) [IsProper q] [IsDominant q] [q.IsOver (Spec (CommRingCat.of K))]
    (happ : ∀ U : B.Opens, Function.Bijective (q.app U).hom)
    (cB : EtaleChart K B k) (Z : Closeds B) (hZ : genericPoint B ∉ (Z : Set B))
    (I : B.IdealSheafData) (hIZ : (I.support : Set B) ⊆ (Z : Set B))
    (cT : EtaleChart K T n) (fT : T.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D E : CartierDivisor T) (hE : E.IsEffective) (hklt : LogPairIsKlt cT fT d D)
    (hEffN : LogPairBoundaryEffective cT fT d (D + d • E))
    (hKltN : LogPairIsKlt cT fT d (D + d • E)) :
    ∃ S : Scheme.BlowUpSequence B,
      (∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
        S.stageMap i.castSucc z ∈ (Z : Set B)) ∧
      ∃ (_ : IsIntegral S.last) (_ : S.last.Over (Spec (CommRingCat.of K)))
        (_ : IsNoetherian S.last)
        (_ : SmoothOfRelativeDimension k (S.last ↘ Spec (CommRingCat.of K)))
        (_ : IsDominant S.composite) (_ : S.composite.IsOver (Spec (CommRingCat.of K)))
        (_ : IsProper S.composite) (_ : IsProjective S.composite)
        (_ : LocallyOfFiniteType (S.last ↘ Spec (CommRingCat.of K)))
        (_ : QuasiCompact (S.last ↘ Spec (CommRingCat.of K)))
        (_ : IsSeparated (S.last ↘ Spec (CommRingCat.of K)))
        (cB₁ : EtaleChart K S.last k),
        Function.Bijective (dominantFunctionFieldAlgHom (K := K) S.composite) ∧
        IsIso (S.composite ∣_ Z.compl) ∧
        ∃ (rB : ℕ) (ξB : Fin rB → S.last), Function.Injective ξB ∧
          (∀ i, Order.coheight (ξB i) = 1) ∧ IsSNCFamily K k ξB ∧
          (∀ b : CodimensionOnePoint S.last, (b : S.last) ∉ Set.range ξB →
            S.composite (b : S.last) ∉ (Z : Set B)) ∧
          (I.comap S.composite).IsInvertible ∧
          ∃ (P : CartierDivisor S.last) (hP : P.IsEffective),
            effectiveCartierIdealSheaf P hP = I.comap S.composite ∧
            (∀ b : CodimensionOnePoint S.last, (b : S.last) ∉ Set.range ξB →
              cartierCoefficient P (b : S.last) = 0) ∧
            ∃ (T₁ : Scheme.{u}) (_ : IsIntegral T₁) (_ : T₁.Over (Spec (CommRingCat.of K)))
              (_ : IsNoetherian T₁)
              (_ : SmoothOfRelativeDimension n (T₁ ↘ Spec (CommRingCat.of K)))
              (τ : T₁ ⟶ T) (_ : IsDominant τ) (_ : τ.IsOver (Spec (CommRingCat.of K)))
              (_ : IsProper τ) (_ : IsProjective τ)
              (_ : LocallyOfFiniteType (T₁ ↘ Spec (CommRingCat.of K)))
              (_ : QuasiCompact (T₁ ↘ Spec (CommRingCat.of K)))
              (_ : IsSeparated (T₁ ↘ Spec (CommRingCat.of K)))
              (hτ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) τ))
              (cT₁ : EtaleChart K T₁ n) (rT : ℕ) (ξT : Fin rT → T₁),
              Function.Injective ξT ∧ (∀ i, Order.coheight (ξT i) = 1) ∧ IsSNCFamily K n ξT ∧
              (∀ t : CodimensionOnePoint T₁, (t : T₁) ∉ Set.range ξT →
                cartierCoefficient (crepantBoundaryCartier τ hτ cT fT d D cT₁ etaleCharts_cover)
                  (t : T₁) = 0) ∧
              LogPairIsKlt cT₁ (crepantPullbackFormUnit τ hτ cT fT cT₁) d (cartierPullback τ D) ∧
              ∃ (q₁ : T₁ ⟶ S.last) (_ : IsDominant q₁) (_ : IsProper q₁)
                (_ : q₁.IsOver (Spec (CommRingCat.of K))),
                q₁ ≫ S.composite = τ ≫ q ∧
                (∀ U : S.last.Opens, Function.Bijective (q₁.app U).hom) ∧
                (∀ b : S.last, ConnectedSpace (q₁.fiber b)) ∧
                ∃ (E₁ : CartierDivisor T₁) (_ : E₁.IsEffective),
                  (∀ t : CodimensionOnePoint T₁, cartierCoefficient E₁ (t : T₁) =
                    ⌈-((cartierCoefficient (crepantBoundaryCartier τ hτ cT fT d D cT₁ etaleCharts_cover)
                      (t : T₁) : ℝ) / (d : ℝ))⌉) ∧
                  Nonempty (E.sheaf ≅ (Scheme.Modules.pushforward τ).obj E₁.sheaf) ∧
                  Nonempty ((Scheme.Modules.pushforward q).obj E.sheaf ≅
                    (Scheme.Modules.pushforward S.composite).obj
                      ((Scheme.Modules.pushforward q₁).obj E₁.sheaf)) := by
  obtain ⟨S, hc, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
    hBft, hBqc, hBsep, cB₁, hρ, hiso, rB, ξB, hinjB, hcodB, hsncB, hoffB, hInv⟩ :=
    exists_principalizing_smooth_snc_base_sequence cB Z hZ I hIZ
  obtain ⟨P, hP, hPI, hP0⟩ := exists_effectiveCartier_of_invertibleIdeal_coefficient_of_overField
    (K := K) (I.comap S.composite) hInv
  have hPsupp : ∀ b : CodimensionOnePoint S.last, (b : S.last) ∉ Set.range ξB →
      cartierCoefficient P (b : S.last) = 0 := by
    intro b hb
    apply hP0 (b : S.last)
    rw [Scheme.IdealSheafData.support_comap]
    exact fun h => hoffB b hb (hIZ h)
  obtain ⟨T₁, hT₁i, instT₁, hT₁N, hT₁sm, τ, hτdom, hτover, hτprop, hτproj,
    hT₁ft, hT₁qc, hT₁sep, hτ, cT₁, rT, ξT, hinjT, hcodT, hsncT, hsuppT, _,
    q₁, hq₁dom, hq₁prop, hq₁over, hsquare⟩ :=
    exists_snc_source_model_over_base_sequence q S Z hc hZ cT fT d D
  haveI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  haveI : Smooth (S.last ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth k _
  haveI : Smooth (T₁ ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hnormB₁ : ∀ b : S.last, IsIntegrallyClosed (S.last.presheaf.stalk b) :=
    fun b => smooth_stalk_isIntegrallyClosed (K := K) b
  have hnormT₁ : ∀ t : T₁, IsIntegrallyClosed (T₁.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hcovT : CodimOneChartCovered n K T := by
    intro t _
    exact Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸ Opens.mem_top t)
  have happ₁ := stein_all_open_app_bijective_of_birational_square q τ S.composite q₁
    hnormT hnormB₁ (fun U => (happ U).2) hτ hρ hsquare
  have hiso₁ (U : S.last.Opens) : IsIso (q₁.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (happ₁ U)
  have hconnected := zariskiConnectednessStatement T₁ S.last q₁ hiso₁
  have hklt₁ := logPairIsKlt_crepant_pullback_without_properness τ hτ cT fT d hd D hklt cT₁
  have hb (t : CodimensionOnePoint T₁) :=
    logPairIsKlt_crepantBoundary_coefficient_lt τ hτ cT fT d D hklt cT₁ t
  obtain ⟨E₁, hE₁eff, hE₁⟩ := exists_effective_snc_boundary_roundup
    (crepantBoundaryCartier τ hτ cT fT d D cT₁ etaleCharts_cover) d hd
    ξT hinjT hcodT hsncT hsuppT (fun i => hb ⟨ξT i, hcodT i⟩)
  let e := normalizedCrepantRoundupPushforwardIso τ hτ hnormT hnormT₁ hcovT
    cT fT d hd D E hE hEffN hKltN cT₁ E₁ hE₁
  let ebase := normalizedCrepantRoundupBaseSquarePushforwardIso τ hτ hnormT hnormT₁ hcovT
    cT fT d hd D E hE hEffN hKltN cT₁ E₁ hE₁ q q₁ S.composite hsquare.symm
  exact ⟨S, hc, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
    hBft, hBqc, hBsep, cB₁, hρ, hiso, rB, ξB, hinjB, hcodB, hsncB, hoffB, hInv,
    P, hP, hPI, hPsupp, T₁, hT₁i, instT₁, hT₁N, hT₁sm, τ, hτdom, hτover, hτprop, hτproj,
    hT₁ft, hT₁qc, hT₁sep, hτ, cT₁, rT, ξT, hinjT, hcodT, hsncT, hsuppT, hklt₁,
    q₁, hq₁dom, hq₁prop, hq₁over, hsquare, happ₁, hconnected, E₁, hE₁eff, hE₁, ⟨e⟩, ⟨ebase⟩⟩

end MixedFujita
