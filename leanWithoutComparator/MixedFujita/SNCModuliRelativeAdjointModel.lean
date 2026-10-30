/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCModuliGenericRankOneModel
public import MixedFujita.RelativeAdjointGenericDirectImage
public import MixedFujita.BlowUpSequenceAmpleModel
public import MixedFujita.SNCDiscriminantModuliCartierModel
public import MixedFujita.GenericDirectImageCartierTwists
public import MixedFujita.KltRoundupExceptional
public import MixedFujita.ExceptionalCartierPushforwardIso
public import MixedFujita.CompatibleSteinSNCDiscriminantSupportModel
public import MixedFujita.CrepantModuliPullbackPresentation
public import MixedFujita.SmoothSNCBaseSequence
public import MixedFujita.SNCSourceOverBaseSequence
public import MixedFujita.SNCWeilCartierMultiple
public import MixedFujita.ModifiedBaseDiscriminantWeilDivisor
public import MixedFujita.SmoothBaseBlowUpResolution
public import MixedFujita.SteinBirationalModelInvariance
public import MixedFujita.CompatibleSteinSNCModel

/-! From the original projective base and arbitrary Cartier presentation, retain
the same SNC discriminant/moduli model and its actual generic direct-image frame.
Clear the Cartier denominators to construct the actual relative adjoint, its exact
principal pullback presentation, and actual adjoint direct-image isomorphisms for
every further multiple, using the same rounded discrepancy divisor and generic open.
No global section or positivity of the moduli divisor is assumed. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n k : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [IsIntegral Y] [IsNoetherian Y]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

/-- The original base projectivity supplies an auxiliary ample divisor on the same
model. The actual moduli multiple and all its further multiples are identified with
the actual relative-adjoint-plus-rounding direct images on the same generic open. -/
theorem exists_compatible_snc_moduli_models_with_relative_adjoint_direct_images
    (g : X ⟶ Y) [IsProper g] [IsDominant g] [g.IsOver (Spec (CommRingCat.of K))]
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hProjY : ∃ A : CartierDivisor Y, CartierIsAmpleProj K A)
    (happ : ∀ U : Y.Opens, Function.Bijective (g.app U).hom)
    (cY : EtaleChart K Y k) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (heff : LogPairBoundaryEffective c f d D) (hklt : LogPairIsKlt c f d D)
    (H : CartierDivisor Y) (s : ℕ) (ψ : X.functionFieldˣ)
    (hD : D = s • cartierPullback g H + principalCartierDivisor X ψ) :
    ∃ (W : Y.Opens), genericPoint Y ∈ W ∧ ∃ S : Scheme.BlowUpSequence Y,
      ∃ (_ : IsIntegral S.last) (_ : S.last.Over (Spec (CommRingCat.of K)))
        (_ : IsNoetherian S.last)
        (_ : SmoothOfRelativeDimension k (S.last ↘ Spec (CommRingCat.of K)))
        (_ : IsDominant S.composite) (_ : S.composite.IsOver (Spec (CommRingCat.of K)))
        (_ : IsProper S.composite) (_ : IsProjective S.composite)
        (_ : LocallyOfFiniteType (S.last ↘ Spec (CommRingCat.of K)))
        (_ : QuasiCompact (S.last ↘ Spec (CommRingCat.of K)))
        (_ : IsSeparated (S.last ↘ Spec (CommRingCat.of K)))
        (cB : EtaleChart K S.last k)
        (hnormB : ∀ b : S.last, IsIntegrallyClosed (S.last.presheaf.stalk b)),
        Function.Bijective (dominantFunctionFieldAlgHom (K := K) S.composite) ∧
        IsIso (S.composite ∣_ W) ∧ ∃ (rB : ℕ) (ξB : Fin rB → S.last),
          Function.Injective ξB ∧ (∀ i, Order.coheight (ξB i) = 1) ∧ IsSNCFamily K k ξB ∧
          (∀ β : CodimensionOnePoint S.last, (β : S.last) ∉ Set.range ξB →
            S.composite (β : S.last) ∈ W) ∧
          ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
            (_ : IsNoetherian T)
            (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
            (π : T ⟶ X) (_ : IsDominant π) (_ : π.IsOver (Spec (CommRingCat.of K)))
            (_ : IsProper π) (_ : IsProjective π)
            (_ : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K)))
            (_ : QuasiCompact (T ↘ Spec (CommRingCat.of K)))
            (_ : IsSeparated (T ↘ Spec (CommRingCat.of K)))
            (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
            (cT : EtaleChart K T n)
            (hkltT : LogPairIsKlt cT (crepantPullbackFormUnit π hπ c f cT) d (cartierPullback π D))
            (rT : ℕ) (ξT : Fin rT → T),
            Function.Injective ξT ∧ (∀ i, Order.coheight (ξT i) = 1) ∧ IsSNCFamily K n ξT ∧
            (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
              cartierCoefficient (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover)
                (t : T) = 0) ∧
            (∀ i, cartierCoefficient (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover)
              (ξT i) < (d : ℤ)) ∧
            ∃ (q : T ⟶ S.last) (_ : IsDominant q) (_ : IsProper q)
              (_ : q.IsOver (Spec (CommRingCat.of K))), q ≫ S.composite = π ≫ g ∧
              (∀ V : S.last.Opens, Function.Bijective (q.app V).hom) ∧
              (∀ b : S.last, ConnectedSpace (q.fiber b)) ∧
              ∃ Δ : CodimensionOnePoint S.last →₀ ℚ,
                (∀ β, Δ β = subKltBasePrimeDiscriminantCoefficients q hnormB cT
                  (crepantPullbackFormUnit π hπ c f cT) d hd (cartierPullback π D) hkltT β) ∧
                (∀ β, Δ β < 1) ∧
                (∀ β : CodimensionOnePoint S.last, (β : S.last) ∉ Set.range ξB → Δ β = 0) ∧
                ∃ hQΔ : OAI.RelativeDenominators.IsQCartier S.last Δ,
                ∃ (m : ℕ), 0 < m ∧ ∃ CΔ : CartierDivisor S.last,
                  (∀ β : CodimensionOnePoint S.last,
                    (cartierCoefficient CΔ (β : S.last) : ℚ) = (m : ℚ) * Δ β) ∧
                  LogPairIsKlt cB 1 m
                    (m • (smoothCanonicalDivisor cB + principalCartierDivisor S.last 1) + CΔ) ∧
                  ∃ (M : CodimensionOnePoint S.last →₀ ℚ)
                    (hQM : OAI.RelativeDenominators.IsQCartier S.last M),
                    M = moduliWeilPart (smoothCanonicalDivisor cB) (cartierPullback S.composite H)
                      Δ ((s : ℚ) / (d : ℚ)) ∧
                    ∃ (ℓ : ℕ), 0 < ℓ ∧ ∃ CM : CartierDivisor S.last,
                      (∀ β : CodimensionOnePoint S.last,
                        (cartierCoefficient CM (β : S.last) : ℚ) = (ℓ : ℚ) * M β) ∧
                      ∃ hQ : OAI.RelativeDenominators.IsQCartier S.last
                          (rationalCartierWeilDivisor (smoothCanonicalDivisor cB) + Δ + M),
                        OAI.RelativeDenominators.pullbackQCartier hnormB q
                          (rationalCartierWeilDivisor (smoothCanonicalDivisor cB) + Δ + M) hQ =
                          ((s : ℚ) / (d : ℚ)) • rationalCartierWeilDivisor
                            (cartierPullback q (cartierPullback S.composite H)) ∧
                        OAI.RelativeDenominators.pullbackQCartier hnormB q
                          (rationalCartierWeilDivisor (smoothCanonicalDivisor cB) + Δ + M) hQ =
                          rationalCartierWeilDivisor (cartierPullback q (smoothCanonicalDivisor cB)) +
                            OAI.RelativeDenominators.pullbackQCartier hnormB q Δ hQΔ +
                            OAI.RelativeDenominators.pullbackQCartier hnormB q M hQM ∧
                        OAI.RelativeDenominators.RationallyLinearlyEquivalent T
                          (rationalCartierWeilDivisor (smoothCanonicalDivisor cT +
                            principalCartierDivisor T (crepantPullbackFormUnit π hπ c f cT)) +
                            (1 / (d : ℚ)) • rationalCartierWeilDivisor
                              (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover))
                          (OAI.RelativeDenominators.pullbackQCartier hnormB q
                            (rationalCartierWeilDivisor (smoothCanonicalDivisor cB) + Δ + M) hQ) ∧
                        genericPoint S.last ∈ S.composite ⁻¹ᵁ W ∧
                        ∃ (E : CartierDivisor T) (hEff : E.IsEffective),
                          (∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
                            ⌈-((cartierCoefficient
                              (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover)
                              (t : T) : ℝ) / (d : ℝ))⌉) ∧
                          (∀ t : CodimensionOnePoint T, Order.coheight (π (t : T)) = 1 →
                            cartierCoefficient E (t : T) = 0) ∧
                          IsIso ((effectiveCartierPushforwardUnitMap q E hEff).over
                            (S.composite ⁻¹ᵁ W)) ∧
                          Nonempty (((Scheme.Modules.pushforward q).obj E.sheaf).restrict
                            (S.composite ⁻¹ᵁ W).ι ≅
                            SheafOfModules.unit ((S.composite ⁻¹ᵁ W) : Scheme).ringCatSheaf) ∧
                          (∀ A : CartierDivisor S.last,
                            Nonempty (A.sheaf.restrict (S.composite ⁻¹ᵁ W).ι ≅
                              ((Scheme.Modules.pushforward q).obj
                                ((Scheme.Modules.pullback q).obj A.sheaf ⊗ E.sheaf)).restrict
                                  (S.composite ⁻¹ᵁ W).ι)) ∧
                          (∃ A : CartierDivisor S.last, CartierIsAmpleProj K A) ∧
                          (d * m) • CM = (ℓ * m * s) • cartierPullback S.composite H -
                            (d * m * ℓ) • smoothCanonicalDivisor cB - (d * ℓ) • CΔ ∧
                          ∃ L : CartierDivisor T,
                            L = relativeAdjointCartier π q D (smoothCanonicalDivisor cB) CΔ d m ℓ ∧
                            L = (ℓ * m) • (d • (smoothCanonicalDivisor cT +
                              principalCartierDivisor T (crepantPullbackFormUnit π hπ c f cT)) +
                              crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover) -
                              (d * m * ℓ) • cartierPullback q (smoothCanonicalDivisor cB) -
                              (d * ℓ) • cartierPullback q CΔ ∧
                            L = cartierPullback q ((d * m) • CM) +
                              principalCartierDivisor T
                                ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m)) ∧
                            ∀ j : ℕ,
                              Nonempty ((j • ((d * m) • CM)).sheaf.restrict (S.composite ⁻¹ᵁ W).ι ≅
                                ((Scheme.Modules.pushforward q).obj (j • L + E).sheaf).restrict
                                  (S.composite ⁻¹ᵁ W).ι) := by
  obtain ⟨W, hW, S, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
      hBft, hBqc, hBsep, cB, hnormB, hρ, hiso, rB, ξB, hinjB, hcodB, hsncB, hgood,
      T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj,
      hTft, hTqc, hTsep, hπ, cT, hkltT, rT, ξT, hinjT, hcodT, hsncT, hBT, hbT,
      q, hqdom, hqprop, hqover, hq, hqapp, hconnected, Δ, hΔ, hlt, hΔsupp,
      hQΔ, m, hm, CΔ, hCΔ, hkltB, M, hQM, hM, ℓ, hℓ, CM, hCM,
      hQ, hpull, hseparate, hlinear, hgen, E, hEff, hEc, hExc, hunit, hframe, htwists⟩ :=
    exists_compatible_snc_moduli_models_with_generic_roundup_direct_image
      g hnormX hnormY happ cY c f d hd D heff hklt H s ψ hD
  have hProjB := blowUpSequence_exists_ample_cartier hProjY S
  have hCM' : ∀ β : CodimensionOnePoint S.last,
      (cartierCoefficient CM (β : S.last) : ℚ) = (ℓ : ℚ) *
        moduliWeilPart (smoothCanonicalDivisor cB) (cartierPullback S.composite H) Δ
          ((s : ℚ) / (d : ℚ)) β := by
    intro β
    rw [← hM]
    exact hCM β
  have hbase := moduli_cartier_integral_presentation hnormB (smoothCanonicalDivisor cB)
    (cartierPullback S.composite H) CΔ CM Δ d (by omega) m ℓ s hCΔ hCM'
  let L := relativeAdjointCartier π q D (smoothCanonicalDivisor cB) CΔ d m ℓ
  have hcrepant := relative_adjoint_cartier_crepant_expression π hπ q c f cT D
    (smoothCanonicalDivisor cB) CΔ d m ℓ
  have hprincipal : L = cartierPullback q ((d * m) • CM) +
      principalCartierDivisor T
        ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m)) := by
    rw [cartierPullback_nsmul]
    exact relative_adjoint_cartier_principal_presentation π g S.composite q hq hnormB
      D H (smoothCanonicalDivisor cB) CΔ CM Δ d (by omega) m ℓ s ψ hD hCΔ hCM'
  have hadjoint : ∀ j : ℕ,
      Nonempty ((j • ((d * m) • CM)).sheaf.restrict (S.composite ⁻¹ᵁ W).ι ≅
        ((Scheme.Modules.pushforward q).obj (j • L + E).sheaf).restrict
          (S.composite ⁻¹ᵁ W).ι) := fun j =>
    ⟨relativeAdjointMultipleDirectImageIso hProjB q (S.composite ⁻¹ᵁ W) ((d * m) • CM)
      L E ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m))
      hprincipal htwists j⟩
  exact ⟨W, hW, S, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
    hBft, hBqc, hBsep, cB, hnormB, hρ, hiso, rB, ξB, hinjB, hcodB, hsncB, hgood,
    T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj,
    hTft, hTqc, hTsep, hπ, cT, hkltT, rT, ξT, hinjT, hcodT, hsncT, hBT, hbT,
    q, hqdom, hqprop, hqover, hq, hqapp, hconnected, Δ, hΔ, hlt, hΔsupp,
    hQΔ, m, hm, CΔ, hCΔ, hkltB, M, hQM, hM, ℓ, hℓ, CM, hCM,
    hQ, hpull, hseparate, hlinear, hgen, E, hEff, hEc, hExc, hunit, hframe, htwists,
    hProjB, hbase, L, rfl, hcrepant, hprincipal, hadjoint⟩

end MixedFujita
