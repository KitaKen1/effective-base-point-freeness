/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCModuliGenericRankOneModel
public import MixedFujita.CanonicalWeilSectionDescent

/-! Starting from the original effective normal klt Stein data and arbitrary
Cartier presentation, construct the same SNC discriminant/moduli model and
its finite canonical integer Weil divisor. Every actual roundup direct-image
section descends uniquely to an actual section of that Weil sheaf. The generic
unit frame, roundup, model and rational prime bounds are internal constructions.
No surjectivity onto the Weil sheaf, reflexivity or positivity is asserted. -/

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

/-- The original data internally supply the same fixed SNC moduli model,
canonical integer Weil divisor and unique actual Weil-section descent for
every roundup direct-image section on every nonempty base open. -/
theorem exists_compatible_snc_moduli_models_with_canonical_weil_section_descent
    (g : X ⟶ Y) [IsProper g] [IsDominant g] [g.IsOver (Spec (CommRingCat.of K))]
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
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
                          ∃ R : SchemeWeilDivisor S.last,
                            (∀ β : CodimensionOnePoint S.last, R β = ⌈-((Δ β : ℚ) : ℝ)⌉) ∧
                            0 ≤ R ∧
                            (letI : ∀ β : CodimensionOnePoint S.last,
                                IsDiscreteValuationRing (S.last.presheaf.stalk (β : S.last)) :=
                              fun β => by
                                letI := hnormB (β : S.last)
                                exact normal_codimensionOne_stalk_DVR β
                             ∀ (V : S.last.Opens) [Nonempty V] (s₀ : Γ(E.sheaf, q ⁻¹ᵁ V)),
                              letI := dominant_preimage_nonempty q V
                              ∃! t : Γ(SchemeWeilDivisor.sheaf R, V),
                                (dominantFunctionFieldMap q).hom
                                  (rationalFunctionsEquiv (X := S.last) V
                                    (Scheme.Modules.Hom.app (SchemeWeilDivisor.sheafι R) V t)) =
                                rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ V)
                                  (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ V) s₀)) := by
  obtain ⟨W, hW, S, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
    hBft, hBqc, hBsep, cB, hnormB, hρ, hiso, rB, ξB, hinjB, hcodB, hsncB, hgood,
    T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj,
    hTft, hTqc, hTsep, hπ, cT, hkltT, rT, ξT, hinjT, hcodT, hsncT, hBT, hbT,
    q, hqdom, hqprop, hqover, hq, hqapp, hconnected, Δ, hΔ, hlt, hΔsupp,
    hQΔ, m, hm, CΔ, hCΔ, hkltB, M, hQM, hM, ℓ, hℓ, CM, hCM,
    hQ, hpull, hseparate, hlinear, hgen, E, hEff, hEc, hExc, hunit, hframe, htwists⟩ :=
    exists_compatible_snc_moduli_models_with_generic_roundup_direct_image
      g hnormX hnormY happ cY c f d hd D heff hklt H s ψ hD
  let R : SchemeWeilDivisor S.last :=
    Δ.mapRange (fun z : ℚ => ⌈-((z : ℚ) : ℝ)⌉) (by norm_num)
  have hR (β : CodimensionOnePoint S.last) : R β = ⌈-((Δ β : ℚ) : ℝ)⌉ := by
    simp only [R, Finsupp.mapRange_apply]
  have hReff : 0 ≤ R := by
    intro β
    change 0 ≤ R β
    rw [hR]
    have hltR : ((Δ β : ℚ) : ℝ) < 1 := by exact_mod_cast hlt β
    have hceil := Int.le_ceil (-((Δ β : ℚ) : ℝ))
    by_contra hneg
    have hi : ⌈-((Δ β : ℚ) : ℝ)⌉ ≤ (-1 : ℤ) := by omega
    have hiR : (⌈-((Δ β : ℚ) : ℝ)⌉ : ℝ) ≤ -1 := by exact_mod_cast hi
    linarith
  refine ⟨W, hW, S, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
    hBft, hBqc, hBsep, cB, hnormB, hρ, hiso, rB, ξB, hinjB, hcodB, hsncB, hgood,
    T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj,
    hTft, hTqc, hTsep, hπ, cT, hkltT, rT, ξT, hinjT, hcodT, hsncT, hBT, hbT,
    q, hqdom, hqprop, hqover, hq, hqapp, hconnected, Δ, hΔ, hlt, hΔsupp,
    hQΔ, m, hm, CΔ, hCΔ, hkltB, M, hQM, hM, ℓ, hℓ, CM, hCM,
    hQ, hpull, hseparate, hlinear, hgen, E, hEff, hEc, hExc, hunit, hframe, htwists, R, hR, hReff, ?_⟩
  letI : ∀ β : CodimensionOnePoint S.last,
      IsDiscreteValuationRing (S.last.presheaf.stalk (β : S.last)) := fun β => by
    letI := hnormB (β : S.last)
    exact normal_codimensionOne_stalk_DVR β
  letI := hunit
  intro V hV s₀
  letI := dominant_preimage_nonempty q V
  apply cartier_direct_image_section_unique_weil_section_of_prime_bounds q E R V s₀
  obtain ⟨z, hz, -⟩ :=
    fixed_snc_direct_image_section_rational_descent_canonical_prime_bounds π hπ q hnormB
      c f d hd D cT hkltT ξT hinjT hcodT hsncT hBT E hEff hEc
      (S.composite ⁻¹ᵁ W) hgen V s₀
  refine ⟨z, hz.1, ?_⟩
  intro β hβV
  have hR' : R β =
      ⌈-(subKltBasePrimeDiscriminantCoefficients q hnormB cT
        (crepantPullbackFormUnit π hπ c f cT) d hd (cartierPullback π D) hkltT β)⌉ := by
    rw [hR, hΔ β]
    rw [← Rat.cast_neg, Rat.ceil_cast]
  simpa only [hR'] using hz.2 β hβV

end MixedFujita
