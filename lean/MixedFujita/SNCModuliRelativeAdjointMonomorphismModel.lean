/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCModuliCanonicalCartierMonomorphismModel
public import MixedFujita.RelativeAdjointCanonicalCartierMonomorphism
public import MixedFujita.SNCModuliRelativeAdjointModel

/-! Retain the same original-input SNC discriminant/moduli model and its actual
canonical Cartier monomorphism. Construct its exact integral relative adjoint
and all-multiple global monomorphisms with one fixed effective Cartier correction.
Only the original base's projectivity is used; the specified H stays arbitrary. -/

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

/-- The same model supplies all relative-adjoint multiples with one fixed
effective Cartier correction, retaining the original principal witness. -/
theorem exists_compatible_snc_moduli_models_with_relative_adjoint_monomorphisms
    (hProjY : ∃ A : CartierDivisor Y, CartierIsAmpleProj K A)
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
                                  (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ V) s₀)) ∧
                            ∃ C : CartierDivisor S.last, C.IsEffective ∧
                              (∀ β : CodimensionOnePoint S.last,
                                cartierCoefficient C (β : S.last) = R β) ∧
                              (∀ (V : S.last.Opens) [Nonempty V] (s₀ : Γ(E.sheaf, q ⁻¹ᵁ V)),
                                letI := dominant_preimage_nonempty q V
                                ∃! t : Γ(C.sheaf, V),
                                  (dominantFunctionFieldMap q).hom
                                    (rationalFunctionsEquiv (X := S.last) V
                                      (Scheme.Modules.Hom.app C.sheafι V t)) =
                                  rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ V)
                                    (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ V) s₀)) ∧
                              ∃ α : (Scheme.Modules.pushforward q).obj E.sheaf ⟶ C.sheaf,
                                Mono α ∧
                                (∀ V : S.last.Opens, Function.Injective (Scheme.Modules.Hom.app α V)) ∧
                                (∀ (V : S.last.Opens) [Nonempty V] (s₀ : Γ(E.sheaf, q ⁻¹ᵁ V)),
                                  letI := dominant_preimage_nonempty q V
                                  (dominantFunctionFieldMap q).hom
                                    (rationalFunctionsEquiv (X := S.last) V
                                      (Scheme.Modules.Hom.app C.sheafι V
                                        (Scheme.Modules.Hom.app α V s₀))) =
                                    rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ V)
                                      (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ V) s₀)) ∧
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
                                  (∀ j : ℕ,
                                    Nonempty ((j • ((d * m) • CM)).sheaf.restrict (S.composite ⁻¹ᵁ W).ι ≅
                                      ((Scheme.Modules.pushforward q).obj (j • L + E).sheaf).restrict
                                        (S.composite ⁻¹ᵁ W).ι)) ∧
                                  ∀ j : ℕ,
                                    ∃ β : (Scheme.Modules.pushforward q).obj (j • L + E).sheaf ⟶
                                        (j • ((d * m) • CM) + C).sheaf,
                                      Mono β ∧
                                      ∀ V : S.last.Opens, Function.Injective (Scheme.Modules.Hom.app β V) := by
  obtain ⟨W, hW, S, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
    hBft, hBqc, hBsep, cB, hnormB, hρ, hiso, rB, ξB, hinjB, hcodB, hsncB, hgood,
    T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj,
    hTft, hTqc, hTsep, hπ, cT, hkltT, rT, ξT, hinjT, hcodT, hsncT, hBT, hbT,
    q, hqdom, hqprop, hqover, hq, hqapp, hconnected, Δ, hΔ, hlt, hΔsupp,
    hQΔ, m, hm, CΔ, hCΔ, hkltB, M, hQM, hM, ℓ, hℓ, CM, hCM,
    hQ, hpull, hseparate, hlinear, hgen, E, hEff, hEc, hExc, hunit, hframe, htwists, R, hR, hReff, hdescWeil, C, hCeff, hCR, hdescC⟩ :=
    exists_compatible_snc_moduli_models_with_canonical_cartier_section_descent
      g hnormX hnormY happ cY c f d hd D heff hklt H s ψ hD
  letI := hunit
  let α := canonicalRoundupCartierHom q E hEff (S.composite ⁻¹ᵁ W) hgen C hdescC
  letI := canonicalRoundupCartierHom_mono q E hEff (S.composite ⁻¹ᵁ W) hgen C hdescC
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
  refine ⟨W, hW, S, hBi, instB, hBN, hBsm, hρdom, hρover, hρprop, hρproj,
    hBft, hBqc, hBsep, cB, hnormB, hρ, hiso, rB, ξB, hinjB, hcodB, hsncB, hgood,
    T, hTi, instT, hTN, hTsm, π, hπdom, hπover, hπprop, hπproj,
    hTft, hTqc, hTsep, hπ, cT, hkltT, rT, ξT, hinjT, hcodT, hsncT, hBT, hbT,
    q, hqdom, hqprop, hqover, hq, hqapp, hconnected, Δ, hΔ, hlt, hΔsupp,
    hQΔ, m, hm, CΔ, hCΔ, hkltB, M, hQM, hM, ℓ, hℓ, CM, hCM,
    hQ, hpull, hseparate, hlinear, hgen, E, hEff, hEc, hExc, hunit, hframe, htwists, R, hR, hReff, hdescWeil, C, hCeff, hCR, hdescC, α,
    canonicalRoundupCartierHom_mono q E hEff (S.composite ⁻¹ᵁ W) hgen C hdescC,
    canonicalRoundupCartierHom_app_injective q E hEff (S.composite ⁻¹ᵁ W) hgen C hdescC,
    canonicalRoundupCartierHom_field_pullback q E hEff (S.composite ⁻¹ᵁ W) hgen C hdescC,
    hProjB, hbase, L, rfl, hcrepant, hprincipal, hadjoint, ?_⟩
  intro j
  exact ⟨relativeAdjointMultipleCanonicalCartierHom hProjB q ((d * m) • CM) L E C
      ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m)) hprincipal α j,
    relativeAdjointMultipleCanonicalCartierHom_mono hProjB q ((d * m) • CM) L E C
      ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m)) hprincipal α j,
    relativeAdjointMultipleCanonicalCartierHom_app_injective hProjB q ((d * m) • CM) L E C
      ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m)) hprincipal α j⟩

end MixedFujita
